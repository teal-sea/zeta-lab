"""Shared instruments for hunts/rh_claim_statements: balls, a branch-and-bound
supremum, sieves, finite fields. Nothing here reads the archive.

Conventions. Every Arb computation runs under an explicit working precision
(`with ctx.workprec(bits)`), taken from the claim's parameters times the
runner's precision scale. A float returned from a ball is an outward-rounded
bound, never a midpoint, unless the name says `mid`.
"""
from __future__ import annotations

import heapq
import math
from fractions import Fraction

import numpy as np
from flint import acb, arb, ctx, fmpq

PREC_SCALE = 1          # the runner sets this for the precision-response rerun


def bits(params, default=64):
    return int(params.get("prec", default)) * PREC_SCALE


def A(x):
    """Exact arb from an int, a Fraction or a decimal string such as '126/100'."""
    if isinstance(x, arb):
        return x
    if isinstance(x, int):
        return arb(x)
    if isinstance(x, Fraction):
        return arb(fmpq(x.numerator, x.denominator))
    if isinstance(x, str):
        return A(Fraction(x))
    if isinstance(x, float):
        return arb(x)            # a double is an exact dyadic rational
    raise TypeError(type(x))


def Q(x):
    return x if isinstance(x, Fraction) else Fraction(x)


def ball(lo, hi):
    """A real ball containing [lo, hi] (floats); inflated against float rounding."""
    mid = 0.5 * (lo + hi)
    rad = 0.5 * (hi - lo)
    if rad == 0.0:
        return arb(mid)
    rad += 4e-16 * max(abs(lo), abs(hi)) + 1e-300
    return arb(mid, rad)


def up(x):
    """Float upper bound of a real ball (inf when the ball is not finite)."""
    if not x.is_finite():
        return math.inf
    m = float(x.mid()); r = float(x.rad())
    return m + r + 2e-15 * abs(m) + 1e-300


def lo(x):
    if not x.is_finite():
        return -math.inf
    m = float(x.mid()); r = float(x.rad())
    return m - r - 2e-15 * abs(m) - 1e-300


def certainly_lt(a, b):
    """True only when every point of ball a is below every point of ball b."""
    return bool(a < b)


def certainly_le(a, b):
    return bool(a <= b)


# ---------------------------------------------------------------------------
# branch and bound for a supremum
# ---------------------------------------------------------------------------

def sup_bnb(f, boxes, tol=1e-3, max_boxes=200000, stop_above=None, min_width=1e-13, probes=None):
    """Enclose sup f over a union of boxes.

    f(box) returns a real ball enclosing f on the box, box a tuple of (lo, hi)
    float pairs; a pair with lo == hi is a point. The result carries
    `hi`, an upper bound valid on the WHOLE union (every box is either bounded
    or split into boxes that are), and `lo`, a lower bound attained at a
    computed point `argmax`. `tight` says whether hi - lo <= tol was reached.
    With `stop_above`, the search returns as soon as a point value certainly
    exceeds it (a counterexample to "f <= stop_above"). `probes(box)` lists
    extra points at which f is sampled for the lower bound (the midpoint is
    always sampled).
    """
    best_lo, arg = -math.inf, None
    heap = []
    n = 0

    def visit(box):
        nonlocal best_lo, arg, n
        n += 1
        pts = [tuple(0.5 * (a + b) for a, b in box)]
        if probes is not None:
            pts += probes(box)
        for pt in pts:
            v = lo(f(tuple((x, x) for x in pt)))
            if v > best_lo:
                best_lo, arg = v, list(pt)
        u = up(f(box))
        if u > best_lo:
            heapq.heappush(heap, (-u, n, box))

    for b in boxes:
        visit(tuple(b))
    while heap:
        if stop_above is not None and best_lo > stop_above:
            return dict(lo=best_lo, hi=math.inf, argmax=arg, boxes=n, tight=False, stopped=True)
        negu, _, box = heapq.heappop(heap)
        u = -negu
        if u <= best_lo + tol:
            # everything left in the heap has upper bound <= u
            return dict(lo=best_lo, hi=max(u, best_lo), argmax=arg, boxes=n, tight=True, stopped=False)
        widths = [b - a for a, b in box]
        k = max(range(len(box)), key=lambda i: widths[i])
        if n >= max_boxes or widths[k] <= min_width:
            return dict(lo=best_lo, hi=u, argmax=arg, boxes=n, tight=False, stopped=False)
        a, b = box[k]
        m = 0.5 * (a + b)
        for part in ((a, m), (m, b)):
            visit(box[:k] + (part,) + box[k + 1:])
    if stop_above is not None and best_lo > stop_above:
        return dict(lo=best_lo, hi=math.inf, argmax=arg, boxes=n, tight=False, stopped=True)
    return dict(lo=best_lo, hi=best_lo, argmax=arg, boxes=n, tight=True, stopped=False)


def verdict_from_sup(res, bound=1.0):
    """True if sup <= bound on the whole cover, False if a point exceeds it, None otherwise."""
    if res["lo"] > bound:
        return False
    if res["hi"] <= bound:
        return True
    return None


def grid(lo_, hi_, n):
    """n dyadic-friendly boxes covering [lo_, hi_]."""
    step = (hi_ - lo_) / n
    return [(lo_ + i * step, lo_ + (i + 1) * step if i < n - 1 else hi_) for i in range(n)]


def boxes2(xr, yr, nx, ny):
    return [(a, b) for a in grid(*xr, nx) for b in grid(*yr, ny)]


def cball(box):
    """Complex ball from a 2D box ((re_lo, re_hi), (im_lo, im_hi))."""
    return acb(ball(*box[0]), ball(*box[1]))


def absup(z):
    return up(z.abs_upper())


def abslo(z):
    return max(0.0, lo(z.abs_lower()))


# ---------------------------------------------------------------------------
# Taylor model with a Cauchy remainder: tight enclosures on wide complex balls
# ---------------------------------------------------------------------------

def taylor_ball(series_at, crude_abs, S, order=6, grow=6.0, arcs=12, poles=(), rmin=0.05):
    """Enclose an analytic f and f' on the complex ball S.

    Arb's zeta and L-functions lose most of their accuracy on a wide input
    ball (the partial sums are bounded term by term), so f is expanded at the
    exact centre c of S: f(c + h) = sum a_k h^k. If |f| <= M on the circle of
    radius R about c (R = max(grow * r, rmin), r the radius of S, shrunk to
    half the distance to the nearest pole) and f is analytic inside, the
    maximum principle and Cauchy's estimate give |a_k| <= M / R^k, hence
        |sum_{k>=n} a_k h^k| <= M x^n / (1 - x),                    x = r/R,
        |sum_{k>=n} k a_k h^(k-1)| <= (M/R) (n x^(n-1)/(1-x) + x^n/(1-x)^2).
    `series_at(c, n)` returns a_0..a_{n-1} as balls. `crude_abs(B)` returns a
    float upper bound of |f| on a small ball B, or inf; M is the largest value
    over `arcs` balls covering the circle. Analyticity inside the circle is the
    caller's statement: every pole of f is listed in `poles` as (re, im), and a
    disc reaching one is refused (for zeta: s = 1; entire functions: the empty
    `poles` list). None is returned when a pole lies in the disc or M is not
    finite: split the box.
    """
    cx, cy = S.real.mid(), S.imag.mid()
    rx, ry = up(S.real.rad()), up(S.imag.rad())
    c = acb(cx, cy)
    r = math.hypot(rx, ry) * (1 + 1e-12)
    if r == 0.0:
        a = series_at(c, 2)
        return a[0], a[1]
    R = max(grow * r, rmin)                 # a small box still uses a disc of radius rmin
    for px, py in poles:
        dist = math.hypot(float(cx) - px, float(cy) - py)
        R = min(R, 0.5 * dist)
    if R < 3.0 * r:                         # a pole too close for a useful remainder
        return None
    half = R * math.pi / arcs * (1 + 1e-9)           # an arc of half-angle pi/arcs fits this square
    def crude(B, depth):
        v = crude_abs(B)
        if math.isfinite(v) or depth == 0:
            return v
        bx, by = B.real.mid(), B.imag.mid()
        q = up(B.real.rad()) / 2
        return max(crude(acb(bx + arb(sx * q, q), by + arb(sy * q, q)), depth - 1)
                   for sx in (-1, 1) for sy in (-1, 1))

    M = 0.0
    for j in range(arcs):
        th = 2 * math.pi * (j + 0.5) / arcs
        M = max(M, crude(acb(cx + arb(R * math.cos(th), half), cy + arb(R * math.sin(th), half)), 3))
        if not math.isfinite(M):
            return None
    a = list(series_at(c, order))
    order = len(a)                          # python-flint caps a series at ctx.cap terms
    if order < 2:
        return None
    h = acb(arb(0, rx), arb(0, ry))
    val, der = acb(0), acb(0)
    for k in range(order - 1, -1, -1):
        val = val * h + a[k]
    for k in range(order - 1, 0, -1):
        der = der * h + k * a[k]
    x = r / R * (1 + 1e-12)
    rem = M * x ** order / (1 - x) * (1 + 1e-12)
    remd = (M / R) * (order * x ** (order - 1) / (1 - x) + x ** order / (1 - x) ** 2) * (1 + 1e-12)
    val += acb(arb(0, rem), arb(0, rem))
    der += acb(arb(0, remd), arb(0, remd))
    return val, der


# ---------------------------------------------------------------------------
# arithmetic tables
# ---------------------------------------------------------------------------

_SIEVE = {}


def prime_mask(n):
    """Boolean numpy array, mask[k] is True iff k is prime, for 0 <= k <= n."""
    if n not in _SIEVE:
        m = np.ones(n + 1, dtype=bool)
        m[:2] = False
        for p in range(2, int(n ** 0.5) + 1):
            if m[p]:
                m[p * p::p] = False
        _SIEVE.clear()
        _SIEVE[n] = m
    return _SIEVE[n]


def primes_upto(n):
    return np.flatnonzero(prime_mask(n))


def is_prime_small(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def factorint(n):
    """Trial-division factorisation {p: e} for n >= 1 (own code, small n)."""
    out = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def totient(n):
    if n == 0:
        return 0                      # Nat.totient 0 = 0
    r = n
    for p in factorint(n):
        r = r // p * (p - 1)
    return r


def totient_sieve(n):
    phi = np.arange(n + 1, dtype=np.int64)
    for p in primes_upto(n):
        phi[p::p] -= phi[p::p] // p
    return phi


def omega_sieve(n):
    w = np.zeros(n + 1, dtype=np.int64)
    for p in primes_upto(n):
        w[p::p] += 1
    return w


def prime_power_base(n):
    """p if n = p^k with k >= 1, else None (so vonMangoldt n = log p or 0)."""
    if n < 2:
        return None
    f = factorint(n)
    return next(iter(f)) if len(f) == 1 else None


def padic_val(p, n):
    """padicValNat p n with Lean's junk values: 0 if n = 0 or p = 1."""
    if n == 0 or p <= 1:
        return 0
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def nat_log(b, n):
    """Nat.log b n: 0 if b <= 1 or n = 0, else the largest k with b^k <= n."""
    if b <= 1 or n == 0:
        return 0
    k = 0
    while n >= b:
        n //= b
        k += 1
    return k


def monus(a, b):
    """Truncated subtraction on the naturals."""
    return a - b if a >= b else 0


def kronecker(a, n):
    """Kronecker symbol (a/n) for n >= 1, own implementation."""
    assert n >= 1
    if n == 1:
        return 1
    res = 1
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    if v:
        if a % 2 == 0:
            return 0
        if v % 2 == 1 and a % 8 in (3, 5):
            res = -res
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a %= n
    return res if n == 1 else 0


def is_fundamental(d):
    if d == 1:
        return True
    if d % 4 == 1:
        return all(e == 1 for e in factorint(abs(d)).values())
    if d % 4 == 0:
        m = d // 4
        return m % 4 in (2, 3) and all(e == 1 for e in factorint(abs(m)).values())
    return False


# ---------------------------------------------------------------------------
# finite fields GF(p^e) as integer-coded tables
# ---------------------------------------------------------------------------

class GF:
    """GF(p^e), elements coded 0..q-1 by base-p digits of the polynomial."""

    def __init__(self, p, e):
        self.p, self.e, self.q = p, e, p ** e
        q = self.q
        digs = np.array([[(x // p ** i) % p for i in range(e)] for x in range(q)])
        self.digs = digs
        code = lambda d: int(sum(int(d[i]) * p ** i for i in range(e)))
        self.add = np.array([[code((digs[a] + digs[b]) % p) for b in range(q)] for a in range(q)])
        self.neg = np.array([code((-digs[a]) % p) for a in range(q)])
        if e == 1:
            self.mul = np.array([[(a * b) % p for b in range(q)] for a in range(q)])
            self.modulus = None
        else:
            self.modulus = self._irreducible()
            self.mul = np.array([[code(self._polymul(digs[a], digs[b])) for b in range(q)] for a in range(q)])
        # sanity: a field has no zero divisors and 1 is the unit
        assert all(self.mul[1][a] == a for a in range(q))
        assert all((self.mul[a][1:] != 0).all() for a in range(1, q))

    def _irreducible(self):
        p, e = self.p, self.e
        assert e in (2, 3), "irreducibility by absence of roots needs degree <= 3"
        for c in range(p ** e):
            coeffs = [(c // p ** i) % p for i in range(e)] + [1]     # monic, low degree first
            if all(sum(co * pow(x, i, p) for i, co in enumerate(coeffs)) % p for x in range(p)):
                return coeffs
        raise RuntimeError("no irreducible polynomial found")

    def _polymul(self, a, b):
        p, e, m = self.p, self.e, self.modulus
        prod = [0] * (2 * e - 1)
        for i in range(e):
            for j in range(e):
                prod[i + j] = (prod[i + j] + int(a[i]) * int(b[j])) % p
        for k in range(2 * e - 2, e - 1, -1):
            c = prod[k]
            if c:
                for i in range(e + 1):
                    prod[k - e + i] = (prod[k - e + i] - c * m[i]) % p
        return prod[:e]

    def power(self, a, n):
        r = 1
        while n:
            if n & 1:
                r = int(self.mul[r][a])
            a = int(self.mul[a][a])
            n >>= 1
        return r

    def convolve(self, f, g):
        """Additive convolution of two integer count vectors indexed by field elements."""
        q = self.q
        out = [0] * q
        for a in range(q):
            if f[a]:
                row = self.add[a]
                for b in range(q):
                    if g[b]:
                        out[row[b]] += f[a] * g[b]
        return out


def result(holds, cases, margin=None, tightest=None, sharp=None, slack=None, notes=None, **extra):
    """Uniform record. holds: True (no violation, in the grade's sense), False
    (a rigorous counterexample, see `witness`), None (undecided somewhere)."""
    d = dict(holds=holds, cases=cases, margin=margin, tightest=tightest,
             sharp_constant=sharp, slack=slack, notes=notes)
    d.update(extra)
    return d
