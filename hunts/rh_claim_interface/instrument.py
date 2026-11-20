"""Instruments for hunt #161: the smoothed von Mangoldt sums G, Gchi and Gm.

The definitions are transcribed from a posted Lean archive (see MISSION.md for
the quoted lines and the tarball hash).  In plain mathematics, for real y >= 1:

    G(y)    = sum_{n<=y} Lambda(n) (y/n - 1) - y log y + (1 + gamma) y
    Gchi(y) = sum_{n<=y} Lambda(n) chi(n) (y/n - 1) + y L'/L(1, chi)   (chi != 1)
    Gm(y)   = G(y) + (3o+1)^-1 sum_{k=1}^{o-1} Re Gchi_{(chi^k)*}(y)

where chi is primitive of order o and (chi^k)* is the primitive character
inducing chi^k.

Two routes are kept apart on purpose.

* The float route (numpy, float64) is for scanning.  It never forms the large
  cancelling terms y*A(n) and y log y.  With

      E(n) = sum_{m<=n} Lambda(m)/m - log n + gamma,   R(n) = psi(n) - n,

  one has, for n <= y < n+1,

      G(y) = y E(n) - y log(y/n) + (y - n) - R(n),   so   G(n) = n E(n) - R(n).

* The Arb route (python-flint, precision set explicitly by the caller) carries
  an enclosure through every step and is the one every reported number comes
  from.

Nothing in this file is a statement about the zeros of zeta.  It evaluates
finite sums.
"""

from __future__ import annotations

import math
from fractions import Fraction
from math import gcd

import numpy as np

EULER_GAMMA = 0.57721566490153286
LOG_2PI = math.log(2.0 * math.pi)
#: c0 = sum over nontrivial zeros of 1/(rho (1 - rho)) = 2 + gamma - log(4 pi).
C0 = 2.0 + EULER_GAMMA - math.log(4.0 * math.pi)


# ---------------------------------------------------------------------------
# sieve
# ---------------------------------------------------------------------------


def small_primes(n: int) -> np.ndarray:
    """Primes <= n by a plain sieve."""
    n = int(n)
    if n < 2:
        return np.zeros(0, dtype=np.int64)
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, math.isqrt(n) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.nonzero(s)[0].astype(np.int64)


def segment_primes(lo: int, hi: int, base: np.ndarray) -> np.ndarray:
    """Primes p with lo <= p < hi.  `base` must hold every prime <= sqrt(hi)."""
    lo = max(int(lo), 2)
    hi = int(hi)
    if hi <= lo:
        return np.zeros(0, dtype=np.int64)
    flags = np.ones(hi - lo, dtype=bool)
    for p in base.tolist():
        if p * p >= hi:
            break
        start = max(p * p, ((lo + p - 1) // p) * p)
        flags[start - lo :: p] = False
    return np.nonzero(flags)[0].astype(np.int64) + lo


def lambda_segment(lo: int, hi: int, base: np.ndarray) -> np.ndarray:
    """Lambda(n) as float64 for lo <= n < hi (prime powers included)."""
    lo = int(lo)
    hi = int(hi)
    lam = np.zeros(hi - lo, dtype=np.float64)
    pr = segment_primes(lo, hi, base)
    lam[pr - lo] = np.log(pr.astype(np.float64))
    for p in base.tolist():
        if p * p >= hi:
            break
        lp = math.log(p)
        pk = p * p
        while pk < hi:
            if pk >= lo:
                lam[pk - lo] = lp
            pk *= p
    return lam


def prime_powers_upto(n: int) -> list[tuple[int, int]]:
    """Sorted list of (p^k, p) with p^k <= n."""
    out = []
    for p in small_primes(n).tolist():
        pk = p
        while pk <= n:
            out.append((pk, p))
            pk *= p
    out.sort()
    return out


# ---------------------------------------------------------------------------
# the elementary correction terms
# ---------------------------------------------------------------------------


def T_float(y):
    """T(y) = -sum_{k>=1} y^(-2k) / (2k (2k+1)), the trivial-zero term (even case).

    Closed form for y > 1: (1/2) log(1 - y^-2) + (y/2) log((y+1)/(y-1)) - 1,
    and T(1) = log 2 - 1.
    """
    y = np.asarray(y, dtype=np.float64)
    out = np.empty_like(y)
    big = y >= 6.0
    yb = y[big]
    x2 = 1.0 / (yb * yb)
    acc = np.zeros_like(yb)
    for k in range(12, 0, -1):
        acc = (acc + 1.0 / (2 * k * (2 * k + 1))) * x2
    out[big] = -acc
    small = ~big
    ys = y[small]
    with np.errstate(divide="ignore", invalid="ignore"):
        val = 0.5 * np.log1p(-1.0 / (ys * ys)) + 0.5 * ys * np.log((ys + 1.0) / (ys - 1.0)) - 1.0
    val = np.where(ys == 1.0, math.log(2.0) - 1.0, val)
    out[small] = val
    return out if out.ndim else float(out)


def T_odd_float(y):
    """T_odd(y) = -sum_{k>=1} y^-(2k-1) / ((2k-1) 2k), the trivial-zero term (odd case).

    Closed form for y > 1: -(artanh(1/y) + (y/2) log(1 - y^-2)); T_odd(1) = -log 2.
    """
    y = np.asarray(y, dtype=np.float64)
    with np.errstate(divide="ignore", invalid="ignore"):
        val = -(np.arctanh(1.0 / y) + 0.5 * y * np.log1p(-1.0 / (y * y)))
    val = np.where(y == 1.0, -math.log(2.0), val)
    return val if val.ndim else float(val)


# ---------------------------------------------------------------------------
# float route
# ---------------------------------------------------------------------------


def G_float(y: float) -> float:
    """G(y) by direct summation in float64 with exactly rounded sums.

    Meant for small y (tests, spot checks); the scan uses `scan_integers`.
    """
    y = float(y)
    if y < 1.0:
        return -y * math.log(y) + (1.0 + EULER_GAMMA) * y
    n = int(math.floor(y))
    terms = [math.log(p) * (y / pk - 1.0) for pk, p in prime_powers_upto(n)]
    return math.fsum(terms) - y * math.log(y) + (1.0 + EULER_GAMMA) * y


def scan_integers(y_max: int, seg: int = 1 << 24, start_state=None):
    """Yield (n, E, R, lam) blocks covering 2 <= n <= y_max.

    n is a float64 array of consecutive integers, E and R are float64 arrays of
    E(n) and R(n), lam is Lambda(n).  The running values are carried between
    blocks in extended precision so that block boundaries add no rounding of
    their own.  G(n) = n*E - R.
    """
    y_max = int(y_max)
    base = small_primes(math.isqrt(y_max) + 2)
    e_run = np.longdouble(EULER_GAMMA)  # E(1) = gamma
    r_run = np.longdouble(-1.0)  # R(1) = psi(1) - 1
    lo = 2
    if start_state is not None:
        lo, e_run, r_run = start_state
    while lo <= y_max:
        hi = min(lo + seg, y_max + 1)
        lam = lambda_segment(lo, hi, base)
        n = np.arange(lo, hi, dtype=np.float64)
        d_e = lam / n + np.log1p(-1.0 / n)
        d_r = lam - 1.0
        ce = np.cumsum(d_e, dtype=np.longdouble)
        cr = np.cumsum(d_r, dtype=np.longdouble)
        e_arr = (e_run + ce).astype(np.float64)
        r_arr = (r_run + cr).astype(np.float64)
        e_run = e_run + ce[-1]
        r_run = r_run + cr[-1]
        yield n, e_arr, r_arr, lam
        lo = hi


def F_from_ER(n, e_arr, r_arr):
    """F(n) = (G(n) - log 2pi - T(n)) / sqrt(n) from the scan state."""
    return (n * e_arr - r_arr - LOG_2PI - T_float(n)) / np.sqrt(n)


def _T_prime_float(y: float) -> float:
    """T'(y) = T(y)/y - log(1 - y^-2)/(2y), from T(y) = (y/2) int_y^inf log(1 - t^-2) t^-2 dt."""
    return float(T_float(y)) / y - math.log1p(-1.0 / (y * y)) / (2.0 * y)


def interior_critical_point(n: int, e_n: float, r_n: float):
    """Critical point of F(y) = (G(y) - log 2pi - T(y))/sqrt(y) on (n, n+1).

    With u(y) = E(n) + log(n/y) one has G'(y) = u on the piece, and F' = 0
    reads  phi(y) = y u(y) - (y - n) + R(n) + log 2pi + T(y) - 2 y T'(y) = 0.
    A closed-form start (T frozen at n) is polished by secant steps on phi.
    Returns (y_c, F(y_c)) or None when the critical point is not in (n, n+1).
    """
    eta = (r_n + LOG_2PI + float(T_float(float(n)))) / n
    rhs = math.log1p(eta) - e_n
    u = (e_n - eta) / 2.0
    for _ in range(40):
        h = math.log1p(-u) - u - rhs
        step = h / (-1.0 / (1.0 - u) - 1.0)
        u -= step
        if abs(step) < 1e-18:
            break
    x = n * math.expm1(e_n - u)  # y_c - n

    def phi(xx: float) -> float:
        y = n + xx
        uu = e_n - math.log1p(xx / n)
        return y * uu - xx + r_n + LOG_2PI + float(T_float(y)) - 2.0 * y * _T_prime_float(y)

    if n >= 2:
        x0, x1 = x, x + 1e-6 * max(abs(x), 1e-3)
        f0, f1 = phi(x0), phi(x1)
        for _ in range(60):
            if f1 == f0:
                break
            x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
            x0, f0, x1 = x1, f1, x2
            if not (-1.0 < x1 < 2.0):
                break
            f1 = phi(x1)
            if abs(x1 - x0) < 1e-15 * max(1.0, abs(x1)):
                break
        x = x1
    if not (0.0 < x < 1.0):
        return None
    y_c = n + x
    u_c = e_n - math.log1p(x / n)
    g_c = y_c * u_c + x - r_n - LOG_2PI - float(T_float(y_c))
    return y_c, g_c / math.sqrt(y_c)


# ---------------------------------------------------------------------------
# Arb route
# ---------------------------------------------------------------------------


def _as_arb(y):
    """Exact conversion of an int, a float (dyadic) or a Fraction to an arb."""
    from flint import arb

    if isinstance(y, Fraction):
        return arb(y.numerator) / arb(y.denominator)
    if isinstance(y, (int, np.integer)):
        return arb(int(y))
    return arb(float(y))  # a float is an exact dyadic rational


def _floor_exact(y) -> int:
    if isinstance(y, Fraction):
        return y.numerator // y.denominator
    return int(math.floor(y))


def T_arb(y):
    """Enclosure of T(y) for an exact y >= 1 given as an arb."""
    from flint import arb

    if (y - 1).is_zero():
        return arb(2).log() - 1
    if y < 4:
        inv2 = 1 / (y * y)
        return (1 - inv2).log() / 2 + y / 2 * ((y + 1) / (y - 1)).log() - 1
    x2 = 1 / (y * y)
    acc = arb(0)
    term = arb(1)
    K = 40
    for k in range(1, K + 1):
        term = term * x2
        acc += term / (2 * k * (2 * k + 1))
    tail = term * x2 / (1 - x2) / ((2 * K + 2) * (2 * K + 3))
    acc = acc + tail * arb(0.5, 0.5)  # the tail lies in [0, tail]
    return -acc


def T_odd_arb(y):
    """Enclosure of T_odd(y) for an exact y >= 1 given as an arb."""
    from flint import arb

    if (y - 1).is_zero():
        return -arb(2).log()
    x = 1 / y
    return -(x.atanh() + y / 2 * (1 - x * x).log())


def arb_prefix_sums(points: list[int], prec: int = 128, seg: int = 1 << 22):
    """Enclosures of (psi(N), A(N)) for each N in `points`, A(N) = sum_{m<=N} Lambda(m)/m.

    One pass over the primes in increasing order with snapshots, then the
    higher prime powers added per point.  Every operation is an Arb ball
    operation at `prec` bits.
    """
    from flint import arb, ctx

    order = sorted(set(int(p) for p in points))
    out: dict[int, tuple] = {}
    old = ctx.prec
    ctx.prec = prec
    try:
        top = order[-1]
        base = small_primes(math.isqrt(top) + 2)
        theta = arb(0)
        a1 = arb(0)
        snaps: dict[int, tuple] = {}
        idx = 0
        lo = 2
        while idx < len(order):
            hi = min(lo + seg, top + 1)
            if hi <= lo:
                break
            for p in segment_primes(lo, hi, base).tolist():
                while idx < len(order) and order[idx] < p:
                    snaps[order[idx]] = (theta, a1)
                    idx += 1
                lp = arb(p).log()
                theta = theta + lp
                a1 = a1 + lp / p
            lo = hi
            while idx < len(order) and order[idx] < lo:
                snaps[order[idx]] = (theta, a1)
                idx += 1
        while idx < len(order):
            snaps[order[idx]] = (theta, a1)
            idx += 1
        for N in order:
            th, aa = snaps[N]
            for p in base.tolist():
                if p * p > N:
                    break
                lp = arb(p).log()
                pk = p * p
                while pk <= N:
                    th = th + lp
                    aa = aa + lp / pk
                    pk *= p
            out[N] = (th, aa)
    finally:
        ctx.prec = old
    return out


def G_arb(ys: list, prec: int = 128) -> list:
    """Enclosures of G(y) for exact y >= 1 (ints, floats read as dyadics, Fractions)."""
    from flint import arb, ctx

    floors = [_floor_exact(y) for y in ys]
    sums = arb_prefix_sums(floors, prec=prec)
    old = ctx.prec
    ctx.prec = prec
    try:
        res = []
        for y, N in zip(ys, floors):
            ya = _as_arb(y)
            psi, a = sums[N]
            res.append(ya * a - psi - ya * ya.log() + (1 + arb.const_euler()) * ya)
        return res
    finally:
        ctx.prec = old


def F_arb(ys: list, prec: int = 128) -> list:
    """Enclosures of F(y) = (G(y) - log 2pi - T(y)) / sqrt(y)."""
    from flint import arb, ctx

    gs = G_arb(ys, prec=prec)
    old = ctx.prec
    ctx.prec = prec
    try:
        out = []
        for y, g in zip(ys, gs):
            ya = _as_arb(y)
            out.append((g - (2 * arb.pi()).log() - T_arb(ya)) / ya.sqrt())
        return out
    finally:
        ctx.prec = old


def F_prime_arb(y, prec: int = 128):
    """Enclosure of F'(y) at an exact non-integer y > 1 (T' included)."""
    from flint import arb, ctx

    N = _floor_exact(y)
    psi, a = arb_prefix_sums([N], prec=prec)[N]
    old = ctx.prec
    ctx.prec = prec
    try:
        ya = _as_arb(y)
        g = ya * a - psi - ya * ya.log() + (1 + arb.const_euler()) * ya - (2 * arb.pi()).log() - T_arb(ya)
        # T'(y) = T(y)/y - (1/2) log(1 - y^-2)/y, from T(y) = (y/2) int_y^inf log(1-t^-2) t^-2 dt
        t_prime = T_arb(ya) / ya - (1 - 1 / (ya * ya)).log() / (2 * ya)
        g_prime = a - ya.log() + arb.const_euler() - t_prime
        return (g_prime - g / (2 * ya)) / ya.sqrt()
    finally:
        ctx.prec = old


def c0_arb(prec: int = 128):
    from flint import arb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        return 2 + arb.const_euler() - (4 * arb.pi()).log()
    finally:
        ctx.prec = old


# ---------------------------------------------------------------------------
# characters
# ---------------------------------------------------------------------------


class Char:
    """A Dirichlet character mod q stored as exact exponents.

    `exps[a]` is a Fraction e in [0, 1) with chi(a) = exp(2 pi i e), or None
    when gcd(a, q) > 1.  `conrey` is the Conrey label of the same character in
    python-flint, kept so that the Arb L-function routines can be called.
    """

    def __init__(self, q: int, exps: tuple, conrey: int | None = None):
        self.q = int(q)
        self.exps = tuple(exps)
        self.conrey = conrey

    # exact data ---------------------------------------------------------
    def key(self):
        return (self.q, self.exps)

    def order(self) -> int:
        o = 1
        for e in self.exps:
            if e is not None:
                o = o * e.denominator // gcd(o, e.denominator)
        return o

    def parity(self) -> int:
        """0 for even (chi(-1) = 1), 1 for odd."""
        if self.q == 1:
            return 0
        e = self.exps[(self.q - 1) % self.q]
        return 0 if e == 0 else 1

    def is_trivial(self) -> bool:
        return all(e is None or e == 0 for e in self.exps)

    def conductor(self) -> int:
        q = self.q
        for d in sorted(x for x in range(1, q + 1) if q % x == 0):
            if all(
                self.exps[a] == 0
                for a in range(1, q + 1)
                if gcd(a, q) == 1 and a % d == 1 % d
            ):
                return d
        return q

    def is_primitive(self) -> bool:
        return self.conductor() == self.q

    # values --------------------------------------------------------------
    def values(self) -> np.ndarray:
        """chi(a) for a = 0..q-1 as complex128 (0 where gcd(a, q) > 1)."""
        out = np.zeros(self.q, dtype=np.complex128)
        for a, e in enumerate(self.exps):
            if e is not None:
                out[a] = complex(math.cos(2 * math.pi * float(e)), math.sin(2 * math.pi * float(e)))
                if e == 0:
                    out[a] = 1.0
                elif e == Fraction(1, 2):
                    out[a] = -1.0
                elif e == Fraction(1, 4):
                    out[a] = 1j
                elif e == Fraction(3, 4):
                    out[a] = -1j
        return out

    def value_acb(self, a: int):
        from flint import acb, arb

        e = self.exps[a % self.q]
        if e is None:
            return acb(0)
        ang = 2 * arb.pi() * arb(e.numerator) / arb(e.denominator)
        return acb(ang.cos(), ang.sin())

    def flint(self):
        from flint import dirichlet_char

        return dirichlet_char(self.q, self.conrey)

    def __repr__(self):
        return f"Char(q={self.q}, conrey={self.conrey}, order={self.order()}, parity={self.parity()})"


def characters_mod(q: int) -> list[Char]:
    """All Dirichlet characters mod q, exponents read from python-flint's Conrey labels."""
    from flint import dirichlet_char, dirichlet_group

    q = int(q)
    if q == 1:
        return [Char(1, (Fraction(0),), 1)]
    den = int(dirichlet_group(q).exponent())
    out = []
    for n in range(1, q):
        if gcd(n, q) != 1:
            continue
        chi = dirichlet_char(q, n)
        exps = []
        for a in range(q):
            e = chi.chi_exponent(a)
            exps.append(None if e is None else Fraction(int(e), den) % 1)
        out.append(Char(q, tuple(exps), n))
    return out


def primitive_characters(q: int) -> list[Char]:
    """Primitive characters of conductor exactly q (the trivial one only for q = 1)."""
    return [c for c in characters_mod(q) if c.is_primitive()]


def power_inducer(chi: Char, k: int) -> Char:
    """The primitive character inducing chi^k, with its Conrey label attached."""
    q = chi.q
    exps = tuple(None if e is None else (k * e) % 1 for e in chi.exps)
    pw = Char(q, exps)
    d = pw.conductor()
    if d == 1:
        return Char(1, (Fraction(0),), 1)
    red = []
    for m in range(d):
        if gcd(m, d) != 1:
            red.append(None)
            continue
        a = m
        while gcd(a, q) != 1:
            a += d
        red.append(exps[a % q])
    red = tuple(red)
    for c in characters_mod(d):
        if c.exps == red:
            return c
    raise RuntimeError("inducing character not found")  # pragma: no cover


def cyc_level(psi: Char) -> dict:
    """The level `Level.cyc psi` of the archive, in plain data.

    members: the primitive characters inducing psi^k, k = 1..o-1 (nontrivial),
    o: the order of psi, lam = 1/(3o+1): the weight on each member.
    """
    o = psi.order()
    members = [power_inducer(psi, k) for k in range(1, o)]
    keys = {m.key() for m in members}
    if len(keys) != o - 1:  # pragma: no cover - distinct by injectivity
        raise RuntimeError("level members are not distinct")
    return {
        "q": psi.q,
        "o": o,
        "lam": Fraction(1, 3 * o + 1),
        "members": members,
        "key": frozenset(keys),
    }


def level_weights(level: dict) -> np.ndarray:
    """v(a) = lam * sum_k Re chi_k(a) for a = 0..q-1, each chi_k at its own conductor."""
    q = level["q"]
    v = np.zeros(q, dtype=np.float64)
    for m in level["members"]:
        vals = m.values()
        v += np.real(vals[np.arange(q) % m.q])
    return v * float(level["lam"])


# ---------------------------------------------------------------------------
# L'/L at 1 and at 0: three routes
# ---------------------------------------------------------------------------


def logderiv_at_one_arb(chi: Char, prec: int = 128):
    """L'/L(1, chi) by Arb's Taylor jet of the L-function at s = 1."""
    from flint import acb_series, ctx

    old_p, old_c = ctx.prec, ctx.cap
    ctx.prec = prec
    ctx.cap = 3
    try:
        ser = acb_series.dirichlet_l(acb_series([1, 1]), chi.flint())
        return ser[1] / ser[0]
    finally:
        ctx.prec, ctx.cap = old_p, old_c


def logderiv_at_one_stieltjes(chi: Char, prec: int = 128):
    """L'/L(1, chi) = -log q - (sum chi(a) gamma_1(a/q)) / (sum chi(a) gamma_0(a/q)).

    A second Arb route through the generalized Stieltjes constants of the
    Hurwitz zeta function; it shares the ball arithmetic with the first route
    and nothing else.
    """
    from flint import acb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        q = chi.q
        h0 = acb(0)
        h1 = acb(0)
        for a in range(1, q):
            if chi.exps[a] is None:
                continue
            x = acb(a) / q
            w = chi.value_acb(a)
            h0 += w * acb.stieltjes(0, x)
            h1 += w * acb.stieltjes(1, x)
        return -acb(q).log() - h1 / h0
    finally:
        ctx.prec = old


def logderiv_at_one_mpmath(chi: Char, dps: int = 30):
    """L'/L(1, chi) in mpmath, by Stieltjes constants: the independent library.

    Returns an mpmath complex number carrying about `dps` digits.
    """
    from mpmath import mp

    with mp.workdps(dps + 10):
        q = chi.q
        h0 = mp.mpc(0)
        h1 = mp.mpc(0)
        for a in range(1, q):
            e = chi.exps[a]
            if e is None:
                continue
            w = mp.expjpi(2 * mp.mpf(e.numerator) / e.denominator)
            x = mp.mpf(a) / q
            h0 += w * mp.stieltjes(0, x)
            h1 += w * mp.stieltjes(1, x)
        val = -mp.log(q) - h1 / h0
    return val


def constants_at_zero_arb(chi: Char, prec: int = 128):
    """The s = 0 constant of the explicit formula, computed directly at s = 0.

    Odd chi: L(0, chi) != 0 and the constant is K = L'/L(0, chi).
    Even chi (nontrivial): L has a simple zero at 0 and the constant is
    b = lim_{s->0} (L'/L(s) - 1/s) = a2/a1 for L(s) = a1 s + a2 s^2 + ...
    """
    from flint import acb_series, ctx

    old_p, old_c = ctx.prec, ctx.cap
    ctx.prec = prec
    ctx.cap = 4
    try:
        ser = acb_series.dirichlet_l(acb_series([0, 1]), chi.flint())
        if chi.parity() == 1:
            return ser[1] / ser[0]
        if not ser[0].contains(0):
            raise RuntimeError("even character without a trivial zero at 0")  # pragma: no cover
        return ser[2] / ser[1]
    finally:
        ctx.prec, ctx.cap = old_p, old_c


def char_constants(chi: Char, prec: int = 128) -> dict:
    """Every constant of the character explicit formula, as Arb enclosures.

    Derived (functional equation of the completed L-function, a = parity):

        c_chi = sum_rho 1/(rho(1-rho)) = 2 Re L'/L(1,chi) + log(q/pi) + digamma((1+a)/2)
        odd:   K = L'/L(0,chi) = -conj(L'/L(1,chi)) - log(q/pi) + gamma + log 2
        even:  b = gamma + log 2 - log(q/pi) - conj(L'/L(1,chi))

    `direct0` is the same constant measured at s = 0 without the functional
    equation; `derived0` is the closed form.  They should overlap.
    """
    from flint import acb, arb, ctx

    l1 = logderiv_at_one_arb(chi, prec)
    direct0 = constants_at_zero_arb(chi, prec)
    old = ctx.prec
    ctx.prec = prec
    try:
        a = chi.parity()
        g = arb.const_euler()
        logq = (arb(chi.q) / arb.pi()).log()
        dig = -g if a == 1 else -g - 2 * arb(2).log()
        c = 2 * l1.real + logq + dig
        derived0 = -acb(l1.real, -l1.imag) - logq + g + arb(2).log()
        return {"l1": l1, "c": c, "direct0": direct0, "derived0": derived0, "parity": a}
    finally:
        ctx.prec = old


def level_model(level: dict, prec: int = 128) -> dict:
    """The GRH envelope data of a level, from the character formula.

    Under GRH for the members and RH,  |Gm(y) - M(y)| <= C sqrt(y)  for y >= 1,
    M(y) = m0 + m1 log y + wT T(y) + wTo T_odd(y), and Gm(1) - M(1) = C.
    `ell` is the coefficient of y in Gm (the weighted sum of Re L'/L(1)).
    """
    from flint import arb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        lam = arb(level["lam"].numerator) / arb(level["lam"].denominator)
        n_even = 0
        n_odd = 0
        m0 = (2 * arb.pi()).log()
        cc = c0_arb(prec)
        ell = arb(0)
        per = []
        for m in level["members"]:
            k = char_constants(m, prec)
            ell += lam * k["l1"].real
            cc += lam * k["c"]
            if k["parity"] == 1:
                n_odd += 1
                m0 += lam * k["direct0"].real
            else:
                n_even += 1
                m0 += lam * (1 + k["direct0"].real)
            per.append(k)
        return {
            "C": cc,
            "m0": m0,
            "m1": lam * n_even,
            "wT": 1 + lam * n_even,
            "wTo": lam * n_odd,
            "ell": ell,
            "n_even": n_even,
            "n_odd": n_odd,
            "per_member": per,
        }
    finally:
        ctx.prec = old


def arb_class_sums(N: int, q: int, prec: int = 128):
    """Enclosures of psi(N; q, a) and A(N; q, a) = sum Lambda(m)/m over m <= N, m = a mod q."""
    from flint import arb, ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        psi = [arb(0) for _ in range(q)]
        aa = [arb(0) for _ in range(q)]
        logs: dict[int, object] = {}
        for pk, p in prime_powers_upto(N):
            lp = logs.get(p)
            if lp is None:
                lp = arb(p).log()
                if p * p <= N:
                    logs[p] = lp
            r = pk % q
            psi[r] = psi[r] + lp
            aa[r] = aa[r] + lp / pk
        return psi, aa
    finally:
        ctx.prec = old


def Gchi_arb(chi: Char, y, prec: int = 128, sums=None):
    """Enclosure (acb) of Gchi(y) for a nontrivial primitive chi and exact y >= 1."""
    from flint import acb, ctx

    N = _floor_exact(y)
    psi, aa = sums if sums is not None else arb_class_sums(N, chi.q, prec)
    l1 = logderiv_at_one_arb(chi, prec)
    old = ctx.prec
    ctx.prec = prec
    try:
        ya = _as_arb(y)
        tot = acb(0)
        for a in range(chi.q):
            if chi.exps[a] is None:
                continue
            tot += chi.value_acb(a) * (ya * aa[a] - psi[a])
        return tot + ya * l1
    finally:
        ctx.prec = old


def Gm_arb(level: dict, y, prec: int = 128):
    """Enclosure of Gm(y) for a level, by its definition (zeta part plus weighted members)."""
    from flint import arb, ctx

    g = G_arb([y], prec=prec)[0]
    N = _floor_exact(y)
    cache: dict[int, tuple] = {}
    vals = []
    for m in level["members"]:
        if m.q not in cache:
            cache[m.q] = arb_class_sums(N, m.q, prec)
        vals.append(Gchi_arb(m, y, prec, sums=cache[m.q]))
    old = ctx.prec
    ctx.prec = prec
    try:
        lam = arb(level["lam"].numerator) / arb(level["lam"].denominator)
        acc = arb(0)
        for v in vals:
            acc = acc + v.real
        return g + lam * acc
    finally:
        ctx.prec = old


def M_arb(model: dict, y, prec: int = 128):
    """Enclosure of the non-oscillating part M(y) of a level model."""
    from flint import ctx

    old = ctx.prec
    ctx.prec = prec
    try:
        ya = _as_arb(y)
        return model["m0"] + model["m1"] * ya.log() + model["wT"] * T_arb(ya) + model["wTo"] * T_odd_arb(ya)
    finally:
        ctx.prec = old


def Gchi_float(chi: Char, y: float, l1: complex) -> complex:
    """Gchi(y) in float64 by direct summation (small y)."""
    y = float(y)
    n = int(math.floor(y))
    vals = chi.values()
    re = []
    im = []
    for pk, p in prime_powers_upto(n):
        v = vals[pk % chi.q]
        if v != 0:
            t = math.log(p) * (y / pk - 1.0)
            re.append(t * v.real)
            im.append(t * v.imag)
    return complex(math.fsum(re), math.fsum(im)) + y * l1


def arb_str(x, digits: int = 30) -> str:
    """Midpoint and radius of an arb as text, independent of the ambient precision."""
    return x.str(digits)


def arb_mid_rad(x) -> tuple[float, float]:
    return float(x.mid()), float(x.rad())
