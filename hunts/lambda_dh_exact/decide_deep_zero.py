"""Decide the height-10^6 off-line zero of f by the argument principle, twice.

Hunt #119, resumption of 2026-10-26, resume-order step 1 (`RESULTS.md`
section 7).  `deep_zeros_1e6.json` holds one float-grade zero of the
Davenport-Heilbronn function

    f(s) = sum_{n>=1} a_n n^{-s},  a_n = (1, kappa, -kappa, -1, 0) mod 5,
         = 5^{-s} [zeta(s,1/5) + kappa zeta(s,2/5) - kappa zeta(s,3/5) - zeta(s,4/5)]

at gamma = 1000459.7433532759, beta = 0.8583118590734415.  This module turns
that into a *decided* statement, or refutes it: f has exactly one zero, counted
with multiplicity, in an exact rational rectangle R lying wholly in
Re s > 1/2.  The count is computed on two independent routes.

Grade vocabulary as in `MISSION.md`: *decided* is a ball enclosure whose exact
endpoints settle an integer or a sign.  Nothing here is a statement about RH
(`docs/08`; f has no Euler product and RH is false for it).

The count
---------

f is entire (the poles of the four Hurwitz pieces cancel, coefficient sum 0).
For a positively oriented rectangle on whose boundary f does not vanish,
N = (1/2pi) * (total continuous variation of arg f).  Per boundary subsegment
[s_a, s_b] two facts are decided, and together they make its contribution
exact (the `zeta.rigor._segment_delta` pattern, re-implemented here because
hunts may not use that module's vocabulary):

1. The image of the subsegment lies in a convex set missing 0.  This is the
   chord tube of `count_zeros` (see the comment above it): with M2 a decided
   bound on |f''| over the rectangle, the image of a subsegment of length ell
   lies within M2 ell^2 / 8 of the chord between the endpoint values, so a
   decided clearance dist(0, chord) > M2 ell^2 / 8 puts it in a convex set
   missing 0.  A convex set missing 0 lies in an open half-plane through 0, so
   the continuous variation of arg along the subsegment satisfies |D| < pi.
   (Docstring corrected 2026-10-26 in review.  It described the segment-ball
   test, f enclosed over the whole subsegment at once, which Run 7 in
   `RUNS.md` replaced by the chord tube before any count was read.)
2. With q = f(s_b)/f(s_a), a decided Re q > 0 gives |Arg q| < pi/2, and since
   D == Arg q (mod 2pi) and |D| < pi, D = Arg q exactly.

A subsegment failing either test is halved at an exact dyadic point, down to
a budget; on exhaustion the run reports "undecided", never an integer.  The
sum of the Arg q enclosures divided by 2pi must contain exactly one integer.

Route A: Arb
------------

python-flint's `acb.zeta(s, a)` (Arb's Hurwitz zeta, its own Euler-Maclaurin
with its own error bounds), kappa as the ball sqrt(1 + phi^2) - phi.

Route B: mpmath.iv, hand-rolled
-------------------------------

No Hurwitz zeta exists in mpmath's interval context, so it is built here.
With X_a = 5N + a and c_a the coefficients,

    f(s) = sum_{n < 5N} a_n n^{-s}
           + sum_{a=1..4} c_a [ X_a^{1-s} / (5(s-1)) + X_a^{-s} / 2
             + sum_{k=1}^{p-1} B_{2k}/(2k)! 5^{2k-1} (s)_{2k-1} X_a^{-s-2k+1} ]
           + E,

    |E| <= sum_a |c_a| * C_p/(2pi)^{2p} * 5^{2p} |(s)_{2p}|
                      * X_a^{1-sigma-2p} / (5 (sigma + 2p - 1)),
    C_p  = 4 (1 - 2^{-2p}) zeta(2p) = 4 (1 + 3^{-2p} + 5^{-2p} + ...),

the Euler-Maclaurin formula for g(x) = (5x + a)^{-s} on [N, inf), summed
through k = p - 1, with the integral of |g^{(2p)}| done in closed form.  For
that truncation the remainder is (DLMF 2.10.1) the integral over [N, inf) of
(B_{2p} - B~_{2p}(x)) / (2p)! * g^{(2p)}(x), and
max_x |B_{2p} - B~_{2p}(x)| = (2 - 2^{1-2p}) |B_{2p}| with
|B_{2p}| = 2 (2p)! zeta(2p) / (2pi)^{2p}, whose product is C_p / (2pi)^{2p}
times (2p)!.  The code (`IvRoute._tail`) uses the constant 4, which falls
short of C_p by the relative amount 3^{-2p} + 5^{-2p} + ..., under 1e-279 at
p = 293 (the only p this module uses at 128 bits).  Every bound passes
through `_upper` before it enters an enclosure, and `_upper`'s relative 2^-50
fudge leaves a relative margin of at least 6e-16 after float rounding, so the
enclosure holds.  (Corrected 2026-10-26 in review.  The text before cited
|B~_{2p}(x)| <= |B_{2p}| and the constant 2 zeta(2p), which bound the
remainder of a sum that also includes the k = p term; the code was not
changed.  Pinned by `test_em_remainder_constant_is_covered_by_the_fudge`.)

The head is the expensive part (about 8e5 terms at this height), so it is
computed once as a Taylor model about the exact rectangle centre s0:

    head(s0 + d) = sum_{j<=K} d^j / j! * D_j,  D_j = sum a_n (-log n)^j n^{-s0},
    |remainder| <= S * (|d| L)^{K+1} / (K+1)! * e^{|d| L},

with S = sum |a_n| n^{-sigma0} and L = log(5N) both enclosed during the same
pass.  Every quantity is an mpmath.iv interval; d ranges over an interval box,
so one Horner evaluation encloses the head over a whole subsegment.

The two routes share the formula f = sum a_n n^{-s}, the closed form of
kappa, and no evaluator.  They do share the counting driver `count_zeros`:
the chord-tube bound M2 ell^2 / 8, the Cauchy bound on |f''|, the float
conversions with their 2^-50 fudges (`LO`, `HI`), and the sum of the Arg
enclosures in mpmath.iv.  A defect there would reach both routes; the
clearance functions and everything that evaluates f are separate.
(Corrected 2026-10-26 in review; the text before said the routes share no
rounding code and no error bound.)

Run:  .venv/bin/python hunts/lambda_dh_exact/decide_deep_zero.py [--quick]
"""
from __future__ import annotations

import argparse
import json
import math
import os
import platform
import sys
import time
from fractions import Fraction

import mpmath
from mpmath import iv, mp

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from flint import acb, arb, ctx as fctx, fmpq  # noqa: E402

from zeta import rigor  # noqa: E402  (read for BACKEND only)

OUT = os.path.join(_HERE, "decide_deep_zero.json")

GAMMA_FLOAT = 1000459.7433532759
BETA_FLOAT = 0.8583118590734415


# ---------------------------------------------------------------------------
# exact geometry
# ---------------------------------------------------------------------------

def dyadic(x: float, bits: int) -> Fraction:
    """x rounded to the nearest multiple of 2^-bits, exactly."""
    return Fraction(round(x * 2**bits), 2**bits)


def rectangle(beta: Fraction, gamma: Fraction, half: Fraction):
    """Corners of the positively oriented rectangle, as (sigma, t) pairs."""
    s0, s1 = beta - half, beta + half
    t0, t1 = gamma - half, gamma + half
    return [(s0, t0), (s1, t0), (s1, t1), (s0, t1)]


# ---------------------------------------------------------------------------
# route A: Arb
# ---------------------------------------------------------------------------

class ArbRoute:
    name = "python-flint"

    def __init__(self, prec: int, kappa_shift: Fraction = Fraction(0)):
        self.prec = prec
        self.kappa_shift = kappa_shift

    def _q(self, q: Fraction):
        return arb(fmpq(q.numerator, q.denominator))

    def _coeffs(self):
        phi = (1 + arb(5).sqrt()) / 2
        kap = (1 + phi * phi).sqrt() - phi + self._q(self.kappa_shift)
        return [arb(1), kap, -kap, arb(-1)]

    def f_box(self, sig_lo, sig_hi, t_lo, t_hi):
        old = fctx.prec
        fctx.prec = self.prec
        try:
            sig = self._q(sig_lo).union(self._q(sig_hi)) if sig_lo != sig_hi else self._q(sig_lo)
            t = self._q(t_lo).union(self._q(t_hi)) if t_lo != t_hi else self._q(t_lo)
            s = acb(sig, t)
            c = self._coeffs()
            tot = acb(0)
            for a in range(1, 5):
                tot += c[a - 1] * s.zeta(acb(arb(a) / 5))
            return tot * acb(5) ** (-s)
        finally:
            fctx.prec = old

    def excludes_zero(self, z) -> bool:
        return bool(z.real.lower() > 0 or z.real.upper() < 0
                    or z.imag.lower() > 0 or z.imag.upper() < 0)

    def arg_quotient(self, zb, za):
        old = fctx.prec
        fctx.prec = self.prec
        try:
            q = zb / za
            if not q.real.lower() > 0:
                return None
            a = q.arg()
            return (float(a.lower()), float(a.upper()), a)
        finally:
            fctx.prec = old

    def as_floats(self, z):
        return [float(z.real.mid()), float(z.imag.mid()),
                float(z.real.rad()), float(z.imag.rad())]


# ---------------------------------------------------------------------------
# route B: mpmath.iv Euler-Maclaurin with a Taylor-model head
# ---------------------------------------------------------------------------

class _ivprec:
    """Set mpmath.iv's precision for a block and restore it (iv has no workprec)."""

    def __init__(self, prec: int):
        self.prec = int(prec)

    def __enter__(self):
        self.old = iv.prec
        iv.prec = self.prec

    def __exit__(self, *exc):
        iv.prec = self.old


def _iq(q: Fraction):
    if q.denominator == 1:
        return iv.mpf(q.numerator)
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _span(lo: Fraction, hi: Fraction):
    if lo == hi:
        return _iq(lo)
    a, b = _iq(lo), _iq(hi)
    return iv.mpf([a.a, b.b])


def _upper(x) -> float:
    """A float upper bound of a real interval (rounded up past the endpoint)."""
    return float(mp.make_mpf(x._mpi_[1])) * (1 + 2**-50) + 1e-300


class IvRoute:
    name = "mpmath.iv"

    def __init__(self, prec: int, centre: tuple[Fraction, Fraction], radius: Fraction,
                 K: int = 6, slack: float = 1.25, kappa_shift: Fraction = Fraction(0),
                 log_every: int = 100000):
        self.prec = prec
        self.centre = centre
        self.radius = radius          # every queried d has |d| <= radius (checked)
        self.K = K
        self.kappa_shift = kappa_shift
        abs_s = math.hypot(float(centre[0]), float(centre[1]))
        # Term k of the Euler-Maclaurin tail scales like ((|s| + 2k) / (2 pi N))^2,
        # so p is fixed first (ratio 1/slack^2 per k, prec bits plus margin) and N
        # is then chosen from |s| + 2p, not from |s| alone: below height ~600 the
        # Pochhammer growth in k would otherwise dominate.
        self.p = int(math.ceil((prec * math.log(2) + 40) / (2 * math.log(slack)))) + 4
        self.N = int(math.ceil(slack * (abs_s + 2 * self.p + 2) / (2 * math.pi)))
        self.log_every = log_every
        self._build()

    def _coeffs(self):
        phi = (1 + iv.sqrt(iv.mpf(5))) / 2
        kap = iv.sqrt(1 + phi * phi) - phi + _iq(self.kappa_shift)
        return [iv.mpf(1), kap, -kap, iv.mpf(-1)]

    def _build(self):
        t0 = time.time()
        with _ivprec(self.prec):
            c = self._coeffs()
            sig0, tau0 = _iq(self.centre[0]), _iq(self.centre[1])
            s0 = iv.mpc(sig0, tau0)
            D = [iv.mpc(0) for _ in range(self.K + 1)]
            S = iv.mpf(0)
            top = 5 * self.N
            for n in range(1, top):
                r = n % 5
                if r == 0:
                    continue
                ln = iv.log(iv.mpf(n))
                term = c[r - 1] * iv.exp(-s0 * ln)
                S += abs(c[r - 1]) * iv.exp(-sig0 * ln)
                mln = -ln
                p = term
                D[0] += p
                for j in range(1, self.K + 1):
                    p = p * mln
                    D[j] += p
                if self.log_every and n % self.log_every == 0:
                    print(f"  iv head n={n}/{top}  {time.time() - t0:.0f}s", flush=True)
            for j in range(2, self.K + 1):
                D[j] = D[j] / math.factorial(j)
            self.D = D
            self.S = S
            self.L = iv.log(iv.mpf(top))
            self.c = c
        self.head_seconds = time.time() - t0

    def _em_coeff(self, k: int):
        """B_{2k}/(2k)! * 5^{2k-1} as an interval, cached per route (same value
        as computing it in place; caching only removes the repeated bernfrac
        and factorial work from every evaluation)."""
        cache = self.__dict__.setdefault("_em_cache", {})
        c = cache.get(k)
        if c is None:
            bp, bq = mpmath.bernfrac(2 * k)
            c = iv.mpf(int(bp)) / iv.mpf(int(bq) * math.factorial(2 * k)) * iv.mpf(5) ** (2 * k - 1)
            cache[k] = c
        return c

    def _tail(self, s, sig):
        """sum_a c_a [EM tail on [N, inf)] plus the remainder disc, for s in the box."""
        N = self.N
        p = self.p
        tot = iv.mpc(0)
        rem = iv.mpf(0)
        for a in range(1, 5):
            X = iv.mpf(5 * N + a)
            lX = iv.log(X)
            Xs = iv.exp(-s * lX)
            part = X * Xs / (5 * (s - 1)) + Xs / 2
            poch = s                                    # (s)_1
            Xpow = Xs / X                                # X^{-s-1}
            inv_X2 = 1 / (X * X)
            for k in range(1, p):
                part += self._em_coeff(k) * poch * Xpow
                poch = poch * (s + (2 * k - 1)) * (s + 2 * k)   # (s)_{2k+1}
                Xpow = Xpow * inv_X2
            # (s)_{2p} = (s)_{2p-1} * (s + 2p - 1); poch is now (s)_{2p-1}
            poch2p = poch * (s + (2 * p - 1))
            bound = (4 / (2 * iv.pi) ** (2 * p)) * iv.mpf(5) ** (2 * p) * abs(poch2p) \
                * iv.exp((1 - sig - 2 * p) * lX) / (5 * (sig + 2 * p - 1))
            tot += self.c[a - 1] * part
            rem += abs(self.c[a - 1]) * bound
        return tot, rem

    def f_box(self, sig_lo, sig_hi, t_lo, t_hi):
        with _ivprec(self.prec):
            sig = _span(sig_lo, sig_hi)
            tau = _span(t_lo, t_hi)
            s = iv.mpc(sig, tau)
            dr = sig - _iq(self.centre[0])
            di = tau - _iq(self.centre[1])
            d = iv.mpc(dr, di)
            dabs = abs(d)
            if not _upper(dabs) <= float(self.radius) * 1.0000001:
                raise ValueError("query outside the Taylor model's radius")
            head = self.D[self.K]
            for j in range(self.K - 1, -1, -1):
                head = head * d + self.D[j]
            x = dabs * self.L
            trunc = self.S * x ** (self.K + 1) / math.factorial(self.K + 1) * iv.exp(x)
            tail, rem = self._tail(s, sig)
            r = _upper(trunc) + _upper(rem)
            tot = head + tail
            out = iv.mpc(iv.mpf([-r, r]), iv.mpf([-r, r]))
            return tot + out

    def excludes_zero(self, z) -> bool:
        rl, rh = z.real.a, z.real.b
        il, ih = z.imag.a, z.imag.b
        return bool(rl > 0 or rh < 0 or il > 0 or ih < 0)

    def arg_quotient(self, zb, za):
        with _ivprec(self.prec):
            q = zb / za
            if not q.real.a > 0:
                return None
            a = iv.atan2(q.imag, q.real)
            return (float(mp.make_mpf(a._mpi_[0])), float(mp.make_mpf(a._mpi_[1])), a)

    def as_floats(self, z):
        return [float(mp.make_mpf(z.real.mid._mpi_[0])), float(mp.make_mpf(z.imag.mid._mpi_[0])),
                float(mp.make_mpf(z.real.delta._mpi_[1])) / 2,
                float(mp.make_mpf(z.imag.delta._mpi_[1])) / 2]


# ---------------------------------------------------------------------------
# the count
# ---------------------------------------------------------------------------
#
# Segment test (the chord-tube pattern of hunts/lambda_dh_bounds/winding.py).
# Let M2 bound |f''| on the rectangle.  Along a subsegment of length ell, the
# image lies within M2 ell^2 / 8 of the chord between the endpoint values, so
# a decided dist(0, chord) > M2 ell^2 / 8 puts the image in a convex set
# missing 0, and |D| < pi.  Re q > 0 then pins D = Arg q.
#
# M2 by Cauchy: if |f| <= B on the closed square of half-width R about the
# rectangle centre, every s in the rectangle (half-width r < R) has the circle
# of radius rho = R - r about it inside that square, so |f''(s)| <= 2 B / rho^2.
# B is one ball (Arb) or interval (iv) evaluation of f over the whole square.
#
# Ball and interval endpoints are converted to float for the comparisons with
# an explicit relative fudge of 2^-50 in the safe direction (float rounding is
# at most 2^-53 relative); every recorded margin is many orders larger.

LO = 1 - 2.0**-50
HI = 1 + 2.0**-50


def _arb_lo(x) -> float:
    v = float(x.lower())
    return v * LO if v > 0 else v * HI


def _arb_hi(x) -> float:
    v = float(x.upper())
    return v * HI if v > 0 else v * LO


def _arb_clearance(A, B) -> float:
    D = B - A
    p = (D.conjugate() * (-A)).real
    d2 = (D.conjugate() * D).real
    if p < 0:
        return _arb_lo(abs(A))
    if p > d2:
        return _arb_lo(abs(B))
    best = _arb_lo(abs(A) - abs(D))
    if d2 > 0:
        best = max(best, _arb_lo(abs((D.conjugate() * A).imag) / d2.sqrt()))
    return best


def _iv_lo(x) -> float:
    v = float(mp.make_mpf(x._mpi_[0]))
    return v * LO if v > 0 else v * HI


def _iv_hi(x) -> float:
    v = float(mp.make_mpf(x._mpi_[1]))
    return v * HI if v > 0 else v * LO


def _iv_conj(z):
    # mpmath 1.3's ivmpc.conjugate passes an interval pair to mpf_neg and
    # raises; the conjugate is built from the parts instead.
    return iv.mpc(z.real, -z.imag)


def _iv_clearance(A, B) -> float:
    with _ivprec(128):
        D = B - A
        Dc = _iv_conj(D)
        p = (Dc * (-A)).real
        d2 = D.real * D.real + D.imag * D.imag
        if _iv_hi(p) < 0:
            return _iv_lo(abs(A))
        if _iv_lo(p - d2) > 0:
            return _iv_lo(abs(B))
        best = _iv_lo(abs(A) - abs(D))
        if _iv_lo(d2) > 0:
            best = max(best, _iv_lo(abs((Dc * A).imag) / iv.sqrt(d2)))
        return best


def _abs_hi(route, z) -> float:
    if route.name == "python-flint":
        old = fctx.prec
        fctx.prec = route.prec
        try:
            return _arb_hi(abs(z))
        finally:
            fctx.prec = old
    with _ivprec(route.prec):
        return _iv_hi(abs(z))


def _clearance(route, A, B) -> float:
    if route.name == "python-flint":
        old = fctx.prec
        fctx.prec = route.prec
        try:
            return _arb_clearance(A, B)
        finally:
            fctx.prec = old
    return _iv_clearance(A, B)


def second_derivative_bound(route, centre, half: Fraction, R: Fraction) -> dict:
    """M2 >= sup |f''| on the rectangle, from one evaluation over the R-square."""
    b, g = centre
    z = route.f_box(b - R, b + R, g - R, g + R)
    B = _abs_hi(route, z)
    rho = float(R - half) * LO
    return {"R": str(R), "B_abs_f_on_square": B, "M2": 2 * B / rho**2 * HI}


def count_zeros(route, centre, half: Fraction, R: Fraction,
                init_per_side: int = 4, max_depth: int = 10):
    """Decided argument-principle count on the rectangle, or 'undecided'."""
    t0 = time.time()
    corners = rectangle(centre[0], centre[1], half)
    m2 = second_derivative_bound(route, centre, half, R)
    M2 = m2["M2"]
    cache = {}

    def pt(p):
        v = cache.get(p)
        if v is None:
            v = route.f_box(p[0], p[0], p[1], p[1])
            cache[p] = v
        return v

    pieces = []
    worst_margin = math.inf
    for e in range(4):
        a, b = corners[e], corners[(e + 1) % 4]
        stack = []
        for i in range(init_per_side, 0, -1):
            pa = (a[0] + (b[0] - a[0]) * Fraction(i - 1, init_per_side),
                  a[1] + (b[1] - a[1]) * Fraction(i - 1, init_per_side))
            pb = (a[0] + (b[0] - a[0]) * Fraction(i, init_per_side),
                  a[1] + (b[1] - a[1]) * Fraction(i, init_per_side))
            stack.append((pa, pb, 0))
        while stack:
            pa, pb, depth = stack.pop()
            ell = float(abs(pb[0] - pa[0]) + abs(pb[1] - pa[1])) * HI
            tube = M2 * ell * ell / 8 * HI
            clear = _clearance(route, pt(pa), pt(pb))
            ok = clear > tube
            got = route.arg_quotient(pt(pb), pt(pa)) if ok else None
            if got is None:
                if depth >= max_depth:
                    return {"status": "undecided", "failing_segment":
                            [[str(pa[0]), str(pa[1])], [str(pb[0]), str(pb[1])]],
                            "tube_ok": ok, "clearance": clear, "tube": tube,
                            "second_derivative": m2, "seconds": time.time() - t0}
                mid = ((pa[0] + pb[0]) / 2, (pa[1] + pb[1]) / 2)
                stack.append((mid, pb, depth + 1))
                stack.append((pa, mid, depth + 1))
                continue
            worst_margin = min(worst_margin, clear / tube)
            pieces.append(got)
    with _ivprec(128):
        tot = iv.mpf(0)
        for lo, hi, _ in pieces:
            lo_f = mpmath.mpf(lo) - abs(mpmath.mpf(lo)) * 2**-50 - mpmath.mpf(2)**-1000
            hi_f = mpmath.mpf(hi) + abs(mpmath.mpf(hi)) * 2**-50 + mpmath.mpf(2)**-1000
            tot += iv.mpf([lo_f, hi_f])
        w = tot / (2 * iv.pi)
        wl = mp.make_mpf(w._mpi_[0])
        wh = mp.make_mpf(w._mpi_[1])
    ints = [k for k in range(int(math.floor(wl)), int(math.ceil(wh)) + 1) if wl <= k <= wh]
    out = {"segments": len(pieces), "point_evals": len(cache),
           "second_derivative": m2, "worst_clearance_over_tube": worst_margin,
           "winding_lo": float(wl), "winding_hi": float(wh),
           "seconds": round(time.time() - t0, 2)}
    if len(ints) == 1:
        out.update(status="decided", count=ints[0])
    else:
        out.update(status="undecided", candidates=ints)
    return out


# ---------------------------------------------------------------------------
# float polish (steering only, labelled measured)
# ---------------------------------------------------------------------------

def polish(beta: float, gamma: float, prec: int = 192):
    """Newton on Arb ball midpoints; steering only, measured grade.

    (mpmath's own Hurwitz zeta costs minutes per call at this height, so the
    steering pass uses Arb midpoints; nothing decided depends on it.)
    """
    route = ArbRoute(prec=prec)
    sb, sg = Fraction(beta), Fraction(gamma)
    h = Fraction(1, 2**60)

    def val(b, g):
        z = route.f_box(b, b, g, g)
        return complex(float(z.real.mid()), float(z.imag.mid()))

    fp = None
    for _ in range(4):
        f0 = val(sb, sg)
        fp = (val(sb + h, sg) - val(sb - h, sg)) / (2 * float(h))
        step = f0 / fp
        sb -= Fraction(step.real)
        sg -= Fraction(step.imag)
        if abs(step) < 1e-15:
            break
    return mp.mpc(float(sb), float(sg)), abs(val(sb, sg)), fp


# ---------------------------------------------------------------------------
# Arb versus iv, on exact endpoints (added 2026-10-26 in review)
# ---------------------------------------------------------------------------
#
# The gate of MISSION.md section 8 asks that the iv route agree with Arb at
# test points to within the union of their enclosures.  The first version of
# this check compared float64 midpoints with a slack of radii + 1e-30.  At
# |f| ~ 1e-8 the float64 spacing is about 1e-24, far above both radii (7e-33
# and 5e-31), so it passed exactly when the two midpoints rounded to the same
# double, and the 1e-30 slack would also have passed enclosures lying apart.
# It could not fail on the property it named.  These functions read every
# endpoint as an exact rational: two enclosures intersect iff, in the real
# and in the imaginary part, lo_A <= hi_B and lo_B <= hi_A.  No float enters.

def _frac_man_exp(m, e) -> Fraction:
    m, e = int(m), int(e)
    return Fraction(m * 2**e) if e >= 0 else Fraction(m, 2**(-e))


def arb_box_exact(z) -> dict:
    """Exact rational endpoints of an Arb complex ball, as {"re": (lo, hi), "im": (lo, hi)}."""
    out = {}
    for name, part in (("re", z.real), ("im", z.imag)):
        out[name] = tuple(_frac_man_exp(*x.man_exp()) for x in (part.lower(), part.upper()))
    return out


def _frac_raw_mpf(raw) -> Fraction:
    """A raw mpmath mpf tuple (sign, man, exp, bc) as an exact rational.

    (mpmath's ``mpf.man_exp`` drops the sign, so the raw tuple is read.)
    """
    sign, man, exp, bc = raw
    if man == 0:
        if raw != (0, 0, 0, 0):
            raise ValueError("infinite or NaN interval endpoint")
        return Fraction(0)
    v = _frac_man_exp(man, exp)
    return -v if sign else v


def iv_box_exact(z) -> dict:
    """Exact rational endpoints of an mpmath.iv complex interval."""
    out = {}
    for name, part in (("re", z.real), ("im", z.imag)):
        out[name] = tuple(_frac_raw_mpf(raw) for raw in part._mpi_)
    return out


def enclosures_intersect(a: dict, b: dict) -> bool:
    """True iff the two boxes share a point: both parts overlap, endpoints exact."""
    return all(a[k][0] <= a[k][1] and b[k][0] <= b[k][1]
               and a[k][0] <= b[k][1] and b[k][0] <= a[k][1] for k in ("re", "im"))


def box_to_json(box: dict) -> dict:
    return {k: [str(box[k][0]), str(box[k][1])] for k in ("re", "im")}


def box_from_json(d: dict) -> dict:
    return {k: (Fraction(d[k][0]), Fraction(d[k][1])) for k in ("re", "im")}


def cross_check_exact(arb_route, iv_route, points) -> list:
    """Arb and iv enclosures of f at each exact point, compared on exact endpoints."""
    rows = []
    for (sg, tt) in points:
        old = fctx.prec
        fctx.prec = arb_route.prec
        try:
            A = arb_box_exact(arb_route.f_box(sg, sg, tt, tt))
        finally:
            fctx.prec = old
        with _ivprec(iv_route.prec):
            B = iv_box_exact(iv_route.f_box(sg, sg, tt, tt))
        part = {}
        for k in ("re", "im"):
            ov = A[k][0] <= B[k][1] and B[k][0] <= A[k][1]
            mid_gap = abs((A[k][0] + A[k][1]) / 2 - (B[k][0] + B[k][1]) / 2)
            part[k] = {"overlap": bool(ov),
                       "width_arb": float(A[k][1] - A[k][0]),
                       "width_iv": float(B[k][1] - B[k][0]),
                       "midpoint_gap": float(mid_gap)}
        rows.append({"s": [str(sg), str(tt)], "arb": box_to_json(A), "iv": box_to_json(B),
                     "parts": part, "intersect": enclosures_intersect(A, B)})
    return rows


def rerun_cross_check() -> None:
    """Recompute the gate's cross-check on exact endpoints and add it to the artifact.

    Reads the recorded rectangle from `decide_deep_zero.json`, rebuilds both
    routes exactly as `main` builds them (Arb at 128 bits; iv at 128 bits, Taylor
    model radius 2^-12, K = 14, about 6 minutes for the head at this height),
    and evaluates the same three points as the recorded check: two corners and
    the centre.  Recorded keys are kept as they are; the new ones are added.
    """
    with open(OUT) as fh:
        result = json.load(fh)
    sl, sh = (Fraction(x) for x in result["rectangle"]["sigma"])
    tl, th = (Fraction(x) for x in result["rectangle"]["t"])
    centre = ((sl + sh) / 2, (tl + th) / 2)
    t0 = time.time()
    arb_route = ArbRoute(prec=128)
    ivr = IvRoute(prec=128, centre=centre, radius=Fraction(1, 2**12), K=14, log_every=0)
    head = time.time() - t0
    rows = cross_check_exact(arb_route, ivr, [(sl, tl), (sh, th), centre])
    result["cross_check_exact"] = rows
    result["cross_check_exact_run"] = {
        "date": "2026-10-26", "python": platform.python_version(), "mpmath": mpmath.__version__,
        "rigor_BACKEND": rigor.BACKEND, "iv_N": ivr.N, "iv_p": ivr.p, "iv_K": ivr.K,
        "iv_head_seconds": round(head, 1), "seconds_total": round(time.time() - t0, 1),
        "all_intersect": all(r["intersect"] for r in rows)}
    result["cross_check_note"] = (
        "Added 2026-10-26 in review (RESULTS.md section 8.16, Run 22 in RUNS.md). The recorded "
        "'cross_check' compared float64 midpoints with a slack of radii + 1e-30, which passes "
        "whenever the two midpoints round to the same double and so could not fail on the "
        "property it names; it is kept as recorded. 'cross_check_exact' compares exact rational "
        "endpoints with no slack and is the check the gate reads.")
    result["steering_route_note"] = (
        "Added 2026-10-26 in review: the recorded 'steering.route' label is wrong. polish() "
        "runs Newton on Arb ball midpoints at 192 bits, not on mpmath's Hurwitz zeta at dps 40. "
        "Steering only; nothing decided depends on it.")
    with open(OUT, "w") as fh:
        json.dump(result, fh, indent=2, default=str)
    print(json.dumps(result["cross_check_exact_run"]), flush=True)
    for r in rows:
        print(r["s"], r["intersect"], r["parts"], flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="Arb only, no iv head")
    ap.add_argument("--cross-check-only", action="store_true",
                    help="recompute the Arb-vs-iv check on exact endpoints into the existing artifact")
    ap.add_argument("--half-bits", type=int, default=27,
                    help="rectangle half-width 2^-bits (default 2^-27 ~ 7.5e-9)")
    args = ap.parse_args()

    print("backend", rigor.BACKEND, rigor.available_backends(), flush=True)
    if args.cross_check_only:
        rerun_cross_check()
        return
    t_all = time.time()

    # steering: one Newton polish on Arb ball midpoints (measured; label corrected
    # 2026-10-26 in review, it said mpmath's own Hurwitz zeta)
    s_pol, fabs, fp = polish(BETA_FLOAT, GAMMA_FLOAT)
    beta_c = dyadic(float(s_pol.real), 40)
    gamma_c = Fraction(round(float(s_pol.imag) * 2**30), 2**30)
    half = Fraction(1, 2**args.half_bits)
    corners = rectangle(beta_c, gamma_c, half)
    centre = (beta_c, gamma_c)
    R = Fraction(1, 2**13)
    shifted_centre = (beta_c + 4 * half, gamma_c)
    print("polish", s_pol, "abs f", fabs, "abs f'", abs(fp), flush=True)

    result = {
        "what": "decided argument-principle count of zeros of the Davenport-Heilbronn f in an exact rectangle near the height-1e6 float zero of deep_zeros_1e6.json",
        "date": "2026-10-26",
        "python": platform.python_version(),
        "mpmath": mpmath.__version__,
        "rigor_BACKEND": rigor.BACKEND,
        "steering": {"route": "Newton on Arb ball midpoints, 192 bits (measured; steering only)",
                     "s": [str(s_pol.real), str(s_pol.imag)],
                     "abs_f": float(fabs), "abs_fprime": float(abs(fp))},
        "rectangle": {"sigma": [str(beta_c - half), str(beta_c + half)],
                      "t": [str(gamma_c - half), str(gamma_c + half)],
                      "half_width": str(half)},
        "routes": {},
        "faults": {},
    }

    arb_route = ArbRoute(prec=128)
    r = count_zeros(arb_route, centre, half, R)
    r["prec_bits"] = 128
    result["routes"]["python-flint"] = r
    print("arb", r, flush=True)

    # planted faults on the Arb route: kappa perturbed by 1e-3, rectangle shifted by 4 half-widths
    bad_k = count_zeros(ArbRoute(prec=128, kappa_shift=Fraction(1, 1000)), centre, half, R)
    bad_s = count_zeros(arb_route, shifted_centre, half, R)
    result["faults"]["python-flint"] = {"kappa_plus_1e-3": bad_k, "rectangle_shifted_4_half_widths": bad_s}
    print("arb faults", bad_k, bad_s, flush=True)

    if not args.quick:
        # the Taylor model must cover both R-squares: radius 2^-12 > sqrt2 (R + 4 half)
        ivr = IvRoute(prec=128, centre=centre, radius=Fraction(1, 2**12), K=14)
        print("iv head", ivr.head_seconds, "N", ivr.N, flush=True)
        r2 = count_zeros(ivr, centre, half, R)
        r2.update(prec_bits=128, N=ivr.N, p=ivr.p, K=ivr.K, head_seconds=round(ivr.head_seconds, 1))
        result["routes"]["mpmath.iv"] = r2
        print("iv", r2, flush=True)
        bad_s2 = count_zeros(ivr, shifted_centre, half, R)
        result["faults"]["mpmath.iv"] = {"rectangle_shifted_4_half_widths": bad_s2}
        # cross-check at three points: the two enclosures must intersect, on exact
        # endpoints (2026-10-26 in review; the float-midpoint version could not fail)
        xs = cross_check_exact(arb_route, ivr, [corners[0], corners[2], (beta_c, gamma_c)])
        result["cross_check_exact"] = xs
        print("cross", xs, flush=True)

    # The decided rectangle must lie in Re s > 1/2 and contain the float datum.
    sig_lo = beta_c - half
    result["rectangle_right_of_half_line"] = sig_lo > Fraction(1, 2)
    result["float_datum_inside"] = (abs(Fraction(BETA_FLOAT) - beta_c) <= half
                                    and abs(Fraction(GAMMA_FLOAT) - gamma_c) <= half)
    result["depth_y0_enclosure"] = [str(beta_c - half - Fraction(1, 2)), str(beta_c + half - Fraction(1, 2))]
    result["seconds_total"] = round(time.time() - t_all, 1)
    with open(OUT, "w") as fh:
        json.dump(result, fh, indent=2, default=str)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
