"""Arb evaluator of the Polymath 15 effective approximation to H_t(x + iy).

Source, read as data and never executed: D.H.J. Polymath, "Effective
approximation of heat flow evolution of the Riemann xi function, and a new upper
bound for the de Bruijn-Newman constant", arXiv:1904.12438v2.  The source tarball
was downloaded on 2026-10-21 into
``<cache>/dbn/evaluator-arxiv-1904.12438v2/`` (sha256
``1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863``); line
numbers below refer to its ``debruijn.tex``.

What is implemented (labels are the paper's own equation labels):

* ``alpha``, ``log_M0``, ``log_Mt``: (alpha-form), (logM), (Mt-def), lines 174-197.
* ``point``: the A + B - C approximation of Corollary (abc-cor), lines 926-948,
  in the normalised form (ratio-form-refined), lines 961-975: f_t, C_t/B_t and
  the error quantities e_A, e_B, e_C, e_{C,0} exactly as defined in
  (ea-def)-(ec-def), with eps_{t,n} of (eps-def) and eps~ of (epsp-def).  Direct
  summation over n <= N.
* ``theorem_bounds``: the closed-form bounds (gamma-bound)-(ec-bound) of
  Theorem (eff), lines 237-243, and Proposition (estimates)(vi), lines 992-996.
* ``trib2_bounds`` and ``euler2_lower_bound``: Lemma (trib2), lines 1975-1992,
  applied as in Section 10 (lines 1965-1994) to bound |f_t(x + i y)| from below
  uniformly over all x with a given N (the "Euler 2" bound of Table 1).
* ``euler_mollified_F``: the Euler-mollified quantity F_{N-,N+} of Section 8.5
  (lines 1570-1742), for any set of primes (2, 3, 5 is the paper's Euler 5).
* ``derivative_bounds``: the |df/dz| and |df/dt| bounds of the Lemma at lines
  1442-1453, as suprema over a rectangle.
* ``FixedTimeMultiEval``: Taylor multi-evaluation of f_t at many mesh points
  (Section 7, lines 1114-1152), here with blocks of bounded log-width and an
  explicit truncation bound charged into every enclosure.
* ``barrier_rectangle``: the Rouche / winding check of Section 8.4 (lines
  1421-1438) on one rectangle at one time t.

Every quantity is an Arb ball (python-flint).  A returned ball contains the
exact value of the formula it implements, for every input in the input balls;
this is what the laboratory's ladder calls enclosure-carrying.  The analytic
step, that H_t/B_t lies within e_A + e_B + e_C of f_t - C_t/B_t, is the
paper's published Theorem 1.3 / Corollary 6.4, used as published.  This module
does not prove it, and nothing here is a statement about the de Bruijn-Newman
constant.

Precision: every public function runs inside its own working precision (default
``PREC`` bits) and restores python-flint's global ``ctx.prec`` on exit.
"""

from __future__ import annotations

import contextlib
import math
import time
from dataclasses import dataclass
from typing import Any, Iterable, Sequence

from flint import acb, acb_poly, arb, ctx, fmpz

__all__ = [
    "PREC",
    "workprec",
    "to_arb",
    "alpha",
    "alpha_prime",
    "log_M0",
    "log_Mt",
    "C0",
    "N_of",
    "x_of_N",
    "Point",
    "point",
    "theorem_bounds",
    "trib2_bounds",
    "euler2_lower_bound",
    "unmollified_triangle_bound",
    "mollifier_coefficients",
    "euler_mollified_F",
    "derivative_bounds",
    "FixedTimeMultiEval",
    "barrier_rectangle",
]

#: Default working precision in bits.  At x ~ 5e12 the phases (x/2) log n are
#: ~3e13 radians, so 128 bits leaves ~80 bits of each phase after the integer
#: part; the tests re-run key points at 192 bits and require the balls to agree.
PREC: int = 128


# --------------------------------------------------------------------------- #
#  Precision and conversion helpers
# --------------------------------------------------------------------------- #

@contextlib.contextmanager
def workprec(bits: int | None):
    """Set python-flint's working precision for the block, then restore it."""
    old = ctx.prec
    ctx.prec = int(PREC if bits is None else bits)
    try:
        yield
    finally:
        ctx.prec = old


def to_arb(v: Any) -> arb:
    """Convert to an arb ball.  Strings are parsed as exact decimals (a ball of
    radius ~2^-prec around the decimal); ints are exact; an ``arb`` passes
    through; a float is taken as its exact binary value."""
    if isinstance(v, arb):
        return v
    if isinstance(v, (int, fmpz)):
        return arb(v)
    if isinstance(v, str):
        return arb(v)
    if isinstance(v, float):
        return arb(v)
    raise TypeError(f"cannot convert {type(v).__name__} to arb")


def _c(s: str) -> arb:
    """A decimal constant printed in the paper, as an exact-decimal ball."""
    return arb(s)


def _hull(a: arb, b: arb) -> arb:
    """Smallest ball containing both balls."""
    return a.union(b)


def _disk(r: arb) -> acb:
    """A complex box containing the closed disk of radius r about 0."""
    ru = r.upper()
    rr = _hull(ru, -ru)
    return acb(rr, rr)


def _pos(v: arb) -> arb:
    """Positive part max(v, 0) of a real ball (a ball containing it)."""
    return v.nonnegative_part()


def _max_upper(a: arb, b: arb) -> arb:
    """An exact point >= every element of both balls: max(upper(a), upper(b))."""
    au, bu = a.upper(), b.upper()
    return au if au > bu else bu


def _pow_ui_upper(r: arb, k: int) -> arb:
    """An upper bound for r^k, r >= 0, by repeated multiplication of upper(r).

    ``arb ** int`` goes through exp(k log r) and returns NaN when the ball
    touches 0, which happens exactly at the expansion centre.
    """
    ru = _hull(arb(0), r.upper()).upper()
    p = arb(1)
    for _ in range(k):
        p = p * ru
    return p.upper()


def _upper_float(v: arb) -> float:
    """A float that is >= every point of the ball (rounded outward)."""
    u = float(v.upper())
    return math.nextafter(u, math.inf)


def _lower_float(v: arb) -> float:
    """A float that is <= every point of the ball (rounded outward)."""
    lo = float(v.lower())
    return math.nextafter(lo, -math.inf)


# --------------------------------------------------------------------------- #
#  The gamma-factor pieces: alpha, M_0, M_t
# --------------------------------------------------------------------------- #

def alpha(s: acb) -> acb:
    """alpha(s) = 1/(2s) + 1/(s-1) + (1/2) Log(s/(2 pi)), (alpha-form).

    The logarithmic derivative of M_0.  Principal branch; valid off (-inf, 1].
    """
    pi = arb.pi()
    return 1 / (2 * s) + 1 / (s - 1) + (s / (2 * pi)).log() / 2


def alpha_prime(s: acb) -> acb:
    """alpha'(s) = -1/(2 s^2) - 1/(s-1)^2 + 1/(2s), (alpha-deriv)."""
    return -1 / (2 * s * s) - 1 / ((s - 1) * (s - 1)) + 1 / (2 * s)


def log_M0(s: acb) -> acb:
    """The holomorphic branch (logM) of log M_0(s) on C minus (-inf, 1].

    M_0(s) = (1/8) (s(s-1)/2) pi^{-s/2} sqrt(2 pi) exp((s/2 - 1/2) Log(s/2) - s/2)
    is the Stirling approximation to (1/8)(s(s-1)/2) pi^{-s/2} Gamma(s/2).
    """
    pi = arb.pi()
    half = arb(1) / 2
    return (
        s.log()
        + (s - 1).log()
        - (s / 2) * pi.log()
        + ((2 * pi).sqrt() / 16).log()
        + (s / 2 - half) * (s / 2).log()
        - s / 2
    )


def log_Mt(s: acb, t: arb) -> acb:
    """log M_t(s) = (t/4) alpha(s)^2 + log M_0(s), (Mt-def)."""
    a = alpha(s)
    return (t / 4) * a * a + log_M0(s)


# --------------------------------------------------------------------------- #
#  The Riemann-Siegel correction: C_0(p), (C0-def)
# --------------------------------------------------------------------------- #

def _C0_num(u: arb) -> acb:
    pi = arb.pi()
    i = acb(0, 1)
    ph = (i * pi * (u * u / 2 + arb(3) / 8)).exp()
    return ph - i * arb(2).sqrt() * (pi * u / 2).cos()


def _C0_num_d1(u: arb) -> acb:
    pi = arb.pi()
    i = acb(0, 1)
    ph = (i * pi * (u * u / 2 + arb(3) / 8)).exp()
    return i * pi * u * ph + i * arb(2).sqrt() * (pi / 2) * (pi * u / 2).sin()


def _C0_num_d2(u: arb) -> acb:
    pi = arb.pi()
    i = acb(0, 1)
    ph = (i * pi * (u * u / 2 + arb(3) / 8)).exp()
    return (i * pi - pi * pi * u * u) * ph + i * arb(2).sqrt() * (pi * pi / 4) * (pi * u / 2).cos()


def C0(p: arb) -> acb:
    """C_0(p) = (e^{pi i (p^2/2 + 3/8)} - i sqrt2 cos(pi p/2)) / (2 cos(pi p)).

    (C0-def), line 695.  The singularities at p = +-1/2 are removable.  Away from
    them (|p -+ 1/2| >= 1e-6) the formula is used directly.  Near p0 = +-1/2,
    with eps = p - p0, the numerator is n'(p0) eps + (eps^2/2) n''(xi) for some
    xi between p0 and p (Taylor with integral remainder, enclosed by evaluating
    n'' on the hull of [p0, p]), and cos(pi p) = -+ pi eps sinc(pi eps), so the
    eps cancels exactly.
    """
    p = to_arb(p)
    pi = arb.pi()
    thr = arb("1e-6")
    for p0, sgn in ((arb(1) / 2, -1), (-arb(1) / 2, 1)):
        eps = p - p0
        if abs(eps) < thr:
            hull = _hull(p0, p)
            numer = _C0_num_d1(p0) + (eps / 2) * _C0_num_d2(hull)
            denom = sgn * 2 * pi * (pi * eps).sinc()
            return numer / denom
    return _C0_num(p) / (2 * (pi * p).cos())


# --------------------------------------------------------------------------- #
#  N and the jump points x_N
# --------------------------------------------------------------------------- #

def N_of(x: arb, t: arb) -> int:
    """N = floor(sqrt(x/(4 pi) + t/16)), (N-def-main).  Refuses if ambiguous."""
    a = (x / (4 * arb.pi()) + t / 16).sqrt()
    fl = a.floor()
    try:
        return int(fl.unique_fmpz())
    except Exception as exc:  # pragma: no cover - ball straddles an integer
        raise ValueError(f"N is not determined by the input balls: a = {a}") from exc


def x_of_N(N: int, t: arb) -> arb:
    """x_N = 4 pi N^2 - pi t / 4: the smallest x at which N(x) = N, (xnn)."""
    return 4 * arb.pi() * N * N - arb.pi() * t / 4


# --------------------------------------------------------------------------- #
#  The point evaluator: f_t, C_t/B_t, e_A, e_B, e_C, e_{C,0}
# --------------------------------------------------------------------------- #

def _eps_tn(alpha_s: acb, L: arb, T: arb, t: arb) -> arb:
    """eps_{t,n}(sigma + iT) of (eps-def): expm1(((t^2/8)|alpha - log n|^2 + t/4 + 1/6)/(T - 3.33))."""
    d = alpha_s - L
    mod2 = d.real * d.real + d.imag * d.imag
    num = (t * t / 8) * mod2 + t / 4 + arb(1) / 6
    return (num / (T - _c("3.33"))).expm1()


def _eps_tilde(sigma: arb, T: arb, a: arb) -> arb:
    """eps~(sigma + iT) of (epsp-def)."""
    return (
        _c("0.397") * (arb(9) ** sigma) / (a - _c("0.865"))
        + arb(5) / (3 * (T - 6))
    ) * (_c("3.49") / (T - 4)).exp()


def _eC_pair(x: arb, y: arb, t: arb) -> tuple[arb, arb]:
    """(e_C, e_{C,0}) exactly as defined in (ecc-def) and (ec-def), lines 972-973.

    e_{C,0} = exp(t pi^2/64) |M_0(iT')| / |M_t(s_+)| (1 + eps~(s_-) + eps~(s_+)) and
    e_C is the same without the 1.  No sum over n is involved, so the inputs may
    be wide balls: the result then contains the value at every (x, y) in them.
    ``point`` and the rectangle error bound both use this one function.
    """
    pi = arb.pi()
    s_plus = acb(1 + y, -x) / 2
    T = x / 2
    Tp = x / 2 + pi * t / 8
    a = (Tp / (2 * pi)).sqrt()
    lM0_iT = log_M0(acb(0, Tp))
    ratio_mod = (t * pi * pi / 64 + lM0_iT.real - log_Mt(s_plus, t).real).exp()
    et = _eps_tilde((1 - y) / 2, T, a) + _eps_tilde((1 + y) / 2, T, a)
    return ratio_mod * et, ratio_mod * (1 + et)


@dataclass
class Point:
    """Everything Theorem 1.3 needs at one point (x, y, t).  All balls."""

    x: arb
    y: arb
    t: arb
    prec: int
    N: int
    s_plus: acb
    s_minus: acb
    alpha_plus: acb
    alpha_minus: acb
    s_star: acb
    s_2star: acb
    kappa: acb
    log_gamma: acb
    gamma: acb
    log_Bt: acb
    sum_B: acb
    sum_A: acb
    abs_B: arb
    abs_A: arb
    f: acb
    CB: acb
    e_A: arb
    e_B: arb
    e_C: arb
    e_C0: arb
    Tp: arb
    a: arb
    p: arb
    C0p: acb
    seconds: float = 0.0
    error_mode: str = "exact"

    # -- normalised enclosures of H_t / B_t ------------------------------- #
    def ratio_ABC(self, drop: Iterable[str] = ()) -> acb:
        """Ball containing H_t/B_t: f - C/B plus a disk of radius e_A + e_B + e_C.

        ``drop`` removes named error terms ("A", "B", "C"); used only by the
        lesion tests, which must see the containment fail when e_C is dropped.
        """
        drop = set(drop)
        r = arb(0)
        if "A" not in drop:
            r += self.e_A
        if "B" not in drop:
            r += self.e_B
        if "C" not in drop:
            r += self.e_C
        with workprec(self.prec):
            return self.f - self.CB + _disk(r)

    def ratio_AB(self) -> acb:
        """Ball containing H_t/B_t: f plus a disk of radius e_A + e_B + e_{C,0}."""
        with workprec(self.prec):
            return self.f + _disk(self.e_A + self.e_B + self.e_C0)

    # -- unnormalised enclosures of H_t itself (moderate x only) ---------- #
    def Bt(self) -> acb:
        with workprec(self.prec):
            return self.log_Bt.exp()

    def Ht_ABC(self, drop: Iterable[str] = ()) -> acb:
        """Ball containing H_t(x+iy) = A + B - C + O(E_A + E_B + E_C)."""
        drop = set(drop)
        with workprec(self.prec):
            Bt = self.log_Bt.exp()
            r = arb(0)
            if "A" not in drop:
                r += self.e_A
            if "B" not in drop:
                r += self.e_B
            if "C" not in drop:
                r += self.e_C
            return Bt * (self.f - self.CB) + _disk(abs(Bt) * r)

    def ABC_value(self) -> acb:
        """A + B - C itself (no error disk)."""
        with workprec(self.prec):
            return self.log_Bt.exp() * (self.f - self.CB)

    def errors_unnormalised(self) -> dict[str, arb]:
        with workprec(self.prec):
            m = abs(self.log_Bt.exp())
            return {"E_A": self.e_A * m, "E_B": self.e_B * m, "E_C": self.e_C * m, "E_C0": self.e_C0 * m}


def _check_region(x: arb, y: arb, t: arb) -> None:
    """The region (region), line 169: 0 < t <= 1/2, 0 <= y <= 1, x >= 200.

    t = 0 is admitted as well.  The paper states Theorem 1.3 and Corollaries
    6.4 and 6.5 only for t > 0; at t = 0 they follow by letting t -> 0+, since at
    fixed (x, y) both sides are continuous in t and N(x, t) = N(x, 0) for all
    small t > 0 (floor is right-continuous).  That extension is this lab's
    derivation, unreviewed; EVALUATOR.md says which results rest on it.
    """
    if not (x >= 200):
        raise ValueError("Theorem 1.3 needs x >= 200")
    if not (y >= 0 and y <= 1):
        raise ValueError("Theorem 1.3 needs 0 <= y <= 1")
    if not (t >= 0 and t <= arb(1) / 2):
        raise ValueError("Theorem 1.3 needs 0 < t <= 1/2 (t = 0 by continuity)")


def point(x: Any, y: Any, t: Any, prec: int | None = None, error_mode: str = "exact") -> Point:
    """Evaluate f_t, C_t/B_t and the error quantities at x + iy, time t.

    ``error_mode="exact"`` sums eps_{t,n} term by term as in (ea-def), (eb-def).
    ``error_mode="envelope"`` replaces eps_{t,n} by its maximum over 1 <= n <= N
    (attained at an endpoint, since |alpha - log n|^2 is convex in log n), which
    can only enlarge e_A and e_B; it is cheaper at large N.
    """
    if error_mode not in ("exact", "envelope"):
        raise ValueError("error_mode must be 'exact' or 'envelope'")
    t_start = time.perf_counter()
    with workprec(prec):
        x, y, t = to_arb(x), to_arb(y), to_arb(t)
        _check_region(x, y, t)
        pi = arb.pi()
        s_plus = acb(1 + y, -x) / 2
        s_minus = acb(1 - y, x) / 2
        a_plus = alpha(s_plus)
        a_minus = alpha(s_minus)
        s_star = s_plus + (t / 2) * a_plus
        s_2star = s_minus + (t / 2) * a_minus
        kappa = (t / 2) * (a_minus - alpha(acb(1 + y, x) / 2))
        lMt_plus = log_Mt(s_plus, t)
        lMt_minus = log_Mt(s_minus, t)
        log_gamma = lMt_minus - lMt_plus
        gamma = log_gamma.exp()
        T = x / 2
        Tp = x / 2 + pi * t / 8
        a = (Tp / (2 * pi)).sqrt()
        N = N_of(x, t)
        p = 1 - 2 * (a - N)
        tq = t / 4

        # eps_{t,n} pieces.  |alpha(s) - L|^2 is a convex quadratic in L, so on
        # 0 <= L <= log N its maximum is at an endpoint (envelope mode).
        logN = arb(N).log()
        if error_mode == "envelope":
            eps_B_max = _eps_tn(a_plus, arb(0), T, t).union(_eps_tn(a_plus, logN, T, t)).upper()
            eps_A_max = _eps_tn(a_minus, arb(0), T, t).union(_eps_tn(a_minus, logN, T, t)).upper()

        sum_B = acb(0)
        sum_A = acb(0)
        abs_B = arb(0)
        abs_A = arb(0)
        eB_sum = arb(0)
        eA_sum = arb(0)
        for n in range(1, N + 1):
            L = arb(n).log()
            qL = tq * L * L
            ex_B = qL - s_star * L
            ex_A = qL - s_2star * L
            term_B = ex_B.exp()
            term_A = ex_A.exp()
            mB = ex_B.real.exp()
            mA = ex_A.real.exp()
            sum_B += term_B
            sum_A += term_A
            abs_B += mB
            abs_A += mA
            if error_mode == "exact":
                eB_sum += mB * _eps_tn(a_plus, L, T, t)
                eA_sum += mA * _eps_tn(a_minus, L, T, t)
        if error_mode == "envelope":
            eB_sum = abs_B * eps_B_max
            eA_sum = abs_A * eps_A_max
        f = sum_B + gamma * sum_A
        e_B = eB_sum
        e_A = abs(gamma) * eA_sum

        # C_t / B_t, (abc-cor) and (ratio-form-refined).
        i = acb(0, 1)
        U = (-i * (Tp / 2 * (Tp / (2 * pi)).log() - Tp / 2 - pi / 8)).exp()
        C0p = C0(p)
        lM0_iT = log_M0(acb(0, Tp))
        Wtilde = (i * lM0_iT.imag).exp() * U * C0p * (i * pi / 8).exp()
        sign = 1 if N % 2 == 0 else -1
        CB = (
            2 * sign * (-i * pi * y / 8).exp() * (t * pi * pi / 64).exp() * Wtilde.real
            * (acb(lM0_iT.real) - lMt_plus).exp()
        )
        e_C, e_C0 = _eC_pair(x, y, t)
        cur = ctx.prec
    return Point(
        x=x, y=y, t=t, prec=cur, N=N, s_plus=s_plus, s_minus=s_minus,
        alpha_plus=a_plus, alpha_minus=a_minus, s_star=s_star, s_2star=s_2star,
        kappa=kappa, log_gamma=log_gamma, gamma=gamma, log_Bt=lMt_plus,
        sum_B=sum_B, sum_A=sum_A, abs_B=abs_B, abs_A=abs_A, f=f, CB=CB,
        e_A=e_A, e_B=e_B, e_C=e_C, e_C0=e_C0, Tp=Tp, a=a, p=p, C0p=C0p,
        seconds=time.perf_counter() - t_start, error_mode=error_mode,
    )


# --------------------------------------------------------------------------- #
#  Closed-form bounds of Theorem 1.3 and Proposition 6.6
# --------------------------------------------------------------------------- #

def theorem_bounds(P: Point) -> dict[str, arb]:
    """The closed-form bounds (gamma-bound)-(ec-bound) and Proposition 6.6(vi).

    Returned as balls; each is to be compared (as an upper or lower bound, see
    the key) with the exact quantity in ``P``.  ``res_bound_thm`` is the
    Theorem's printed form with 4y(1+y)/x^2; ``res_bound_prop`` is Proposition
    (estimates)(ii)'s 8y(1-y)/x^2, which is what the proof at lines 1032-1041
    actually derives.  They differ for y < 1/3 by O(t/x^4).

    ``eC_upper_prop`` and ``eC0_upper_prop`` are Proposition 6.6(vi) as printed
    (lines 992-996).  They are not bounds everywhere in the region: just above a
    jump x_N with small N the exact e_C exceeds the printed (vi) (by about 14%
    at N = 4; pinned by ``test_prop66_vi_fails_just_above_small_jumps``).  The
    step at line 1107 that replaces 0.397 9^sigma e^{3.49/(T-4)}/(a - 0.865) by
    1.24 3^{+-y}/(a - 0.125) needs a large a.  Nothing in this module relies on
    (vi): the barrier rectangle uses the exact (ec-def) through ``_eC_pair``.
    """
    with workprec(P.prec):
        x, y, t, N = P.x, P.y, P.t, P.N
        pi = arb.pi()
        X4 = x / (4 * pi)
        lX4 = X4.log()
        out: dict[str, arb] = {}
        out["gamma_upper"] = (_c("0.02") * y).exp() * (-(y / 2) * lX4).exp()
        out["res_bound_thm"] = (
            (1 + y) / 2 + (t / 4) * lX4
            - (t / (2 * x * x)) * _pos(1 - 3 * y + 4 * y * (1 + y) / (x * x))
        )
        out["res_bound_prop"] = (
            (1 + y) / 2 + (t / 4) * lX4
            - (t / (2 * x * x)) * _pos(1 - 3 * y + 8 * y * (1 - y) / (x * x))
        )
        out["kappa_upper"] = t * y / (2 * (x - 6))
        g = abs(P.gamma)
        Nk = (abs(P.kappa) * arb(N).log()).exp()
        rs = P.s_star.real
        tot = arb(0)
        for n in range(1, N + 1):
            L = arb(n).log()
            bn_over = ((t / 4) * L * L - rs * L).exp()
            l2 = (X4 / (n * n)).log()
            eps = (((t * t / 16) * l2 * l2 + _c("0.626")) / (x - _c("6.66"))).expm1()
            tot += (1 + g * Nk * (y * L).exp()) * bn_over * eps
        out["eAB_upper"] = tot
        lab = acb(lX4, pi / 2)
        out["eC0_upper_thm"] = (-((1 + y) / 4) * lX4).exp() * (
            -(t / 16) * lX4 * lX4
            + _c("1.24") * ((arb(3) ** y) + (arb(3) ** (-y))) / (N - _c("0.125"))
            + (3 * abs(lab) + _c("10.44")) / (x - 12)
        ).exp()
        pref = (-((1 + y) / 4) * lX4).exp() * (
            -(t / 16) * lX4 * lX4 + (3 * abs(lab) + _c("3.58")) / (x - _c("8.52"))
        ).exp()
        inner = _c("1.24") * ((arb(3) ** y) + (arb(3) ** (-y))) / (N - _c("0.125")) + _c("6.92") / (x - 12)
        out["eC_upper_prop"] = pref * inner
        out["eC0_upper_prop"] = pref * (1 + inner)
        out["C0_abs_upper"] = arb(1) / 2  # (cop), Arias de Reyna Thm 6.1, n = 0
    return out


# --------------------------------------------------------------------------- #
#  Lemma trib2 and the Euler 2 lower bound of Section 10
# --------------------------------------------------------------------------- #

def trib2_bounds(abs_terms: Sequence[arb], lam_abs: arb) -> tuple[arb, arb]:
    """Lemma (trib2).  For complex a_1..a_N and lambda with lambda a_{n/2} on the
    segment [0, a_n] for every even n <= N:

        |1 - lambda| |sum a_n| >= 2|a_1| - (1-|lambda|) sum|a_n| - 2|lambda| sum_{N/2<n<=N} |a_n|
        |1 - lambda| |sum a_n| <= (1-|lambda|) sum|a_n| + 2|lambda| sum_{N/2<n<=N} |a_n|

    ``abs_terms[k]`` is |a_{k+1}|.  Returns (lower, upper) for |1-lambda||sum a_n|.
    """
    N = len(abs_terms)
    S = arb(0)
    S_hi = arb(0)
    for n in range(1, N + 1):
        S += abs_terms[n - 1]
        if 2 * n > N:
            S_hi += abs_terms[n - 1]
    lower = 2 * abs_terms[0] - (1 - lam_abs) * S - 2 * lam_abs * S_hi
    upper = (1 - lam_abs) * S + 2 * lam_abs * S_hi
    return lower, upper


def _euler2_sums(N: int, t: arb, y: arb, sigma: arb) -> dict[str, arb]:
    """S_b = sum b_n n^-sigma, S_b_hi over N/2 < n <= N, and the n^y-weighted pair."""
    S_b = arb(0)
    S_b_hi = arb(0)
    S_a = arb(0)
    S_a_hi = arb(0)
    tq = t / 4
    for n in range(1, N + 1):
        L = arb(n).log()
        e = tq * L * L - sigma * L
        tb = e.exp()
        ta = (e + y * L).exp()
        S_b += tb
        S_a += ta
        if 2 * n > N:
            S_b_hi += tb
            S_a_hi += ta
    return {"S_b": S_b, "S_b_hi": S_b_hi, "S_a": S_a, "S_a_hi": S_a_hi}


def euler2_lower_bound(
    N: int,
    t: Any,
    y: Any,
    sigma: arb,
    gamma_abs: arb,
    kappa_abs: arb,
    prec: int | None = None,
) -> dict[str, Any]:
    """Lower bounds for |f_t(x + iy)| from Lemma (trib2), Section 10 (ftxy-2).

    Write s_* = sigma + iT.  Then f_t = sum beta_n + gamma conj(sum alpha_n n^-kappa)
    with beta_n = b_n n^{-s_*}, alpha_n = n^y b_n n^{-s_*}.  With
    lambda = b_2 2^{-s_*} one has lambda beta_{n/2} = (b_2 b_{n/2}/b_n) beta_n and
    lambda alpha_{n/2} = 2^{-y}(b_2 b_{n/2}/b_n) alpha_n, both factors in (0, 1]
    because log^2(2m) >= log^2 2 + log^2 m.  So Lemma (trib2) applies to both sums
    with the same lambda, |lambda| = r = b_2 2^{-sigma}, and

        |f| >= (LB_beta - |gamma| UB_alpha) / |1 - lambda| - Z
            >= (LB_beta - |gamma| UB_alpha) / (1 + r) - Z           ("joint")

    uniformly in T.  Also returned, for comparison with the printed Table 1 value:
    "separate" = LB_beta/(1+r) - |gamma| UB_alpha/(1-r) - Z and the unmollified
    "trivial" = 2 - S_b - |gamma| S_a - Z.  Z bounds the kappa term:
    |gamma| sum n^y b_n n^-sigma (n^|kappa| - 1) <= |gamma| S_a (N^|kappa| - 1).

    ``sigma``, ``gamma_abs`` and ``kappa_abs`` may be balls covering a range of
    x; the result then bounds every x in the range (each sum term is monotone
    in sigma, so the ball arithmetic loses only the tiny dependency width).
    """
    with workprec(prec):
        t, y = to_arb(t), to_arb(y)
        sums = _euler2_sums(N, t, y, sigma)
        r = ((t / 4) * arb(2).log() ** 2 - sigma * arb(2).log()).exp()
        S_b, S_b_hi, S_a, S_a_hi = sums["S_b"], sums["S_b_hi"], sums["S_a"], sums["S_a_hi"]
        LB_beta = 2 - (1 - r) * S_b - 2 * r * S_b_hi
        UB_alpha = (1 - r) * S_a + 2 * r * S_a_hi
        Z = gamma_abs * S_a * ((kappa_abs * arb(N).log()).exp() - 1)
        joint = (LB_beta - gamma_abs * UB_alpha) / (1 + r) - Z
        separate = LB_beta / (1 + r) - gamma_abs * UB_alpha / (1 - r) - Z
        trivial = 2 - S_b - gamma_abs * S_a - Z
        return {
            "r": r, "LB_beta": LB_beta, "UB_alpha": UB_alpha, "Z": Z,
            "joint": joint, "separate": separate, "trivial": trivial, **sums,
        }


def _tail_integral(llim: arb, ulim: arb, a: arb, b: arb) -> arb:
    """int_llim^ulim u^{-a + b log u} du = (sqrt(pi)/(2 sqrt b)) e^{-(1-a)^2/(4b)} [erfi]."""
    pi = arb.pi()
    sb = b.sqrt()
    pref = pi.sqrt() / sb / 2 * (-(a - 1) ** 2 / (4 * b)).exp()
    return pref * (((2 * b * ulim.log() - a + 1) / sb / 2).erfi() - ((2 * b * llim.log() - a + 1) / sb / 2).erfi())


def unmollified_triangle_bound(N: int, t: Any, y: Any, M: int = 2000, prec: int | None = None) -> dict[str, arb]:
    """Lower bound 2 - S_b - |gamma| S_a for |f_t(x + iy)| at every x with N(x) = N.

    The triangle inequality of Section 8.3, claim (c): f_t = 1 + O(S_b - 1 + |gamma| S_a)
    with S_b = sum_{n<=N} b_n n^{-sigma}, S_a = sum_{n<=N} n^y b_n n^{-sigma}, sigma the
    (res-bound) lower bound of Re s_* at x_N and |gamma| its (gamma-bound) majorant
    at x_N.  Terms n <= M are summed; for M < n <= N both summands decrease in n
    (their log-derivative in log n is (t/2) log n - sigma (+ y) < 0, because
    sigma > (1+y)/2 + (t/2) log N - small), so the tail is at most the integral
    from M to N, evaluated in closed form with erfi.  The kappa term is dropped
    (it is ~1e-15 relative at these heights and is not bounded here), so this
    is a projection aid; monotonicity in N is not established.
    """
    with workprec(prec):
        t, y = to_arb(t), to_arb(y)
        pi = arb.pi()
        xN = x_of_N(N, t)
        lX4 = (xN / (4 * pi)).log()
        sig = (1 + y) / 2 + (t / 4) * lX4 - (t / (2 * xN * xN)) * _pos(1 - 3 * y + 8 * y * (1 - y) / (xN * xN))
        g = (_c("0.02") * y).exp() * (-(y / 2) * lX4).exp()
        Sb = arb(0)
        Sa = arb(0)
        for n in range(1, min(M, N) + 1):
            L = arb(n).log()
            e = (t / 4) * L * L - sig * L
            Sb += e.exp()
            Sa += (e + y * L).exp()
        if N > M:
            Sb += _tail_integral(arb(M), arb(N), sig, t / 4)
            Sa += _tail_integral(arb(M), arb(N), sig - y, t / 4)
        return {"bound": 2 - Sb - g * Sa, "S_b": Sb, "S_a": Sa, "sigma": sig, "gamma_upper": g}


# --------------------------------------------------------------------------- #
#  The Euler mollifier of Section 8.5 (Euler 5 = primes 2, 3, 5)
# --------------------------------------------------------------------------- #

def _divisors(D: int) -> list[int]:
    return [d for d in range(1, D + 1) if D % d == 0]


def mollifier_coefficients(primes: Sequence[int], t: arb) -> dict[int, arb]:
    """lambda_d = prod_{p | d} (-b_p^t) for d | D = prod(primes)."""
    D = 1
    for q in primes:
        D *= q
    lam: dict[int, arb] = {}
    for d in _divisors(D):
        v = arb(1)
        for q in primes:
            if d % q == 0:
                v *= -(((t / 4) * arb(q).log() ** 2).exp())
        lam[d] = v
    return lam


def euler_mollified_F(
    N_minus: int,
    N_plus: int,
    t: Any,
    y: Any,
    primes: Sequence[int] = (2, 3, 5),
    c_gamma: arb | None = None,
    sigma: arb | None = None,
    truncation: str = "worst",
    prec: int | None = None,
    progress: bool = False,
) -> dict[str, Any]:
    """F_{N-,N+} of Section 8.5 (lines 1712-1736), generalised to any y and primes.

    For every N in [N-, N+] and x with that N, on the line y (time t),

        dist(E f_t, (-inf, 0]) >= F_{N-,N+} - Z,

    where E = prod_{p in primes} (1 - b_p p^{-s_*}) and
    F = 1 - a1 - sum_{n=2}^{D N+} max(|beta_n - a_n|, ((1-a1)/(1+a1)) |beta_n + a_n|) n^{-sigma},
    a_n = N-^{-y} alpha_n, alpha_n = c_gamma sum_{d | (n,D), n/d <= N} lambda_d (n/d)^y b_{n/d},
    beta_n = sum_{d | (n,D), n/d <= N} lambda_d b_{n/d}, a1 = c_gamma N-^{-y}.

    ``c_gamma`` defaults to the bound e^{0.02y} (1 - t/(16 N-^2))^{-y/2} on
    |gamma| N-^y, which follows from (gamma-bound) and x >= x_{N-}; the paper's
    y = 0.2 run used 1.03.  ``sigma`` defaults to the (res-bound) lower bound of
    Re s_* at x = x_{N-}; the paper used 0.599 + 0.1 log N-.

    The coefficients depend on N through the truncation n/d <= N.
    ``truncation="worst"`` takes, for each n, the maximum of the summand over
    every truncation that occurs for some N in [N-, N+], which makes F a bound
    for all of them.  "N_plus" and "N_minus" use a single truncation and are
    provided only to compare with printed values.  "none" drops the condition
    n/d <= N, as the paper's printed definition of beta_n (line 1654) does; the
    identity E sum_{n<=N} b_n n^{-s} = sum_{n<=DN} beta_n n^{-s} it is used for
    needs the condition, so "none" is a reading of the text, not a bound.
    """
    if truncation not in ("worst", "N_plus", "N_minus", "none"):
        raise ValueError("truncation must be 'worst', 'N_plus', 'N_minus' or 'none'")
    t0 = time.perf_counter()
    with workprec(prec):
        t, y = to_arb(t), to_arb(y)
        D = 1
        for q in primes:
            D *= q
        lam = mollifier_coefficients(primes, t)
        if c_gamma is None:
            c_gamma = (_c("0.02") * y).exp() * (1 - t / (16 * arb(N_minus) ** 2)) ** (-y / 2)
        if sigma is None:
            xN = x_of_N(N_minus, t)
            lX4 = (xN / (4 * arb.pi())).log()
            sigma = (1 + y) / 2 + (t / 4) * lX4 - (t / (2 * xN * xN)) * _pos(
                1 - 3 * y + 8 * y * (1 - y) / (xN * xN)
            )
        a_scale = c_gamma * (-y * arb(N_minus).log()).exp()  # c_gamma N-^{-y}
        a1 = a_scale
        rho = (1 - a1) / (1 + a1)
        # b_m and m^y b_m for m <= N+.
        tq = t / 4
        bm = [arb(0)] * (N_plus + 1)
        ym = [arb(0)] * (N_plus + 1)
        for m in range(1, N_plus + 1):
            L = arb(m).log()
            bm[m] = (tq * L * L).exp()
            ym[m] = (tq * L * L + y * L).exp()
        divs_of = {r: [d for d in _divisors(D) if r % d == 0] for r in _divisors(D)}
        total = arb(0)
        n_max = D * N_plus
        for n in range(2, n_max + 1):
            g = math.gcd(n, D)
            ds = divs_of[g]
            # Truncations that occur for N in [N-, N+]: d is present iff n/d <= N.
            if truncation == "worst":
                cuts = {N_minus}
                for d in ds:
                    m = n // d
                    if N_minus < m <= N_plus:
                        cuts.add(m)
            elif truncation == "N_plus":
                cuts = {N_plus}
            elif truncation == "N_minus":
                cuts = {N_minus}
            else:
                cuts = {n}  # every d | (n, D): no truncation
            best = arb(0)
            for Ncut in cuts:
                bet = arb(0)
                alp = arb(0)
                any_term = False
                for d in ds:
                    m = n // d
                    if m <= Ncut:
                        if m <= N_plus:
                            bmm, ymm = bm[m], ym[m]
                        else:
                            Lm = arb(m).log()
                            bmm = (tq * Lm * Lm).exp()
                            ymm = (tq * Lm * Lm + y * Lm).exp()
                        bet += lam[d] * bmm
                        alp += lam[d] * ymm
                        any_term = True
                if any_term:
                    an = a_scale * alp
                    val = _max_upper(abs(bet - an), rho * abs(bet + an))
                    best = _max_upper(best, val)
            if best != 0:
                total += best * (-sigma * arb(n).log()).exp()
            if progress and n % 1000000 == 0:  # pragma: no cover
                print(f"  F: n = {n} / {n_max}", flush=True)
        F = 1 - a1 - total
        return {
            "F": F, "a1": a1, "Y": total, "c_gamma": c_gamma, "sigma": sigma,
            "N_minus": N_minus, "N_plus": N_plus, "D": D, "terms": n_max - 1,
            "truncation": truncation, "seconds": time.perf_counter() - t0,
        }


# --------------------------------------------------------------------------- #
#  Derivative bounds of the Lemma at lines 1442-1453
# --------------------------------------------------------------------------- #

def derivative_bounds(
    x_lo: Any,
    x_hi: Any,
    y_grid: Sequence[Any],
    t: Any,
    N: int | None = None,
    prec: int | None = None,
    n_range: tuple[int, int] | None = None,
) -> dict[str, Any]:
    """Upper bounds for |df_t/dz| and |df_t/dt| on the rectangle [x_lo, x_hi] x [y_0, y_J].

    The Lemma bounds |df/dz| and |df/dt| pointwise by sums over n of terms in
    Re s_*, |gamma|, N^{|kappa|} and elementary functions of (x, y).  Here every
    ingredient is replaced by a majorant valid on the whole rectangle:
    Re s_* >= (1+y)/2 + tau_lo with tau_lo the lower end of (t/2) Re alpha(s_+)
    over the rectangle, |gamma| <= e^{0.02y} (x_lo/4pi)^{-y/2} (gamma-bound),
    |kappa| <= t y_J / (2(x_lo - 6)) (kappa-bound), and the x-dependent factors
    at their worst ends.  Every majorant term is then c_n exp(k_n y) with c_n >= 0
    independent of (x, y), so the majorant M(y) is convex in y and its supremum
    over [y_j, y_{j+1}] is max(M(y_j), M(y_{j+1})).  ``line_z[j]`` and
    ``line_t[j]`` are M(y_j), bounds on the whole segment y = y_j, x_lo <= x <= x_hi;
    ``strip_z[j]`` and ``strip_t[j]`` bound the strip [x_lo, x_hi] x [y_j, y_{j+1}].

    ``line_z_beta`` and ``line_z_gamma`` (and the ``_t`` pair) are the two parts
    of the Lemma's majorant, the first sum (b_n n^{-s_*}) and the second
    (gamma b_n n^{-s_**}); ``line_z`` is their sum.  Each part dominates, term by
    term, the exact |d/dz| of the corresponding summand, which is what the tests
    compare it with.  ``n_range = (n_lo, n_hi)`` restricts every sum to
    n_lo <= n <= n_hi; it exists so that a test can see each weight in a window
    of n where it is nearly sharp, and the barrier never passes it.
    """
    with workprec(prec):
        x_lo, x_hi, t = to_arb(x_lo), to_arb(x_hi), to_arb(t)
        ys = [to_arb(v) for v in y_grid]
        J = len(ys)
        if N is None:
            N = N_of(x_lo, t)
            if N_of(x_hi, t) != N:
                raise ValueError("N jumps inside [x_lo, x_hi]; f_t is not holomorphic there")
        n_lo, n_hi = (1, N) if n_range is None else (int(n_range[0]), int(n_range[1]))
        if not (1 <= n_lo <= n_hi <= N):
            raise ValueError("n_range must satisfy 1 <= n_lo <= n_hi <= N")
        pi = arb.pi()
        xs = _hull(x_lo, x_hi)
        yb = _hull(ys[0], ys[-1])
        tau = (t / 2) * alpha(acb(1 + yb, -xs) / 2).real
        tau_lo = tau.lower()
        lX4lo = (x_lo / (4 * pi)).log()
        lX4hi = (x_hi / (4 * pi)).log()
        Nk = ((t * ys[-1] / (2 * (x_lo - 6))) * arb(N).log()).exp()
        Cmax = (abs(acb(1 + ys[-1], x_hi)) / (4 * pi)).log() + pi + 3 / x_lo
        c1 = t / (4 * (x_lo - 6))
        cz_g = Cmax * (arb(1) / 2 + c1)
        ct_g = (pi / 2 + 8 / (x_lo - 6)) * (lX4hi + 8 / (x_lo - 6)) / 4
        # gamma-part exponent slope in y: 0.02 - (1/2) log(x_lo/4pi) + (1/2) L
        g0 = _c("0.02") - lX4lo / 2
        line_zb = [arb(0)] * J   # first-sum part of the |df/dz| majorant
        line_zg = [arb(0)] * J   # second-sum part
        line_tb = [arb(0)] * J
        line_tg = [arb(0)] * J
        plain_b = [arb(0)] * J   # majorant of sum b_n n^{-Re s_*}, for e_A + e_B
        plain_g = [arb(0)] * J   # majorant of |gamma| N^|kappa| sum n^y b_n n^{-Re s_*}
        tq = t / 4
        half = arb(1) / 2
        for n in range(n_lo, n_hi + 1):
            L = arb(n).log()
            base = (tq * L * L - (half + tau_lo) * L).exp()  # b_n n^{-1/2 - tau_lo}
            lx = (x_hi / (4 * pi * n)).log()
            wz_b = L / 2 + c1 * L
            wt_b = L * lx / 4 + pi * L / 8 + 2 * L / (x_lo - 6)
            wz_g = c1 * L + cz_g
            wt_g = wt_b + ct_g
            slope_g = g0 + L / 2
            for j, yv in enumerate(ys):
                pb = base * (-(yv / 2) * L).exp()        # beta-part: n^{-(1+y)/2 - tau_lo} b_n
                pg = Nk * base * (yv * slope_g).exp()    # gamma-part majorant
                line_zb[j] += pb * wz_b
                line_zg[j] += pg * wz_g
                line_tb[j] += pb * wt_b
                line_tg[j] += pg * wt_g
                plain_b[j] += pb
                plain_g[j] += pg
        line_z = [line_zb[j] + line_zg[j] for j in range(J)]
        line_t = [line_tb[j] + line_tg[j] for j in range(J)]
        strip_z = [_max_upper(line_z[j], line_z[j + 1]) for j in range(J - 1)]
        strip_t = [_max_upper(line_t[j], line_t[j + 1]) for j in range(J - 1)]
        return {
            "N": N, "n_range": (n_lo, n_hi), "tau_lo": tau_lo, "line_z": line_z, "line_t": line_t,
            "line_z_beta": line_zb, "line_z_gamma": line_zg, "line_t_beta": line_tb, "line_t_gamma": line_tg,
            "strip_z": strip_z, "strip_t": strip_t, "plain_b": plain_b, "plain_g": plain_g,
            "y_grid": ys,
        }


def _eC0_upper_on_box(x_lo: arb, x_hi: arb, y_lo: arb, y_hi: arb, t: arb, nx: int, ny: int) -> arb:
    """An exact point >= e_{C,0}(x + iy) for every x in [x_lo, x_hi], y in [y_lo, y_hi].

    e_{C,0} is the exact (ec-def) of ``_eC_pair``, evaluated on each of nx x ny
    sub-boxes with x and y as balls; the maximum of the upper ends bounds the
    supremum.  Subdividing only controls the overestimate from the dependency
    of |M_0(iT')| and |M_t(s_+)| on the same x (each varies like e^{-pi x/8});
    soundness does not depend on nx, ny.
    """
    best: arb | None = None
    for i in range(nx):
        xa = x_lo + (x_hi - x_lo) * i / nx
        xb = x_lo + (x_hi - x_lo) * (i + 1) / nx
        xs = _hull(xa, xb)
        for j in range(ny):
            ya = y_lo + (y_hi - y_lo) * j / ny
            yb = y_lo + (y_hi - y_lo) * (j + 1) / ny
            _, eC0 = _eC_pair(xs, _hull(ya, yb), t)
            if not eC0.is_finite():
                raise ArithmeticError("e_{C,0} enclosure is not finite on a sub-box")
            u = eC0.upper()
            if best is None or u > best:
                best = u
    assert best is not None
    return best


def _rectangle_error_bound(
    x_lo: arb, x_hi: arb, y_lo: arb, y_hi: arb, t: arb, N: int, db: dict[str, Any], nx: int = 64, ny: int = 16
) -> dict[str, arb]:
    """An upper bound for e_A + e_B + e_{C,0} on the whole rectangle.

    e_A + e_B: (eab-bound) of Theorem 1.3 with the n-dependence of the exponential
    factor bounded by its value at n = 1 (log^2(x/(4 pi n^2)) <= log^2(x/(4 pi)) for
    1 <= n <= N, line 1053), its x-dependence at x = x_lo (it decreases in x), and
    the sums by the derivative pass's majorants.
    e_{C,0}: the exact (ec-def), bounded over the rectangle by ``_eC0_upper_on_box``.
    An earlier version used Proposition 6.6(vi) here, which is false just above
    jumps x_N with small N (see ``theorem_bounds``).
    """
    pi = arb.pi()
    lX4 = (x_lo / (4 * pi)).log()
    d1 = (((t * t / 16) * lX4 * lX4 + _c("0.626")) / (x_lo - _c("6.66"))).expm1()
    # plain_b, plain_g are convex in y (sums of c_n e^{k_n y}): sup at an end.
    sb = _max_upper(db["plain_b"][0], db["plain_b"][-1])
    sg = _max_upper(db["plain_g"][0], db["plain_g"][-1])
    eAB = d1 * (sb + sg)
    eC0 = _eC0_upper_on_box(x_lo, x_hi, y_lo, y_hi, t, nx, ny)
    return {"eAB": eAB.upper(), "eC0": eC0, "E": (eAB + eC0).upper()}


# --------------------------------------------------------------------------- #
#  Taylor multi-evaluation (Section 7), at one fixed time t
# --------------------------------------------------------------------------- #

def _taylor_tail_bound(A: arb, rho: arb, K: int, fact_K: arb) -> arb:
    """A sum_{k>=K} rho^k/k! <= A rho^K / (K! (1 - rho/(K+1))), for 0 <= rho < K + 1.

    The k-th term is (rho^K/K!) rho^{k-K} K!/k! <= (rho^K/K!) (rho/(K+1))^{k-K}:
    a geometric majorant.  It bounds the omitted part of
    sum_n c_n exp(-delta ell_n) = sum_k (-delta)^k sum_n c_n ell_n^k/k! truncated at
    K terms, with A = sum_n |c_n| and rho = |delta| max|ell_n|.
    """
    if not (rho < K + 1):
        raise ValueError("rho must be below K + 1 for the geometric tail bound")
    return A * _pow_ui_upper(rho, K) / (fact_K * (1 - rho / (K + 1)))


@dataclass
class _Block:
    n_lo: int
    n_hi: int  # exclusive
    Lc: arb
    ell_max: arb
    polyB: acb_poly
    polyA: acb_poly
    absB: arb
    absA: arb


class FixedTimeMultiEval:
    """f_t(z) at many z near a centre z_c, at one time t, with explicit tails.

    Write s_*(z) = s_*(z_c) + delta.  For n in a block with centre log L_c and
    ell_n = log n - L_c,

        sum_n b_n n^{-s_*(z)} = exp(-delta L_c) sum_k m_k (-delta)^k,
        m_k = sum_n b_n n^{-s_*(z_c)} ell_n^k / k!,

    and the omitted tail k >= K is at most
    A sum_{k>=K} rho^k/k! <= A rho^K / (K! (1 - rho/(K+1))), with A = sum_n |b_n n^{-s_*(z_c)}|
    and rho = |delta| max|ell_n|.  The same for the second sum with s_**(z)
    = s_-(z) + (t/2) alpha(s_-(z)).  Terms n < n_head are summed directly.
    This is the single-time form of the paper's Section 7 expansion, with the
    sum split into blocks of log-width ``log_width`` (the footnote at line 1128)
    so that a small K suffices.
    """

    def __init__(
        self,
        x_c: Any,
        y_c: Any,
        t: Any,
        N: int,
        n_head: int = 32,
        log_width: float = 0.5,
        K: int = 16,
        prec: int | None = None,
        progress: bool = False,
    ) -> None:
        t0 = time.perf_counter()
        self.prec = PREC if prec is None else int(prec)
        self.K = K
        self.N = N
        self.n_head = min(n_head, N + 1)
        with workprec(self.prec):
            self.x_c, self.y_c, self.t = to_arb(x_c), to_arb(y_c), to_arb(t)
            t_ = self.t
            sp = acb(1 + self.y_c, -self.x_c) / 2
            sm = acb(1 - self.y_c, self.x_c) / 2
            self.sB0 = sp + (t_ / 2) * alpha(sp)
            self.sA0 = sm + (t_ / 2) * alpha(sm)
            tq = t_ / 4
            fact = [arb(1)]
            for k in range(1, K + 1):
                fact.append(fact[-1] * k)
            self._fact_K = fact[K]
            self.blocks: list[_Block] = []
            n = self.n_head
            ratio = math.exp(log_width)
            while n <= N:
                n_hi = min(N + 1, max(n + 1, int(math.floor(n * ratio))))
                Llo = arb(n).log()
                Lhi = arb(n_hi - 1).log()
                Lc = (Llo + Lhi) / 2
                ell_max = ((Lhi - Llo) / 2).upper()
                mB = acb_poly([0] * K)
                mA = acb_poly([0] * K)
                aB = arb(0)
                aA = arb(0)
                for m in range(n, n_hi):
                    L = arb(m).log()
                    ell = L - Lc
                    qL = tq * L * L
                    eB = qL - self.sB0 * L
                    eA = qL - self.sA0 * L
                    cB = eB.exp()
                    cA = eA.exp()
                    aB += eB.real.exp()
                    aA += eA.real.exp()
                    # coefficients (-ell)^k / k!, k = 0..K-1, built explicitly.  An
                    # earlier version used arb_series(...).exp(), which python-flint
                    # silently truncates at ctx.cap (10) terms; with K = 16 the
                    # tail bound below then under-counted, and the off-centre
                    # overlap test caught it (|diff| ~ 1e-20 against radii ~ 1e-28).
                    coef = [arb(1)]
                    for k in range(1, K):
                        coef.append(coef[-1] * (-ell) / k)
                    ser = acb_poly(coef)
                    mB += cB * ser
                    mA += cA * ser
                if mB.degree() != K - 1 or mA.degree() != K - 1:
                    raise AssertionError("moment polynomial has the wrong length")
                self.blocks.append(_Block(n, n_hi, Lc, ell_max, mB, mA, aB, aA))
                if progress:  # pragma: no cover
                    print(f"  block [{n}, {n_hi}) done", flush=True)
                n = n_hi
            self._head = []
            for m in range(1, self.n_head):
                L = arb(m).log()
                self._head.append((L, tq * L * L))
        self.setup_seconds = time.perf_counter() - t0

    def evaluate_parts(self, x: Any, y: Any) -> tuple[acb, acb, acb]:
        """Enclosures of (sum_n b_n n^{-s_*}, sum_n b_n n^{-s_**}, gamma) at x + iy.

        f_t = first + gamma * second.  Returned separately so that a test can hold
        each sum against direct summation; ``evaluate`` combines them.
        """
        with workprec(self.prec):
            x, y = to_arb(x), to_arb(y)
            t_ = self.t
            sp = acb(1 + y, -x) / 2
            sm = acb(1 - y, x) / 2
            s_star = sp + (t_ / 2) * alpha(sp)
            s_2star = sm + (t_ / 2) * alpha(sm)
            gamma = (log_Mt(sm, t_) - log_Mt(sp, t_)).exp()
            sumB = acb(0)
            sumA = acb(0)
            for L, qL in self._head:
                sumB += (qL - s_star * L).exp()
                sumA += (qL - s_2star * L).exp()
            dB = s_star - self.sB0
            dA = s_2star - self.sA0
            aB_abs = abs(dB)
            aA_abs = abs(dA)
            K = self.K
            for b in self.blocks:
                rhoB = (aB_abs * b.ell_max).upper()
                rhoA = (aA_abs * b.ell_max).upper()
                if not (rhoB < K + 1 and rhoA < K + 1):
                    raise ValueError("evaluation point too far from the expansion centre")
                tailB = _taylor_tail_bound(b.absB, rhoB, K, self._fact_K)
                tailA = _taylor_tail_bound(b.absA, rhoA, K, self._fact_K)
                prefB = (-dB * b.Lc).exp()
                prefA = (-dA * b.Lc).exp()
                vB = b.polyB(dB) + _disk(tailB)
                vA = b.polyA(dA) + _disk(tailA)
                sumB += prefB * vB
                sumA += prefA * vA
            return sumB, sumA, gamma

    def evaluate(self, x: Any, y: Any) -> acb:
        """An enclosure of f_t(x + iy), N fixed at ``self.N``."""
        sumB, sumA, gamma = self.evaluate_parts(x, y)
        with workprec(self.prec):
            return sumB + gamma * sumA


# --------------------------------------------------------------------------- #
#  One barrier rectangle at one time: Rouche plus a winding count
# --------------------------------------------------------------------------- #

def barrier_rectangle(
    x_lo: Any,
    x_hi: Any,
    y_lo: Any,
    y_hi: Any,
    t: Any,
    n_strips: int = 8,
    initial_per_edge: int = 64,
    max_depth: int = 30,
    K: int = 16,
    prec: int | None = None,
    margin_target: float | None = None,
    progress: bool = False,
    eC0_subdivisions: tuple[int, int] = (64, 16),
) -> dict[str, Any]:
    """Section 8.4 on one rectangle R = [x_lo, x_hi] x [y_lo, y_hi] at time t.

    Mesh the boundary with dyadic points.  A segment of length h with derivative
    bound D (``derivative_bounds``) is accepted when both endpoint values satisfy
    |f(z_j)| > E + D h / 2, where E bounds e_A + e_B + e_{C,0} on R; otherwise it
    is bisected.  When every segment is accepted, H_t/B_t has no zero on dR and its
    winding number around 0 equals that of the polygon through the f(z_j), which is
    computed as a ball (1/2pi) sum Arg(f_{j+1}/f_j).  ``winding`` is the integer
    that ball contains, or None.  The result is a statement about this one
    rectangle at this one time; the t-direction is not covered.

    ``segments`` lists every accepted segment in boundary order with the data its
    acceptance used (edge, dyadic endpoints num0/den and num1/den of the edge
    parameter, the derivative bound D, and the two endpoint balls), so that the
    whole decision can be re-derived independently; the tests do exactly that.
    """
    timings: dict[str, float] = {}
    t_all = time.perf_counter()
    with workprec(prec):
        x_lo, x_hi, y_lo, y_hi, t = (to_arb(v) for v in (x_lo, x_hi, y_lo, y_hi, t))
        cur_prec = ctx.prec
        if not (x_lo < x_hi and y_lo < y_hi):
            raise ValueError("the rectangle needs x_lo < x_hi and y_lo < y_hi")
        _check_region(x_lo, y_lo, t)
        _check_region(x_hi, y_hi, t)
        N = N_of(x_lo, t)
        if N_of(x_hi, t) != N:
            raise ValueError("N jumps inside the rectangle")
        ys = [y_lo + (y_hi - y_lo) * j / n_strips for j in range(n_strips + 1)]
        t1 = time.perf_counter()
        db = derivative_bounds(x_lo, x_hi, ys, t, N=N)
        timings["derivative_bounds"] = time.perf_counter() - t1
        t1 = time.perf_counter()
        eb = _rectangle_error_bound(x_lo, x_hi, y_lo, y_hi, t, N, db, *eC0_subdivisions)
        timings["error_bound"] = time.perf_counter() - t1
        E = eb["E"]
        xc = (x_lo + x_hi) / 2
        yc = (y_lo + y_hi) / 2
        t1 = time.perf_counter()
        ev = FixedTimeMultiEval(xc, yc, t, N, K=K)
        timings["multieval_setup"] = time.perf_counter() - t1
        # Boundary parametrised counterclockwise by u in [0, 4): bottom, right, top, left.
        W = x_hi - x_lo
        H = y_hi - y_lo

        def z_of(edge: int, num: int, den: int) -> tuple[arb, arb]:
            fr = arb(num) / den
            if edge == 0:
                return x_lo + W * fr, y_lo
            if edge == 1:
                return x_hi, y_lo + H * fr
            if edge == 2:
                return x_hi - W * fr, y_hi
            return x_lo, y_hi - H * fr

        def D_of(edge: int, num0: int, num1: int, den: int) -> arb:
            if edge == 0:
                return db["line_z"][0]
            if edge == 2:
                return db["line_z"][-1]
            # vertical: y fractions [num0/den, num1/den] (edge 1 upward, edge 3 downward)
            f0, f1 = (num0 / den, num1 / den) if edge == 1 else (1 - num1 / den, 1 - num0 / den)
            j0 = max(0, min(n_strips - 1, int(math.floor(f0 * n_strips))))
            j1 = max(0, min(n_strips - 1, int(math.ceil(f1 * n_strips)) - 1))
            Dm = arb(0)
            for j in range(j0, j1 + 1):
                Dm = _hull(arb(0), Dm.upper().union(db["strip_z"][j].upper()).upper())
            return Dm

        n_evals = 0
        cache: dict[tuple[int, int, int], acb] = {}

        def fval(edge: int, num: int, den: int) -> acb:
            nonlocal n_evals
            g = math.gcd(num, den)
            key = (edge, num // g, den // g)
            if key not in cache:
                xx, yy = z_of(edge, num, den)
                cache[key] = ev.evaluate(xx, yy)
                n_evals += 1
            return cache[key]

        accepted: list[tuple[int, int, int, int]] = []  # (edge, num0, num1, den)
        seg_D: dict[tuple[int, int, int, int], arb] = {}
        failed: list[tuple[int, int, int, int]] = []
        min_abs = None
        min_margin = None
        t1 = time.perf_counter()
        for edge in range(4):
            length = W if edge in (0, 2) else H
            stack = [(edge, k, k + 1, initial_per_edge, 0) for k in range(initial_per_edge - 1, -1, -1)]
            while stack:
                e_, a, b, den, depth = stack.pop()
                fa = fval(e_, a, den)
                fb = fval(e_, b, den)
                h = length * (b - a) / den
                D = D_of(e_, a, b, den)
                need = E + D * h / 2
                la = fa.abs_lower()
                lb = fb.abs_lower()
                if la > need and lb > need:
                    accepted.append((e_, a, b, den))
                    seg_D[(e_, a, b, den)] = D
                    lo_ab = la if la < lb else lb          # exact points
                    m = (lo_ab - need).lower()
                    if min_margin is None or m < min_margin:
                        min_margin = m
                    if min_abs is None or lo_ab < min_abs:
                        min_abs = lo_ab
                elif depth < max_depth:
                    stack.append((e_, 2 * a + 1, 2 * b, 2 * den, depth + 1))
                    stack.append((e_, 2 * a, 2 * a + 1, 2 * den, depth + 1))
                else:
                    failed.append((e_, a, b, den))
            if progress:  # pragma: no cover
                print(f"  edge {edge}: evals so far {n_evals}", flush=True)
        timings["mesh"] = time.perf_counter() - t1
        winding = None
        wind_ball = None
        accepted.sort(key=lambda s: (s[0], s[1] / s[3]))
        if not failed:
            tot = arb(0)
            for (e_, a, b, den) in accepted:
                fa = fval(e_, a, den)
                fb = fval(e_, b, den)
                tot += (fb / fa).arg()
            wind_ball = tot / (2 * arb.pi())
            lo = math.ceil(_lower_float(wind_ball))
            hi = math.floor(_upper_float(wind_ball))
            if lo == hi:
                winding = int(lo)
        segments = [
            {"edge": e_, "num0": a, "num1": b, "den": den, "D": seg_D[(e_, a, b, den)],
             "f0": fval(e_, a, den), "f1": fval(e_, b, den)}
            for (e_, a, b, den) in accepted
        ]
        timings["total"] = time.perf_counter() - t_all
        return {
            "N": N,
            "prec": cur_prec,
            "K": K,
            "n_strips": n_strips,
            "E_upper": E,
            "eAB_upper": eb["eAB"],
            "eC0_upper": eb["eC0"],
            "segments": segments,
            "Dz_bottom": db["line_z"][0],
            "Dz_top": db["line_z"][-1],
            "Dz_strips": db["strip_z"],
            "Dt_bottom": db["line_t"][0],
            "Dt_strips": db["strip_t"],
            "n_evaluations": n_evals,
            "n_segments": len(accepted),
            "n_failed": len(failed),
            "min_abs_f_lower": min_abs,
            "min_margin": min_margin,
            "winding_ball": wind_ball,
            "winding": winding,
            "blocks": len(ev.blocks),
            "n_head": ev.n_head,
            "timings": timings,
        }
