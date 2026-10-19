"""Hunt #135, phase 2 (MISSION Q2): explicit constants for both wedges.

Run from the repository root:

    .venv/bin/python hunts/jensen_wedge/effective.py --time-unit   # one subinterval of each chain
    .venv/bin/python hunts/jensen_wedge/effective.py               # writes results_effective.json

`EFFECTIVE.md` is the derivation; this module evaluates every numeric step of it
in Arb ball arithmetic. Arb is reached through python-flint, and the module
refuses to run unless `zeta.rigor.BACKEND` is "python-flint": mpmath's interval
fallback has no complex balls, and a silent fallback is exactly what the
repository's rules forbid. Nothing here is graded above "derivation,
self-reviewed"; the ball arithmetic makes each numeric step an enclosure, it
does not review the derivation.

Layout (section letters match EFFECTIVE.md):

A. ball helpers;
B. the main term G(s) of log I(s) and its exact derivative ratios F_k(e, m);
C. Lemma V (the complex saddle) and Lemma L (the Laplace remainder on a contour
   through it), giving |log I(s) - G(s)| <= lambda on a sector-shaped disk;
D. derivative enclosures for h = log M_z (Lemma D) and the targets tau_j;
E. the five-coefficient model with D = n/2 (Lemma M5), its root localisation
   (Lemma G), Holland's Lemma 9.1 with explicit constants, Lemma 8.1 with
   explicit constants, and the constant K of n^3 log^2(n+2) >= K d^5;
F. the six-coefficient Pade model (Lemma M6, H1 made explicit), Lemmas A to C
   with the review's R2 hypotheses, the sixth-order residual, and K';
G. the effectivity check: claimed constants against their recomputation, and
   the planted weakenings that must turn it red.

The parameter of every uniform statement is e = 1/v_1, with v_1 the real saddle
of I at s = 2n: v_1 (pi e^{v_1} - 9/4) = 2n. A statement "for all n >= n_0" is
checked by covering [0, 1/v_1(2 n_0)] with closed subintervals of e and
evaluating every quantity over each subinterval as a ball. The last
subinterval contains e = 0, that is n = infinity.
"""

from __future__ import annotations

import argparse
import functools
import json
import math
import subprocess
import sys
import time
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from zeta import rigor  # noqa: E402

if rigor.BACKEND != "python-flint":  # pragma: no cover - depends on the machine
    raise RuntimeError(
        f"effective.py needs Arb (python-flint); zeta.rigor.BACKEND is {rigor.BACKEND!r}: "
        f"{rigor.BACKEND_REASON}"
    )

from flint import acb, arb  # noqa: E402

PREC = 256  # bits; every entry point runs under rigor._flint_prec(PREC)

#: the exponent of the leading Mellin term: Phi_T(v/4) = 2 pi^2 e^{9v/4 - pi e^v} alpha(v)
A_PHASE = Fraction(9, 4)

#: Laplace region: |z - x| <= RHO x for real x >= x_0, contour step T on each side of the saddle
RHO = Fraction(1, 4)
T_STEP = Fraction(1, 2)
#: derivatives are used on |z - x| <= RHO_D x; Cauchy's inequality spends RHO - RHO_D
RHO_D = Fraction(1, 8)

#: Proposition 2.2 (Holland) needs sup |c - 1| < 16, Proposition 2.2_6 needs < 32
PROP22_EPS = 16
PROP22_6_EPS = 32

#: GORTTW Corollary 1.3: J^{d,n} is hyperbolic for every n >= 0 when d <= 9.36e20
D_GORTTW = Fraction(936, 1) * 10**18


# ---------------------------------------------------------------------------
# A. ball helpers
# ---------------------------------------------------------------------------


def ab(q) -> arb:
    """Exact ball for an int, a Fraction or a decimal string."""
    if isinstance(q, arb):
        return q
    if isinstance(q, str):
        q = Fraction(q)
    if isinstance(q, int):
        return arb(q)
    q = Fraction(q)
    return arb(q.numerator) / arb(q.denominator)


def hull(lo, hi) -> arb:
    return ab(lo).union(ab(hi))


def nonneg(x: arb) -> arb:
    """[0, upper(x)]: the ball for a quantity known to lie between 0 and x."""
    return hull(0, x.upper())


def up(x) -> float:
    """A float at or above the ball (for reporting; checks compare balls)."""
    if isinstance(x, acb):
        x = x.abs_upper()
    u = x.upper()
    f = float(u.mid())
    return f + abs(f) * 2.0**-50 + 1e-300


def lo(x: arb) -> float:
    l = x.lower()
    f = float(l.mid())
    return f - abs(f) * 2.0**-50 - 1e-300


def sqrt_nn(x) -> arb:
    """sqrt of a ball known to be >= 0 (Arb returns nan when a ball touches 0)."""
    x = ab(x)
    lo_ = x.lower()
    lo_ = arb(0) if not (lo_ > 0) else lo_.sqrt().lower()
    return hull(lo_, x.upper().sqrt().upper())


def cpow(z, k):
    """z^k for a ball z in the right half-plane. For complex boxes, repeated
    multiplication wraps (a box to the 5th power can come to contain 0); the
    principal branch exp(k log z) stays tight. Real balls use ordinary powers."""
    if isinstance(z, acb):
        return (k * z.log()).exp()
    return z**k


def disk(r) -> acb:
    """A complex ball containing the closed disk |w| <= r."""
    r = ab(r).upper()
    return acb(arb(0, r), arb(0, r))


def cabs_up(z) -> arb:
    """An arb upper bound for |z| (works for arb and acb)."""
    if isinstance(z, acb):
        return z.abs_upper()
    return abs(z).upper() if not z.is_zero() else arb(0)


def pos(x: arb) -> bool:
    """True when the ball is certainly positive."""
    return bool(x > 0)


def fraction_up(x: arb, digits: int = 4) -> Fraction:
    """A decimal Fraction with `digits` significant digits, at or above x."""
    u = up(x)
    if u <= 0:
        return Fraction(0)
    e = math.floor(math.log10(u)) - digits + 1
    m = math.ceil(u / 10.0**e * (1 + 1e-12))
    return Fraction(m) * Fraction(10) ** e


# ---------------------------------------------------------------------------
# B. the main term and its derivative ratios
# ---------------------------------------------------------------------------
#
# I(s) = int_0^inf v^s e^{a v - pi e^v} alpha(v) dv, a = 9/4, with the complex
# saddle v_0(s): s/v_0 + a = pi e^{v_0}. Put e := 1/v_0 and m := 1/(pi e^{v_0}).
# The main term G(s) = s log v_0 + a v_0 - pi e^{v_0} + log(2 pi/Psi)/2, with
# Psi = s/v_0^2 + s/v_0 + a, has derivatives
#
#     G^(k)(s) = (-1)^k (k-2)! e s^{-(k-1)} F_k(e, m),          k >= 2,
#
# where F_k is an explicit rational function with F_k(0, 0) = 1. The derivation
# uses only d/ds = (e m/Q) (-e^2 d/de - m d/dm), Q = 1 + e - a e m, and
# s = (1 - a m)/(e m), all exact consequences of the saddle equation.


@functools.lru_cache(maxsize=None)
def derive_F(kmax: int = 7) -> dict:
    """{k: (numerator {(i, j): Fraction}, constant c_k, power p_k)} with
    F_k(e, m) = N_k(e, m) / (c_k (4 + 4e - 9em)^{p_k}), exact."""
    import sympy as sp

    e, m = sp.symbols("e m")
    a = sp.Rational(A_PHASE.numerator, A_PHASE.denominator)
    Q = 1 + e - a * e * m
    dvds = e * m / Q

    def Ds(f):
        return sp.cancel(dvds * (-(e**2) * sp.diff(f, e) - m * sp.diff(f, m)))

    # G'(s) = log v_0 - Psi'/(2 Psi); Psi = (1 + e - a e m)/m = Q/m, and
    # d/ds log Psi = dvds * (1 + (a e m - e^2 (1 - a m))/Q), d/ds(-log e) = dvds * e.
    G1_rest = -sp.Rational(1, 2) * dvds * (1 + (a * e * m - e**2 * (1 - a * m)) / Q)
    G = {2: sp.cancel(dvds * e + Ds(G1_rest))}
    for k in range(3, kmax + 1):
        G[k] = Ds(G[k - 1])
    inv_s = e * m / (1 - a * m)
    Q4 = 4 + 4 * e - 9 * e * m
    out = {}
    for k in range(2, kmax + 1):
        Fk = sp.cancel(G[k] / ((-1) ** k * sp.factorial(k - 2) * e * inv_s ** (k - 1)))
        num, den = sp.fraction(Fk)
        # den = c (9em - 4e - 4)^{p}; recover c and p exactly
        p = sp.Poly(den, e, m).total_degree() // 2 * 1  # degree of den in (e, m) is 2p
        pden = sp.Poly(den, e, m)
        p = pden.degree(e)
        c = sp.cancel(den / Q4**p)
        assert c.is_number, (k, den)
        poly = sp.Poly(sp.expand(num), e, m)
        coeffs = {mon: Fraction(int(sp.fraction(cf)[0]), int(sp.fraction(cf)[1]))
                  for mon, cf in poly.terms()}
        cq = sp.Rational(c)
        out[k] = (coeffs, Fraction(int(cq.p), int(cq.q)), int(p))
    return out


def _horner2(rows_by_i: list, e, m):
    """sum_i e^i P_i(m) with P_i given as [(j, coeff)] sorted by j descending."""
    rows = []
    for row in rows_by_i:
        if not row:
            rows.append(arb(0))
            continue
        acc = ab(row[0][1])
        last = row[0][0]
        for j, cf in row[1:]:
            acc = acc * m ** (last - j) + ab(cf)
            last = j
        rows.append(acc * m**last)
    out = rows[-1]
    for i in range(len(rows) - 2, -1, -1):
        out = out * e + rows[i]
    return out


@functools.lru_cache(maxsize=None)
def _F_rows(k: int):
    coeffs, c, p = derive_F()[k]
    deg_e = max(i for i, _ in coeffs)
    N = [sorted(((j, cf) for (ii, j), cf in coeffs.items() if ii == i), reverse=True)
         for i in range(deg_e + 1)]
    Ne = [sorted(((j, (i + 1) * cf) for (ii, j), cf in coeffs.items() if ii == i + 1), reverse=True)
          for i in range(deg_e)]
    return N, Ne, c, p


def F_plain(k: int, e, m):
    """F_k(e, m) by plain ball arithmetic."""
    N, _, c, p = _F_rows(k)
    return _horner2(N, e, m) / (ab(c) * cpow(4 + 4 * e - 9 * e * m, p))


def dFde_plain(k: int, e, m):
    """dF_k/de by plain ball arithmetic: N_e/(c Q^p) - p N (4 - 9m)/(c Q^{p+1}), Q = 4 + 4e - 9em."""
    N, Ne, c, p = _F_rows(k)
    Q = 4 + 4 * e - 9 * e * m
    return (_horner2(Ne, e, m) / cpow(Q, p)
            - p * _horner2(N, e, m) * (4 - 9 * m) / cpow(Q, p + 1)) / ab(c)


def F_ball(k: int, e, m):
    """F_k(e, m) over balls e (arb or acb) and m, in mean-value form around the
    midpoint of e: F(e) in F(c) + F'(hull) (e - c). For complex e the segment
    integral of F' lies in the convex ball F'(hull), so the form stays valid."""
    c = e.mid()
    return F_plain(k, c, m) + dFde_plain(k, e, m) * (e - c)


def first_order_coefficient(k: int) -> Fraction:
    """d F_k/de at (0, 0); EFFECTIVE.md Lemma D says it is H_{k-2} - 1."""
    coeffs, c, p = derive_F()[k]
    n0 = coeffs.get((0, 0), Fraction(0))
    n1 = coeffs.get((1, 0), Fraction(0))
    # F = N/(c 4^p (1 + e - 9em/4)^p): dF/de at 0 = (n1 - p n0)/(c 4^p)
    return (n1 - p * n0) / (c * 4**p)


# ---------------------------------------------------------------------------
# C. Lemma V (the complex saddle) and Lemma L (the Laplace remainder)
# ---------------------------------------------------------------------------


def s_of_v(v):
    """s(v) = v (pi e^v - a), the inverse of the saddle map, for a ball v."""
    return v * (arb.pi() * v.exp() - ab(A_PHASE))


def v_of_s_real(s: float) -> arb:
    """The real saddle v_1(s), s > 0, as a tight ball (bisection on the monotone s(v))."""
    s_b = ab(Fraction(s)) if not isinstance(s, arb) else s
    lo_v, hi_v = arb(1), arb(1)
    while not (s_of_v(hi_v) > s_b):
        hi_v = hi_v * 2
    for _ in range(PREC):
        mid = arb(((lo_v + hi_v) / 2).mid())
        if s_of_v(mid) > s_b:
            hi_v = mid
        elif s_of_v(mid) < s_b:
            lo_v = mid
        else:
            break
        if (hi_v - lo_v) < arb(2) ** (-PREC + 40):
            break
    if not (s_of_v(lo_v) < s_b and s_of_v(hi_v) > s_b):  # pragma: no cover
        raise RuntimeError("v_of_s_real lost its bracket")
    return hull(lo_v, hi_v)


def alpha_tail(X: arb, cos_b: arb) -> arb:
    """Upper bound for |alpha(v) - 1| when Re v >= X and |Im v| <= b, cos b >= cos_b:
    (3/(2 pi)) e^{-X} + sum_{n>=2} (n^4 + n^2) e^{-pi (n^2 - 1) e^X cos b}."""
    c = ab(3) / (2 * arb.pi())
    head = c * (-X).exp()
    tail = arb(0)
    q = arb.pi() * X.exp() * cos_b
    for n in range(2, 12):
        tail += (ab(n**4 + n**2)) * (-(ab(n * n - 1)) * q).exp()
    # n >= 12: each term below the n = 11 term times 2^{-(n-11)}
    tail += ab(11**4 + 11**2) * (-(ab(120)) * q).exp()
    return (head + tail).upper()


@dataclass
class LaplaceBound:
    """Constants of Lemmas V and L on the region |z - x| <= RHO x, x >= x0."""

    x0: Fraction
    V: arb  # half-strip Re v >= V, |Im v| <= 1 where |g'| <= q
    q: arb
    theta: arb  # |arg s| <= theta
    b: arb  # |Im v_0| <= b
    R_min: arb  # Re v_0 >= R_min
    p_min: arb  # pi e^{R_min}
    pieces: dict  # rho_i * sqrt(p) majorants
    C_rho: arb  # rho <= C_rho / sqrt(p_min)
    rho_bar: arb
    lam: arb  # |log(1 + rho)| <= lam
    conditions: dict


def laplace_bound(x0) -> LaplaceBound:
    """Lemma V and Lemma L, evaluated at the threshold x0 (see EFFECTIVE.md, C)."""
    with rigor._flint_prec(PREC):
        x0 = Fraction(x0)
        a = ab(A_PHASE)
        rho = ab(RHO)
        T = ab(T_STEP)
        theta = rho.asin()
        s_min = 2 * ab(x0) * (1 - rho)
        v1_min = v_of_s_real(s_min).lower()
        V = v1_min - 1
        delta_a = (a / arb.pi() * (-V).exp())
        q = (1 / V + delta_a / (1 - delta_a)).upper()
        b = (theta / (1 - q)).upper()
        R = (v1_min - b).lower()
        cos_b = b.cos().lower()
        p = (arb.pi() * R.exp()).lower()
        Rb = (R * (1 + b**2 / R**2).sqrt()).upper()
        conds = {
            "q < 1": pos(1 - q),
            "b <= 1 (disk inside the half-strip)": pos(1 - b),
            "R_min >= 10": pos(R - 10),
            # Lemma L (i): Re[s g] >= 0 on both tails
            "|arg s| + 2 atan(2b/R) <= pi/2": pos(arb.pi() / 2 - theta - 2 * (2 * b / R).atan()),
        }
        # Psi = P (1 + 1/v) - a/v:  Re Psi >= p cos b - a/R, |Psi| <= p (1 + 1/R) + a/R
        c_psi = (cos_b - a / (R * p)).lower()  # Re Psi / p >= c_psi
        c_abs = (1 + 1 / R + a / (R * p)).upper()  # |Psi| / p <= c_abs
        # M_3 / p <= 2 R_b (1 + a/p)/(R - T)^3 + e^T
        m3 = (2 * Rb * (1 + a / p) / (R - T) ** 3 + T.exp()).upper()
        conds["M_3 T/6 <= Re Psi/4"] = pos(c_psi / 4 - m3 * T / 6)
        a1 = alpha_tail(R - T, cos_b)
        a2 = alpha_tail(R / 2, cos_b)
        k_T = T.exp() - 1 - T  # k(T) = e^T - 1 - T
        k_mT = (-T).exp() - 1 + T  # k(-T)
        # rho_3 sqrt(p): cubic Taylor part plus the alpha - 1 part
        r3 = (1 + a1) * (ab(8) / 3) * m3 / c_psi**2 * (c_abs / (2 * arb.pi())).sqrt() \
            + a1 * p.sqrt() * (c_abs / c_psi).sqrt()
        # Gaussian tails beyond |t| = T
        rG = 2 * (-(c_psi * p * T**2 / 2)).exp() / (c_psi * T) * (c_abs / (2 * arb.pi())).sqrt()
        # right tail t >= T: Re Delta <= -Re P k(t), k convex
        r4 = (1 + a1) * (-(p * cos_b * k_T)).exp() / (cos_b * (T.exp() - 1)) \
            * (c_abs / (2 * arb.pi())).sqrt()
        # left tail t in [-R/2, -T]: length <= R/2, Re Delta <= -Re P k(-T)
        r2 = (1 + a2) * (R / 2) * (-(p * cos_b * k_mT)).exp() * p \
            * (c_abs / (2 * arb.pi())).sqrt()
        # segment [0, w_1], w_1 = R/2 + i Im v_0
        lw = (ab(2).log() - (1 + 4 * b**2 / R**2).log() / 2).lower()  # log(|v_0|/|w_1|) >= lw
        A1 = arb(0)
        for n in range(1, 12):
            A1 += (ab(n**4) + ab(3) / (2 * arb.pi()) * n * n) * (-(arb.pi() * n * n * cos_b)).exp()
        A1 += ab(11**4 + 11**2) * (-(arb.pi() * 121 * cos_b)).exp()  # n >= 12, geometric
        sin_t = theta.sin()
        bracket = -theta.cos() * lw * R * (1 - a / p) \
            + 3 * b * sin_t * (1 + b**2 / (2 * R**2)) * (1 + a / p) + 1
        conds["segment bracket negative"] = pos(-bracket)
        E1 = p * bracket - a * R / 2
        r1 = (Rb / 2 + b) * A1 * E1.exp() * (c_abs * p / (2 * arb.pi())).sqrt() * p.sqrt()
        pieces = {"rho_3": r3.upper(), "rho_G": rG.upper(), "rho_4": r4.upper(),
                  "rho_2": r2.upper(), "rho_1": r1.upper()}
        C_rho = sum(pieces.values(), arb(0)).upper()
        rho_bar = (C_rho / p.sqrt()).upper()
        conds["rho_bar <= 1/2"] = pos(ab(Fraction(1, 2)) - rho_bar)
        lam = (-(1 - rho_bar).log()).upper()
        return LaplaceBound(x0, V, q, theta, b, R, p, pieces, C_rho, rho_bar, lam, conds)


# ---------------------------------------------------------------------------
# D. derivative enclosures and the targets tau_j
# ---------------------------------------------------------------------------


@dataclass
class Sub:
    """A closed subinterval [e_lo, e_hi] of e = 1/v_1(2n) and what it implies for n."""

    e_lo: Fraction
    e_hi: Fraction
    e: arb = field(init=False)
    v_lo: arb = field(init=False)
    n_lo: arb = field(init=False)  # n >= n_lo
    eta: arb = field(init=False)  # 1/n in [0 or 1/n_hi, 1/n_lo]
    m_hi: arb = field(init=False)  # m = 1/(pi e^{v_1}) <= m_hi

    def __post_init__(self):
        self.e = hull(self.e_lo, self.e_hi)
        self.v_lo = (1 / ab(self.e_hi)).lower()
        self.n_lo = (s_of_v(self.v_lo) / 2).lower()
        if self.e_lo == 0:
            eta_lo = arb(0)
        else:
            eta_lo = (2 / s_of_v(1 / ab(self.e_lo))).lower()
        self.eta = hull(eta_lo, (1 / self.n_lo).upper())
        self.m_hi = (1 / (arb.pi() * self.v_lo.exp())).upper()


def deriv_ball(k: int, sub: Sub, lb: LaplaceBound, y, q_lip: arb):
    """The normalised derivative

        H_k(y) := (-1)^k h^(k)(n (1 + y)) n^{k-1} / (2 (k-2)! e_1),   e_1 = 1/v_1(2n),

    as a ball, for every n in `sub` and every y in the ball `y` (arb or acb, |y| small).
    Lemma D: H_k = (e/e_1) F_k(e, m) (1 + y)^{-(k-1)} + Cauchy part, where
    e = 1/v_0(2n(1+y)) and |v_0(2n(1+y)) - v_1(2n)| <= |log(1+y)|/(1 - q).
    """
    complex_y = isinstance(y, acb)
    ymax = cabs_up(y)
    Lg = (-(1 - ymax).log()).upper()  # |log(1 + y)| <= -log(1 - |y|)
    rv = (Lg / (1 - q_lip)).upper()
    e1 = sub.e
    if complex_y:
        # e/e_1 = 1/(1 + e_1 dv), |dv| <= rv
        dvb = disk(rv)
        ratio = 1 / (1 + e1 * dvb)
        e_ball = e1 * ratio
        m_ball = disk((sub.m_hi * rv.exp()).upper())
    else:
        # real y >= 0: v_0 in [v_1, v_1 + rv], so e/e_1 in [1/(1 + e_1 rv), 1]
        ratio = hull((1 / (1 + e1.upper() * rv)).lower(), 1)
        e_ball = e1 * ratio
        m_ball = hull(0, sub.m_hi)
    Fk = F_ball(k, e_ball, m_ball)
    main = ratio * Fk * cpow(1 + y, -(k - 1))
    # Cauchy: |R^(k)| <= k! lam/((RHO - RHO_D) n)^k; normalised by n^{k-1}/(2 (k-2)! e_1)
    # n e_1 = n/v_1(2n) increases with n, so it is smallest at n_lo, where e_1 = e_hi
    cau = (ab(k * (k - 1)) * lb.lam / (2 * ab(RHO - RHO_D) ** k * sub.n_lo * ab(sub.e_hi))).upper()
    if complex_y:
        return main + disk(cau)
    return main + arb(0, cau)


def targets(sub: Sub, lb: LaplaceBound, jmax: int) -> list:
    """[T_0, ..., T_jmax] with T_j := tau_j/(2 e_1) enclosed for every n in `sub`.

    tau_j = (-1)^j n^{j+1}/j! Delta^{j+2} h(n) is the average of
    (-1)^j n^{j+1}/j! h^{(j+2)}(n + sigma) over the cube, sigma in [0, j+2],
    which is 2 e_1 H_{j+2}(sigma/n)."""
    out = []
    for j in range(jmax + 1):
        y = hull(0, ((j + 2) * sub.eta).upper())
        out.append(deriv_ball(j + 2, sub, lb, y, lb.q))
    return out


# ---------------------------------------------------------------------------
# matching systems: shared pieces
# ---------------------------------------------------------------------------
#
# Both models are products of Jacobi factors; with w_P := n/P for every
# parameter P, w_b := n/b, b = n + 1/2, matching R_0..R_{m-1} is exactly
#
#     tau_j = int_G u_j'(t) dt,   u_j'(t) = (j+1) t^j prod_{i=1}^{j+1} (1 + i t/n)^{-1},
#
# over the signed gap set G of the model (H1_H3.md section 4.1, j = 0..m-3).


def pi_j(j: int, y):
    """prod_{i=1}^{j+1} (1 + i y)^{-1}."""
    out = arb(1)
    for i in range(1, j + 2):
        out = out / (1 + i * y)
    return out


def pi_range(j: int, ymax) -> arb:
    """The ball [pi_j(ymax), 1] containing pi_j(y) for every 0 <= y <= ymax."""
    return hull(pi_j(j, ab(ymax).upper()).lower(), 1)


def upj(j: int, t, eta):
    """u_j'(t) for balls t >= 0 and eta = 1/n."""
    return (j + 1) * t**j * pi_j(j, eta * t)


def P_poly(j: int, c, e):
    """((c)^{j+1} - (c - e)^{j+1})/e = int_0^1 (j+1)(c - e theta)^j d theta, exactly."""
    out = arb(0)
    for k in range(1, j + 2):
        out += math.comb(j + 1, k) * c ** (j + 1 - k) * (-1) ** (k + 1) * e ** (k - 1)
    return out


def mat_vec(M, x):
    return [sum((M[i][k] * x[k] for k in range(len(x))), arb(0)) for i in range(len(M))]


def mat_mul(M, N):
    n, p = len(M), len(N[0])
    return [[sum((M[i][k] * N[k][j] for k in range(len(N))), arb(0)) for j in range(p)]
            for i in range(n)]


def approx_inverse(M) -> list:
    """An exact-rational approximate inverse of the midpoint of M (any nonsingular Y
    serves in Krawczyk's operator)."""
    import mpmath as mpm

    with mpm.workdps(40):
        A = mpm.matrix([[mpm.mpf(x.mid().str(40, radius=False)) for x in row] for row in M])
        B = A**-1
        return [[ab(Fraction(mpm.nstr(B[i, j], 30))) for j in range(B.cols)]
                for i in range(B.rows)]


def krawczyk(Phi, DPhi, x0: list, rad0: list, max_iter: int = 40):
    """Interval Krawczyk test for Phi(X) = 0 near x0, with every parameter of Phi a ball.

    Returns (box, ok): if ok, every parameter value in the balls has exactly one zero
    of Phi in `box`, and box is K(box) for the last iterate."""
    n = len(x0)
    # a few Newton steps at the midpoint
    x = [arb(xi.mid()) for xi in x0]
    Y = approx_inverse(DPhi([xi for xi in x]))
    for _ in range(6):
        F = Phi(x)
        step = mat_vec(Y, [arb(f.mid()) for f in F])
        x = [arb((xi - si).mid()) for xi, si in zip(x, step)]
        Y = approx_inverse(DPhi(x))
    F = Phi(x)
    YF = mat_vec(Y, F)
    rad = [max(ab(r), (4 * cabs_up(v)).upper()) for r, v in zip(rad0, YF)]
    for _ in range(max_iter):
        box = [xi + arb(0, ri) for xi, ri in zip(x, rad)]
        DB = DPhi(box)
        YD = mat_mul(Y, DB)
        IM = [[(1 if i == j else 0) - YD[i][j] for j in range(n)] for i in range(n)]
        K = [x[i] - YF[i] + sum((IM[i][j] * arb(0, rad[j]) for j in range(n)), arb(0))
             for i in range(n)]
        inside = all(
            bool(K[i].lower() > box[i].lower()) and bool(K[i].upper() < box[i].upper())
            for i in range(n)
        )
        if inside:
            return K, True
        rad = [(2 * max(ri, (abs(K[i] - x[i])).upper())).upper() for i, ri in enumerate(rad)]
    return box, False


# ---------------------------------------------------------------------------
# E. the five-coefficient model, D = n/2
# ---------------------------------------------------------------------------
#
# Holland fixes D = B_J/2, which needs the auxiliary Jacobi fit (his Lemmas 4.3
# to 5.4). Any D within relative O(1/L) of n/2 serves his Lemma 6.1, and we fix
# D = n/2 (w_D = 2), so the data enter only through tau_0..tau_2. The model is
# still F_j(A, B, C, D, S) of his eq. (4). Unknowns X = (g0, gb, gc):
#
#     w_A = eps g0,   w_B = w_b - eps gb,   w_C = 2 - eps gc,   eps := tau_0,
#
# and the signed gap set is [0, w_A] u [w_B, w_b] minus [w_C, 2]. The limit of
# the system is linear, (g0 + gb - gc, 2 gb - 4 gc, 3 gb - 12 gc) = (1, 1, 1), with
# the unique solution X* = (5/12, 2/3, 1/12) and determinant -12.

X5_STAR = (Fraction(5, 12), Fraction(2, 3), Fraction(1, 12))


@dataclass
class Data:
    sub: Sub
    T: list  # T_j = tau_j/(2 e_1)
    eps: arb  # tau_0
    t: list  # t_j = tau_j/tau_0 - 1
    w_b: arb
    n_eps_lo: arb  # n tau_0 >= this


def make_data(sub: Sub, lb: LaplaceBound, jmax: int) -> Data:
    T = targets(sub, lb, jmax)
    eps = 2 * sub.e * T[0]
    t = [arb(0)] + [Tj / T[0] - 1 for Tj in T[1:]]  # t_0 = 0 exactly, since eps := tau_0
    w_b = 1 / (1 + sub.eta / 2)
    n_eps_lo = (2 * sub.n_lo * ab(sub.e_hi) * T[0].lower()).lower()
    return Data(sub, T, eps, t, w_b, n_eps_lo)


def m5_system(D: Data):
    eps, eta, w_b, t = D.eps, D.sub.eta, D.w_b, D.t

    def Phi(X):
        g0, gb, gc = X
        out = []
        for j in range(3):
            tA = g0 ** (j + 1) * eps**j * pi_range(j, (eta * eps * g0).upper())
            tB = gb * P_poly(j, w_b, eps * gb) * pi_range(j, (eta * w_b).upper())
            tC = gc * P_poly(j, ab(2), eps * gc) * pi_range(j, (2 * eta).upper())
            out.append(tA + tB - tC - (1 + t[j]))
        return out

    def DPhi(X):
        g0, gb, gc = X
        return [[upj(j, eps * g0, eta), upj(j, w_b - eps * gb, eta), -upj(j, 2 - eps * gc, eta)]
                for j in range(3)]

    return Phi, DPhi


def solve_m5(D: Data):
    Phi, DPhi = m5_system(D)
    x0 = [ab(q) for q in X5_STAR]
    box, ok = krawczyk(Phi, DPhi, x0, [Fraction(1, 10**6)] * 3)
    return box, ok


@dataclass
class Model5:
    """Scaled parameters of the five-coefficient model on a subinterval."""

    w_A: arb
    w_B: arb
    w_C: arb
    w_D: arb
    X: list
    ok: bool


def model5(D: Data) -> Model5:
    X, ok = solve_m5(D)
    g0, gb, gc = X
    return Model5(D.eps * g0, D.w_b - D.eps * gb, 2 - D.eps * gc, ab(2), X, ok)


def localize5(M: Model5, delta: arb, eta: arb, kappa: arb, eps: arb, gc: arb) -> dict:
    """Lemma G: every root and critical point y of p_F has |y - B| <= C_loc sqrt(Bd).

    Gershgorin on Holland's Jacobi matrices (75), (76), with sharper row bounds
    than his (79). `delta` is the ball [0, d/n max], and every quantity is in units
    where n = 1; sqrt(Bd) = sqrt(delta/w_B)."""
    wA, wB, wC = M.w_A, M.w_B, M.w_C
    dpe = delta + eta  # (d + 1)/n <= delta + eta
    sd = sqrt_nn(delta)
    # first factor q_{A,B}: roots in B + sqrt(Bd) [-2 beta1, abar1 + 2 beta1]
    shrinkA = 1 - dpe * wA  # (U - d - 1)/U
    beta1 = sqrt_nn(1 + delta * wB) / shrinkA
    abar1 = sqrt_nn(delta * wB) * (2 + wA / wB) / shrinkA
    # second factor q_{C,D}: in units n = 1, C = 1/w_C, D = 1/2, G = C - D, H = C - d - 1
    C = 1 / wC
    Dd = ab(Fraction(1, 2))
    G = C - Dd
    H = C - dpe
    bbar2 = (C / H) * sqrt_nn(delta * (delta + Dd) * G / H)
    eta_minus = (2 * delta * abs(C - 1) / H + 2 * bbar2) / Dd
    eta_plus = (Dd * delta / H + 2 * bbar2) / Dd
    # B eta / sqrt(Bd) = eta sqrt(B/d) = eta / sqrt(delta w_B), written without 0/0:
    #   eta_minus/sqrt(delta w_B) = 2 sqrt(delta/w_B)|C-1|/(H D) + 2 (C/H) sqrt((delta + D) G/(H w_B))/D
    em_scaled = (2 * sd * abs(C - 1) / (H * Dd)) / wB.sqrt() \
        + 2 * (C / H) * sqrt_nn((delta + Dd) * G / (H * wB)) / Dd
    ep_scaled = (sd / H) / wB.sqrt() + 2 * (C / H) * sqrt_nn((delta + Dd) * G / (H * wB)) / Dd
    left = 2 * beta1 * (1 - eta_minus) + em_scaled
    right = (abar1 + 2 * beta1) * (1 + eta_plus) + ep_scaled
    C_loc = left.union(right).upper()
    conds = {
        "(77) A >= B + d": pos(wB - wA * (1 + delta * wB)),
        "(77) B >= 32 d": pos(1 / wB - 32 * delta),
        # C - D = n eps gc/(2 w_C) >= d  <=>  gc/(2 w_C) >= d/(n eps)
        "(77) C >= D + d": pos(gc / (2 * wC) - kappa),
        "(77) D >= 32 d": pos(Dd - 32 * delta),
        "eta_minus < 1": pos(1 - eta_minus),
        # the diagonal bounds of Lemma G are case-wise: U >= 2V for the first factor,
        # U < 2V for the second
        "Lemma G case: A >= 2B": pos(wB - 2 * wA),
        "Lemma G case: C < 2D": pos(wC - 1),
    }
    return {"C_loc": C_loc, "beta1": beta1.upper(), "eta_minus": eta_minus.upper(),
            "eta_plus": eta_plus.upper(), "conds": conds}


def ratios91(M: Model5, C_loc: arb, K6, delta: arb, eta: arb) -> dict:
    """Holland's Lemma 9.1 with explicit constants: |T_k| <= r^k at every critical point
    for r = K6 sqrt(Bd), provided a + b + theta < 1 (EFFECTIVE.md, Lemma 9.1-E)."""
    K6 = ab(K6)
    wA, wB, wC = M.w_A, M.w_B, M.w_C
    sdw = sqrt_nn(delta * wB)  # sqrt(d/B)
    yB = 1 + C_loc * sdw  # y_+/B
    yA = yB * wA / wB  # y_+/A
    a_m = (C_loc + sdw * (1 + yA)) / ((1 - yA) * K6)
    b_m = (1 + delta * wA) * yB / ((1 - yA) * K6**2)
    eps_p = 1 - wC / 2  # (C - D)/C
    rD = 2 * K6 * sqrt_nn(delta / wB)  # r/D
    sd = sqrt_nn(delta)
    c_V = (1 + K6 * sdw * wA / wB + (2 * delta + 3 * eta) * wA + 2 * sdw / K6
           + 10 * delta * sd * wA * wB.sqrt() / K6 + delta * wB / (4 * K6**2)
           + delta**2 * wA * wB / (4 * K6**2))
    theta = yB * (2 / wB) * eps_p * c_V / ((1 - yA) * (1 - rD))
    total = a_m + b_m + theta
    conds = {"y_+/A < 1": pos(1 - yA), "r/D < 1": pos(1 - rD), "a + b + theta < 1": pos(1 - total)}
    return {"a": a_m.upper(), "b": b_m.upper(), "theta": theta.upper(), "total": total.upper(),
            "conds": conds}


def residual5(D: Data, M: Model5, lb: LaplaceBound, zeta_max) -> arb:
    """Theta_5 >= sup over |y| <= zeta_max of |E_F^(5)(n y)| n^4/(6 eps) (Lemma 8.1-E).

    E^(5)(z) = h^(5)(n+z) - psi4(b+z) + psi4(B+z) + psi4(D+z) - psi4(A+z) - psi4(C+z),
    psi4(y) = -6/y^4 + r(y), |r(y)| <= 24/(Re y)^5. With omega(w) = w^4/(1 + w y)^4:
    the -6/y^4 parts give (6 eps/n^4)[g0 w_A^3 (1+w_A y)^-4 + gb omega'[w_B, w_b] - gc omega'[w_C, 2]]
    (integral form, convex hull of the range), and h^(5) = -(12 e_1/n^4) H_5(y)."""
    zmax = ab(zeta_max).upper()
    y = disk(zmax)
    g0, gb, gc = M.X
    H5 = deriv_ball(5, D.sub, lb, y, lb.q)

    def om_p(w):
        return 4 * w**3 * cpow(1 + w * y, -5)

    IB = acb(D.w_b.union(M.w_B))
    IC = acb(M.w_C.union(ab(2)))
    main = -H5 / D.T[0] + g0 * M.w_A**3 * cpow(1 + M.w_A * y, -4) + gb * om_p(IB) - gc * om_p(IC)
    # psi remainders: sum over P of 24/(n^5 (1/w_P - |y|)^5), normalised by n^4/(6 eps)
    rem = arb(0)
    for w in (D.w_b, M.w_B, M.w_D, M.w_A, M.w_C):
        rem += w.upper() ** 5 / (1 - zmax * w.upper()) ** 5
    rem = 4 * rem / D.n_eps_lo
    return (main.abs_upper() + rem).upper()


def wedge_delta(sub: Sub, K, power: int, logpow: int, logd_lo=None) -> arb:
    """Upper bound for d/n on the subinterval under the wedge hypothesis.

    Five coefficients (power 5): n^3 log^2(n+2) >= K d^5 gives
    d/n <= (log^2(n+2)/(K n^2))^{1/5}, decreasing in n, so its value at n_lo.
    Six coefficients (power 6): n^4 log^2(n+2) >= K d^6 log^12(d+2) >= K d^6 log^12(3)
    gives d/n <= (log^2(n+2)/(K log^12(3) n^2))^{1/6}, also decreasing."""
    L = (sub.n_lo + 2).log()
    if power == 5:
        x = L**2 / (ab(K) * sub.n_lo**2)
        return hull(0, (x ** (arb(1) / 5)).upper())
    x = L**2 / (ab(K) * logd_lo**12 * sub.n_lo**2)
    return hull(0, (x ** (arb(1) / 6)).upper())


def log_ratio(sub: Sub) -> arb:
    """max over the subinterval of log(n+2)/v_1(2n): the function decreases for
    n >= 1000 (EFFECTIVE.md, Lemma W), so it is the value at n_lo, where v_1 = v_lo."""
    return ((sub.n_lo + 2).log() / sub.v_lo).upper()


def chain5(sub: Sub, lb: LaplaceBound, K, K6) -> dict:
    """Every step of the five-coefficient chain on one subinterval, for the claimed K, K6.

    Returns the constants and the conditions; `K_req` is the smallest K this
    subinterval needs (with the given K6 and the d/n range implied by the claimed K)."""
    if not bool(sub.n_lo >= ab(lb.x0)):
        raise ValueError("subinterval below the Laplace threshold")
    D = make_data(sub, lb, 2)
    M = model5(D)
    delta = wedge_delta(sub, K, 5, 2)
    v_lo = sub.v_lo
    # d/(n tau_0) = delta v_1/(2 T_0): decreasing in n, value at n_lo
    kappa = hull(0, (delta.upper() * v_lo / (2 * D.T[0].lower())).upper())
    g0, gb, gc = M.X
    loc = localize5(M, delta, sub.eta, kappa, D.eps, gc)
    rat = ratios91(M, loc["C_loc"], K6, delta, sub.eta)
    K6b = ab(K6)
    zeta = (sqrt_nn(delta) * (sqrt_nn(delta) + 2 * K6b / M.w_B.sqrt())).upper()
    Th = residual5(D, M, lb, zeta)
    C_E = (D.T[0] * Th * (sqrt_nn(delta) + 2 * K6b / M.w_B.sqrt()) ** 5 / 10).upper()
    lr = log_ratio(sub)
    K_req = ((C_E * lr / ab(17).log()) ** 2).upper()
    conds = {"matching (Krawczyk)": M.ok, **loc["conds"], **rat["conds"],
             "zeta <= RHO_D": pos(ab(RHO_D) - zeta),
             "n_lo >= 1000 (Lemma W)": pos(sub.n_lo - 1000)}
    return {"e": (sub.e_lo, sub.e_hi), "n_lo": sub.n_lo, "X": M.X, "T": D.T, "t": D.t,
            "C_loc": loc["C_loc"], "a": rat["a"], "b": rat["b"], "theta": rat["theta"],
            "total91": rat["total"], "zeta": zeta, "Theta5": Th, "C_E": C_E, "log_ratio": lr,
            "K_req": K_req, "conds": conds}


# ---------------------------------------------------------------------------
# covers and the threshold n_0
# ---------------------------------------------------------------------------


def e_of_n(n) -> Fraction:
    """A rational at or above e(n) = 1/v_1(2n)."""
    with rigor._flint_prec(PREC):
        v = v_of_s_real(ab(2 * Fraction(n)))
        return fraction_up(1 / v, 12)


def cover(e_max: Fraction, step: Fraction) -> list:
    """Closed subintervals [k step, (k+1) step] covering [0, e_max]."""
    out, k = [], 0
    while k * step < e_max:
        out.append((k * step, (k + 1) * step))
        k += 1
    return out


def n_threshold_gorttw(K, power: int = 5, logd: bool = False) -> arb:
    """The n above which the wedge allows d > 9.36e20 (GORTTW Cor. 1.3 covers the rest).

    Five coefficients: n^3 log^2(n+2) >= K d^5 with d > D_G forces
    n^3 log^2(n+2) > K D_G^5; returns the n solving equality (a lower bound for
    every n the wedge machinery must handle). Six coefficients: n^4 log^2(n+2) >
    K D_G^6 log^12(D_G + 2)."""
    with rigor._flint_prec(PREC):
        DG = ab(D_GORTTW)
        if power == 5:
            rhs = ab(K) * DG**5
            f = lambda n: n**3 * (n + 2).log() ** 2  # noqa: E731
        else:
            rhs = ab(K) * DG**6 * (DG + 2).log() ** 12
            f = lambda n: n**4 * (n + 2).log() ** 2  # noqa: E731
        lo_n, hi_n = arb(1), arb(2)
        while not (f(hi_n) > rhs):
            hi_n = hi_n * hi_n
        for _ in range(400):
            mid = arb(((lo_n + hi_n) / 2).mid())
            if f(mid) > rhs:
                hi_n = mid
            else:
                lo_n = mid
            if hi_n / lo_n < 1 + arb(2) ** -60:
                break
        return lo_n.lower()


def cover_threshold(n0, step: Fraction):
    """The cover of [0, e(n0)] by subintervals of length `step`, and the true threshold
    it covers: every n >= n_cover, where n_cover <= n0 is n_lo of the top subinterval."""
    with rigor._flint_prec(PREC):
        subs = cover(e_of_n(n0), step)
        top = Sub(*subs[-1])
        n_cover = Fraction(math.floor(lo(top.n_lo) * (1 - 1e-12)))
        return subs, n_cover


def run5(n0, K, K6, step) -> dict:
    """The five-coefficient chain over every n >= n_cover (<= n0), for claimed K and K6.
    The Laplace threshold is n_cover itself."""
    with rigor._flint_prec(PREC):
        subs, n_cover = cover_threshold(n0, step)
        lb = laplace_bound(n_cover)
        rows = [chain5(Sub(a, b), lb, K, K6) for a, b in subs]
        K_req = max((r["K_req"] for r in rows), key=lambda x: up(x))
        failed = [(str(r["e"][0]), k) for r in rows for k, v in r["conds"].items() if not v]
        failed += [("laplace", k) for k, v in lb.conditions.items() if not v]
        return {"lb": lb, "rows": rows, "K_req": K_req, "failed": failed, "n_cover": n_cover}


# ---------------------------------------------------------------------------
# F. the six-coefficient Pade model (H1 made explicit), Lemmas A to C, K'
# ---------------------------------------------------------------------------
#
# H1_H3.md section 4: unknowns X = (g0, gx, g1, x),
#     w_A = eps g0, w_B = x - eps gx/2, w_C = x + eps gx/2, w_D = 1 - eps g1,
# gap set [0, w_A] u [w_B, w_C] u [w_D, w_b], equations j = 0..3. The limit
# vanishes at Simpson's rule X* = (1/6, 2/3, 1/6, 1/2).

X6_STAR = (Fraction(1, 6), Fraction(2, 3), Fraction(1, 6), Fraction(1, 2))


def P_odd(j: int, x, e):
    """((x + e/2)^{j+1} - (x - e/2)^{j+1})/e, exactly (only odd k survive)."""
    out = arb(0)
    for k in range(1, j + 2, 2):
        out += math.comb(j + 1, k) * x ** (j + 1 - k) * (e / 2) ** (k - 1)
    return out


def upp(j: int, t, eta):
    """u_j''(t) = (j+1)[j t^{j-1} pi_j(eta t) + t^j eta pi_j'(eta t)],
    pi_j'(y) = -pi_j(y) sum_i i/(1 + i y)."""
    y = eta * t
    pj = pi_j(j, y)
    s = arb(0)
    for i in range(1, j + 2):
        s += ab(i) / (1 + i * y)
    first = j * t ** (j - 1) * pj if j >= 1 else arb(0)
    return (j + 1) * (first - t**j * eta * pj * s)


def m6_system(D: Data):
    eps, eta, w_b, t = D.eps, D.sub.eta, D.w_b, D.t
    beta_b = hull(0, (ab(Fraction(1, 2)) / D.n_eps_lo).upper())  # (1 - w_b)/eps = eta/((2 + eta) eps)

    def Phi(X):
        g0, gx, g1, x = X
        out = []
        for j in range(4):
            tA = g0 ** (j + 1) * eps**j * pi_range(j, (eta * eps * g0).upper())
            tX = gx * P_odd(j, x, eps * gx) * pi_range(j, (eta * (x + eps * gx / 2)).upper())
            g1b = g1 - beta_b
            t1 = g1b * P_poly(j, w_b, eps * g1b) * pi_range(j, (eta * w_b).upper())
            out.append(tA + tX + t1 - (1 + t[j]))
        return out

    def DPhi(X):
        g0, gx, g1, x = X
        wB, wC = x - eps * gx / 2, x + eps * gx / 2
        rows = []
        for j in range(4):
            # d/dx = (u_j'(w_C) - u_j'(w_B))/eps, with u_j' = (j+1) t^j pi_j(eta t):
            # (j+1) gx P_odd(j-1, x, eps gx) pi_j(eta w_C) + (j+1) w_B^j (pi_j(eta w_C) - pi_j(eta w_B))/eps,
            # and |pi_j'| <= c_j = (j+1)(j+2)/2, so the second part is gx eta c_j (j+1) w_B^j [-1, 1].
            cj = (j + 1) * (j + 2) // 2
            if j >= 1:
                dx = (j + 1) * gx * P_odd(j - 1, x, eps * gx) * pi_range(j, (eta * wC).upper())
            else:
                dx = arb(0)
            dx += arb(0, ((j + 1) * cj * cabs_up(gx) * eta.upper() * cabs_up(wB) ** j).upper())
            rows.append([upj(j, eps * g0, eta), (upj(j, wC, eta) + upj(j, wB, eta)) / 2,
                         upj(j, 1 - eps * g1, eta), dx])
        return rows

    return Phi, DPhi


@dataclass
class Model6:
    w_A: arb
    w_B: arb
    w_C: arb
    w_D: arb
    X: list
    ok: bool
    beta_b: arb


def model6(D: Data) -> Model6:
    Phi, DPhi = m6_system(D)
    X, ok = krawczyk(Phi, DPhi, [ab(q) for q in X6_STAR], [Fraction(1, 10**6)] * 4)
    g0, gx, g1, x = X
    beta_b = hull(0, (ab(Fraction(1, 2)) / D.n_eps_lo).upper())
    return Model6(D.eps * g0, x - D.eps * gx / 2, x + D.eps * gx / 2, 1 - D.eps * g1, X, ok, beta_b)


def residual6(D: Data, M: Model6, lb: LaplaceBound, zeta_max) -> arb:
    """Theta_6 >= sup over |y| <= zeta_max of |E^(6)(n y)| n^5/(24 eps): the analogue of
    residual5 with psi5(y) = 24/y^5 + r, |r| <= 120/(Re y)^6, omega5(w) = w^5/(1 + w y)^5,
    and h^(6) = (48 e_1/n^5) H_6(y). The Simpson cancellation is kept: at leading order
    the bracket is 1 - 25/24."""
    zmax = ab(zeta_max).upper()
    y = disk(zmax)
    g0, gx, g1, x = M.X
    H6 = deriv_ball(6, D.sub, lb, y, lb.q)

    def om5p(w):
        return 5 * w**4 * cpow(1 + w * y, -6)

    IX = acb(M.w_B.union(M.w_C))
    I1 = acb(M.w_D.union(D.w_b))
    main = H6 / D.T[0] - (g0 * M.w_A**4 * cpow(1 + M.w_A * y, -5) + gx * om5p(IX)
                          + (g1 - M.beta_b) * om5p(I1))
    rem = arb(0)
    for w in (D.w_b, M.w_B, M.w_D, M.w_A, M.w_C):
        rem += w.upper() ** 6 / (1 - zmax * w.upper()) ** 6
    rem = 5 * rem / D.n_eps_lo
    return (main.abs_upper() + rem).upper()


def harmonic_log_constant(d_min) -> Fraction:
    """c_H with 4 + 3 H_d <= c_H log(d + 2) for every d >= d_min (>= 6):
    H_d <= log d + gamma + 1/(2d) <= log(d + 2) + 0.6607, so
    4 + 3 H_d <= 3 log(d + 2) + 5.983, and log(d + 2) >= log(d_min + 2)."""
    with rigor._flint_prec(PREC):
        L = (ab(d_min) + 2).log()
        return fraction_up(3 + ab(Fraction(5983, 1000)) / L, 6)


def chain6(sub: Sub, lb: LaplaceBound, K, d_min, d_wedge_min=1) -> dict:
    """Every step of the six-coefficient chain on one subinterval, for claimed K'.

    d_min is the smallest degree the residual step must handle (6: below it the model
    matches every coefficient; or 9.36e20 + 1 when GORTTW Cor. 1.3 covers the rest).
    d_wedge_min is the smallest degree whose d/n range must be covered (1, or the
    GORTTW cut)."""
    if not bool(sub.n_lo >= ab(lb.x0)):
        raise ValueError("subinterval below the Laplace threshold")
    D = make_data(sub, lb, 3)
    M = model6(D)
    logd_lo = (ab(d_min) + 2).log().lower()
    delta = wedge_delta(sub, K, 6, 2, logd_lo=(ab(d_wedge_min) + 2).log().lower())
    c_H = ab(harmonic_log_constant(d_min))
    wA, wB, wC, wD = M.w_A, M.w_B, M.w_C, M.w_D
    sd = sqrt_nn(delta)
    eta8 = 8 * sqrt_nn(delta * wD)  # 8 sqrt(d/D)
    rho_r = ab(9) / (2 * arb.pi()) * (1 + eta8) / (1 - eta8) * c_H
    # sqrt(2.47 + 6.07/d) <= sqrt(2.47 + 6.07/d_min)
    s247 = (ab(Fraction(247, 100)) + ab(Fraction(607, 100)) / ab(d_min)).sqrt()
    bracket = sd / logd_lo + 2 * rho_r * s247 / wB.sqrt()  # (d + 2r)/(n sqrt(delta) log(d+2))
    # zeta = (d + 2r)/n <= sqrt(delta) log(d+2) bracket. On a subinterval with finite
    # n_hi: sqrt(delta_max(n)) <= its value at n_lo and log(d+2) <= log(d_max(n_hi) + 2).
    # On the subinterval reaching n = infinity: sqrt(delta_max) log(d_max + 2) decreases
    # once d_max(n) > 150 (EFFECTIVE.md, Lemma W), so its value at n_lo bounds it.
    dmax_lo = (delta.upper() * sub.n_lo).upper()
    if sub.e_lo > 0:
        n_hi = (s_of_v(1 / ab(sub.e_lo)) / 2).upper()
        L_hi = (n_hi + 2).log()
        x_hi = L_hi**2 / (ab(K) * ((ab(d_wedge_min) + 2).log().lower()) ** 12 * n_hi**2)
        dmax_hi = (x_hi ** (arb(1) / 6) * n_hi).upper()
        zeta = (sd.upper() * (dmax_hi + 2).log() * bracket).upper()
        zeta_ok = True
    else:
        zeta = (sd.upper() * (dmax_lo + 2).log() * bracket).upper()
        zeta_ok = pos(dmax_lo - 150)
    Th = residual6(D, M, lb, zeta)
    C_E = (D.T[0] * Th * bracket**6 / 15).upper()
    lr = log_ratio(sub)
    K_req = ((C_E * lr / ab(33).log()) ** 2).upper()
    conds = {
        "matching (Krawczyk)": M.ok,
        # eps > 0 at every finite n, so the ordering 0 < w_A < w_B < w_C < w_D < 1 is
        # g0 > 0, w_B > w_A, gx > 0, w_D > w_C, g1 > 0
        "0 < w_A < w_B < w_C < w_D < 1": pos(M.X[0]) and pos(wB - wA) and pos(M.X[1])
        and pos(wD - wC) and pos(M.X[2]),
        "Lemma B: A >= 8B": pos(wB - 8 * wA),
        "Lemma B: B >= 256 d": pos(1 - 256 * delta * wB),
        "R2: C >= D + d": pos(wD - wC - delta * wC * wD),
        "R2: D >= 32 d": pos(1 - 32 * delta * wD),
        "R2: D > 64 d (eta < 1)": pos(1 - eta8),
        "zeta <= RHO_D": pos(ab(RHO_D) - zeta),
        "d_max(n_lo) > 150 (zeta decreasing, top subinterval)": zeta_ok,
        "n_lo >= 1000 (Lemma W)": pos(sub.n_lo - 1000),
    }
    return {"e": (sub.e_lo, sub.e_hi), "n_lo": sub.n_lo, "X": M.X, "T": D.T, "t": D.t,
            "Theta6": Th, "C_E": C_E, "bracket": bracket, "zeta": zeta, "log_ratio": lr,
            "K_req": K_req, "conds": conds}


def run6(n0, K, step, d_min, d_wedge_min=1) -> dict:
    """The six-coefficient chain over every n >= n_cover (<= n0), for claimed K'."""
    with rigor._flint_prec(PREC):
        subs, n_cover = cover_threshold(n0, step)
        lb = laplace_bound(n_cover)
        rows = [chain6(Sub(a, b), lb, K, d_min, d_wedge_min) for a, b in subs]
        K_req = max((r["K_req"] for r in rows), key=lambda x: up(x))
        failed = [(str(r["e"][0]), k) for r in rows for k, v in r["conds"].items() if not v]
        failed += [("laplace", k) for k, v in lb.conditions.items() if not v]
        return {"lb": lb, "rows": rows, "K_req": K_req, "failed": failed, "n_cover": n_cover}


# ---------------------------------------------------------------------------
# the smallest self-consistent K
# ---------------------------------------------------------------------------


def _valid(run: dict, K) -> bool:
    return not run["failed"] and bool(ab(K) >= run["K_req"])


def smallest_K(run_fn, K_hi, digits: int = 3, max_steps: int = 60):
    """The smallest K (with `digits` significant digits, rounded up) for which the chain
    `run_fn(K)` has no failed condition and K >= K_req(K). K_req decreases in K (it
    depends on K only through d/n), so the valid K form an up-set; bisect in log K.
    Returns (K, run at K)."""
    K_hi = Fraction(K_hi)
    r_hi = run_fn(K_hi)
    steps = 0
    while not _valid(r_hi, K_hi):
        K_hi *= 10
        r_hi = run_fn(K_hi)
        steps += 1
        if steps > max_steps:  # pragma: no cover
            raise RuntimeError("no valid K found")
    K_lo = K_hi / 10
    r_lo = run_fn(K_lo)
    while _valid(r_lo, K_lo):
        K_hi, r_hi = K_lo, r_lo
        K_lo = K_hi / 10
        r_lo = run_fn(K_lo)
    for _ in range(40):
        mid = Fraction(math.sqrt(float(K_lo) * float(K_hi)))
        mid = fraction_up(ab(mid), digits)
        if mid >= K_hi or mid <= K_lo:
            break
        r_mid = run_fn(mid)
        if _valid(r_mid, mid):
            K_hi, r_hi = mid, r_mid
        else:
            K_lo = mid
    return fraction_up(ab(K_hi), digits), r_hi


# ---------------------------------------------------------------------------
# G. the four variants, their claimed constants, and the effectivity check
# ---------------------------------------------------------------------------
#
# "assisted": GORTTW Corollary 1.3 (J^{d,n} hyperbolic for every n when
# d <= 9.36e20, via Platt's RH verification to 3.06e10) covers small d, so the
# chain is needed only where the wedge allows d > 9.36e20, which forces
# n > n_min(K); the cover starts below n_min(K). "standalone": no outside input
# for small n; K is raised above n_cover^3 log^2(n_cover + 2) (five) or
# n_cover^4 log^2(n_cover + 2)/log^12 3 (six) so that the wedge is empty below
# n_cover, which is Holland's own section 10 device with n_0 explicit.

SPECS = {
    "five_assisted": {"chain": 5, "n0": 10**34, "step": Fraction(1, 10**4),
                      "K6": Fraction(253, 100), "gorttw": True},
    "five_standalone": {"chain": 5, "n0": 8 * 10**5, "step": Fraction(5, 10**4),
                        "K6": Fraction(282, 100), "gorttw": False},
    "six_assisted": {"chain": 6, "n0": 10**36, "step": Fraction(1, 10**4),
                     "d_min": D_GORTTW + 1, "d_wedge_min": D_GORTTW + 1, "gorttw": True},
    "six_standalone": {"chain": 6, "n0": 15 * 10**6, "step": Fraction(5, 10**4),
                       "d_min": 6, "d_wedge_min": 1, "gorttw": False},
}

#: Claimed explicit constants, upper bounds unless the name says otherwise. They are
#: written down here, rounded up from `derive_claims()`, so that the effectivity
#: check compares a recomputation against fixed numbers. Any edit that makes a
#: recomputed constant exceed its claim turns the check red.
CLAIMS = {
    "five_assisted": {
        "K": Fraction(17900), "K_req": Fraction(17710), "lambda": Fraction("1.507e-16"),
        "rho_bar": Fraction("1.507e-16"), "C_rho": Fraction("1.888"), "log_ratio": Fraction("1.065"),
        "C_E": Fraction("354.1"), "C_loc": Fraction("2.094"), "a_plus_b_plus_theta": Fraction("0.997"),
        "Theta5": Fraction("1.034"), "n_min_over_n_cover": Fraction("12.64"),
    },
    "five_standalone": {
        "K": Fraction("9.10e19"), "K_req": Fraction(249300), "lambda": Fraction("0.006978"),
        "rho_bar": Fraction("0.006954"), "C_rho": Fraction("2.029"), "log_ratio": Fraction("1.263"),
        "C_E": Fraction(1121), "C_loc": Fraction("2.22"), "a_plus_b_plus_theta": Fraction("0.9977"),
        "Theta5": Fraction("1.571"), "absorption": Fraction("9.082e19"),
    },
    "six_assisted": {
        "K": Fraction("7.21e9"), "K_req": Fraction("7.20e9"), "lambda": Fraction("2.048e-17"),
        "rho_bar": Fraction("2.048e-17"), "C_rho": Fraction("1.887"), "log_ratio": Fraction("1.062"),
        "C_E": Fraction(279400), "Theta6": Fraction("0.06606"), "bracket": Fraction("20.02"),
        "n_min_over_n_cover": Fraction("177.8"),
    },
    "six_standalone": {
        "K": Fraction("3.61e30"), "K_req": Fraction("1.479e16"), "lambda": Fraction("0.00179"),
        "rho_bar": Fraction("0.001788"), "C_rho": Fraction("1.985"), "log_ratio": Fraction("1.228"),
        "C_E": Fraction("3.466e8"), "Theta6": Fraction("0.5381"), "bracket": Fraction("46.98"),
        "absorption": Fraction("3.606e30"),
    },
}

#: constants that are lower bounds (a weakening raises them); everything else is an upper bound
LOWER_BOUNDS = {"n_min_over_n_cover"}


def absorption(chain: int, n_cover) -> arb:
    """K (or K') above which the wedge is empty for n < n_cover and every d >= 1."""
    with rigor._flint_prec(PREC):
        n = ab(n_cover)
        L2 = (n + 2).log() ** 2
        if chain == 5:
            return (n**3 * L2).upper()
        return (n**4 * L2 / ab(3).log() ** 12).upper()


def evaluate(name: str, K, K6=None) -> dict:
    """Run the variant's chain at a claimed K (and K6), and aggregate every constant
    over the cover. Pure recomputation: nothing here reads CLAIMS."""
    spec = SPECS[name]
    K6 = spec.get("K6") if K6 is None else K6
    with rigor._flint_prec(PREC):
        if spec["chain"] == 5:
            run = run5(Fraction(spec["n0"]), K, K6, spec["step"])
        else:
            run = run6(Fraction(spec["n0"]), K, spec["step"], spec["d_min"], spec["d_wedge_min"])
        rows, lb = run["rows"], run["lb"]

        def mx(key):
            return max((r[key] for r in rows), key=lambda x: up(x))

        agg = {"lambda": lb.lam, "rho_bar": lb.rho_bar, "C_rho": lb.C_rho, "K_req": run["K_req"],
               "log_ratio": mx("log_ratio"), "C_E": mx("C_E")}
        if spec["chain"] == 5:
            agg.update({"C_loc": mx("C_loc"), "a_plus_b_plus_theta": mx("total91"),
                        "Theta5": mx("Theta5")})
        else:
            agg.update({"Theta6": mx("Theta6"), "bracket": mx("bracket")})
        n_cover = run["n_cover"]
        if spec["gorttw"]:
            agg["n_min_over_n_cover"] = (n_threshold_gorttw(K, power=spec["chain"]) / ab(n_cover)).lower()
        else:
            agg["absorption"] = absorption(spec["chain"], n_cover)
        return {"name": name, "K": Fraction(K), "K6": K6, "n_cover": n_cover, "agg": agg,
                "failed": run["failed"], "rows": rows, "lb": lb, "subintervals": len(rows)}


def derive_claims(name: str) -> dict:
    """The smallest self-consistent K for the variant, and every aggregated constant
    rounded up to 4 significant digits (lower bounds rounded down). This is how the
    CLAIMS table was produced; the check never calls it."""
    spec = SPECS[name]
    if spec["gorttw"]:
        start = 10**4 if spec["chain"] == 5 else 10**9
        K, _ = smallest_K(lambda K: evaluate_run(name, K), start)
    else:
        subs, n_cover = cover_threshold(Fraction(spec["n0"]), spec["step"])
        K = fraction_up(absorption(spec["chain"], n_cover) * (1 + ab(Fraction(1, 10**3))), 3)
    ev = evaluate(name, K)
    claims = {"K": K}
    for key, val in ev["agg"].items():
        if key in LOWER_BOUNDS:
            l = lo(val)
            e = math.floor(math.log10(l)) - 3
            claims[key] = Fraction(math.floor(l / 10.0**e)) * Fraction(10) ** e
        else:
            claims[key] = fraction_up(val, 4)
    return claims


def evaluate_run(name: str, K) -> dict:
    spec = SPECS[name]
    if spec["chain"] == 5:
        return run5(Fraction(spec["n0"]), K, spec["K6"], spec["step"])
    return run6(Fraction(spec["n0"]), K, spec["step"], spec["d_min"], spec["d_wedge_min"])


def effectivity_check(name: str, claims: dict | None = None, K6=None) -> dict:
    """Green only if every claimed constant covers its recomputation, every condition of
    the chain holds at the claimed K, K >= K_req, and the threshold is consistent
    (assisted: n_min(K) >= n_cover; standalone: K >= the absorption constant).

    Returns {check: bool}; `all(result.values())` is the verdict."""
    claims = dict(CLAIMS[name] if claims is None else claims)
    spec = SPECS[name]
    K = claims["K"]
    ev = evaluate(name, K, K6=K6)
    out = {"every condition of the chain holds": not ev["failed"]}
    for key, val in ev["agg"].items():
        if key not in claims:
            continue
        if key in LOWER_BOUNDS:
            out[f"claimed {key} <= recomputed"] = bool(ab(claims[key]) <= val)
        else:
            out[f"claimed {key} >= recomputed"] = bool(ab(claims[key]) >= val)
    out["K >= K_req"] = bool(ab(K) >= ev["agg"]["K_req"])
    if spec["gorttw"]:
        out["n_min(K) >= n_cover"] = bool(ev["agg"]["n_min_over_n_cover"] >= 1)
    else:
        out["K >= absorption(n_cover)"] = bool(ab(K) >= ev["agg"]["absorption"])
    return out


def planted_weakenings(name: str, claims: dict | None = None) -> dict:
    """For every claimed constant, plant a value just past its recomputation (0.1 percent
    on the unsafe side) and report whether the effectivity check turns red. The MISSION's
    kill condition is met if any entry is False."""
    claims = dict(CLAIMS[name] if claims is None else claims)
    ev = evaluate(name, claims["K"])
    out = {}
    for key in claims:
        planted = dict(claims)
        if key == "K":
            target = ev["agg"]["K_req"]
            planted["K"] = Fraction(lo(target)) * Fraction(999, 1000)
        elif key in LOWER_BOUNDS:
            planted[key] = Fraction(up(ev["agg"][key])) * Fraction(1001, 1000)
        else:
            planted[key] = Fraction(lo(ev["agg"][key])) * Fraction(999, 1000)
        verdict = effectivity_check(name, planted)
        out[key] = not all(verdict.values())  # True means the plant turned the check red
    spec = SPECS[name]
    if spec["chain"] == 5:
        # K6 is a chosen radius; weakening it means a smaller r, which must fail
        out["K6"] = not all(effectivity_check(name, claims, K6=spec["K6"] - Fraction(1, 100)).values())
    return out


# ---------------------------------------------------------------------------
# H. measurements beside the derivation (mpmath, no ball arithmetic)
# ---------------------------------------------------------------------------
#
# The effectivity check catches a claim weaker than its own recomputation; it
# cannot catch a wrong formula, because it recomputes with the same formula.
# These measurements read the same quantities off independent routes (direct
# quadrature of I(s), route B of phase 0, Newton solves of the exact systems,
# actual model polynomials), and the tests plant formula faults that they must
# catch. Each reports its slack: bound/measured.


def _mp():
    import mpmath

    return mpmath


def measure_laplace(n, phi: float = 0.0, dps: int = 40) -> dict:
    """|log I(s) e^{-G(s)}| at s = 2 n (1 + i tan(phi)), by mpmath quadrature along the
    horizontal line Im v = Im v_0 + 0.001 (not the proof's contour), against lambda."""
    mpm = _mp()
    with mpm.workdps(dps):
        a = mpm.mpf(9) / 4
        s = 2 * mpm.mpf(n) * (1 + 1j * mpm.tan(phi))
        g = mpm.log(abs(s) / mpm.pi)
        v0 = mpm.findroot(lambda v: s / v + a - mpm.pi * mpm.exp(v), mpm.mpc(g - mpm.log(g), phi))
        Psi = s / v0**2 + s / v0 + a
        G = s * mpm.log(v0) + a * v0 - (s / v0 + a) + mpm.log(2 * mpm.pi / Psi) / 2

        def alpha(v):
            tot = 0
            for k in range(1, 6):
                tot += (k**4 - 3 / (2 * mpm.pi) * k**2 * mpm.exp(-v)) * mpm.exp(-mpm.pi * (k * k - 1) * mpm.exp(v))
            return tot

        beta = mpm.im(v0) + mpm.mpf("0.001")
        R = mpm.re(v0)

        def f(v):
            return mpm.exp(s * mpm.log(v) + a * v - mpm.pi * mpm.exp(v) - G) * alpha(v)

        w = 1 / mpm.sqrt(abs(Psi))
        pts = [R + c * w for c in (-60, -20, -8, -3, 0, 3, 8, 20, 60)]
        line = [mpm.mpc(R / 2, beta)] + [mpm.mpc(x, beta) for x in pts if x > R / 2] + [mpm.mpc(R + 4, beta)]
        val = mpm.quad(f, [0] + line)
        meas = abs(mpm.log(val))
    with rigor._flint_prec(PREC):
        lb = laplace_bound(Fraction(n))
    return {"n": n, "phi": phi, "measured": float(meas), "lambda": up(lb.lam),
            "slack": up(lb.lam) / float(meas)}


def route_b_taus(n, jmax: int = 4) -> list:
    """tau_j = (-1)^j n^{j+1}/j! Delta^{j+2} h(n), j = 0..jmax, from phase 0's route B
    (Laplace series, no quadrature): h(n + z) = log gamma(n + z) + log Gamma(n + 1/2 + z)
    + linear, and Delta^m z^i at 0 = sum_k (-1)^{m-k} C(m, k) k^i."""
    import probe

    mpm = _mp()
    dps = int(5 * math.log10(n)) + 50
    with mpm.workdps(dps):
        g = probe.saddle_expansion(n, dps, order=9)
        nn = mpm.mpf(n)
        h = [mpm.mpf(0), mpm.mpf(0)] + [g[i] + mpm.polygamma(i - 1, nn + mpm.mpf(1) / 2) / mpm.factorial(i)
                                       for i in range(2, 10)]
        out = []
        for j in range(jmax + 1):
            m = j + 2
            dm = mpm.fsum(h[i] * mpm.fsum((-1) ** (m - k) * mpm.binomial(m, k) * mpm.mpf(k) ** i
                                          for k in range(m + 1)) for i in range(2, 10))
            out.append((-1) ** j * nn ** (j + 1) / mpm.factorial(j) * dm)
        return out


def _u(j: int, w, n):
    mpm = _mp()
    return mpm.quad(lambda t: (j + 1) * t**j / mpm.fprod(1 + i * t / n for i in range(1, j + 2)), [0, w])


def newton_model5(n, taus: list) -> dict:
    """The exact D = n/2 system with route B targets, solved by mpmath (no Krawczyk)."""
    mpm = _mp()
    with mpm.workdps(40):
        nn = mpm.mpf(n)
        eps = taus[0]
        wb = nn / (nn + mpm.mpf(1) / 2)
        U = {}

        def u(j, w):
            return _u(j, w, nn)

        def eqs(g0, gb, gc):
            return [(u(j, eps * g0) + u(j, wb) - u(j, wb - eps * gb) - u(j, 2) + u(j, 2 - eps * gc)) / eps
                    - taus[j] / eps for j in range(3)]

        sol = mpm.findroot(eqs, [mpm.mpf(5) / 12, mpm.mpf(2) / 3, mpm.mpf(1) / 12])
        g0, gb, gc = sol
        return {"X": [g0, gb, gc], "A": nn / (eps * g0), "B": nn / (wb - eps * gb),
                "C": nn / (2 - eps * gc), "D": nn / 2, "eps": eps}


def newton_model6(n, taus: list) -> dict:
    """The exact Pade system (H1) with route B targets, solved by mpmath."""
    mpm = _mp()
    with mpm.workdps(40):
        nn = mpm.mpf(n)
        eps = taus[0]
        wb = nn / (nn + mpm.mpf(1) / 2)

        def u(j, w):
            return _u(j, w, nn)

        def eqs(g0, gx, g1, x):
            wA, wB, wC, wD = eps * g0, x - eps * gx / 2, x + eps * gx / 2, 1 - eps * g1
            return [(u(j, wA) + u(j, wC) - u(j, wB) + u(j, wb) - u(j, wD)) / eps - taus[j] / eps
                    for j in range(4)]

        sol = mpm.findroot(eqs, [mpm.mpf(1) / 6, mpm.mpf(2) / 3, mpm.mpf(1) / 6, mpm.mpf(1) / 2])
        g0, gx, g1, x = sol
        return {"X": [g0, gx, g1, x], "A": nn / (eps * g0), "B": nn / (x - eps * gx / 2),
                "C": nn / (x + eps * gx / 2), "D": nn / (1 - eps * g1), "eps": eps}


def sub_around(n) -> Sub:
    """A subinterval of width about 1e-24 around e(n)."""
    with rigor._flint_prec(PREC):
        v = v_of_s_real(ab(2 * Fraction(n)))
        e = 1 / v
        lo_ = Fraction(e.lower().mid().str(40, radius=False)) - Fraction(1, 10**24)
        hi_ = Fraction(e.upper().mid().str(40, radius=False)) + Fraction(1, 10**24)
        return Sub(lo_, hi_)


def measure_data_and_models(n) -> dict:
    """Route B targets inside the T_j enclosures; Newton solutions inside the Krawczyk
    boxes, for both models, on a tight subinterval around n."""
    taus = route_b_taus(n, 4)
    m5 = newton_model5(n, taus)
    m6 = newton_model6(n, taus)
    with rigor._flint_prec(PREC):
        lb = laplace_bound(Fraction(n) / 2)
        sub = sub_around(n)
        D = make_data(sub, lb, 3)
        e1 = 1 / v_of_s_real(ab(2 * Fraction(n)))
        T_in = [bool(D.T[j].contains(arb(_mp().nstr(taus[j], 45)) / (2 * e1))) for j in range(4)]
        M5 = model5(D)
        M6 = model6(D)
        in5 = [bool(M5.X[i].contains(arb(_mp().nstr(m5["X"][i], 40)))) for i in range(3)]
        in6 = [bool(M6.X[i].contains(arb(_mp().nstr(m6["X"][i], 40)))) for i in range(4)]
        return {"n": n, "T_contains_route_B": T_in, "model5_box_contains_newton": in5,
                "model6_box_contains_newton": in6, "m5": m5, "m6": m6, "taus": taus,
                "model5_box": [str(x) for x in M5.X], "model6_box": [str(x) for x in M6.X]}


def measure_polynomials(n, ds=(10, 40)) -> dict:
    """Actual roots, critical points and derivative ratios of both model polynomials at n,
    and the actual multiplier defects E_F(j) = log(R_j/R_j^F), against the chain's bounds."""
    import probe
    import probe_phase1 as P1

    mpm = _mp()
    meas = measure_data_and_models(n)
    out = {"n": n, "five": [], "six": []}
    with rigor._flint_prec(PREC):
        lb = laplace_bound(Fraction(n) / 2)
        sub = sub_around(n)
        D = make_data(sub, lb, 3)
        M5 = model5(D)
        M6 = model6(D)
    for d in ds:
        dps = 80 + int(d * (math.log10(n) + 3))  # Horner at y ~ B ~ n over degree d
        with mpm.workdps(dps):
            g = probe.saddle_expansion(n, int(5 * math.log10(n)) + 50, order=9)
            logR = [probe.log_R_from_expansion(g, j, top=9) for j in range(d + 1)]
            for chain, m in ((5, meas["m5"]), (6, meas["m6"])):
                A, B, C, Dd = (mpm.mpf(m[k]) for k in ("A", "B", "C", "D"))
                factors = [(A, B), (C, Dd)]
                c = P1.model_coeffs(d, factors)
                half = 6 * mpm.sqrt(B * d) + 10 * d
                rp = P1.real_roots(c, B - half, B + half, mpm.sqrt(B / d) / 20)
                row = {"d": d, "real_roots": len(rp)}
                if len(rp) == d:
                    crit = P1.critical_points(c, rp)
                    st = P1.ratio_stats(rp, crit)
                    sBd = mpm.sqrt(B * d)
                    row["C_loc_measured"] = float(max(abs(y - B) for y in rp + crit) / sBd)
                    row["r_needed_over_sqrt_Bd"] = float(st["r_needed"] / sBd)
                    S = B * mpm.exp(logR[1])
                    E = [logR[j] - j * mpm.log(S) - P1.log_m(j, factors) for j in range(d + 1)]
                    row["max_abs_E_F_at_integers"] = float(max(abs(x) for x in E))
                    row["_E"] = E
                out["five" if chain == 5 else "six"].append(row)
    # the chain's bounds at this n, with d/n exactly
    with rigor._flint_prec(PREC):
        for row in out["five"]:
            d = row["d"]
            delta = ab(Fraction(d) / Fraction(n))
            loc = localize5(M5, delta, sub.eta, hull(0, 1), D.eps, M5.X[2])
            row["C_loc_bound"] = up(loc["C_loc"])
            row["K6"] = float(SPECS["five_standalone"]["K6"])
            # real-axis Hermite-Genocchi at integers 5 <= j <= d: |E(j)| <= sup|E^(5)| prod/120
            Th = residual5(D, M5, lb, (delta + ab(Fraction(1, 10**30))).upper())
            if "_E" in row:
                worst = 0.0
                for j in range(5, d + 1):
                    bound = 6 * up(D.eps) * up(Th) / float(n) ** 4 * math.prod(j - i for i in range(5)) / 120
                    worst = max(worst, float(abs(row["_E"][j])) / bound)
                row["E_F_measured_over_bound"] = worst
                del row["_E"]
        for row in out["six"]:
            d = row["d"]
            row.pop("_E", None)
            Bm = meas["m6"]["B"]
            Dm = meas["m6"]["D"]
            eta8 = 8 * math.sqrt(d / float(Dm))
            Hd = sum(1 / k for k in range(1, d + 1))
            r12 = (9 / (2 * math.pi)) * (1 + eta8) / (1 - eta8) * (4 + 3 * Hd) * math.sqrt(float(Bm) * (2.47 * d + 6.07))
            row["r_12_3_over_sqrt_Bd"] = r12 / math.sqrt(float(Bm) * d)
    return out


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def git_head() -> str:
    try:
        return subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"], capture_output=True,
                              text=True, check=True).stdout.strip()
    except Exception:  # pragma: no cover
        return "unknown"


def _s(x) -> str:
    if isinstance(x, Fraction):
        return str(x) if x.denominator == 1 else repr(float(x))
    if isinstance(x, arb):
        return f"{x.str(8, radius=False)} (ball upper end {up(x):.10g})"
    if isinstance(x, acb):
        return f"|.| <= {up(x):.10g}"
    return str(x)


def time_unit() -> None:
    """One subinterval of each chain, and one Laplace bound: the unit of every sweep."""
    derive_F()
    t0 = time.time()
    with rigor._flint_prec(PREC):
        lb = laplace_bound(10**30)
        t1 = time.time()
        r5 = chain5(Sub(Fraction(130, 10**4), Fraction(131, 10**4)), lb, CLAIMS["five_assisted"]["K"],
                    SPECS["five_assisted"]["K6"])
        t2 = time.time()
        r6 = chain6(Sub(Fraction(120, 10**4), Fraction(121, 10**4)), lb, CLAIMS["six_assisted"]["K"],
                    D_GORTTW + 1, D_GORTTW + 1)
        t3 = time.time()
    print(f"Laplace bound {t1 - t0:.3f} s; five-coefficient subinterval {t2 - t1:.3f} s; "
          f"six-coefficient subinterval {t3 - t2:.3f} s")
    print(f"  K_req there: {up(r5['K_req']):.6g} (five), {up(r6['K_req']):.6g} (six)")
    n_sub = sum(len(cover(e_of_n(SPECS[k]["n0"]), SPECS[k]["step"])) for k in SPECS)
    unit = max(t2 - t1, t3 - t2)
    print(f"estimate: {n_sub} subintervals per full evaluation x about 50 evaluations "
          f"(claims, 44 plants, bisection) ~ {n_sub * unit * 50:.0f} s, plus measurements ~ 60 s")


def run(out: Path) -> dict:
    t0 = time.time()
    derive_F()
    res = {"hunt": "jensen_wedge", "phase": "2 (MISSION Q2, effectivity)", "git_head": git_head(),
           "backend": rigor.BACKEND, "prec_bits": PREC,
           "parameters": {"a": str(A_PHASE), "RHO": str(RHO), "T_STEP": str(T_STEP), "RHO_D": str(RHO_D),
                          "PROP22_EPS": PROP22_EPS, "PROP22_6_EPS": PROP22_6_EPS,
                          "D_GORTTW": str(D_GORTTW)},
           "first_order_coefficients_F_k": {str(k): str(first_order_coefficient(k)) for k in range(2, 8)},
           "variants": {}}
    for name, spec in SPECS.items():
        ev = evaluate(name, CLAIMS[name]["K"])
        chk = effectivity_check(name)
        pw = planted_weakenings(name)
        rows = ev["rows"]
        res["variants"][name] = {
            "spec": {k: _s(v) for k, v in spec.items()},
            "claims": {k: _s(v) for k, v in CLAIMS[name].items()},
            "recomputed": {k: _s(v) for k, v in ev["agg"].items()},
            "n_cover": str(ev["n_cover"]),
            "subintervals": ev["subintervals"],
            "laplace": {"R_min": _s(ev["lb"].R_min), "b": _s(ev["lb"].b), "q": _s(ev["lb"].q),
                        "pieces_times_sqrt_p": {k: _s(v) for k, v in ev["lb"].pieces.items()},
                        "conditions": ev["lb"].conditions},
            "effectivity_check": chk, "verdict": "green" if all(chk.values()) else "red",
            "planted_weakenings_turn_red": pw,
            "kill_condition_met": not all(pw.values()),
            "rows_sample": [{"e": [str(r["e"][0]), str(r["e"][1])], "n_lo": _s(r["n_lo"]),
                             "X": [_s(x) for x in r["X"]], "K_req": _s(r["K_req"]),
                             **({"C_loc": _s(r["C_loc"]), "a_b_theta": _s(r["total91"]),
                                 "Theta5": _s(r["Theta5"])} if spec["chain"] == 5 else
                                {"Theta6": _s(r["Theta6"]), "bracket": _s(r["bracket"])})}
                            for r in rows[:: max(1, len(rows) // 12)]],
        }
        print(f"{name}: K = {_s(CLAIMS[name]['K'])}, check {res['variants'][name]['verdict']}, "
              f"{sum(pw.values())}/{len(pw)} plants red ({time.time() - t0:.0f} s)", flush=True)
    meas = {"laplace": [measure_laplace(n, phi) for n, phi in ((10**6, 0.0), (10**6, 0.2),
                                                                  (10**8, 0.0), (10**8, 0.15))]}
    mdm = []
    for n in (10**8, 10**12, 10**20):
        m = measure_data_and_models(n)
        mdm.append({"n": n, "T_contains_route_B": m["T_contains_route_B"],
                    "model5_box_contains_newton": m["model5_box_contains_newton"],
                    "model6_box_contains_newton": m["model6_box_contains_newton"],
                    "model5_box": m["model5_box"], "model6_box": m["model6_box"]})
    meas["data_and_models"] = mdm
    meas["polynomials_n_1e12"] = measure_polynomials(10**12, ds=(10, 40))
    res["measurements"] = meas
    res["seconds"] = round(time.time() - t0, 1)
    out.write_text(json.dumps(res, indent=1, default=str) + "\n")
    print(f"wrote {out} ({res['seconds']} s)")
    return res


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--time-unit", action="store_true")
    ap.add_argument("--out", default=str(HERE / "results_effective.json"))
    args = ap.parse_args()
    if args.time_unit:
        time_unit()
        return
    run(Path(args.out))


if __name__ == "__main__":
    main()
