"""Independent reproduction of hunt #135 phase 2's explicit constants (review).

Run from the repository root:

    .venv/bin/python hunts/jensen_wedge/review_p2/reproduce_p2.py           # all four variants
    .venv/bin/python hunts/jensen_wedge/review_p2/reproduce_p2.py --quick   # coarse covers

This file is the reproduction half of `REVIEW_PHASE2.md`. It was written from the
formulas of `EFFECTIVE.md` and from this review's own derivations of the steps that
`EFFECTIVE.md` states only in words (the assembly of C_loc, the Laplace majorants of
Lemma L, the Krawczyk enclosures). It does not import `effective.py`, `probe.py`, or
anything under `review/` or `review_h1h3/`.

Every numeric step is an Arb ball (python-flint), reached only after checking that
`zeta.rigor.BACKEND` is python-flint. A ball makes a number a bound; it does not review
the derivation behind the formula it evaluates.

Conventions: a = 9/4; e_1 = 1/v_1(2n) with v_1 the real saddle, v (pi e^v - a) = s;
iota = 1/n; delta = d/n; every model parameter P enters through w_P = n/P.
"""

from __future__ import annotations

import argparse
import contextlib
import functools
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from zeta import rigor  # noqa: E402

if rigor.BACKEND != "python-flint":  # pragma: no cover
    raise RuntimeError(f"reproduce_p2.py needs Arb; zeta.rigor.BACKEND is {rigor.BACKEND!r}")

from flint import acb, arb, ctx  # noqa: E402

PREC = 256
A_PH = Fraction(9, 4)
RHO = Fraction(1, 4)
T_STEP = Fraction(1, 2)
D_GORTTW = 936 * 10**18  # GORTTW Cor. 1.3: hyperbolic for every n when d <= 9.36e20


@contextlib.contextmanager
def prec(bits: int = PREC):
    old = ctx.prec
    ctx.prec = bits
    try:
        yield
    finally:
        ctx.prec = old


def Q(x) -> arb:
    """Exact ball for a rational."""
    x = Fraction(x)
    return arb(x.numerator) / arb(x.denominator)


def iv(lo, hi) -> arb:
    """The ball hull of [lo, hi]."""
    lo = lo if isinstance(lo, arb) else Q(lo)
    hi = hi if isinstance(hi, arb) else Q(hi)
    return lo.union(hi)


def up(x) -> float:
    """A float at or above every point of the ball (abs for acb)."""
    if isinstance(x, acb):
        x = x.abs_upper()
    u = x.upper()
    f = float(u.mid()) + float(u.rad())
    return math.nextafter(f, math.inf)


def lo(x: arb) -> float:
    l = x.lower()
    f = float(l.mid()) - float(l.rad())
    return math.nextafter(f, -math.inf)


def disk(r: arb) -> acb:
    """A complex ball containing the closed disk |z| <= r."""
    r = r.upper()
    return acb(arb(0, up(r)), arb(0, up(r)))


def certainly(x) -> bool:  # noqa: D401 - a predicate on balls
    return bool(x)


def cpow(z, k: int):
    """z^k; for a complex box near 1, exp(k log z) avoids the wrapping of repeated products."""
    if isinstance(z, acb):
        return (k * z.log()).exp()
    return z**k


def sqrt0(x: arb) -> arb:
    """sqrt of a ball known to be >= 0 (Arb gives nan when the ball reaches below 0)."""
    l = x.lower()
    l = arb(0) if not certainly(l > 0) else l.sqrt().lower()
    return l.union(x.upper().sqrt().upper())


# ---------------------------------------------------------------------------
# 1. Lemma D(i): G^(k)(s) = (-1)^k (k-2)! e s^-(k-1) F_k(e, m), derived here in sympy
# ---------------------------------------------------------------------------


@functools.lru_cache(maxsize=1)
def derive_F(kmax: int = 7) -> dict:
    """F_k as (numerator coefficients, denominator coefficients) in (e, m), exact rationals.

    Independent derivation: G'(s) = -log e - (1/2) D_s log(Q/m), D_s = (e m/Q)(-e^2 d/de - m d/dm),
    Q = 1 + e - a e m, s = (1 - a m)/(e m)."""
    import sympy as sp

    e, m = sp.symbols("e m")
    a = sp.Rational(9, 4)
    Qs = 1 + e - a * e * m
    s = (1 - a * m) / (e * m)

    def Ds(f):
        return sp.together((e * m / Qs) * (-e**2 * sp.diff(f, e) - m * sp.diff(f, m)))

    g = -sp.log(e) - sp.Rational(1, 2) * Ds(sp.log(Qs) - sp.log(m))
    out = {}
    for k in range(2, kmax + 1):
        g = sp.factor(Ds(g))
        Fk = sp.cancel(g / ((-1) ** k * sp.factorial(k - 2) * e * s ** (-(k - 1))))
        num, den = sp.fraction(sp.together(Fk))
        pn = sp.Poly(sp.expand(num), e, m)
        pd = sp.Poly(sp.expand(den), e, m)
        out[k] = (
            {mon: Fraction(int(c.p), int(c.q)) for mon, c in zip(pn.monoms(), pn.coeffs())},
            {mon: Fraction(int(c.p), int(c.q)) for mon, c in zip(pd.monoms(), pd.coeffs())},
        )
    return out


def _shifted(coeffs: dict, e0: arb, m0: arb) -> dict:
    """Coefficients of sum c_ij e^i m^j in powers of (e - e0), (m - m0), as balls.

    Evaluating the shifted form on a small box keeps the dependency overestimate of ball
    arithmetic to first order in the box width (naive evaluation inflates it 7 to 50 times)."""
    out: dict = {}
    for (i, j), c in coeffs.items():
        cq = Q(c)
        for l in range(i + 1):
            ce = cq * math.comb(i, l) * e0 ** (i - l)
            for jj in range(j + 1):
                key = (l, jj)
                term = ce * math.comb(j, jj) * m0 ** (j - jj)
                out[key] = out[key] + term if key in out else term
    return out


def _horner(coeffs: dict, h, k):
    by_j: dict = {}
    for (i, j), c in coeffs.items():
        by_j.setdefault(j, {})[i] = c
    total = None
    for j in sorted(by_j, reverse=True):
        row = by_j[j]
        acc = None
        for i in range(max(row), -1, -1):
            c = row.get(i, arb(0))
            acc = c if acc is None else acc * h + c
        total = acc if total is None else total * k + acc
    return total


def _center(x) -> arb:
    if isinstance(x, acb):
        return arb(x.real.mid())
    return arb(x.mid())


def _d(coeffs: dict, var: int) -> dict:
    out = {}
    for (i, j), c in coeffs.items():
        p = i if var == 0 else j
        if p:
            key = (i - 1, j) if var == 0 else (i, j - 1)
            out[key] = out.get(key, 0) + p * c
    return out


@functools.lru_cache(maxsize=None)
def _parts(k: int):
    num, den = derive_F()[k]
    return num, den, _d(num, 0), _d(den, 0), _d(num, 1), _d(den, 1)


def _ev(coeffs: dict, e, m):
    e0, m0 = _center(e), _center(m)
    return _horner(_shifted(coeffs, e0, m0), e - e0, m - m0)


def F_point(k: int, e, m):
    num, den = derive_F()[k]
    return _ev(num, e, m) / _ev(den, e, m)


def F_grad(k: int, e, m):
    """Balls containing dF_k/de and dF_k/dm on the box."""
    N, D, Ne, De, Nm, Dm = _parts(k)
    n_, d_ = _ev(N, e, m), _ev(D, e, m)
    return ((_ev(Ne, e, m) * d_ - n_ * _ev(De, e, m)) / d_**2,
            (_ev(Nm, e, m) * d_ - n_ * _ev(Dm, e, m)) / d_**2)


def F_ball(k: int, e, m):
    """F_k on a (real or complex) box, in mean-value form about the box centre.

    F(e, m) - F(e0, m0) = int_0^1 grad F(segment) . (e - e0, m - m0), and the gradient
    on the convex box lies in the gradient's ball enclosure."""
    e0, m0 = _center(e), _center(m)
    Fe, Fm = F_grad(k, e, m)
    return F_point(k, e0, m0) + Fe * (e - e0) + Fm * (m - m0)


def F_diff(k1: int, k2: int, e, m):
    """F_k1 - F_k2 on the box, mean-value form (keeps the correlation through e)."""
    e0, m0 = _center(e), _center(m)
    a_e, a_m = F_grad(k1, e, m)
    b_e, b_m = F_grad(k2, e, m)
    return F_point(k1, e0, m0) - F_point(k2, e0, m0) + (a_e - b_e) * (e - e0) + (a_m - b_m) * (m - m0)


# ---------------------------------------------------------------------------
# 2. The real saddle, and Lemmas V, L, R (the review's own majorants)
# ---------------------------------------------------------------------------


def s_of_v(v):
    return v * (arb.pi() * v.exp() - Q(A_PH))


def v1_bounds(s) -> tuple:
    """Rigorous (lower, upper) floats with s_of_v(lower) < s < s_of_v(upper)."""
    s = Fraction(s)
    sf = float(s)
    v = math.log(sf / math.log(sf))
    for _ in range(200):
        f = v * (math.pi * math.exp(v) - 2.25) - sf
        fp = math.pi * math.exp(v) * (1 + v) - 2.25
        v -= f / fp
    lo_v, hi_v = v * (1 - 1e-12), v * (1 + 1e-12)
    for _ in range(60):
        if certainly(s_of_v(arb(lo_v)) < Q(s)):
            break
        lo_v -= 1e-9 * v
    for _ in range(60):
        if certainly(s_of_v(arb(hi_v)) > Q(s)):
            break
        hi_v += 1e-9 * v
    assert certainly(s_of_v(arb(lo_v)) < Q(s)) and certainly(s_of_v(arb(hi_v)) > Q(s))
    return lo_v, hi_v


def alpha_dev(X: arb, cosb: arb) -> arb:
    """Upper bound of |alpha(v) - 1| for Re v >= X, |Im v| <= b (cosb = cos b), X >= 1.

    alpha - 1 = -(3/(2 pi)) e^-v + sum_{k>=2} (k^4 - (3/(2 pi)) k^2 e^-v) exp(-pi (k^2-1) e^v)."""
    c = Q(3) / (2 * arb.pi())
    Y = arb.pi() * X.exp() * cosb  # Re(pi e^v) >= Y
    tail = arb(0)
    for k in range(2, 8):
        tail += (Q(k**4) + c * k * k) * (-(k * k - 1) * Y).exp()
    # k >= 8: k^4 e^{-(k^2-1) Y} <= e^{-(k^2-1)Y/2} for Y >= 1, a geometric tail below e^{-63 Y/2}
    tail += 2 * (-Q(63) * Y / 2).exp()
    return c * (-X).exp() + tail


def laplace(x0) -> dict:
    """Lemmas V and L at threshold x0, with this review's majorants (see REVIEW_PHASE2.md, R1)."""
    a = Q(A_PH)
    rho, T = Q(RHO), Q(T_STEP)
    s_min = 2 * Fraction(x0) * (1 - RHO)
    v_lo, _ = v1_bounds(s_min)
    V = arb(v_lo) - 1
    dA = a / arb.pi() * (-V).exp()
    q = 1 / V + dA / (1 - dA)
    theta = rho.asin()
    b = theta / (1 - q)
    Rm = V + 1 - b
    conds = {
        "q < 1": certainly(q < 1),
        "b <= 1 (disk inside the strip of H_V)": certainly(b <= 1),
        "R_min >= 10": certainly(Rm >= 10),
        "(i) theta + 2 atan(2b/R) <= pi/2": certainly(theta + 2 * (2 * b / Rm).atan() <= arb.pi() / 2),
    }
    p = arb.pi() * Rm.exp()
    cosb = b.cos()
    R = Rm
    # M_3 <= 2|s|/(R-T)^3 + p e^T, |s| <= |v0|(p + a), |v0| <= sqrt(R^2 + b^2); Re Psi >= p cos b
    bracket3 = 2 * (R * R + b * b).sqrt() * (1 + a / p) / (R - T) ** 3 + T.exp()
    conds["(ii) M_3 T/6 <= Re Psi/4"] = certainly(bracket3 * T / 6 <= cosb / 4)
    psi_abs = 1 + (1 + a / p) / R  # |Psi| <= p (1 + (1 + a/p)/R)
    a1 = alpha_dev(R - T, cosb)
    rho3 = (psi_abs / (2 * arb.pi())).sqrt() * (1 + a1) * Q(16) / 6 * bracket3 / cosb**2 \
        + p.sqrt() * a1 * (psi_abs / cosb).sqrt()
    # the other four pieces, as log10 of (piece) * sqrt(p) * sqrt(|Psi|/(2 pi)) upper bounds
    ReP = p * cosb
    ReP_psi = p * cosb
    scale = p * (psi_abs / (2 * arb.pi())).sqrt()  # sqrt(p) sqrt(|Psi|/(2 pi)) <= scale
    lg = {}
    lg["rho_G"] = (2 / (ReP_psi * T)).log() - ReP_psi * T * T / 2 + scale.log()
    kT = T.exp() - 1 - T
    kmT = (-T).exp() - 1 + T
    lg["rho_4"] = (1 + a1).log() - ReP * kT - (ReP * (T.exp() - 1)).log() + scale.log()
    a_half = alpha_dev(R / 2, cosb)
    lg["rho_2"] = (R / 2 * (1 + a_half)).log() - ReP * kmT + scale.log()
    lw = Q(2).log() - (1 + 4 * b * b / (R * R)).log() / 2
    sin_t = rho
    cos_t = (1 - rho * rho).sqrt()
    expo = p * (-cos_t * lw * R * (1 - a / p) + 3 * b * sin_t * (1 + b * b / (2 * R * R)) * (1 + a / p) + 1) - a * R / 2
    # on [0, w_1]: Re v in [0, R/2], |Im v| <= b, so |e^{-pi e^v} alpha(v)| <= A1 below
    cdef = Q(3) / (2 * arb.pi())
    A1 = (-arb.pi() * cosb).exp() * sum(
        ((Q(k**4) + cdef * k * k) * (-arb.pi() * (k * k - 1) * cosb).exp() for k in range(1, 12)), arb(0)
    ) + Q(Fraction(1, 10**6))
    lg["rho_1"] = ((R * R / 4 + b * b).sqrt() * A1).log() + expo + scale.log()
    lg = {k: v / arb(10).log() for k, v in lg.items()}
    for k, v in lg.items():
        conds[f"{k} * sqrt(p) < 1e-300"] = certainly(v < -300)
    C_rho = rho3 + Q(Fraction(4, 10**300))
    rbar = C_rho / p.sqrt()
    conds["C_rho/sqrt(p) < 1"] = certainly(rbar < 1)
    lam = -(1 - rbar).log()
    return {"x0": Fraction(x0), "V": V, "q": q, "theta": theta, "b": b, "R_min": Rm, "p": p,
            "C_rho": C_rho, "rho_bar": rbar, "lambda": lam, "log10_pieces": lg, "conds": conds}


# ---------------------------------------------------------------------------
# 3. The cover in e_1 = 1/v_1(2n), and enclosures of H_k (Lemma D(ii))
# ---------------------------------------------------------------------------


def n_of_v(v):
    return s_of_v(v) / 2


def make_sub(e_a: Fraction, e_b: Fraction, n0: Fraction) -> dict:
    """Every quantity of the subinterval e_1 in [e_a, e_b], n >= n0, as a ball."""
    v_lo = Q(1 / e_b)
    n_at_vlo = n_of_v(v_lo)
    clipped = not certainly(n_at_vlo.lower() > Q(n0))
    if clipped:
        n_lo = Q(n0)
        vl, vh = v1_bounds(2 * Fraction(n0))
        vl, vh = arb(vl), arb(vh)
    else:
        n_lo = n_at_vlo.lower()  # n of the subinterval is >= n(v_lo) >= n_lo
        vl = vh = v_lo           # v_1(2 n(v_lo)) = v_lo
    last = e_a == 0
    if last:
        n_hi = None
        iota = iv(0, 1 / n_lo)
        m1 = iv(0, 1 / (arb.pi() * v_lo.exp()))
    else:
        v_hi = Q(1 / e_a)
        n_hi = n_of_v(v_hi).upper()
        iota = iv(1 / n_hi, 1 / n_lo)
        m1 = iv(1 / (arb.pi() * v_hi.exp()), 1 / (arb.pi() * v_lo.exp()))
    # n e_1 = n/v_1(2n) increases in n; its least value is at n_lo, where v_1(2 n_lo) <= vh
    ne1_lo = n_lo / vh
    v1_at_nlo = vh
    # Lemma W(i): log(n+2)/v_1(2n) decreases in n, so its largest value is at the least n
    n_first = Q(n0) if clipped else n_at_vlo.upper()
    logratio = (n_first + 2).log() / vl
    return {"e_a": e_a, "e_b": e_b, "e1": iv(e_a, e_b), "n_lo": n_lo, "n_hi": n_hi, "last": last,
            "iota": iota, "m1": m1, "ne1_lo": ne1_lo, "logratio": logratio, "v1_hi": v1_at_nlo}


def target_err(k: int, sub: dict, lb: dict, Y: arb) -> arb:
    """sup over y in [0, Y] and n of the subinterval of |H_k(y) - F_k(e_1, m_1)|."""
    Dm = (1 + Y).log() / (1 - lb["q"])
    e1, m1 = sub["e1"], sub["m1"]
    eb, mb = e1.upper(), m1.upper()
    Ebig = e1.union(e1 / (1 + eb * Dm))
    Mbig = m1.union(m1 * (-Dm).exp())
    Fe, Fm = F_grad(k, Ebig, Mbig)
    Fabs = F_ball(k, Ebig, Mbig).abs_upper()
    scale_dev = 1 - 1 / ((1 + eb * Dm) * (1 + Y) ** (k - 1))
    rem = Q(k * (k - 1) * 8**k) * lb["lambda"] / (2 * sub["ne1_lo"])
    return (scale_dev * Fabs + Fe.abs_upper() * eb * eb * Dm + Fm.abs_upper() * mb * Dm + rem).upper()


def targets(sub: dict, lb: dict, jmax: int) -> tuple:
    """(T_0, [T_j - T_0 for j <= jmax]): T_j = tau_j/(2 e_1) lies in the hull of H_(j+2)
    over y in [0, (j+2)/n] (Lemma D(ii)); the differences keep the correlation in e."""
    e1, m1 = sub["e1"], sub["m1"]
    err = [target_err(j + 2, sub, lb, (j + 2) * sub["iota"].upper()) for j in range(jmax + 1)]
    T0 = F_ball(2, e1, m1) + iv(-err[0], err[0])
    dif = [arb(0)] + [F_diff(j + 2, 2, e1, m1) + iv(-(err[j] + err[0]), err[j] + err[0])
                      for j in range(1, jmax + 1)]
    return T0, dif


def H_cplx(k: int, sub: dict, lb: dict, zeta: arb) -> acb:
    """Complex ball containing H_k(y) for every |y| <= zeta (<= 1/8)."""
    rv = -(1 - zeta).log() / (1 - lb["q"])
    D = disk(rv)
    e1 = acb(sub["e1"])
    ratio = 1 / (1 + e1 * D)
    e = e1 * ratio
    m = acb(sub["m1"]) * (-D).exp()
    y = disk(zeta)
    rem = Q(k * (k - 1) * 8**k) * lb["lambda"] / (2 * sub["ne1_lo"])
    return ratio * F_ball(k, e, m) * cpow(1 + y, -(k - 1)) + disk(rem)


# ---------------------------------------------------------------------------
# 4. Interval Krawczyk
# ---------------------------------------------------------------------------


def _inv(M):
    n = len(M)
    A = [list(map(float, row)) + [1.0 if i == j else 0.0 for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(A[r][c]))
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        A[c] = [x / piv for x in A[c]]
        for r in range(n):
            if r != c:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]


def _mid(x) -> float:
    return float(x.mid())


def krawczyk(Phi, DPhi, x_guess: list, iters: int = 60):
    """Returns (box, ok): ok means K(B) lies strictly inside B, so B holds exactly one zero."""
    n = len(x_guess)
    x = [float(v) for v in x_guess]
    for _ in range(30):  # float Newton on the parameter midpoints
        F = [_mid(f) for f in Phi([arb(v) for v in x])]
        J = [[_mid(c) for c in row] for row in DPhi([arb(v) for v in x])]
        Y = _inv(J)
        step = [sum(Y[i][k] * F[k] for k in range(n)) for i in range(n)]
        x = [x[i] - step[i] for i in range(n)]
        if max(abs(s) for s in step) < 1e-15:
            break
    xb = [arb(v) for v in x]
    J = [[_mid(c) for c in row] for row in DPhi(xb)]
    Yf = _inv(J)
    Y = [[arb(c) for c in row] for row in Yf]
    Fx = Phi(xb)
    YF = [sum((Y[i][k] * Fx[k] for k in range(n)), arb(0)) for i in range(n)]
    r = [max(4 * up(abs(YF[i])), 1e-14) for i in range(n)]
    for _ in range(iters):
        B = [xb[i] + arb(0, r[i]) for i in range(n)]
        DB = DPhi(B)
        Kb = []
        for i in range(n):
            acc = xb[i] - YF[i]
            for k in range(n):
                Mik = (1 if i == k else 0) - sum((Y[i][l] * DB[l][k] for l in range(n)), arb(0))
                acc += Mik * arb(0, r[k])
            Kb.append(acc)
        dev = [up(abs(Kb[i] - xb[i])) for i in range(n)]
        if all(dev[i] < r[i] for i in range(n)):
            return [Kb[i].intersection(B[i]) for i in range(n)], True
        r = [max(2 * dev[i], 1.5 * r[i]) for i in range(n)]
        if max(r) > 1:
            break
    return None, False


def fprod(j: int, t, iota):
    """prod_{i=1}^{j+1} (1 + i t iota)^-1, decreasing in t >= 0."""
    out = arb(1)
    for i in range(1, j + 2):
        out = out / (1 + i * t * iota)
    return out


def upr(j: int, t, iota):
    """u_j'(t) = (j+1) t^j prod (1 + i t/n)^-1."""
    return (j + 1) * t**j * fprod(j, t, iota)


def psum(j: int, x, y):
    """sum_{i=0}^{j} x^i y^(j-i) = (x^(j+1) - y^(j+1))/(x - y)."""
    return sum((x**i * y ** (j - i) for i in range(j + 1)), arb(0))


# ---------------------------------------------------------------------------
# 5. The five-coefficient chain (Lemma M5, Lemma G, Lemma 9.1-E, Lemma 8.1-E)
# ---------------------------------------------------------------------------


def delta_max(sub: dict, K, chain: int) -> arb:
    """d_max(n_lo)/n_lo (Lemma W(ii)); six: d^6 log^12 3 <= n^4 log^2(n+2)/K'."""
    n = sub["n_lo"]
    L2 = (n + 2).log() ** 2
    if chain == 5:
        return ((n**3 * L2 / Q(K)) ** Q(Fraction(1, 5)) / n).upper()
    return ((n**4 * L2 / (Q(K) * Q(3).log() ** 12)) ** Q(Fraction(1, 6)) / n).upper()


def chain5(sub: dict, lb: dict, K, K6) -> dict:
    out = {"ok": True, "fail": []}

    def need(name, cond):
        if not certainly(cond):
            out["ok"] = False
            out["fail"].append(name)

    need("n_lo >= x0 (Lemma R region)", sub["n_lo"] >= Q(lb["x0"]))
    need("n_lo >= 1000 (Lemma W)", sub["n_lo"] >= 1000)
    T0, dif = targets(sub, lb, 2)
    eps = 2 * sub["e1"] * T0
    t = [dj / T0 for dj in dif]
    iota = sub["iota"]
    wb = 1 / (1 + iota / 2)

    def Phi(X):
        g0, gb, gc = X
        wA, wB, wC = eps * g0, wb - eps * gb, 2 - eps * gc
        res = []
        for j in range(3):
            v = eps**j * g0 ** (j + 1) * iv(fprod(j, wA, iota), 1)
            v += gb * psum(j, wb, wB) * fprod(j, wb, iota).union(fprod(j, wB, iota))
            v -= gc * psum(j, Q(2), wC) * fprod(j, Q(2), iota).union(fprod(j, wC, iota))
            res.append(v - (1 + t[j]))
        return res

    def DPhi(X):
        g0, gb, gc = X
        wA, wB, wC = eps * g0, wb - eps * gb, 2 - eps * gc
        return [[upr(j, wA, iota), upr(j, wB, iota), -upr(j, wC, iota)] for j in range(3)]

    box, ok = krawczyk(Phi, DPhi, [Fraction(5, 12), Fraction(2, 3), Fraction(1, 12)])
    need("Krawczyk M5", ok)
    if not ok:
        return out
    g0, gb, gc = box
    wA, wB, wC = eps * g0, wb - eps * gb, 2 - eps * gc
    Gn = eps * gc / (2 * wC)                     # (C - D)/n, without cancellation
    dl = delta_max(sub, K, 5)
    di = dl + iota                               # (d + 1)/n
    # (77) and the cases of Lemma G
    # eps = 2 e_1 T_0 > 0 for every finite n (e_1 > 0), even where the ball reaches e_1 = 0
    need("A > B > 0, C > D > 0", (T0 > 0) & (g0 > 0) & (gb > 0) & (gc > 0) & (eps * (g0 + gb) < wb) & (wC > 0))
    need("A >= 2B", wB >= 2 * wA)
    need("C < 2D", wC > 1)
    need("(77) A >= B + d", 1 >= wA * (1 / wB + dl))
    need("(77) B >= 32 d", 1 >= 32 * dl * wB)
    # C - D >= d  <=>  T_0 gc/w_C >= (d/n) v_1(2n), and (d_max/n) v_1 decreases (Lemma W(ii))
    need("(77) C >= D + d", T0 * gc / wC >= dl * sub["v1_hi"])
    need("(77) D >= 32 d", Q(Fraction(1, 2)) >= 32 * dl)
    # Lemma G in units of sqrt(Bd), every ratio written without a shared factor twice
    sB = sqrt0(dl * wB)                          # sqrt(d/B)
    h1 = 1 - di * wA                             # H_1/A
    beta1 = (1 + dl * wB).sqrt() / h1            # off-diagonal of q_{A,B} over sqrt(Bd)
    abar1 = sB * (2 + wA / wB) / h1              # diagonal excess (case A >= 2B: a_k >= B)
    rho1 = abar1 + 2 * beta1
    h2 = 1 - di * wC                             # H_2/C
    b2 = 2 * sqrt0(dl * Gn * (dl + Q(Fraction(1, 2))) * wC) / h2 ** Q(Fraction(3, 2))  # b_2/D
    eta_p = dl * wC / h2 + 2 * b2
    eta_m = 4 * dl * abs(1 - wC) / h2 + 2 * b2
    need("eta_- < 1", eta_m < 1)
    # eta/sqrt(d/B) without 0/0: b_2/D carries sqrt(d) and the rest carries d
    sw = wB.sqrt()
    b2s = 2 * sqrt0(Gn * (dl + Q(Fraction(1, 2))) * wC) / (h2 ** Q(Fraction(3, 2)) * sw)
    ep_s = sqrt0(dl) * wC / (h2 * sw) + 2 * b2s
    em_s = 4 * sqrt0(dl) * abs(1 - wC) / (h2 * sw) + 2 * b2s
    left = 2 * beta1 * (1 - eta_m) + em_s       # B - u_- v_-, u_- = B - 2 beta1 sqrt(Bd)
    right = rho1 * (1 + eta_p) + ep_s           # u_+ v_+ - B
    Cloc = left.union(right).upper()
    # Lemma 9.1-E
    K6 = Q(K6)
    rn = K6 * sqrt0(dl / wB)
    yB = 1 + Cloc * sB
    yA = yB * wA / wB
    yD = yB * 2 / wB
    rD = 2 * rn
    need("y_+ < A", yA < 1)
    need("r < D", rD < 1)
    # c_V with d >= 1: (2d+3)/A <= 5 d/A, (d+1)/r <= 2 d/r, 5d^2+4d+1 <= 10 d^2
    cV = 1 + rn * wA + 5 * dl * wA + 2 * sB / K6 + 10 * dl * sB * wA / K6 + dl * wB / (4 * K6**2) \
        + dl**2 * wA * wB / (4 * K6**2)
    eps_p = eps * gc / 2
    a_ = (Cloc + sB * (1 + yA)) / ((1 - yA) * K6)
    b_ = (1 + dl * wA) * yB / ((1 - yA) * K6**2)
    th = yD * eps_p * cV / ((1 - yA) * (1 - rD))
    abt = (a_ + b_ + th).upper()
    need("a + b + theta < 1", abt < 1)
    # Lemma 8.1-E
    zeta = (dl + 2 * K6 * sqrt0(dl / wB)).upper()
    need("zeta <= 1/8", zeta <= Q(Fraction(1, 8)))
    y = disk(zeta)
    H5 = H_cplx(5, sub, lb, zeta)

    def om_avg(I):
        tt = acb(I)
        return 4 * tt**3 * cpow(1 + tt * y, -5)

    term = -H5 / T0 + g0 * wA**3 * cpow(1 + wA * y, -4) + gb * om_avg(wB.union(wb)) - gc * om_avg(wC.union(Q(2)))
    # 4/(n eps) = 2/(n e_1 T_0) <= 2/(ne1_lo T_0)
    rem = 2 / (sub["ne1_lo"] * T0) * sum((w**5 / (1 - zeta * w) ** 5 for w in (wA, wB, wb, wC, Q(2))), arb(0))
    Theta5 = (term.abs_upper() + rem).upper()
    CE = (T0 * Theta5 * (dl.sqrt() + 2 * K6 / wB.sqrt()) ** 5 / 10).upper()
    Kreq = ((CE * sub["logratio"] / Q(17).log()) ** 2).upper()
    out.update({"T0": T0, "eps": eps, "t": t, "box": box, "delta": dl, "C_loc": Cloc, "abt": abt,
                "a": a_.upper(), "b": b_.upper(), "theta": th.upper(), "zeta": zeta,
                "Theta5": Theta5, "C_E": CE, "K_req": Kreq, "logratio": sub["logratio"]})
    return out


# ---------------------------------------------------------------------------
# 6. The six-coefficient chain (Lemma M6, Lemmas A to C with R2, the sixth residual)
# ---------------------------------------------------------------------------

C_HARM = Fraction(59821, 10000)  # 4 + 3 H_d <= 3 log(d+2) + 5.9821 for d >= 1 (review, R10)


def dd_omega(p: int, w1, w2, y):
    """The average of d/dw [w^p/(1 + w y)^p] over [w1, w2], exactly:
    (u2^p - u1^p)/(w2 - w1) with u = w/(1 + w y), u2 - u1 = (w2 - w1)/((1 + w1 y)(1 + w2 y))."""
    u1 = w1 / (1 + w1 * y)
    u2 = w2 / (1 + w2 * y)
    s_ = sum((u2**i * u1 ** (p - 1 - i) for i in range(p)), acb(0))
    return s_ / ((1 + w1 * y) * (1 + w2 * y))


def chain6(sub: dict, lb: dict, K, d_min, d_cut=None) -> dict:
    """d_min: least degree the residual step handles; d_cut: if set, the chain is needed
    only for d > d_cut (GORTTW Cor. 1.3 below), which bounds log(d+2) from below."""
    out = {"ok": True, "fail": []}

    def need(name, cond):
        if not certainly(cond):
            out["ok"] = False
            out["fail"].append(name)

    need("n_lo >= x0 (Lemma R region)", sub["n_lo"] >= Q(lb["x0"]))
    need("n_lo >= 1000 (Lemma W)", sub["n_lo"] >= 1000)
    T0, dif = targets(sub, lb, 3)
    eps = 2 * sub["e1"] * T0
    t = [dj / T0 for dj in dif]
    iota = sub["iota"]
    wb = 1 / (1 + iota / 2)
    beta_b = iv(0, (1 / (4 * sub["ne1_lo"] * T0)).upper())  # (1 - w_b)/eps

    def ws(X):
        g0, gx, g1, x = X
        return eps * g0, x - eps * gx / 2, x + eps * gx / 2, 1 - eps * g1

    def Phi(X):
        g0, gx, g1, x = X
        wA, wB, wC, wD = ws(X)
        res = []
        for j in range(4):
            v = eps**j * g0 ** (j + 1) * iv(fprod(j, wA, iota), 1)
            v += gx * psum(j, wC, wB) * fprod(j, wC, iota).union(fprod(j, wB, iota))
            v += (g1 - beta_b) * psum(j, wb, wD) * fprod(j, wb, iota).union(fprod(j, wD, iota))
            res.append(v - (1 + t[j]))
        return res

    def DPhi(X):
        g0, gx, g1, x = X
        wA, wB, wC, wD = ws(X)
        rows = []
        for j in range(4):
            dx = (j + 1) * gx * (psum(j - 1, wC, wB) * fprod(j, wC, iota) if j >= 1 else arb(0))
            dx += (j + 1) * gx * wB**j * iv(-Q((j + 1) * (j + 2)) / 2 * iota.upper(), 0)
            rows.append([upr(j, wA, iota), (upr(j, wB, iota) + upr(j, wC, iota)) / 2, upr(j, wD, iota), dx])
        return rows

    box, ok = krawczyk(Phi, DPhi, [Fraction(1, 6), Fraction(2, 3), Fraction(1, 6), Fraction(1, 2)])
    need("Krawczyk M6", ok)
    if not ok:
        return out
    g0, gx, g1, x = box
    wA, wB, wC, wD = ws(box)
    log3 = Q(3).log()
    Lmin = log3 if d_cut is None else (Q(d_cut) + 2).log()   # log(d+2) >= Lmin on the range
    n = sub["n_lo"]
    dl = (((n**4 * (n + 2).log() ** 2 / (Q(K) * Lmin**12)) ** Q(Fraction(1, 6))) / n).upper()
    need("0 < w_A < w_B < w_C < w_D < 1", (T0 > 0) & (g0 > 0) & (gx > 0) & (g1 > 0)
         & (x - eps * (g0 + gx / 2) > 0) & (1 - x - eps * (g1 + gx / 2) > 0))
    need("Lemma B: A >= 8B", wB >= 8 * wA)
    need("Lemma B: B >= 256 d", 1 >= 256 * dl * wB)
    need("R2: C >= D + d", wD - wC >= dl * wC * wD)
    need("R2: D >= 32 d", 1 >= 32 * dl * wD)
    need("R2: D > 64 d", 64 * dl * wD < 1)
    eta = 8 * sqrt0(dl * wD)
    cH = 3 + Q(C_HARM) / (Q(d_min) + 2).log()
    rho_r = Q(9) / (2 * arb.pi()) * (1 + eta) / (1 - eta) * cH
    bracket = (sqrt0(dl) / (Q(d_min) + 2).log()
               + 2 * rho_r * (Q(Fraction(247, 100)) + Q(Fraction(607, 100)) / Q(d_min)).sqrt() / wB.sqrt()).upper()
    dmax_lo = (dl * n).upper()
    if sub["last"]:
        need("d_max(n_lo) > 150 (Lemma W(iii))", dmax_lo > 150)
        Lmax = (dmax_lo + 2).log()
    else:
        nh = sub["n_hi"]
        dmax_hi = ((nh**4 * (nh + 2).log() ** 2 / (Q(K) * Lmin**12)) ** Q(Fraction(1, 6))).upper()
        Lmax = (dmax_hi + 2).log()
    zeta = (sqrt0(dl) * Lmax * bracket).upper()
    need("zeta <= 1/8", zeta <= Q(Fraction(1, 8)))
    y = disk(zeta)
    H6 = H_cplx(6, sub, lb, zeta)
    ya = acb(wA)
    model = g0 * wA**4 * cpow(1 + ya * y, -5) + gx * dd_omega(5, acb(wB), acb(wC), y) \
        + (g1 - beta_b) * dd_omega(5, acb(wD), acb(wb), y)
    term = H6 / T0 - model
    # 5/(n eps) = 5/(2 n e_1 T_0)
    rem = 5 / (2 * sub["ne1_lo"] * T0) * sum((w**6 / (1 - zeta * w) ** 6 for w in (wA, wB, wC, wD, wb)), arb(0))
    Theta6 = (term.abs_upper() + rem).upper()
    CE = (T0 * Theta6 * bracket**6 / 15).upper()
    Kreq = ((CE * sub["logratio"] / Q(33).log()) ** 2).upper()
    out.update({"T0": T0, "eps": eps, "t": t, "box": box, "delta": dl, "bracket": bracket, "zeta": zeta,
                "Theta6": Theta6, "C_E": CE, "K_req": Kreq, "logratio": sub["logratio"]})
    return out


# ---------------------------------------------------------------------------
# 7. Covers, thresholds and the four variants
# ---------------------------------------------------------------------------

VARIANTS = {
    # name: chain, n0 (the chain covers n >= n0), claimed constant, K_6, step in e_1, GORTTW cut
    "5a": {"chain": 5, "n0": Fraction("9.9e33"), "K": Fraction(17900), "K6": Fraction("2.53"),
           "step": Fraction(1, 10**4), "gorttw": True},
    "5s": {"chain": 5, "n0": Fraction(789702), "K": Fraction("9.10e19"), "K6": Fraction("2.82"),
           "step": Fraction(1, 10**4), "gorttw": False},
    "6a": {"chain": 6, "n0": Fraction("5.6e35"), "K": Fraction("7.21e9"),
           "step": Fraction(1, 10**4), "gorttw": True},
    "6s": {"chain": 6, "n0": Fraction(14237025), "K": Fraction("3.61e30"),
           "step": Fraction(1, 10**4), "gorttw": False},
}


def cover(n0: Fraction, step: Fraction) -> list:
    """Subintervals [e_a, e_b] covering e_1 in [0, e_1(n0)]: the top one reaches above e_1(n0)
    (n is clipped to n >= n0 there), the last one contains e_1 = 0 (n = infinity)."""
    vl, _ = v1_bounds(2 * n0)
    e_top = Fraction(1) / Fraction(vl)  # >= e_1(n0)
    edges = [Fraction(0)]
    while edges[-1] + step < e_top:
        edges.append(edges[-1] + step)
    edges.append(e_top)
    return list(zip(edges[:-1], edges[1:]))


def gorttw_threshold_ok(chain: int, K, n0) -> bool:
    """Every (d, n) in the wedge with d > 9.36e20 has n >= n0: n0's wedge value is below
    the wedge value at d = 9.36e20 (both sides increase)."""
    n, D = Q(n0), Q(D_GORTTW)
    if chain == 5:
        return certainly(n**3 * (n + 2).log() ** 2 < Q(K) * D**5)
    return certainly(n**4 * (n + 2).log() ** 2 < Q(K) * D**6 * (D + 2).log() ** 12)


def absorption(chain: int, n0) -> arb:
    """The wedge is empty for n < n0 and every d >= 1 once K is at least this."""
    n = Q(n0)
    if chain == 5:
        return (n**3 * (n + 2).log() ** 2).upper()
    return (n**4 * (n + 2).log() ** 2 / Q(3).log() ** 12).upper()


def run_variant(name: str, K=None, K6=None, step=None, n0=None, log=None) -> dict:
    spec = dict(VARIANTS[name])
    K = Fraction(K if K is not None else spec["K"])
    K6 = Fraction(K6 if K6 is not None else spec.get("K6", 0))
    step = Fraction(step if step is not None else spec["step"])
    n0 = Fraction(n0 if n0 is not None else spec["n0"])
    t0 = time.time()
    with prec():
        lb = laplace(n0)
        rows, fails = [], []
        agg: dict = {}
        todo = [(ea, eb, 0) for (ea, eb) in cover(n0, step)]
        while todo:
            ea, eb, depth = todo.pop()
            sub = make_sub(ea, eb, n0)
            if spec["chain"] == 5:
                r = chain5(sub, lb, K, K6)
                keys = ("K_req", "C_loc", "abt", "Theta5", "C_E", "logratio")
            else:
                r = chain6(sub, lb, K, 6 if not spec["gorttw"] else D_GORTTW + 1,
                           d_cut=D_GORTTW if spec["gorttw"] else None)
                keys = ("K_req", "Theta6", "bracket", "C_E", "logratio", "zeta")
            if not r["ok"]:
                # a failed Krawczyk test is retried on the two halves (at most 3 times);
                # every other failed condition is final
                if depth < 3 and all(f.startswith("Krawczyk") for f in r["fail"]):
                    mid = (ea + eb) / 2
                    todo += [(ea, mid, depth + 1), (mid, eb, depth + 1)]
                    continue
                fails.append((float(ea), float(eb), r["fail"]))
                continue
            for k_ in keys:
                v = up(r[k_])
                agg[k_] = max(agg.get(k_, 0.0), v)
            rows.append((float(ea), float(eb), up(r["K_req"])))
        res = {"name": name, "K": K, "K6": K6, "n0": n0, "subintervals": len(rows) + len(fails),
               "fails": fails, "agg": agg, "laplace": {k: up(lb[k]) for k in ("R_min", "b", "q", "C_rho", "lambda")},
               "laplace_conds": lb["conds"], "seconds": time.time() - t0}
        res["K >= max K_req"] = (not fails) and agg.get("K_req", math.inf) <= float(K)
        if spec["gorttw"]:
            res["threshold"] = gorttw_threshold_ok(spec["chain"], K, n0)
        else:
            res["threshold"] = certainly(Q(K) >= absorption(spec["chain"], n0))
            res["absorption"] = up(absorption(spec["chain"], n0))
        res["green"] = bool(res["K >= max K_req"] and res["threshold"] and all(lb["conds"].values()))
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", default=None)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", default=str(HERE / "results_review_p2.json"))
    args = ap.parse_args()
    names = [args.variant] if args.variant else list(VARIANTS)
    out = {}
    for nm in names:
        step = Fraction(1, 10**3) if args.quick else None
        r = run_variant(nm, step=step)
        out[nm] = {k: (str(v) if isinstance(v, Fraction) else v) for k, v in r.items()}
        print(nm, "green" if r["green"] else "RED", r["agg"], "fails:", r["fails"][:3], f"{r['seconds']:.0f}s", flush=True)
    if not args.quick:
        Path(args.out).write_text(json.dumps(out, indent=1, default=str))


if __name__ == "__main__":
    main()
