"""Hunt #135: the two open inputs H1 and H3 of the conditional six-coefficient wedge.

Run from the repository root:

    .venv/bin/python hunts/jensen_wedge/probe_h1_h3.py --time-unit   # time one unit first
    .venv/bin/python hunts/jensen_wedge/probe_h1_h3.py               # writes results_h1_h3.json

`H1_H3.md` is the derivation; this probe supplies its exact constants and measures
the inputs the derivation does not prove. It reuses phases 0 and 1 (`probe.py`,
`probe_phase1.py`) unchanged and adds four things.

(a) The model side of the matching system in scaled variables, exactly. With
    eps := tau_0 (the first target, below) and X = (g0, gx, g1, x), the
    four-parameter system with D free reads Phi_n(X) = 0, where
    w_A = eps g0, w_B = x - eps gx/2, w_C = x + eps gx/2, w_D = 1 - eps g1 and
    w_P = n/P. Its limit Phi_inf vanishes at Simpson's rule X* = (1/6, 2/3, 1/6,
    1/2). Every constant of the contraction (the Jacobian, its inverse, the
    nonlinearity of Phi_inf on a weighted box, the eps-polynomial part and the
    explicit 1/n parts) is computed here in exact rational arithmetic, from the
    closed form u_j'(t) = (j+1) t^j / prod_{i=1}^{j+1} (1 + i t/n).

(b) The target vector tau_j = (-1)^j n^(j+1)/j! Delta^(j+2) h(n), j = 0..4, from
    the exact gamma table (route A, n = 50..3200) and the saddle (route B, to
    n = 1e20). It is the only input of H1 that depends on xi, and the only one
    whose asymptotics come from Holland's saddle estimate. tau_4 is the sixth
    difference, the real-axis form of H3.

(c) The contraction inequality evaluated on the measured targets at every n,
    and the measured Pade configuration (phase 1's solve) placed against the
    radius it predicts.

(d) Holland's main saddle term G_0(N) and its derivatives to order 6 on the real
    axis and on complex rays, against the asymptotic (-1)^k (k-2)!/(N^(k-1) L_N)
    and its first-order correction (H_(k-2) - 1)/L_N derived in H1_H3.md.

Grade: measured, except the rational constants, which are exact. Nothing here
bears on RH.
"""

from __future__ import annotations

import argparse
import functools
import json
import platform
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

import mpmath
import sympy as sp
from mpmath import mp, mpf

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from hunts.jensen_wedge import probe as p0  # noqa: E402
from hunts.jensen_wedge import probe_phase1 as p1  # noqa: E402

SUBGRID = p0.SUBGRID
LARGE_NS = ("1e4", "1e5", "1e6", "1e7", "1e8", "1e10", "1e12", "1e16", "1e20")
J_TOP = 6  # log R_0..R_6: tau_0..tau_4
K_LO, K_HI = p0.N_LO - 1, p0.N_HI + J_TOP
#: Simpson's rule in the scaled coordinates (g0, gx, g1, x)
X_STAR = (Fr(1, 6), Fr(2, 3), Fr(1, 6), Fr(1, 2))
#: the weighted box of the contraction: |X_i - X*_i| <= R_BOX * WEIGHTS[i]
WEIGHTS = (Fr(3, 4), Fr(1), Fr(3, 2), Fr(3, 4))
R_BOX = Fr(2, 25)
#: first-order prediction of (X_n - X*) L, H1_H3.md section 4.4
FIRST_ORDER_DX = (Fr(-2, 9), Fr(-2, 9), Fr(4, 9), Fr(1, 4))
G0_REAL_NS = ("1e3", "1e5", "1e8", "1e12", "1e16", "1e20", "1e30", "1e50")
G0_ANGLES = ("0", "0.25", "0.5")


def s(x, digits: int = 15) -> str:
    return mpmath.nstr(x, digits)


# ---------------------------------------------------------------------------
# (a) the model side, exactly
# ---------------------------------------------------------------------------

_g0, _gx, _g1, _x, _eps = sp.symbols("g0 gx g1 x eps")
_X = (_g0, _gx, _g1, _x)
_D = sp.symbols("d0 d1 d2 d3")


def _P(j: int):
    """P_j(X; eps) = (j+1)/eps * (the leading part of the gap integral), j = 0..3."""
    e, g0, gx, g1, x = _eps, _g0, _gx, _g1, _x
    return sp.expand(((e * g0) ** (j + 1) + (x + e * gx / 2) ** (j + 1)
                      - (x - e * gx / 2) ** (j + 1) + 1 - (1 - e * g1) ** (j + 1)) / e)


def _build():
    star = dict(zip(_X, (sp.Rational(v.numerator, v.denominator) for v in X_STAR)))
    shift = {_X[i]: star[_X[i]] + _D[i] for i in range(4)}
    P = [_P(j) for j in range(4)]
    phi_inf = [sp.expand(1 - p.subs(_eps, 0)) for p in P]
    DPhi = sp.Matrix([[sp.diff(phi_inf[j], v) for v in _X] for j in range(4)])
    J = DPhi.subs(star)
    Ji = J.inv()
    M = (sp.eye(4) - Ji * DPhi).subs(shift).applyfunc(sp.expand)
    eS = sp.Matrix([sp.expand(p - p.subs(_eps, 0)) for p in P])  # eps * S_j
    JieS = Ji * eS
    DJieS = JieS.jacobian(_X).subs(shift).applyfunc(sp.expand)
    JieS_star = JieS.subs(star).applyfunc(sp.expand)
    return {"phi_inf": phi_inf, "J": J, "Ji": Ji, "M": M, "eS": eS,
            "DJieS": DJieS, "JieS_star": JieS_star}


MODEL = _build()


def to_fr(v) -> Fr:
    v = sp.Rational(v)
    return Fr(int(v.p), int(v.q))


def J_exact() -> list:
    return [[to_fr(MODEL["J"][i, k]) for k in range(4)] for i in range(4)]


def J_inv_exact() -> list:
    return [[to_fr(MODEL["Ji"][i, k]) for k in range(4)] for i in range(4)]


def monomial_bound(poly, rho, eps=None) -> Fr:
    """sup |poly| over |d_i| <= rho_i (and 0 <= eps' <= eps), by the triangle
    inequality on monomials: sum |c_a| rho^a eps^b. Rigorous, and tight up to the
    signs it gives away."""
    poly = sp.expand(poly)
    if poly == 0:
        return Fr(0)
    tot = Fr(0)
    for mon, c in sp.Poly(poly, *_D, _eps).terms():
        v = abs(to_fr(c))
        for i in range(4):
            v *= rho[i] ** mon[i]
        if mon[4]:
            v *= eps ** mon[4]
        tot += v
    return tot


def weighted_row_sums(mat, rho, w, eps=None) -> list:
    return [sum(monomial_bound(mat[i, k], rho, eps) * w[k] for k in range(4)) / w[i]
            for i in range(4)]


@functools.lru_cache(maxsize=None)
def kappa_bar(r=R_BOX, w=WEIGHTS) -> Fr:
    """sup over the box of ||I - J^-1 DPhi_inf(X)||_w."""
    rho = [r * wi for wi in w]
    return max(weighted_row_sums(MODEL["M"], rho, w))


@functools.lru_cache(maxsize=None)
def sigma_bar(eps: Fr, r=R_BOX, w=WEIGHTS) -> Fr:
    """sup over the box and 0 <= eps' <= eps of ||J^-1 D_X(eps S)(X; eps')||_w."""
    rho = [r * wi for wi in w]
    return max(weighted_row_sums(MODEL["DJieS"], rho, w, eps))


@functools.lru_cache(maxsize=None)
def nu_w(w=WEIGHTS) -> Fr:
    """max_i sum_k |J^-1_ik| / w_i: J^-1 from the max norm into the w-norm."""
    Ji = J_inv_exact()
    return max(sum(abs(Ji[i][k]) for k in range(4)) / w[i] for i in range(4))


def JieS_star(eps: Fr) -> list:
    """J^-1 (eps S)(X*; eps), exact in eps."""
    e = sp.Rational(eps.numerator, eps.denominator)
    return [to_fr(MODEL["JieS_star"][i].subs(_eps, e)) for i in range(4)]


def fr_mpf(v: Fr):
    return mpf(v.numerator) / v.denominator


def box_is_admissible(eps: Fr, r=R_BOX, w=WEIGHTS) -> bool:
    """Every X in the box gives 0 < w_A < w_B < w_C < w_D < 1: both factors are
    in the positive-root class (A > B > 0, C > D > 0)."""
    lo = [X_STAR[i] - r * w[i] for i in range(4)]
    hi = [X_STAR[i] + r * w[i] for i in range(4)]
    return (lo[0] > 0 and lo[1] > 0 and lo[2] > 0
            and eps * (hi[0] + hi[1] / 2) < lo[3]
            and hi[3] + eps * (hi[1] / 2 + hi[2]) < 1)


def rho_hat(j: int, t, n):
    """u_j'(t) / ((j+1) t^j) - 1 = prod_{i=1}^{j+1} (1 + i t/n)^-1 - 1, exactly."""
    v = mpf(1)
    for i in range(1, j + 2):
        v /= 1 + i * mpf(t) / n
    return v - 1


def lam(j: int, p, n):
    """lambda_j(p) = (-1)^j n^(j+1)/j! Delta^(j+1) log(p): the model side of the
    j-th differenced equation, exactly (H1_H3.md section 4.1)."""
    d = mp.fsum((-1) ** (j + 1 - i) * mp.binomial(j + 1, i) * mp.log(p + i) for i in range(j + 2))
    return (-1) ** j * mpf(n) ** (j + 1) / mp.factorial(j) * d


def lam_from_integral(j: int, w, n):
    """lambda_j(n/w) = int_0^w u_j'(t) dt, the same quantity through the closed form."""
    return mp.quad(lambda t: (j + 1) * t ** j * (1 + rho_hat(j, t, n)), [0, w])


def explicit_small_terms(n, eps, r=R_BOX, w=WEIGHTS) -> dict:
    """Bounds on beta (the shift of w_b = n/b below 1) and rho (the 1/n part of
    u_j'), both explicit (H1_H3.md section 4.2). Floats are fine: they enter
    only through bounds that are several decades below the margin."""
    n, eps = mpf(n), mpf(eps)
    gsum = fr_mpf(1 + r * (w[0] + w[1] + w[2]))
    g0max = fr_mpf(X_STAR[0] + r * w[0])
    wf = [fr_mpf(v) for v in w]
    beta = [(j + 1) / ((2 * n + 1) * eps) for j in range(4)]
    rho0 = [mpf((j + 1) ** 2 * (j + 2)) / (2 * n) * (gsum + 1 / ((2 * n + 1) * eps))
            for j in range(4)]
    rho1 = max(mpf((j + 1) ** 2 * (j + 2)) / (2 * n)
               * (wf[0] * (eps * g0max) ** (j + 1) + wf[1] + wf[2] + 2 * wf[3] / eps)
               for j in range(4))
    return {"beta": beta, "rho0": rho0, "rho1_rowsum": rho1}


def contraction(n, tau: list, r=R_BOX, w=WEIGHTS) -> dict:
    """The explicit contraction inequality of H1_H3.md section 4.3 at one n,
    from the data tau_0..tau_3 alone."""
    eps = tau[0]
    t = [tau[j] / eps - 1 for j in range(4)]
    eps_fr = Fr(mpmath.nstr(eps, 30)) * Fr(1000001, 1000000)  # a rational upper bound
    kap = kappa_bar(r, w)
    sig = sigma_bar(eps_fr, r, w)
    nu = nu_w(w)
    small = explicit_small_terms(n, eps, r, w)
    q = fr_mpf(kap) + fr_mpf(sig) + fr_mpf(nu) * small["rho1_rowsum"]
    Ji = J_inv_exact()
    jes = JieS_star(Fr(mpmath.nstr(eps, 40)))
    lead = [mp.fsum(fr_mpf(Ji[i][k]) * t[k] for k in range(4)) - fr_mpf(jes[i]) for i in range(4)]
    d0_lead = max(abs(lead[i]) / fr_mpf(w[i]) for i in range(4))
    d0 = d0_lead + fr_mpf(nu) * max(small["beta"][j] + small["rho0"][j] for j in range(4))
    rhs = (1 - q) * fr_mpf(r)
    closes = bool(q < 1 and d0 <= rhs and box_is_admissible(eps_fr, r, w))
    return {"eps": eps, "t": t, "kappa_bar": kap, "sigma_bar": sig, "nu_w": nu,
            "rho1_rowsum": small["rho1_rowsum"], "q": q, "d0_lead": d0_lead, "d0": d0,
            "rhs": rhs, "closes": closes, "radius": d0 / (1 - q) if q < 1 else None,
            "admissible": box_is_admissible(eps_fr, r, w)}


# ---------------------------------------------------------------------------
# (b) the target vector and the scaled configuration
# ---------------------------------------------------------------------------


def targets(lr: list, n) -> list:
    """tau_j = (-1)^j n^(j+1)/j! Delta^j delta(0), delta_k = ell(b+k) - log q_k
    = Delta^2 h(n+k), from log R_0..log R_(j+2)."""
    lq = p0.log_q_from_log_R(lr)
    b = mpf(n) + mpf(1) / 2
    dl = [mp.log1p(1 / (b + k)) - lq[k] for k in range(len(lq))]
    out = []
    for j in range(len(dl)):
        dj = mp.fsum((-1) ** (j - i) * mp.binomial(j, i) * dl[i] for i in range(j + 1))
        out.append((-1) ** j * mpf(n) ** (j + 1) / mp.factorial(j) * dj)
    return out


def scaled_config(n, eps, A, B, C, D) -> list:
    n = mpf(n)
    wA, wB, wC, wD = n / A, n / B, n / C, n / D
    return [wA / eps, (wC - wB) / eps, (1 - wD) / eps, (wB + wC) / 2]


def phi_exact(X: list, n, tau: list) -> list:
    """Phi_n(X) of H1_H3.md (4.2): [lambda_j(B) + lambda_j(D) - lambda_j(A)
    - lambda_j(C) - lambda_j(b) + tau_j] / eps, j = 0..3."""
    n, eps = mpf(n), tau[0]
    g0, gx, g1, x = X
    A, B = n / (eps * g0), n / (x - eps * gx / 2)
    C, D = n / (x + eps * gx / 2), n / (1 - eps * g1)
    b = n + mpf(1) / 2
    return [(lam(j, B, n) + lam(j, D, n) - lam(j, A, n) - lam(j, C, n) - lam(j, b, n) + tau[j]) / eps
            for j in range(4)]


def first_order_parameters(Ln) -> dict:
    """The parameter limits H1's first-order term predicts (H1_H3.md section 4.4)."""
    L = mpf(Ln)
    return {"A_over_nL": 3 + 7 / L, "D_minus_n_L_over_n": mpf(1) / 3 + mpf(2) / (3 * L),
            "B_minus_2n_L_over_n": mpf(5) / 3, "C_minus_2n_L_over_n": mpf(-11) / 3,
            "B_minus_C_L_over_n": mpf(16) / 3 - mpf(112) / (9 * L)}


def row(n, lr: list, Ln, guess=None) -> dict:
    """Everything H1 and H3 measure at one n, from log R_0..R_6."""
    n_ = mpf(n)
    tau = targets(lr, n_)
    lq = p0.log_q_from_log_R(lr)
    sol = p1.pade_solve(lq, n_, guess if guess is not None else p1.pade_guess(n_, Ln))
    X = scaled_config(n_, tau[0], sol["A"], sol["B"], sol["C"], sol["D"])
    dX = [X[i] - fr_mpf(X_STAR[i]) for i in range(4)]
    dX_w = max(abs(dX[i]) / fr_mpf(WEIGHTS[i]) for i in range(4))
    c = contraction(n_, tau)
    res = phi_exact(X, n_, tau)
    fo = first_order_parameters(Ln)
    out = {
        "n": n if isinstance(n, int) else str(n), "L_n": s(Ln, 12),
        "tau": [s(v, 15) for v in tau],
        "tau0_L_over_2": s(tau[0] * Ln / 2, 12),
        "tau_over_2_over_L_minus_1_times_L": [s((v * Ln / 2 - 1) * Ln, 8) for v in tau],
        "t_times_L": [s(c["t"][j] * Ln, 8) for j in range(1, 4)],
        "X": [s(v, 12) for v in X], "dX_times_L": [s(v * Ln, 8) for v in dX],
        "dX_w_norm": s(dX_w, 8),
        "phi_exact_residual_at_X": s(max(abs(v) for v in res), 3),
        "pade_match_residual": s(sol["res"], 3),
        "contraction": {
            "kappa_bar": str(c["kappa_bar"]), "sigma_bar": s(fr_mpf(c["sigma_bar"]), 10),
            "rho1_rowsum": s(c["rho1_rowsum"], 4), "q": s(c["q"], 10),
            "d0_lead": s(c["d0_lead"], 10), "d0": s(c["d0"], 10), "rhs": s(c["rhs"], 10),
            "admissible": c["admissible"], "closes": c["closes"],
            "radius": None if c["radius"] is None else s(c["radius"], 10),
            "measured_X_within_radius": (bool(dX_w <= c["radius"]) if c["closes"] else None),
        },
        "params": {"A_over_nL": s(sol["A"] / (n_ * Ln), 10),
                   "D_minus_n_L_over_n": s((sol["D"] - n_) * Ln / n_, 10),
                   "B_minus_2n_L_over_n": s((sol["B"] - 2 * n_) * Ln / n_, 10),
                   "C_minus_2n_L_over_n": s((sol["C"] - 2 * n_) * Ln / n_, 10),
                   "B_minus_C_L_over_n": s((sol["B"] - sol["C"]) * Ln / n_, 10)},
        "first_order": {k: s(v, 10) for k, v in fo.items()},
        "all_positive_and_U_gt_V": bool(sol["A"] > sol["B"] > 0 and sol["C"] > sol["D"] > 0),
    }
    sol["tau"] = tau
    return out, sol


# ---------------------------------------------------------------------------
# (d) Holland's main saddle term G_0 on the real axis and on complex rays
# ---------------------------------------------------------------------------


def _L_eq(N):
    """log L + log(pi e^L + 3/4) - log N: Holland (16) in a form whose residual is
    relative, so Newton converges at any size of N; principal logs are on the
    right branch for |arg N| < pi/2, where arg L and arg(pi e^L + 3/4) stay small."""
    lN = mp.log(N)
    return lambda y: mp.log(y) + mp.log(mp.pi * mp.exp(y) + mpf(3) / 4) - lN


def L_branch(N):
    """L_N with N = L (pi e^L + 3/4), Holland (16), continued from the real axis:
    Newton from the real solution at |N|, then along the arc in 16 steps."""
    r = abs(N)
    g = mp.log(r / mp.pi)
    L = mp.findroot(_L_eq(r), g - mp.log(g))
    phi = mp.arg(N)
    if phi == 0:
        return L
    for k in range(1, 17):
        L = mp.findroot(_L_eq(r * mp.expj(phi * k / 16)), L)
    return L


def G0(N, L=None):
    """Holland (17): G_0(N) = (N+1) log L + L/4 - N/L - (1/2) log Q,
    Q = (1 + L) N - (3/4) L^2, L = L_N on the branch above."""
    if L is None:
        L = L_branch(N)
    Q = (1 + L) * N - mpf(3) / 4 * L ** 2
    return (N + 1) * mp.log(L) + L / 4 - N / L - mp.log(Q) / 2


def G0_function(N0):
    """G_0 near N0 as an analytic function, its branch L found by Newton from L(N0)."""
    L0 = L_branch(N0)

    def f(N):
        return G0(N, mp.findroot(_L_eq(N), L0))
    return f, L0


def G0_derivatives(N0, kmax: int = 6) -> tuple:
    """[G_0^(k)(N0) for k = 0..kmax], by Cauchy's integral on |N - N0| = |N0|/8
    with 64 nodes (exact to rounding for a polynomial of degree < 64; the
    Taylor tail at radius |N0|/8 decays like 8^-64 relative to the disk scale)."""
    f, L0 = G0_function(N0)
    rad = abs(N0) / 8
    m = 64
    vals = [f(N0 + rad * mp.expjpi(2 * mpf(i) / m)) for i in range(m)]
    out = []
    for k in range(kmax + 1):
        ck = mp.fsum(vals[i] * mp.expjpi(-2 * mpf(i * k) / m) for i in range(m)) / m
        out.append(ck * mp.factorial(k) / rad ** k)
    return out, L0


def g0_row(N_abs, angle) -> dict:
    N0 = mpf(N_abs) * mp.expj(mpf(angle))
    if mpf(angle) == 0:
        N0 = mpf(N_abs)
    der, L0 = G0_derivatives(N0)
    rec = {"N_abs": str(N_abs), "angle": str(angle), "L_N": s(L0, 12)}
    ratios, firsts = {}, {}
    for k in range(2, 7):
        lead = (-1) ** k * mp.factorial(k - 2) / (N0 ** (k - 1) * L0)
        rk = der[k] / lead
        ratios[str(k)] = s(abs(rk) if mpf(angle) else mp.re(rk), 12)
        if mpf(angle) == 0:
            firsts[str(k)] = s((mp.re(rk) - 1) * L0.real, 8)
    rec["ratio_to_leading"] = ratios
    if firsts:
        rec["ratio_minus_1_times_L"] = firsts
        rec["predicted_first_order"] = {str(k): s(mp.harmonic(k - 2) - 1, 8) for k in range(2, 7)}
    # Holland's identity G_0'(N) = log L + (1 + L)/Q - Q'/(2Q), Q' = (1 + L) + (N - 3L/2) L/Q
    L = L0
    Q = (1 + L) * N0 - mpf(3) / 4 * L ** 2
    Qp = (1 + L) + (N0 - 3 * L / 2) * L / Q
    rec["G0_prime_identity_defect"] = s(abs(der[1] - (mp.log(L) + (1 + L) / Q - Qp / (2 * Q))), 3)
    rec["Q_over_NL_minus_1_times_L"] = s(abs((Q / (N0 * L) - 1) * L), 8)
    return rec


# ---------------------------------------------------------------------------
# (e) h itself on a complex circle: Holland's Proposition 4.1 at one n, measured
# ---------------------------------------------------------------------------


def log_I_complex(ys: list, dps: int, rho: int = 16, unwrap: bool = False) -> tuple:
    """log I(y), I(y) = int_0^inf u^(2y) e^(u/4) omega(e^u) du (Holland's F(2y)), at
    complex y, by the trapezoid rule on one grid spanning the windows of Re y
    (|u^(2y)| = u^(2 Re y) on the real axis, so the real windows apply). The
    phase 2y log u_c is factored out before the logarithm, u_c the saddle of the
    middle index, so that log stays on one branch; the caller checks it. Returns
    the values and max |coarse/fine - 1| (step 2h against h). With unwrap, ys is
    a closed path starting on the real axis and each imaginary part is moved by
    a multiple of 2 pi to within pi of its predecessor; the number of moves is
    returned too."""
    with mp.workdps(dps + p0.GUARD):
        re = [mp.re(y) for y in ys]
        k0, k1 = int(mp.floor(min(re))) - 1, int(mp.ceil(max(re))) + 1
        decades = dps + p0.GUARD + 10
        lo, hi = p0.window(k0, decades)[0], p0.window(k1, decades)[1]
        _, sigma = p0._peak_width(k1)
        N = int(mp.ceil((hi - lo) * rho / sigma))
        N += N % 2
        h = (hi - lo) / N
        ts = [lo + i * h for i in range(N + 1)]
        lw = [t / 4 + mp.log(p0._omega_series(mp.exp(t))) for t in ts]
        lt = [mp.log(t) for t in ts]
        uc = p0.saddle((k0 + k1) / 2)
        luc = mp.log(uc)
        lwc = uc / 4 + mp.log(p0._omega_series(mp.exp(uc)))
        out, worst, moves, prev = [], mpf(0), 0, None
        for y in ys:
            terms = [mp.exp(2 * y * (a - luc) + (b - lwc)) for a, b in zip(lt, lw)]
            ends = (terms[0] + terms[-1]) / 2
            fine = h * (mp.fsum(terms) - ends)
            coarse = 2 * h * (mp.fsum(terms[::2]) - ends)
            worst = max(worst, abs(coarse / fine - 1))
            lf = mp.log(fine)
            if unwrap and prev is not None:
                k = int(mp.nint((mp.im(prev) - mp.im(lf)) / (2 * mp.pi)))
                if k:
                    lf += 2j * mp.pi * k
                    moves += 1
            prev = lf
            out.append(2 * y * luc + lwc + lf)
        return out, worst, moves


def h_complex(zs: list, dps: int, unwrap: bool = False) -> tuple:
    """h(z) = log M_z, M_z = 2^(-2z-2) (32 z (2z-1) I(z-1) - I(z)), Holland (15)."""
    la, dev_a, mv_a = log_I_complex([z - 1 for z in zs], dps, unwrap=unwrap)
    lb, dev_b, mv_b = log_I_complex(list(zs), dps, unwrap=unwrap)
    out = []
    with mp.workdps(dps + p0.GUARD):
        for z, a, b in zip(zs, la, lb):
            out.append(-(2 * z + 2) * mp.log(2) + a + mp.log(32 * z * (2 * z - 1) - mp.exp(b - a)))
    return out, max(dev_a, dev_b), mv_a + mv_b


def h_circle(n: int, dps: int = 30, m: int = 64, unwrap: bool = True) -> dict:
    """h on |z - n| = n/8 at m points: its Taylor coefficients at n by the
    discrete Cauchy formula, h^(k)(n) for k = 2..6 against route B on the real
    axis and against Lemma S's leading term, sup |h^(6)| on |z - n| = n/16 from
    the same Taylor series, and the variation of Holland's remainder
    R(z) = h(z) - G_0(2z - 2) - log(32 z (2z - 1)) + (2z + 2) log 2 on the circle."""
    rad = mpf(n) / 8
    with mp.workdps(dps + p0.GUARD):
        zs = [n + rad * mp.expjpi(2 * mpf(i) / m) for i in range(m)]
        hz, dev, moves = h_complex(zs, dps, unwrap=unwrap)
        hn, _, _ = h_complex([mpf(n)], dps)
        closure = abs(mp.im(hz[0] - hz[-1]))
        c = [mp.fsum(hz[i] * mp.expjpi(-2 * mpf(i * k) / m) for i in range(m)) / m for k in range(m)]
        der = [mp.factorial(k) * c[k] / rad ** k for k in range(8)]
        Ln = p0.script_L(n)
        lead = {k: (-1) ** k * 2 * mp.factorial(k - 2) / (mpf(n) ** (k - 1) * Ln) for k in range(2, 8)}
        # route B on the real axis: h^(k)(n) = k! g_k + psi^(k-1)(n + 1/2)
        g = p0.saddle_expansion(n, dps, order=7)
        hB = {k: mp.factorial(k) * g[k] + mp.polygamma(k - 1, mpf(n) + mpf(1) / 2) for k in range(2, 8)}
        inner = []
        for i in range(m):
            w = rad / 2 * mp.expjpi(2 * mpf(i) / m)
            v = mp.fsum(mp.factorial(k) / mp.factorial(k - 6) * c[k] * w ** (k - 6) / rad ** k
                        for k in range(6, m // 2))
            inner.append(abs(v))
        Rz = [hz[i] - G0(2 * zs[i] - 2) - mp.log(32 * zs[i] * (2 * zs[i] - 1)) + (2 * zs[i] + 2) * mp.log(2)
              for i in range(m)]
        Rn = hn[0] - G0(2 * mpf(n) - 2) - mp.log(32 * n * (2 * n - 1)) + (2 * n + 2) * mp.log(2)
        return {
            "n": n, "radius": s(rad, 6), "points": m, "L_n": s(Ln, 10),
            "trapezoid_coarse_fine": s(dev, 3), "unwrap_moves": moves,
            "imag_step_last_to_first": s(closure, 4),
            # the mean-value property: one holomorphic branch on the whole disk
            "center_value_vs_mean_of_circle": s(abs(c[0] - hn[0]), 3),
            "h_k_over_leading_cauchy": {str(k): s(mp.re(der[k]) / lead[k], 10) for k in range(2, 8)},
            "h_k_over_leading_route_B": {str(k): s(hB[k] / lead[k], 10) for k in range(2, 8)},
            "cauchy_vs_route_B_rel": {str(k): s(abs(der[k] / hB[k] - 1), 3) for k in range(2, 8)},
            "sup_h6_inner_circle_over_leading": s(max(inner) / abs(lead[6]), 8),
            "R_n": s(mp.re(Rn), 10),
            "max_R_variation_on_circle_times_n": s(max(abs(r - Rn) for r in Rz) * n, 6),
        }


# ---------------------------------------------------------------------------
# the psi^(5) bound used in the E^(6) assembly (H1_H3.md section 3.3)
# ---------------------------------------------------------------------------


def psi5_defect(y):
    """|psi^(5)(y) - 24/y^5| * (Re y)^6 / 120; at most 1 for Re y > 0."""
    return abs(mp.polygamma(5, y) - 24 / y ** 5) * mp.re(y) ** 6 / 120


def psi5_sum_vs_gap_integral(n, A, B, C, D) -> dict:
    """sum_V psi^(5)(V) - sum_U psi^(5)(U) - psi^(5)(b) against -(24/n^5) times the
    fifth moments of the three gaps, at z = 0; their difference is at most
    600/(min parameter)^6."""
    n = mpf(n)
    b = n + mpf(1) / 2
    exact = (mp.polygamma(5, B) + mp.polygamma(5, D) - mp.polygamma(5, A)
             - mp.polygamma(5, C) - mp.polygamma(5, b))
    wA, wB, wC, wD, wb = n / A, n / B, n / C, n / D, n / b
    gap = -24 / n ** 5 * (wA ** 5 + wC ** 5 - wB ** 5 + wb ** 5 - wD ** 5)
    pmin = min(A, B, C, D, b)
    return {"exact_n5": s(exact * n ** 5, 12), "gap_integral_n5": s(gap * n ** 5, 12),
            "abs_diff_n6": s(abs(exact - gap) * n ** 6, 6),
            "bound_n6": s(600 * (n / pmin) ** 6, 6),
            "within_bound": bool(abs(exact - gap) <= 600 / pmin ** 6)}


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def lr_route_A(I: dict, n: int, dps: int) -> list:
    ell = {m: p0.log_gamma_from_moments(I, m, dps) for m in range(n, n + J_TOP + 1)}
    return [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, J_TOP + 1)]


def route_B_dps(n) -> int:
    return int(6 * mp.log10(mpf(n))) + 60


def time_unit(dps: int) -> None:
    t0 = time.perf_counter()
    p0.moments_trapezoid(3200 - 1, 3200 + J_TOP, dps)
    print(f"[unit] route A, moments k=3199..3206, dps={dps}: {time.perf_counter() - t0:.2f} s")
    for n in ("1e4", "1e20"):
        t0 = time.perf_counter()
        with mp.workdps(route_B_dps(n)):
            lr = p1.lr_route_B_direct(mpf(n), p0.M_ROUTE_B)
            row(mpf(n), lr, p0.script_L(mpf(n)))
        print(f"[unit] route B row at n={n}: {time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    with mp.workdps(40):
        g0_row("1e20", "0.5")
    print(f"[unit] G_0 derivatives on one complex point: {time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    kappa_bar.cache_clear(), sigma_bar.cache_clear()
    kappa_bar(), sigma_bar(Fr(1, 8))
    print(f"[unit] exact box constants: {time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    h_circle(400)
    print(f"[unit] h on a 64-point complex circle at n=400: {time.perf_counter() - t0:.2f} s")


def run(dps: int, out: Path) -> dict:
    t_all = time.perf_counter()
    rec: dict = {"hunt": "jensen_wedge", "phase": "H1_H3", "grade": "measured; rational constants exact",
                 "source": "Holland arXiv:2608.08682v1, Lemma 4.2, Proposition 4.1, Lemma 6.1",
                 "git_head": p0.git_head(), "python": platform.python_version(),
                 "mpmath": mpmath.__version__, "sympy": sp.__version__, "dps": dps}

    # exact constants
    J, Ji = J_exact(), J_inv_exact()
    rec["exact"] = {
        "J": [[str(v) for v in r] for r in J], "J_inv": [[str(v) for v in r] for r in Ji],
        "weights": [str(v) for v in WEIGHTS], "r_box": str(R_BOX),
        "kappa_bar": str(kappa_bar()), "nu_w": str(nu_w()),
        "sigma_bar_at_eps": {e: str(sigma_bar(Fr(e))) for e in ("1/32", "1/16", "1/8", "1/6")},
        "box_admissible_at_eps": {e: box_is_admissible(Fr(e)) for e in ("1/8", "1/4", "1/2")},
    }
    print("[exact]", rec["exact"]["kappa_bar"], rec["exact"]["nu_w"], flush=True)

    # route A: validation, then the subgrid
    t0 = time.perf_counter()
    rec["validation_vs_li"] = [p0.validate_against_li(dps=50, m_lo=17, m_hi=47),
                               p0.validate_against_li(dps=30, m_lo=17, m_hi=127)]
    I, dev = p0.moments(range(K_LO, K_HI + 1), dps)
    rec["route_A"] = {"k_range": [K_LO, K_HI], "moments_computed": len(I),
                      "max_coarse_fine_deviation": s(dev, 3), "seconds": round(time.perf_counter() - t0, 1)}
    print("[route A]", rec["route_A"], flush=True)
    rows_A, sols_A = [], {}
    with mp.workdps(dps + p0.GUARD):
        for n in SUBGRID:
            r, sol = row(n, lr_route_A(I, n, dps), p0.script_L(n))
            rows_A.append(r)
            sols_A[n] = sol
            print(f"[A] n={n} tL={r['t_times_L']} closes={r['contraction']['closes']}", flush=True)
        rec["psi5_sum_vs_gap_integral_n3200"] = psi5_sum_vs_gap_integral(
            3200, sols_A[3200]["A"], sols_A[3200]["B"], sols_A[3200]["C"], sols_A[3200]["D"])
    rec["subgrid_route_A"] = rows_A

    # route B: the subgrid (agreement with route A) and large n
    t0 = time.perf_counter()
    agree = []
    for n, rA in zip(SUBGRID, rows_A):
        if n < 400:
            continue
        with mp.workdps(dps + p0.GUARD):
            tauB = targets(p1.lr_route_B_direct(mpf(n), p0.M_ROUTE_B), mpf(n))
            tauB5 = targets(p1.lr_route_B_direct(mpf(n), p0.M_ROUTE_B - 1), mpf(n))
            tauA = sols_A[n]["tau"]
            agree.append({"n": n, "max_rel_dev_A_B": s(max(abs(tauB[j] / tauA[j] - 1) for j in range(5)), 3),
                          "B_spread_M5_M6": s(max(abs(tauB5[j] / tauB[j] - 1) for j in range(5)), 3)})
    rec["route_B_vs_A_targets"] = agree
    rows_B = []
    for n in LARGE_NS:
        with mp.workdps(route_B_dps(n)):
            lr = p1.lr_route_B_direct(mpf(n), p0.M_ROUTE_B)
            lr5 = p1.lr_route_B_direct(mpf(n), p0.M_ROUTE_B - 1)
            r, sol = row(mpf(n), lr, p0.script_L(mpf(n)))
            r["n"] = n
            tau5 = targets(lr5, mpf(n))
            r["tau_spread_M5_M6"] = s(max(abs(tau5[j] / mpf(r["tau"][j]) - 1) for j in range(5)), 3)
            r["dps"] = route_B_dps(n)
            rows_B.append(r)
            print(f"[B] n={n} tL={r['t_times_L']} closes={r['contraction']['closes']} "
                  f"q={r['contraction']['q']} d0={r['contraction']['d0']} rhs={r['contraction']['rhs']}",
                  flush=True)
    rec["large_n_route_B"] = rows_B
    rec["route_B_seconds"] = round(time.perf_counter() - t0, 1)

    # G_0 on the real axis and on complex rays
    t0 = time.perf_counter()
    g0rows = []
    with mp.workdps(60):
        for N in G0_REAL_NS:
            for ang in G0_ANGLES:
                g0rows.append(g0_row(N, ang))
        rec["psi5_defect_samples"] = {
            f"{y}": s(psi5_defect(mpmath.mpmathify(y)), 8)
            for y in ("1", "2", "10", "100", "1e4", "3+4j", "10+30j", "100+90j", "1000+500j")}
    rec["G0"] = g0rows
    rec["G0_seconds"] = round(time.perf_counter() - t0, 1)
    t0 = time.perf_counter()
    rec["h_circle"] = [h_circle(400), h_circle(3200)]
    rec["h_circle_seconds"] = round(time.perf_counter() - t0, 1)
    print("[h circle]", [(r["n"], r["sup_h6_inner_circle_over_leading"]) for r in rec["h_circle"]], flush=True)
    rec["total_seconds"] = round(time.perf_counter() - t_all, 1)
    out.write_text(json.dumps(rec, indent=1) + "\n")
    print(f"wrote {out} in {rec['total_seconds']} s")
    return rec


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--out", type=Path, default=HERE / "results_h1_h3.json")
    ap.add_argument("--time-unit", action="store_true")
    a = ap.parse_args()
    if a.time_unit:
        time_unit(a.dps)
        return
    run(a.dps, a.out)


if __name__ == "__main__":
    main()
