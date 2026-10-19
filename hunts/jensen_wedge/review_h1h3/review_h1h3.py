"""Independent review of hunt #135's `H1_H3.md` (see `../REVIEW_H1_H3.md`).

Written from the formulas in `H1_H3.md` and in Holland, arXiv:2608.08682v1, by a
session that did not write them. It imports nothing from `probe.py`,
`probe_h1_h3.py` or `review/`. Grades: the rational constants are exact (sympy);
everything else is measured. Nothing here bears on RH.

Routes used here and nowhere else in the hunt:

* the derivatives of Holland's main term G_0 are computed **symbolically**, as
  exact rational functions of (N, L) obtained from the operator
  D = d/dN + (L/Q) d/dL; the hunt measured them by Cauchy's formula;
* the targets tau_j = (-1)^j n^(j+1)/j! Delta^(j+2) h(n) come from the Mellin
  moment M_z = int_0^oo Phi(u) u^(2z) du of Titchmarsh's kernel
  Phi(u) = sum_k (2 pi^2 k^4 e^(9u) - 3 pi k^2 e^(5u)) exp(-pi k^2 e^(4u)), by
  tanh-sinh quadrature in the saddle variable t = (u - u_c)/s, all shifts
  n..n+6 from one cached set of integrand values. The u-scale differs from
  Holland's by a factor 2, which changes h by a linear function of z and so no
  Delta^m, m >= 2. Validated against `zeta.li`'s Cauchy route (no Mellin
  representation) and against Holland's main term G_0 + E_l at large n;
* the matching system is solved twice, in the gap-moment form (4.2) and in
  Holland's quotient form (52) at k = 0..3, which shares no formula with (4.2).

Run: `.venv/bin/python hunts/jensen_wedge/review_h1h3/review_h1h3.py`
(about 2 minutes, writes `results_review_h1h3.json` next to this file).
"""

from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import sympy as sp
from mpmath import mp, mpc, mpf

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_ROOT))

Q = sp.Rational

# ---------------------------------------------------------------------------
# Part A. Exact algebra of H1_H3.md section 4 (sympy, rational)
# ---------------------------------------------------------------------------

g0, gx, g1, xx, EPS = sp.symbols("g0 gx g1 x eps")
XVARS = (g0, gx, g1, xx)
XSTAR = (Q(1, 6), Q(2, 3), Q(1, 6), Q(1, 2))
WEIGHTS = (Q(3, 4), Q(1), Q(3, 2), Q(3, 4))
R_BOX = Q(2, 25)
DVARS = sp.symbols("dg0 dgx dg1 dx")


def phi_inf():
    """Phi_inf,j(X) = 1 - [j = 0] g0 - (j+1)(gx x^j + g1), as written in 4.2."""
    return sp.Matrix([1 - (g0 if j == 0 else 0) - (j + 1) * (gx * xx**j + g1) for j in range(4)])


def p_numerator(j, eps=EPS):
    """eps * P_j(X; eps): the j-th monomial moment of the gap set, from its endpoints."""
    wA, wB, wC, wD = eps * g0, xx - eps * gx / 2, xx + eps * gx / 2, 1 - eps * g1
    return sp.expand(wA ** (j + 1) + wC ** (j + 1) - wB ** (j + 1) + 1 - wD ** (j + 1))


@lru_cache(maxsize=1)
def s_vector():
    """S_j(X; eps) with eps S_j = P_j(X; eps) - P_j(X; 0), derived from the endpoints."""
    out = []
    for j in range(4):
        P = sp.expand(sp.cancel(p_numerator(j) / EPS))
        out.append(sp.expand(sp.cancel((P - P.subs(EPS, 0)) / EPS)))
    return tuple(out)


@lru_cache(maxsize=1)
def p_at_zero():
    return tuple(sp.expand(sp.cancel(p_numerator(j) / EPS)).subs(EPS, 0) for j in range(4))


@lru_cache(maxsize=1)
def jacobian():
    J = phi_inf().jacobian(XVARS).subs(dict(zip(XVARS, XSTAR)))
    return J, J.inv()


def _shift():
    return {v: s + d for v, s, d in zip(XVARS, XSTAR, DVARS)}


def monomial_bound(expr, weights=WEIGHTS, r=R_BOX):
    """Sum over monomials of |coefficient| * prod (w_k r)^e_k, eps kept as a symbol with
    eps >= 0 (each eps-coefficient taken in absolute value)."""
    poly = sp.Poly(sp.expand(expr), *DVARS)
    total = sp.Integer(0)
    for mon, c in poly.terms():
        c = sp.expand(c)
        if c.free_symbols:
            cb = sum(abs(cc) * EPS ** e[0] for e, cc in sp.Poly(c, EPS).terms())
        else:
            cb = abs(c)
        for k, e in enumerate(mon):
            cb *= (weights[k] * r) ** e
        total += cb
    return sp.expand(total)


@lru_cache(maxsize=1)
def contraction_matrix():
    """I - J^-1 D Phi_inf(X* + d), entries polynomial in the deviations d."""
    _, Ji = jacobian()
    return (sp.eye(4) - Ji * phi_inf().jacobian(XVARS).subs(_shift())).applyfunc(sp.expand)


def weighted_row_sums(bounds, weights=WEIGHTS):
    return [sp.expand(sum(bounds[i, k] * weights[k] for k in range(4)) / weights[i]) for i in range(4)]


@lru_cache(maxsize=1)
def kappa_rows():
    return tuple(weighted_row_sums(contraction_matrix().applyfunc(monomial_bound)))


@lru_cache(maxsize=1)
def nu_w_rows():
    _, Ji = jacobian()
    return tuple(sum(abs(Ji[i, k]) for k in range(4)) / WEIGHTS[i] for i in range(4))


@lru_cache(maxsize=1)
def sigma_rows():
    """Row bounds of sup_B ||J^-1 D_X(eps S)||_w, polynomials in eps."""
    _, Ji = jacobian()
    eS = sp.Matrix([EPS * s for s in s_vector()])
    K = (Ji * eS.jacobian(XVARS).subs(_shift())).applyfunc(sp.expand)
    return tuple(weighted_row_sums(K.applyfunc(monomial_bound)))


def sigma_bar(eps):
    return max(sp.nsimplify(r.subs(EPS, eps)) for r in sigma_rows())


def eps_part_at_xstar():
    """J^-1 (eps S)(X*; eps), factored."""
    _, Ji = jacobian()
    eS = sp.Matrix([EPS * s for s in s_vector()]).subs(dict(zip(XVARS, XSTAR)))
    return (Ji * eS).applyfunc(sp.factor)


def admissibility_threshold():
    """Largest eps for which every X in the closed box has 0 < w_A < w_B < w_C < w_D < 1.
    Both nontrivial constraints are linear in each coordinate, so the worst case is a
    corner: eps (g0 + gx/2) < x and eps (gx/2 + g1) < 1 - x."""
    lo = [s - w * R_BOX for s, w in zip(XSTAR, WEIGHTS)]
    hi = [s + w * R_BOX for s, w in zip(XSTAR, WEIGHTS)]
    assert min(lo[:3]) > 0, "a gap weight reaches 0 on the box"
    t1 = lo[3] / (hi[0] + hi[1] / 2)
    t2 = (1 - hi[3]) / (hi[1] / 2 + hi[2])
    return min(t1, t2), (t1, t2)


def corner_admissible(eps):
    """Exhaustive corner check of the ordering at a given eps (exact)."""
    import itertools
    for signs in itertools.product((-1, 1), repeat=4):
        g = [s + sg * w * R_BOX for s, sg, w in zip(XSTAR, signs, WEIGHTS)]
        wA, wB, wC, wD = eps * g[0], g[3] - eps * g[1] / 2, g[3] + eps * g[1] / 2, 1 - eps * g[2]
        if not (0 < wA < wB < wC < wD < 1):
            return False
    return True


def first_order_configuration():
    """(X_n - X*) L -> -J^-1 (0, H_1, H_2, H_3) + 2 (1/18, -1/9, 1/18, 0), and the
    parameter expansions it implies, with eps L/2 = 1 - 1/L + O(1/L^2) (Lemma T)."""
    _, Ji = jacobian()
    tl = sp.Matrix([0, 1, Q(3, 2), Q(11, 6)])
    Jt = Ji * tl
    dX = -Jt + 2 * sp.Matrix([Q(1, 18), -Q(1, 9), Q(1, 18), 0])
    y = sp.symbols("y")  # y = 1/L
    epsv = 2 * y * (1 - y)
    G = [XSTAR[i] + dX[i] * y for i in range(4)]
    wA = epsv * G[0]
    wB = G[3] - epsv * G[1] / 2
    wC = G[3] + epsv * G[1] / 2
    wD = 1 - epsv * G[2]
    ser = lambda e, k=2: sp.series(e, y, 0, k).removeO()
    out = {
        "J_inv_t_first_order": [str(v) for v in Jt],
        "dX_times_L_limit": [str(v) for v in dX],
        "A_over_nL": str(sp.expand(ser(y / wA, 2))),
        "D_minus_n_L_over_n": str(sp.expand(ser((1 / wD - 1) / y, 2))),
        "B_minus_2n_L_over_n": str(ser((1 / wB - 2) / y, 1)),
        "C_minus_2n_L_over_n": str(ser((1 / wC - 2) / y, 1)),
        "B_minus_C_L_over_n": str(sp.expand(ser((1 / wB - 1 / wC) / y, 2))),
    }
    return out, dX


def rho_prime(n, eps, j=3):
    """w-weighted row sum of section 4.2's derivative bounds for rho_j, sup over the box."""
    c = Fraction((j + 1) ** 2 * (j + 2))
    g0max = Fraction(1, 6) + Fraction(3, 4) * Fraction(2, 25)
    w = [Fraction(3, 4), Fraction(1), Fraction(3, 2), Fraction(3, 4)]
    d = [c * (eps * g0max) ** (j + 1) / (2 * n), c / (2 * n), c / (2 * n), c / (n * eps)]
    return sum(di * wi for di, wi in zip(d, w))


def uniform_sufficient_form(eps=Fraction(1, 16), neps=Fraction(10**5)):
    """Section 4.3's uniform form, evaluated exactly at eps = 1/16, n eps = 1e5 (n = neps/eps)."""
    n = neps / eps
    kap = Fraction(4533, 15625)
    sig = Fraction(str(sigma_bar(Q(eps.numerator, eps.denominator))))
    nu = Fraction(86, 9)
    rp = max(rho_prime(n, eps, j) for j in range(4))
    q = kap + sig + nu * rp
    r = Fraction(2, 25)
    room = (1 - q) * r
    eps_part_exact = eps * (1 - eps) / 9
    eps_part_doc = eps / 9
    beta3 = Fraction(4) / ((2 * n + 1) * eps)
    rho3_xstar = Fraction(80) / (2 * n) * (1 + 1 / ((2 * n + 1) * eps))
    rho3_box = Fraction(80) / (2 * n) * (1 + Fraction(13, 4) * r + 1 / ((2 * n + 1) * eps))
    tail_xstar = nu * (beta3 + rho3_xstar)
    tail_box = nu * (beta3 + rho3_box)
    return {
        "q": q, "room": room, "eps_part_exact": eps_part_exact, "eps_part_doc": eps_part_doc,
        "tail_xstar": tail_xstar, "tail_box": tail_box,
        "max_Jinv_t_sharp": room - eps_part_exact - tail_xstar,
        "max_Jinv_t_doc_bounds": room - eps_part_doc - tail_box,
    }


# ---------------------------------------------------------------------------
# Part B. Holland's main term G_0, symbolically (Lemma S)
# ---------------------------------------------------------------------------

NS, LS = sp.symbols("N L", positive=True)
AS, BS = sp.symbols("a b")  # a = 1/L, b = L/N
QS = (1 + LS) * NS - Q(3, 4) * LS**2


def _D(f):
    """d/dN along the saddle branch: L' = L/Q (Holland, proof of Lemma 4.2)."""
    return sp.diff(f, NS) + (LS / QS) * sp.diff(f, LS)


def g0_symbolic():
    return (NS + 1) * sp.log(LS) + LS / 4 - NS / LS - sp.log(QS) / 2


def rho_g_identity_defect():
    """G_0' - log L - rho_G with rho_G = (1 + L)/Q - Q'/(2Q): exactly 0 if 4's display holds."""
    rho = (1 + LS) / QS - _D(QS) / (2 * QS)
    return sp.simplify(_D(g0_symbolic()) - sp.log(LS) - rho)


@lru_cache(maxsize=1)
def g0_derivatives(kmax=8):
    """{k: G_0^(k)(N)} for k = 2..kmax as exact rational functions of (N, L)."""
    cur = sp.together(_D(_D(g0_symbolic())))
    out = {2: sp.factor(cur)}
    for k in range(3, kmax + 1):
        cur = sp.factor(sp.together(_D(cur)))
        out[k] = cur
    return out


@lru_cache(maxsize=None)
def normalized_g0(k):
    """f_k(a, b) := (-1)^k N^(k-1) L G_0^(k)(N)/(k-2)! in a = 1/L, b = L/N."""
    G = g0_derivatives()[k]
    F = (-1) ** k * NS ** (k - 1) * LS * G / sp.factorial(k - 2)
    return sp.factor(sp.together(F.subs({NS: 1 / (AS * BS), LS: 1 / AS})))


def harmonic(m):
    return sum(Q(1, i) for i in range(1, m + 1))


@lru_cache(maxsize=None)
def lemma_s_first_order(k):
    """Coefficients of 1, a, a^2 in f_k(a, 0): Lemma S(c) says 1 + (H_(k-2) - 1) a + ..."""
    f0 = sp.series(normalized_g0(k).subs(BS, 0), AS, 0, 3).removeO()
    p = sp.Poly(sp.expand(f0), AS)
    return [p.coeff_monomial(AS**i) for i in range(3)]


def lemma_s_explicit_bound(k, amax=Q(1, 4), bmax=Q(1, 8)):
    """sup |f_k(a, b)| over |a| <= 1/4, |b| <= 1/8 (the region (P2) gives), bounded by
    monomials over the minimum of the denominator |4 + 4a - 3b| >= 4 - 1 - 3/8 = 21/8.
    Returns (bound, power of the denominator)."""
    num, den = sp.fraction(normalized_g0(k))
    dp = sp.Poly(den, AS, BS)
    # den is c (4a - 3b + 4)^m
    m = sp.degree(den, AS)
    c = sp.Poly(sp.expand(den / (4 * AS - 3 * BS + 4) ** m), AS, BS).as_expr()
    assert sp.expand(c * (4 * AS - 3 * BS + 4) ** m - den) == 0 and not c.free_symbols, dp
    P = sp.Poly(sp.expand(num), AS, BS)
    nb = sum(abs(cf) * amax ** e[0] * bmax ** e[1] for e, cf in P.terms())
    return nb / (abs(c) * (4 - 4 * amax - 3 * bmax) ** m), m


# ---------------------------------------------------------------------------
# Part C. The saddle L_N and G_0 numerically
# ---------------------------------------------------------------------------


def saddle_L(N, L0=None):
    """Solve N = L (pi e^L + 3/4) by Newton, starting from log N - log log N (complex ok)."""
    N = mp.mpmathify(N)
    if isinstance(N, mpc) and N.imag == 0:
        N = N.real
    L = L0 if L0 is not None else mp.log(N / mp.pi) - mp.log(mp.log(N / mp.pi))
    for _ in range(200):
        f = L * (mp.pi * mp.exp(L) + mpf(3) / 4) - N
        fp = mp.pi * mp.exp(L) * (1 + L) + mpf(3) / 4
        dL = f / fp
        L -= dL
        if abs(dL) < mpf(10) ** (-mp.dps + 5) * abs(L):
            break
    return L


def script_L(x):
    """Holland's script L_x := L_(2x - 2)."""
    return saddle_L(2 * mpf(x) - 2)


@lru_cache(maxsize=None)
def _g0k_func(k):
    return sp.lambdify((NS, LS), g0_derivatives()[k], modules="mpmath")


def g0_ratio(N, k):
    """G_0^(k)(N) divided by its leading term (-1)^k (k-2)!/(N^(k-1) L_N)."""
    L = saddle_L(N)
    lead = (-1) ** k * mp.factorial(k - 2) / (N ** (k - 1) * L)
    return _g0k_func(k)(N, L) / lead, L


def p2_scan(theta, zmin, zmax=1e30, n_r=60, n_phi=13):
    """(P2) on the sector {|z| in [zmin, zmax], |arg z| <= theta}: min |L_N| and max |L_N/N|
    over a log-polar grid, N = 2z - 2, each L continued along its ray from the real axis."""
    worst_L, worst_ratio = mpf("inf"), mpf(0)
    for i in range(n_r):
        rad = mpf(zmin) * (mpf(zmax) / zmin) ** (mpf(i) / (n_r - 1))
        Lprev = None
        for jj in range(n_phi):
            ph = theta * mpf(jj) / (n_phi - 1)
            for sgn in (1, -1):
                z = rad * mp.expj(sgn * ph)
                N = 2 * z - 2
                L = saddle_L(N, Lprev if (Lprev is not None and sgn == 1) else None)
                assert abs(L * (mp.pi * mp.exp(L) + mpf(3) / 4) - N) < mpf(10) ** (-mp.dps // 2) * abs(N)
                assert mp.re(L) > 0
                worst_L = min(worst_L, abs(L))
                worst_ratio = max(worst_ratio, abs(L / N))
                if sgn == 1:
                    Lprev = L
    return worst_L, worst_ratio


def p2_fixed_point_margin(ell, theta):
    """The reviewer's derivation of (P2) (REVIEW_H1_H3.md): with l = log|N|, T(L) = log(N/L - 3/4)
    - log pi maps D = {|L - l| <= l/2} into itself when log(1.5 pi l) + log(1/(1 - eta)) + theta
    + pi/6 + asin(eta) <= l/2, where eta = 3 (3l/2)/(4|N|) bounds |3L/(4N)|. Returns the slack
    l/2 - lhs (positive = the map is a self-map) and the contraction factor bound
    (1/(l/2)) / (1 - eta)."""
    ell = mpf(ell)
    Nabs = mp.exp(ell)
    eta = mpf(9) / 8 * ell / Nabs
    lhs = mp.log(mpf(3) / 2 * mp.pi * ell) + mp.log(1 / (1 - eta)) + theta + mp.pi / 6 + mp.asin(eta)
    return ell / 2 - lhs, (2 / ell) / (1 - eta)


# ---------------------------------------------------------------------------
# Part D. The targets tau_j from the Mellin moment (independent quadrature route)
# ---------------------------------------------------------------------------


def log_phi(u):
    """log Phi(u), Phi(u) = sum_k (2 pi^2 k^4 e^(9u) - 3 pi k^2 e^(5u)) exp(-pi k^2 e^(4u))."""
    e4 = mp.exp(4 * u)
    a1 = 2 * mp.pi**2 * mp.exp(9 * u) - 3 * mp.pi * mp.exp(5 * u)
    corr = mpf(0)
    k = 2
    while True:
        t = -mp.pi * (k * k - 1) * e4
        if t < -(mp.prec * 0.7 + 50):
            break
        ak = 2 * mp.pi**2 * k**4 * mp.exp(9 * u) - 3 * mp.pi * k**2 * mp.exp(5 * u)
        corr += ak / a1 * mp.exp(t)
        k += 1
    return mp.log(a1) - mp.pi * e4 + mp.log1p(corr)


def _saddle_u(n):
    u = mp.log(mpf(n)) / 4 if n > 50 else mpf("0.5")
    for _ in range(300):
        f = 2 * n / u + 9 - 4 * mp.pi * mp.exp(4 * u)
        fp = -2 * n / u**2 - 16 * mp.pi * mp.exp(4 * u)
        du = -f / fp
        u += du
        if abs(du) < mpf(10) ** (-mp.dps // 2):
            break
    s = 1 / mp.sqrt(2 * n / u**2 + 16 * mp.pi * mp.exp(4 * u))
    return u, s


def log_moment_shifts(n, imax=6, dps=None, width=40):
    """[log I_0, ..., log I_imax] with I_i = M_(n+i)/(e^(F_n(u_c)) u_c^(2i)), so that
    Delta^m log I = Delta^m h(n) for m >= 2. One cached set of integrand values serves
    every shift."""
    if dps is None:
        dps = int(50 + 7 * mp.log10(max(n, 10)))
    with mp.workdps(dps):
        n = mpf(n)
        uc, s = _saddle_u(n)
        Fc = 2 * n * mp.log(uc) + log_phi(uc)
        cache = {}

        def base(u):
            if u not in cache:
                cache[u] = (mp.exp(2 * n * mp.log(u) + log_phi(u) - Fc), u / uc)
            return cache[u]

        lo = uc - width * s
        if lo > 0:
            pts = [uc + c * s for c in (-width, -width / 2, -10, -4, 0, 4, 10, width / 2, width)]
        else:
            pts = [mpf(0), uc / 2] + [uc + c * s for c in (-4, 0, 4, 10, width / 2, width) if uc + c * s > uc / 2]
        out = []
        for i in range(imax + 1):
            v = mp.quad(lambda u: base(u)[0] * base(u)[1] ** (2 * i), pts)
            out.append(mp.log(v))
        return out


def forward_differences(vals):
    """[Delta^0 f(0), Delta^1 f(0), ...] in the current precision."""
    out, cur = [], list(vals)
    while cur:
        out.append(cur[0])
        cur = [cur[k + 1] - cur[k] for k in range(len(cur) - 1)]
    return out


def taus_from_deltas(n, d):
    """tau_j = (-1)^j n^(j+1)/j! Delta^(j+2) h(n), j = 0..len(d)-3."""
    return [(-1) ** j * mpf(n) ** (j + 1) / mp.factorial(j) * d[j + 2] for j in range(len(d) - 2)]


def holland_main_term_deltas(n, imax=6, dps=None):
    """Delta^m of G_0(2z - 2) + log(32 z (2z - 1)) at z = n (Holland's (18) without R)."""
    if dps is None:
        dps = int(50 + 7 * mp.log10(max(n, 10)))
    with mp.workdps(dps):
        vals = []
        for i in range(imax + 1):
            z = mpf(n) + i
            N = 2 * z - 2
            L = saddle_L(N)
            Qv = (1 + L) * N - mpf(3) / 4 * L**2
            G = (N + 1) * mp.log(L) + L / 4 - N / L - mp.log(Qv) / 2
            vals.append(G + mp.log(32 * z * (2 * z - 1)))
        return forward_differences(vals)


def li_validation(n_lo=20, n_hi=26, dps=50):
    """Delta^m log gamma(n) from zeta.li's Cauchy route against this file's moments."""
    from zeta.li import xi_taylor_coefficients

    with mp.workdps(dps + 20):
        gam = xi_taylor_coefficients(n_hi + 7, dps=dps + 20, method="cauchy", cache=False)
        rows = []
        for n in range(n_lo, n_hi + 1):
            ref = forward_differences([mp.log(gam[n + i]) for i in range(7)])
            mine = log_moment_shifts(n, imax=6, dps=dps + 30)
            fact = [mp.loggamma(n + i + 1) - mp.loggamma(2 * (n + i) + 1) for i in range(7)]
            md = forward_differences([a + b for a, b in zip(mine, fact)])
            rows.append({"n": n, "max_rel_diff_m2_6": max(abs(md[m] - ref[m]) / abs(ref[m]) for m in range(2, 7))})
        return rows


# ---------------------------------------------------------------------------
# Part E. Lemma C on measured data, and the system solved two ways
# ---------------------------------------------------------------------------

JINV_F = [[Fraction(-1), Fraction(5, 2), Fraction(-8, 3), Fraction(1)],
          [Fraction(0), Fraction(-2), Fraction(4, 3), Fraction(0)],
          [Fraction(0), Fraction(-1, 2), Fraction(4, 3), Fraction(-1)],
          [Fraction(0), Fraction(3, 2), Fraction(-3), Fraction(3, 2)]]
W_F = [Fraction(3, 4), Fraction(1), Fraction(3, 2), Fraction(3, 4)]


def _m(fr):
    return mpf(fr.numerator) / fr.denominator


def wnorm(v):
    return max(abs(v[i]) / _m(W_F[i]) for i in range(4))


def jinv_apply(v):
    return [sum(_m(JINV_F[i][k]) * v[k] for k in range(4)) for i in range(4)]


def lemma_c_on_data(n, tau, box_sum=True):
    """q, d_0, (1 - q) r and whether Lemma C closes, exactly as section 4.3 defines them.
    box_sum=True bounds rho_j with g0 + gx + g1 <= 1 + 13r/4 (as the hunt's JSON does);
    False uses the value 1 at X*, which is what T(X*) - X* needs."""
    n = mpf(n)
    eps = tau[0]
    t = [tau[j] / eps - 1 for j in range(4)]
    S2 = -(1 - eps) / 12
    S3 = -(1 - eps) / 6
    v = [t[0], t[1], t[2] - eps * S2, t[3] - eps * S3]
    lead = wnorm(jinv_apply(v))
    sig = max(mpf(sp.N(row.subs(EPS, sp.Float(str(eps), 60)), 50)) for row in sigma_rows())
    r = mpf(2) / 25
    g0max = mpf(1) / 6 + mpf(3) / 4 * r
    rp = mpf(0)
    tails = []
    gsum = 1 + mpf(13) / 4 * r if box_sum else mpf(1)
    for j in range(4):
        c = (j + 1) ** 2 * (j + 2)
        rp = max(rp, c * (eps * g0max) ** (j + 1) / (2 * n) * mpf(3) / 4 + c / (2 * n) * (1 + mpf(3) / 2)
                 + c / (n * eps) * mpf(3) / 4)
        beta = (j + 1) / ((2 * n + 1) * eps)
        rho = c / (2 * n) * (gsum + 1 / ((2 * n + 1) * eps))
        tails.append(beta + rho)
    nu = mpf(86) / 9
    q = mpf(4533) / 15625 + sig + nu * rp
    d0 = lead + nu * max(tails)
    rhs = (1 - q) * r
    closes = bool(q < 1 and d0 <= rhs and eps < mpf(2) / 3)
    return {"eps": eps, "t": t, "sigma": sig, "rho_prime": rp, "q": q, "d0_lead": lead, "d0": d0,
            "rhs": rhs, "closes": closes, "radius": d0 / (1 - q) if closes else None}


def _dlog(p, m):
    """Delta^m log p."""
    return sum((-1) ** (m - i) * mp.binomial(m, i) * mp.log(p + i) for i in range(m + 1))


def lam(j, p, n):
    return (-1) ** j * mpf(n) ** (j + 1) / mp.factorial(j) * _dlog(p, j + 1)


def phi_n(X, n, tau):
    """Phi_n(X) of section 4.1 through lambda_j (exact finite differences of log)."""
    eps = tau[0]
    G0, GX, G1, XX = X
    wA, wB, wC, wD = eps * G0, XX - eps * GX / 2, XX + eps * GX / 2, 1 - eps * G1
    b = mpf(n) + mpf(1) / 2
    P = {k: mpf(n) / w for k, w in (("A", wA), ("B", wB), ("C", wC), ("D", wD))}
    return [(tau[j] - (lam(j, P["A"], n) + lam(j, P["C"], n) - lam(j, P["B"], n) + lam(j, b, n)
                       - lam(j, P["D"], n))) / eps for j in range(4)]


def solve_moment_form(n, tau, X0):
    sol = mp.findroot(lambda a, b_, c, d: phi_n((a, b_, c, d), n, tau), X0, tol=mpf(10) ** (-mp.dps + 15))
    return [sol[i] for i in range(4)]


def solve_quotient_form(n, d2h, P0):
    """Holland's (52) with D free at k = 0..3: q_k(A,B) q_k(C,D) = q_k with
    log q_k = log(1 + 1/(b + k)) - Delta^2 h(n + k). Unknowns are log A, log B, log C, log D."""
    b = mpf(n) + mpf(1) / 2

    def qq(U, V, k):
        return mp.log((U + k) * (V + k + 1) / ((V + k) * (U + k + 1)))

    def eqs(la, lb, lc, ld):
        A, B, C, D = mp.exp(la), mp.exp(lb), mp.exp(lc), mp.exp(ld)
        return [(qq(A, B, k) + qq(C, D, k) - (mp.log(1 + 1 / (b + k)) - d2h[k])) * mpf(n) ** (k + 1)
                for k in range(4)]

    s = mp.findroot(eqs, [mp.log(p) for p in P0], tol=mpf(10) ** (-mp.dps + 15))
    return [mp.exp(s[i]) for i in range(4)]


def analyse_n(n, imax=6):
    """Everything section 4.6 and section 3.3 measure at one n, on this file's route."""
    dps = int(50 + 7 * mp.log10(max(n, 10)))
    t0 = time.time()
    logs = log_moment_shifts(n, imax=imax, dps=dps)
    with mp.workdps(dps):
        d = forward_differences(logs)
        tau = taus_from_deltas(n, d)
        hol = holland_main_term_deltas(n, imax=imax, dps=dps)
        Ln = script_L(n)
        res = {"n": n, "dps": dps, "L_n": Ln, "tau": tau, "eps_L_over_2": tau[0] * Ln / 2,
               "t_times_L": [(tau[j] / tau[0] - 1) * Ln for j in (1, 2, 3)],
               "tau_L_over_2_minus_1_times_L": [(tau[j] * Ln / 2 - 1) * Ln for j in range(len(tau))],
               "holland_main_term_rel_diff": [abs(hol[m] - d[m]) / abs(d[m]) for m in range(2, imax + 1)]}
        c12 = {k: lemma_s_first_order(k) for k in range(2, imax + 1)}
        res["tau_second_order_residual_times_L3"] = [
            (tau[j] * Ln / 2 - (1 + mpf(str(c12[j + 2][1])) / Ln + mpf(str(c12[j + 2][2])) / Ln**2)) * Ln**3
            for j in range(len(tau))]
        res["lemma_c"] = lemma_c_on_data(n, tau, box_sum=True)
        res["lemma_c_sharp"] = lemma_c_on_data(n, tau, box_sum=False)
        _, dX1 = first_order_configuration()
        X0 = [mpf(sp.N(XSTAR[i] + dX1[i] / sp.Float(str(Ln), 30), 30)) for i in range(4)]
        X = solve_moment_form(n, tau[:4], X0)
        eps = tau[0]
        res["X"] = X
        res["phi_residual"] = max(abs(v) for v in phi_n(X, n, tau[:4]))
        dX = [X[i] - mpf(sp.N(XSTAR[i], 40)) for i in range(4)]
        res["dX_times_L"] = [v * Ln for v in dX]
        res["dX_w_norm"] = wnorm(dX)
        wA, wB, wC, wD = eps * X[0], X[3] - eps * X[1] / 2, X[3] + eps * X[1] / 2, 1 - eps * X[2]
        A, B, C, D = n / wA, n / wB, n / wC, n / wD
        res["ABCD"] = [A, B, C, D]
        res["ordered"] = bool(0 < wA < wB < wC < wD < 1)
        res["params"] = {"A_over_nL": A / (n * Ln), "D_minus_n_L_over_n": (D - n) * Ln / n,
                         "B_minus_2n_L_over_n": (B - 2 * n) * Ln / n, "C_minus_2n_L_over_n": (C - 2 * n) * Ln / n,
                         "B_minus_C_L_over_n": (B - C) * Ln / n}
        d2h = [sum((-1) ** (2 - i) * mp.binomial(2, i) * logs[k + i] for i in range(3)) for k in range(4)]
        P2 = solve_quotient_form(n, d2h, [A, B, C, D])
        res["quotient_form_rel_diff"] = max(abs(P2[i] - p) / p for i, p in enumerate((A, B, C, D)))
        res["seconds"] = time.time() - t0
        return res


def box_point(rng):
    """A uniformly random point of the closed box B (weighted radius 2/25 about X*)."""
    r = mpf(2) / 25
    return [mpf(sp.N(XSTAR[i], 40)) + (2 * mpf(rng.random()) - 1) * _m(W_F[i]) * r for i in range(4)]


def t_map(X, n, tau):
    ph = phi_n(X, n, tau)
    v = jinv_apply(ph)
    return [X[i] - v[i] for i in range(4)]


def dt_norm(X, n, tau, h=None):
    """||DT(X)||_w by central differences (induced weighted max norm)."""
    h = h or mpf(10) ** (-mp.dps // 3)
    cols = []
    for k in range(4):
        Xp = list(X)
        Xm = list(X)
        Xp[k] += h
        Xm[k] -= h
        tp, tm = t_map(Xp, n, tau), t_map(Xm, n, tau)
        cols.append([(tp[i] - tm[i]) / (2 * h) for i in range(4)])
    return max(sum(abs(cols[k][i]) * _m(W_F[k]) for k in range(4)) / _m(W_F[i]) for i in range(4))


def adversarial_lemma_c(n, samples=120, starts=24, seed=135):
    """Try to break Lemma C at one n where it closes: the largest ||DT||_w found at random
    points of B (must not exceed q), the largest ||T(X) - X*||_w over B's sampled points (must
    not exceed r), and Newton from random starts in B (every root found in B must coincide)."""
    import random

    rng = random.Random(seed)
    dps = int(50 + 7 * mp.log10(max(n, 10)))
    logs = log_moment_shifts(n, imax=5, dps=dps)
    with mp.workdps(dps):
        tau = taus_from_deltas(n, forward_differences(logs))[:4]
        lc = lemma_c_on_data(n, tau)
        xs = [mpf(sp.N(v, 40)) for v in XSTAR]
        pts = [box_point(rng) for _ in range(samples)]
        max_dt = max(dt_norm(X, n, tau) for X in pts)
        max_image = max(wnorm([a - b for a, b in zip(t_map(X, n, tau), xs)]) for X in pts)
        roots = []
        for _ in range(starts):
            X0 = box_point(rng)
            try:
                X = solve_moment_form(n, tau, X0)
            except (ZeroDivisionError, ValueError):
                continue
            if wnorm([a - b for a, b in zip(X, xs)]) <= mpf(2) / 25:
                roots.append(X)
        spread = max((wnorm([a - b for a, b in zip(X, roots[0])]) for X in roots), default=None)
        return {"n": n, "q": lc["q"], "max_DT_w_sampled": max_dt, "max_T_image_w_sampled": max_image,
                "r": mpf(2) / 25, "roots_in_B": len(roots), "starts": starts, "root_spread_w": spread}


# ---------------------------------------------------------------------------
# Part F. Section 3.3 items 1 and 2
# ---------------------------------------------------------------------------


def psi5_defect_ratio(y):
    """|psi^(5)(y) - 24/y^5| / (120/(Re y)^6), item 1 of section 3.3."""
    y = mpc(y)
    return abs(mp.psi(5, y) - 24 / y**5) / (120 / mp.re(y) ** 6)


def item2(n, ABCD):
    """The five psi^(5) terms at z = 0 against -int_G f_0', both times n^5, and the
    difference times n^6 against the bound sum 120/p^6 (with every p >= b) times n^6."""
    n = mpf(n)
    A, B, C, D = ABCD
    b = n + mpf(1) / 2
    exact = -mp.psi(5, b) + mp.psi(5, B) + mp.psi(5, D) - mp.psi(5, A) - mp.psi(5, C)
    f = lambda w: 24 * w**5 / n**5
    gap = -(f(n / A) + f(n / C) - f(n / B) + f(n / b) - f(n / D))
    return {"exact_n5": exact * n**5, "gap_integral_n5": gap * n**5,
            "abs_diff_n6": abs(exact - gap) * n**6, "bound_n6_min_param": 600 * (n / b) ** 6,
            "bound_n6_each_param": 120 * sum((n / p) ** 6 for p in (A, B, C, D, b))}


# ---------------------------------------------------------------------------
# Part G. (P1) on a complex circle, through Holland's (15)
# ---------------------------------------------------------------------------


def log_F15(s, yc=None, width=40):
    """log F(s), F(s) = int_1^oo (log t)^s t^(-3/4) sum_k exp(-pi k^2 t) dt (Holland, before
    (15)), as int_0^oo y^s e^(y/4) psi(e^y) dy, with s log y_c + y_c/4 - pi e^(y_c) taken out
    so the remaining integral has a small phase. Returns (value, y_c)."""
    s = mp.mpmathify(s)
    sr = mp.re(s)
    if yc is None:
        y = mp.log(sr)
        for _ in range(200):
            f = sr / y + mpf(1) / 4 - mp.pi * mp.exp(y)
            fp = -sr / y**2 - mp.pi * mp.exp(y)
            dy = -f / fp
            y += dy
            if abs(dy) < mpf(10) ** (-mp.dps // 2):
                break
        yc = y
    w = 1 / mp.sqrt(sr / yc**2 + mp.pi * mp.exp(yc))
    ec = mp.exp(yc)

    def g(y):
        e = mp.exp(y)
        corr = mpf(0)
        k = 2
        while True:
            t = -mp.pi * (k * k - 1) * e
            if t < -(mp.prec * 0.7 + 50):
                break
            corr += mp.exp(t)
            k += 1
        return mp.exp(s * mp.log(y / yc) + (y - yc) / 4 - mp.pi * (e - ec) + mp.log1p(corr))

    pts = [yc + c * w for c in (-width, -width / 2, -10, -4, 0, 4, 10, width / 2, width)]
    assert pts[0] > 0
    val = mp.quad(g, pts)
    # the large phase sits in s log y_c, which is continuous in s; the residual must stay far
    # from the branch cut or a 2 pi i jump could pass unseen
    assert abs(mp.arg(val)) < 1, ("residual phase too large for the principal branch", s)
    return s * mp.log(yc) + yc / 4 - mp.pi * ec + mp.log(val), yc


def h15(z):
    """h(z) = log M_z from Holland's (15). Continuous in z: the only logs taken of
    oscillating quantities have their phase checked in log_F15."""
    z = mp.mpmathify(z)
    lf0, _ = log_F15(2 * z - 2)
    lf1, _ = log_F15(2 * z)
    tail = mp.log(1 - mp.exp(lf1 - lf0) / (32 * z * (2 * z - 1)))
    return -(2 * z + 2) * mp.log(2) + mp.log(32 * z * (2 * z - 1)) + lf0 + tail, lf0 + tail


def g0_complex(N, L):
    Qv = (1 + L) * N - mpf(3) / 4 * L**2
    return (N + 1) * mp.log(L) + L / 4 - N / L - mp.log(Qv) / 2


def circle_check(n, M=64, dps=40):
    """h on |z - n| = n/8 from (15); R + c_sad = h - G_0(2z - 2) - log(32 z (2z - 1)) + (2z + 2) log 2
    on the circle; Taylor coefficients at n; sup |h^(6)| on |z - n| = n/16 from the Taylor series
    at n (coefficients from M and from M/2 points, for a convergence check)."""
    with mp.workdps(dps):
        n = mpf(n)
        rad = n / 8
        hs, Rs = [], []
        Lprev = None
        for m in range(M):
            zeta = n + rad * mp.expj(2 * mp.pi * m / M)
            h, core = h15(zeta)
            L = saddle_L(2 * zeta - 2, Lprev)
            Lprev = L
            Rs.append(core - g0_complex(2 * zeta - 2, L))
            hs.append(h)
        hn, coren = h15(n)
        Rn = coren - g0_complex(2 * n - 2, saddle_L(2 * n - 2))
        zs = [n + rad * mp.expj(2 * mp.pi * m / M) for m in range(M)]

        def taylor(k, step=1):
            pts = range(0, M, step)
            return sum(hs[m] * (zs[m] - n) ** (-k) for m in pts) / len(pts)

        coeffs = [taylor(k) for k in range(M // 2)]
        coeffs_half = [taylor(k, 2) for k in range(M // 4)]
        Ln = script_L(n)
        lead6 = 48 / (n**5 * Ln)

        def h6_at(z0, cs):
            # the Taylor series at n, not Cauchy's formula at z0: the latter carries h's large
            # linear part through an aliasing factor (1/2)^M and loses about ten digits at M = 64
            return sum(cs[k] * mp.factorial(k) / mp.factorial(k - 6) * (z0 - n) ** (k - 6)
                       for k in range(6, len(cs)))

        inner = [n + n / 16 * mp.expj(2 * mp.pi * m / 64) for m in range(64)]
        sup6 = max(abs(h6_at(z0, coeffs)) for z0 in inner) / lead6
        sup6_half = max(abs(h6_at(z0, coeffs_half)) for z0 in inner) / lead6
        d_from_taylor = [mp.factorial(m) * sum(mp.stirling2(k, m) * coeffs[k] for k in range(m, M // 2))
                         for m in range(2, 7)]
        return {"n": n, "M": M, "R_n": Rn, "center_vs_mean": abs(hn - sum(hs) / M),
                "max_R_variation_times_n": max(abs(R - Rn) for R in Rs) * n,
                "max_R_spread_times_n": max(abs(a - b) for a in Rs for b in Rs) * n,
                "h_k_over_leading": {k: coeffs[k] * mp.factorial(k) / ((-1) ** k * 2 * mp.factorial(k - 2) / (n ** (k - 1) * Ln))
                                     for k in range(2, 8)},
                "sup_h6_inner_over_leading": sup6, "sup_h6_inner_half_points": sup6_half,
                "delta_m_from_circle": d_from_taylor}


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

N_VALUES = [50, 200, 800, 3200, 10**4, 10**5, 10**6, 10**7, 10**8, 10**10, 10**12, 10**16, 10**20]


def _s(v, k=12):
    if isinstance(v, (list, tuple)):
        return [_s(w, k) for w in v]
    if isinstance(v, dict):
        return {kk: _s(w, k) for kk, w in v.items()}
    if isinstance(v, (Fraction, sp.Basic)):
        return str(v)
    if isinstance(v, (mpf, mpc)):
        return mp.nstr(v, k)
    return v


def main():
    t_start = time.time()
    out = {"hunt": "jensen_wedge", "what": "independent review of H1_H3.md", "grade": "measured; rational constants exact"}
    J, Ji = jacobian()
    kap = kappa_rows()
    out["exact"] = {
        "J": [[str(J[i, k]) for k in range(4)] for i in range(4)], "det_J": str(J.det()),
        "J_inv": [[str(Ji[i, k]) for k in range(4)] for i in range(4)],
        "S": [str(s) for s in s_vector()],
        "kappa_rows": [str(v) for v in kap], "kappa": str(max(kap)),
        "nu_w_rows": [str(v) for v in nu_w_rows()], "nu_w": str(max(nu_w_rows())),
        "sigma_rows": [str(v) for v in sigma_rows()],
        "sigma_at": {str(e): str(sigma_bar(e)) for e in (Q(1, 32), Q(1, 16), Q(1, 8), Q(1, 6))},
        "eps_part_at_xstar": [str(v) for v in eps_part_at_xstar()],
        "admissibility_threshold": str(admissibility_threshold()[0]),
        "first_order": first_order_configuration()[0],
        "uniform_sufficient_form": {k: str(v) for k, v in uniform_sufficient_form().items()},
    }
    out["lemma_s"] = {
        "rho_G_identity_defect": str(rho_g_identity_defect()),
        "first_order_coeffs": {k: [str(c) for c in lemma_s_first_order(k)] for k in range(2, 9)},
        "H_minus_1": {k: str(harmonic(k - 2) - 1) for k in range(2, 9)},
        "explicit_main_term_bound_on_P2_region": {k: str(lemma_s_explicit_bound(k)[0]) for k in range(2, 7)},
    }
    with mp.workdps(60):
        rows = []
        for N in (mpf(10) ** 3, mpf(10) ** 20, mpf(10) ** 50):
            for ang in (0, mpf("0.25"), mpf("0.5")):
                Nc = N * mp.expj(ang) if ang else N
                row = {"N_abs": mp.nstr(N, 3), "angle": str(ang)}
                rr = {}
                for k in range(2, 7):
                    ratio, L = g0_ratio(Nc, k)
                    rr[k] = ratio
                row["L_N"] = L
                row["ratio"] = {k: (v if ang == 0 else abs(v)) for k, v in rr.items()}
                if ang == 0:
                    row["ratio_minus_1_times_L"] = {k: (v - 1) * L for k, v in rr.items()}
                rows.append(row)
        out["G0_measured"] = _s(rows, 10)
        out["P2_scan"] = {}
        for theta, zmin in ((mpf("0.5"), 346), (mpf(1), 346), (mpf("0.5"), 50)):
            wl, wr = p2_scan(theta, zmin)
            out["P2_scan"][f"theta={theta},zmin={zmin}"] = {"min_abs_L": mp.nstr(wl, 8), "max_abs_L_over_N": mp.nstr(wr, 8)}
        out["P2_fixed_point"] = {str(ell): _s(p2_fixed_point_margin(ell, mp.pi / 2), 6) for ell in (12, 13, 14, 20)}
        out["psi5_item1"] = {str(y): mp.nstr(psi5_defect_ratio(y), 8) for y in
                             (1, 2, 10, 100, 10**4, 3 + 4j, 10 + 30j, 100 + 90j, 1000 + 500j)}
    out["li_validation"] = _s(li_validation(), 4)
    out["circle"] = []
    for n in (400, 3200):
        c = circle_check(n)
        with mp.workdps(40):
            d = forward_differences(log_moment_shifts(n, imax=6, dps=70))
            c["delta_m_circle_vs_real_route_rel"] = [abs(mp.re(c["delta_m_from_circle"][m - 2]) - d[m]) / abs(d[m])
                                                     for m in range(2, 7)]
        c.pop("delta_m_from_circle")
        c["h_k_over_leading"] = {k: mp.re(v) for k, v in c["h_k_over_leading"].items()}
        out["circle"].append(_s(c, 10))
    out["n_rows"] = []
    for n in N_VALUES:
        res = analyse_n(n)
        if n == 3200:
            with mp.workdps(res["dps"]):
                out["item2_n3200"] = _s(item2(n, res["ABCD"]), 8)
        out["n_rows"].append(_s(res, 10))
        print(n, "done", round(res["seconds"], 1), "s", flush=True)
    out["adversarial_lemma_c"] = [_s(adversarial_lemma_c(n), 8) for n in (10**7, 10**20)]
    out["total_seconds"] = round(time.time() - t_start, 1)
    path = _HERE / "results_review_h1h3.json"
    path.write_text(json.dumps(out, indent=1) + "\n", encoding="utf-8")
    print("wrote", path, "in", out["total_seconds"], "s")
    return out


if __name__ == "__main__":
    main()
