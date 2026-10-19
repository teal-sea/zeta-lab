"""Independent reproduction code for the phase 1 review of hunt #135 (jensen_wedge).

Written from the formulas in Holland, arXiv:2608.08682v1, and from RESULTS.md
sections 11 and 12, without importing `probe.py` or `probe_phase1.py`. Nothing
here bears on RH. Every number this file produces is measured (one route, float
or mpmath grade); none is a proof.

The target sequence comes from a route the hunt did not use: the Mellin moments
of Riemann's kernel,

    M_x = int_0^inf phi(u) u^(2x) du,
    phi(u) = sum_k (2 pi^2 k^4 e^(9u/2) - 3 pi k^2 e^(5u/2)) exp(-pi k^2 e^(2u)),

so that gamma(n) = const * n! M_n / (2n)! (Holland's eq. (10)) and
h(x) = log M_x is Holland's h up to an additive constant. The hunt's route A
integrates u^(2k) e^(u/4) omega(e^u) by a trapezoid rule; this file integrates
phi(u) u^(2x) by Gauss-Legendre panels around the saddle. They share no
integrand, no rule and no node. `zeta.li` is used only as an outside check of
the gamma ratios at small n, and for its exact Sturm count.
"""

from __future__ import annotations

import math
from fractions import Fraction
from itertools import combinations

from mpmath import mp, mpf

# ---------------------------------------------------------------------------
# 1. The target: log gamma(n) from Riemann's kernel
# ---------------------------------------------------------------------------


def _phi(u):
    """Riemann's kernel phi(u), u >= 0, summed until a term is negligible."""
    total = mpf(0)
    e2u = mp.exp(2 * u)
    a, b = mp.exp(9 * u / 2), mp.exp(5 * u / 2)
    tiny = mp.mpf(2) ** (-mp.prec - 40)
    k = 1
    while True:
        term = (2 * mp.pi ** 2 * k ** 4 * a - 3 * mp.pi * k ** 2 * b) * mp.exp(-mp.pi * k * k * e2u)
        total += term
        if k > 1 and abs(term) < tiny * abs(total):
            return total
        k += 1


def _saddle(x):
    """Peak of 2x log u + 9u/2 - pi e^(2u) and its Gaussian width."""
    u = mpf(1)
    for _ in range(80):
        f = 2 * x / u + mpf(9) / 2 - 2 * mp.pi * mp.exp(2 * u)
        fp = -2 * x / u ** 2 - 4 * mp.pi * mp.exp(2 * u)
        step = f / fp
        u -= step
        if u <= 0:
            u = mpf("0.05")
        if abs(step) < mpf(10) ** (-20):
            break
    sigma = 1 / mp.sqrt(2 * x / u ** 2 + 4 * mp.pi * mp.exp(2 * u))
    return u, sigma


_GL_CACHE: dict = {}


def _gl_nodes(m: int):
    """Gauss-Legendre nodes and weights on [-1, 1] at the current precision."""
    key = (m, mp.prec)
    if key not in _GL_CACHE:
        nodes, weights = [], []
        for i in range(1, m + 1):
            x = mp.cos(mp.pi * (i - mpf(1) / 4) / (m + mpf(1) / 2))
            for _ in range(100):
                p0, p1 = mpf(1), x
                for j in range(2, m + 1):
                    p0, p1 = p1, ((2 * j - 1) * x * p1 - (j - 1) * p0) / j
                dp = m * (x * p1 - p0) / (x * x - 1)
                dx = p1 / dp
                x -= dx
                if abs(dx) < mpf(2) ** (-mp.prec + 8):
                    break
            nodes.append(x)
            weights.append(2 / ((1 - x * x) * dp * dp))
        _GL_CACHE[key] = (nodes, weights)
    return _GL_CACHE[key]


def log_moments(xs, dps: int = 60, panels: int = 48, width: float = 50.0, order: int = 40):
    """log M_x for each x in `xs` (all within a few units of each other).

    One panel grid spans [u* - width sigma, u* + width sigma] (clipped at 0) for
    the middle x; phi is evaluated once per node and reused for every x. Returns
    (logs, tail) where tail is the larger endpoint value of the integrand
    relative to its peak, which must be negligible."""
    xs = list(xs)
    with mp.workdps(dps + 20):
        xm = mpf(xs[len(xs) // 2])
        u0, sig = _saddle(xm)
        lo = max(mpf(0), u0 - width * sig)
        hi = u0 + width * sig
        nodes, weights = _gl_nodes(order)
        h = (hi - lo) / panels
        pts, wts = [], []
        for p in range(panels):
            a = lo + p * h
            for t, w in zip(nodes, weights):
                pts.append(a + h * (t + 1) / 2)
                wts.append(w * h / 2)
        ph = [_phi(u) for u in pts]
        lu = [mp.log(u) for u in pts]
        logs, tails = [], []
        for x in xs:
            x = mpf(x)
            logs_i = [2 * x * l + mp.log(f) for l, f in zip(lu, ph)]
            top = max(logs_i)
            s = mp.fsum(w * mp.exp(v - top) for w, v in zip(wts, logs_i))
            logs.append(top + mp.log(s))
            ends = [2 * x * mp.log(u) + mp.log(_phi(u)) for u in (lo, hi) if u > 0]
            tails.append(max(mp.exp(e - top) for e in ends) if ends else mpf(0))
        return [+v for v in logs], max(tails)


def log_gamma_window(n: int, count: int, dps: int = 60, **kw):
    """log gamma(n + j), j = 0..count-1, up to one common additive constant."""
    xs = [n + j for j in range(count)]
    lm, tail = log_moments(xs, dps=dps, **kw)
    with mp.workdps(dps + 20):
        out = [lm[j] + mp.loggamma(n + j + 1) - mp.loggamma(2 * (n + j) + 1) for j in range(count)]
    return out, tail


def log_q(lg):
    """log q_k = 2 lg(k+1) - lg(k) - lg(k+2) from a window of log gamma."""
    return [2 * lg[k + 1] - lg[k] - lg[k + 2] for k in range(len(lg) - 2)]


def holland_L(x):
    """Holland's eq. (16): the positive solution of x = L (pi e^L + 3/4)."""
    x = mpf(x)
    L = mp.log(x) if x > 3 else mpf(1)
    for _ in range(200):
        f = L * (mp.pi * mp.exp(L) + mpf(3) / 4) - x
        fp = mp.pi * mp.exp(L) * (1 + L) + mpf(3) / 4
        step = f / fp
        L -= step
        if abs(step) < mpf(10) ** (-mp.dps + 5):
            break
    return L


def script_L(n):
    """Holland's script L_n := L_(2n - 2) (Lemma 4.2)."""
    return holland_L(2 * mpf(n) - 2)


# ---------------------------------------------------------------------------
# 2. The model families and their solvers
# ---------------------------------------------------------------------------


def log_qq(k: int, U, V):
    """log of Holland's eq. (49): (U+k)(V+k+1)/((V+k)(U+k+1))."""
    return mp.log(U + k) + mp.log(V + k + 1) - mp.log(V + k) - mp.log(U + k + 1)


def _dlog_qq(k: int, U, V):
    return (1 / (U + k) - 1 / (U + k + 1), 1 / (V + k + 1) - 1 / (V + k))


def jacobi_fit(lq):
    """Holland's eq. (38): A_J, B_J from q_0, q_1."""
    q0, q1 = mp.exp(lq[0]), mp.exp(lq[1])
    T = (q0 - 1) / (q1 - 1)
    AJ = 2 * q0 / (T - q0)
    BJ = 1 / (q0 * (1 + 1 / AJ) - 1)
    return AJ, BJ


def newton_factors(lq, x0, free, fixed=None, n=None, tol_digits=None, maxit=100):
    """Solve sum over factors of log qq_k(U_i, V_i) = log q_k for k = 0..len(free)-1.

    The unknowns are the logs of the parameters named in `free` (a subset of
    'A', 'B', 'C', 'D'), the rest come from `fixed`. Factors are (A, B) and
    (C, D). Equation k is scaled by n^(k+1) so that all rows are of order one.
    Returns the parameter dict and the largest unscaled residual."""
    names = list(free)
    m = len(names)
    p = dict(fixed or {})
    p.update(x0)
    z = [mp.log(p[s]) for s in names]
    tol = mpf(10) ** (-(tol_digits or (mp.dps - 10)))
    for _ in range(maxit):
        for s, v in zip(names, z):
            p[s] = mp.exp(v)
        F, J = [], []
        for k in range(m):
            F.append((log_qq(k, p["A"], p["B"]) + log_qq(k, p["C"], p["D"]) - lq[k]) * mpf(n) ** (k + 1))
            dA, dB = _dlog_qq(k, p["A"], p["B"])
            dC, dD = _dlog_qq(k, p["C"], p["D"])
            grads = {"A": dA, "B": dB, "C": dC, "D": dD}
            J.append([grads[s] * p[s] * mpf(n) ** (k + 1) for s in names])
        dz = mp.lu_solve(mp.matrix(J), mp.matrix(F))
        step = max(abs(dz[i]) for i in range(m))
        lam = mpf(1)
        while lam * step > mpf("0.2"):
            lam /= 2
        z = [z[i] - lam * dz[i] for i in range(m)]
        if step < tol:
            break
    for s, v in zip(names, z):
        p[s] = mp.exp(v)
    resid = max(abs(log_qq(k, p["A"], p["B"]) + log_qq(k, p["C"], p["D"]) - lq[k]) for k in range(m))
    return p, resid


def defect(lq, p, k: int):
    """E(k+2) = log(R_(k+2)/R_(k+2)^model) once q_0..q_(k-1) are matched."""
    return log_qq(k, p["A"], p["B"]) + log_qq(k, p["C"], p["D"]) - lq[k]


def pade_guess(n, eps):
    """Leading-order [2/2] Pade configuration mapped to (A, B, C, D)."""
    a1, b1, a2, b2 = pade22(eps)
    return {"A": n / a1, "B": n / b1, "C": n / a2, "D": n / b2}


def solve_pade(n: int, lq, eps=None):
    """Holland's four-parameter system with D free, matching q_0..q_3."""
    L = script_L(n)
    eps = eps if eps is not None else 2 / L
    return newton_factors(lq, pade_guess(n, eps), "ABCD", n=n)


def solve_holland(n: int, lq, D):
    """Holland's three-parameter system at fixed D (his eqs. (51), (52))."""
    L = script_L(n)
    AJ, BJ = jacobi_fit(lq)
    x0 = {"A": AJ * mpf(6) / 5, "B": BJ + n / (3 * L), "C": D + n / (24 * L)}
    return newton_factors(lq, x0, "ABC", fixed={"D": D}, n=n)


# ---------------------------------------------------------------------------
# 3. The leading-order model of section 11
# ---------------------------------------------------------------------------


def stieltjes_coeffs(eps, K: int):
    """Taylor coefficients of f_eps(z) = (1 - z)^(eps - 1)."""
    c = [mpf(1)]
    for k in range(1, K):
        c.append(c[-1] * (k - eps) / k)
    return c


def pade22(eps):
    """[2/2] Pade approximant of f_eps, as (a1, b1, a2, b2) in w = 1/z:
    the a's are the zeros (w_U), the b's the poles (w_V), each sorted."""
    c = stieltjes_coeffs(mpf(eps), 5)
    M = mp.matrix([[c[2], c[1]], [c[3], c[2]]])
    q1, q2 = mp.lu_solve(M, mp.matrix([-c[3], -c[4]]))
    p1 = c[1] + q1 * c[0]
    p2 = c[2] + q1 * c[1] + q2 * c[0]
    poles = sorted(mp.polyroots([1, q1, q2]), key=lambda v: mp.re(v))
    zeros = sorted(mp.polyroots([c[0], p1, p2]), key=lambda v: mp.re(v))
    return zeros[0], poles[0], zeros[1], poles[1]


def betas(eps, intervals, smax: int):
    """beta_s = sum (w_V^s - w_U^s) - (1 - eps), s = 1..smax (section 11.1)."""
    return [mp.fsum(b ** s - a ** s for a, b in intervals) - (1 - eps) for s in range(1, smax + 1)]


def first_order_family(omega):
    """Section 11.2's first-order D-fixed family, scaled by eps:
    (gamma, beta, alpha, beta_4) / eps, derived here from beta_1..beta_3 = 0."""
    w = Fraction(omega) if not isinstance(omega, Fraction) else omega
    # unknowns alpha, beta, gamma; equations (first order in eps, divided by eps):
    #   -alpha - beta + gamma = -1;  -2 beta + 2 w gamma = -1;  -3 beta + 3 w^2 gamma = -1
    g = Fraction(1, 6) / (w * w - w)
    b = Fraction(1, 2) + w * g
    a = 1 - b + g
    beta4 = 1 - 4 * b + 4 * w ** 3 * g
    return g, b, a, beta4


def obstruction_lp(omegas, b_grid):
    """Section 11.5's first-order system with g_j >= 0 on a grid of nodes:
    is there any b in b_grid and g >= 0 with sum g_j w_j^k = b - 1/(k+1), k = 1..3?
    Returns the smallest residual found (zero would mean feasible)."""
    import numpy as np
    from scipy.optimize import nnls

    A = np.array([[w ** k for w in omegas] for k in (1, 2, 3)], dtype=float)
    best = math.inf
    for b in b_grid:
        rhs = np.array([b - 1 / (k + 1) for k in (1, 2, 3)])
        _, r = nnls(A, rhs)
        best = min(best, r)
    return best


def three_factor_config(eps, X2, X3, guess):
    """Leading-order three-factor model (section 11.5, mesoscopic part).

    Factors [a_i, b_i], i = 1..3; factor 1 is the main one, factors 2 and 3 have
    prescribed relative gaps X_i = 1 - a_i/b_i. Unknowns a1, b1, b2, b3; the four
    equations are beta_1..beta_4 = 0. Float arithmetic (scipy), leading order only."""
    import numpy as np
    from scipy.optimize import fsolve

    def F(v):
        a1, b1, b2, b3 = v
        out = []
        for s in range(1, 5):
            tot = b1 ** s - a1 ** s + b2 ** s * (1 - (1 - X2) ** s) + b3 ** s * (1 - (1 - X3) ** s)
            out.append(tot - (1 - eps))
        return out

    sol, info, ier, _ = fsolve(F, guess, full_output=True, xtol=1e-14)
    return sol, ier == 1 and max(abs(np.array(F(sol)))) < 1e-11


# ---------------------------------------------------------------------------
# 4. Root geometry: Lemmas A, B, C and Proposition 2.2_m
# ---------------------------------------------------------------------------


def harmonic(d: int):
    return mp.fsum(mpf(1) / k for k in range(1, d + 1))


def poly_from_roots(roots):
    """Ascending coefficients of prod (y - r)."""
    c = [mpf(1)]
    for r in roots:
        new = [mpf(0)] * (len(c) + 1)
        for i, ci in enumerate(c):
            new[i] += -r * ci
            new[i + 1] += ci
        c = new
    return c


def critical_points(roots):
    """Critical points of prod (y - r), one strictly between each pair of roots,
    by bisection on p'/p = sum 1/(y - r) (decreasing between consecutive roots)."""
    out = []
    rs = sorted(roots)
    for lo, hi in zip(rs, rs[1:]):
        a, b = lo, hi
        for _ in range(mp.prec + 20):
            mid = (a + b) / 2
            s = mp.fsum(1 / (mid - r) for r in rs)
            if s > 0:
                a = mid
            else:
                b = mid
        out.append((a + b) / 2)
    return out


def derivative_ratios(roots, y):
    """|T_k| = |y^k p^(k)(y)/p(y)| = k! y^k |e_k(1/(y - y_j))| for k = 0..d."""
    x = [1 / (y - r) for r in roots]
    d = len(x)
    e = [mpf(1)] + [mpf(0)] * d
    for xi in x:
        for k in range(d, 0, -1):
            e[k] += e[k - 1] * xi
    return [abs(mp.factorial(k) * y ** k * e[k]) for k in range(d + 1)]


def lemma_a_check(roots):
    """For each critical point: the needed r = max_k |T_k|^(1/k), Lemma A's
    y sum 1/|y - y_j|, and the explicit y (4 + 3 H_d)/g. Returns the maxima."""
    rs = sorted(roots)
    d = len(rs)
    g = min(b - a for a, b in zip(rs, rs[1:]))
    need = lem = expl = mpf(0)
    worst_slack = mpf("inf")
    for y in critical_points(rs):
        T = derivative_ratios(rs, y)
        r_need = max(T[k] ** (mpf(1) / k) for k in range(1, d + 1))
        s = y * mp.fsum(1 / abs(y - r) for r in rs)
        e = y * (4 + 3 * harmonic(d)) / g
        need, lem, expl = max(need, r_need), max(lem, s), max(expl, e)
        worst_slack = min(worst_slack, s - r_need, e - s)
    return {"r_needed": need, "lemma_a": lem, "explicit": expl, "gap": g, "min_slack": worst_slack}


def jacobi_factor_coeffs(d: int, U, V, scale):
    """Ascending coefficients of 2F1(-d, U; V; scale * y) (exact if inputs are Fractions)."""
    out = []
    term = Fraction(1) if isinstance(U, Fraction) else mpf(1)
    for j in range(d + 1):
        out.append(term)
        term = term * (-d + j) * (U + j) / ((V + j) * (j + 1)) * scale
    return out


def holland_box(p_coeffs, q_coeffs):
    """Holland's convolution: if p = sum (-1)^j C(d,j) a_j y^j, q likewise with b_j,
    then (p box q) = sum (-1)^j C(d,j) a_j b_j y^j."""
    d = len(p_coeffs) - 1
    out = []
    for j in range(d + 1):
        bj = math.comb(d, j)
        a = p_coeffs[j] * (-1) ** j / bj
        b = q_coeffs[j] * (-1) ** j / bj
        out.append((-1) ** j * bj * a * b)
    return out


def real_roots_mp(coeffs, dps: int = 80):
    """Roots of an ascending real polynomial, checked to be real to working precision."""
    with mp.workdps(dps):
        desc = list(reversed([mpf(c.numerator) / c.denominator if isinstance(c, Fraction) else mpf(c)
                              for c in coeffs]))
        rts = mp.polyroots(desc, maxsteps=400, extraprec=4 * dps)
        top = max(abs(r) for r in rts)
        imag = max(abs(mp.im(r)) for r in rts) / top
        return sorted(mp.re(r) for r in rts), imag


def lmesh(roots):
    rs = sorted(roots)
    return min(b / a for a, b in zip(rs, rs[1:]))


def lemma_b_gap(d: int, B):
    """Lemma B's Sturm separation: pi sqrt(B/(2.47 d + 6.07))."""
    return mp.pi * mp.sqrt(mpf(B) / (mpf("2.47") * d + mpf("6.07")))


def prop22m_margin(roots, c_fun, m: int):
    """Proposition 2.2_m on a planted multiplier: at each critical point of p,
    |P/p - 1| where P = sum p_j c(j) y^j. Returns the largest such value."""
    p = poly_from_roots(roots)
    P = [p[j] * c_fun(j) for j in range(len(p))]
    worst = mpf(0)
    for y in critical_points(roots):
        pv = mp.polyval(list(reversed(p)), y)
        Pv = mp.polyval(list(reversed(P)), y)
        worst = max(worst, abs(Pv / pv - 1))
    return worst, P


def lobatto_jacobian_det(x=Fraction(1, 2), w1=Fraction(2, 3)):
    """Determinant of the first-order Pade system in this file's coordinates:
    (x1, x4, g, nu) with a1 = eps x1, b2 = 1 - eps x4, interior gap of length
    eps g centred at nu, equations F_s = 1 - s x4 - s nu^(s-1) g - [s = 1] x1."""
    nu, g = x, w1
    rows = []
    for s in range(1, 5):
        rows.append([Fraction(-1 if s == 1 else 0), Fraction(-s), -s * nu ** (s - 1),
                     -s * (s - 1) * nu ** (s - 2) * g if s > 1 else Fraction(0)])

    def det(m):
        if len(m) == 1:
            return m[0][0]
        return sum((-1) ** c * m[0][c] * det([r[:c] + r[c + 1:] for r in m[1:]]) for c in range(len(m)))

    return det(rows)


def all_subsets_check(xs, k):
    """|e_k(x)| <= e_k(|x|) <= (sum |x|)^k / k!, the inequality behind Lemma A."""
    ek = mp.fsum(mp.fprod(c) for c in combinations(xs, k))
    ek_abs = mp.fsum(mp.fprod(abs(v) for v in c) for c in combinations(xs, k))
    bound = mp.fsum(abs(v) for v in xs) ** k / mp.factorial(k)
    return abs(ek), ek_abs, bound


# ---------------------------------------------------------------------------
# 5. The report behind REVIEW_PHASE1.md
# ---------------------------------------------------------------------------


def _pade_row(n: int, dps: int):
    lg, tail = log_gamma_window(n, 8, dps=dps)
    lq = log_q(lg)
    L = script_L(n)
    AJ, BJ = jacobi_fit(lq)
    p, res = solve_pade(n, lq)
    ph, resh = solve_holland(n, lq, BJ / 2)
    A, B, C, D = p["A"], p["B"], p["C"], p["D"]
    wA, wB, wC, wD = n / A, n / B, n / C, n / D
    return {
        "n": n, "L": mp.nstr(L, 8), "tail": mp.nstr(tail, 3),
        "theta_star": mp.nstr(D / BJ, 12),
        "A_over_nL": mp.nstr(A / (n * L), 6), "D_minus_n_L_over_n": mp.nstr((D - n) * L / n, 6),
        "B_minus_C_L_over_n": mp.nstr((B - C) * L / n, 6), "rho_CD": mp.nstr(1 - D / C, 6),
        "gap_total_times_L": mp.nstr((wA + (wC - wB) + (1 - wD)) * L, 6),
        "n5_L_E_S6": mp.nstr(n ** 5 * L * defect(lq, p, 4), 6),
        "n4_L_E_F5_theta_half": mp.nstr(n ** 4 * L * defect(lq, ph, 3), 6),
        "positive_and_ordered": bool(A > B > 0 and C > D > 0 and wA < wB < wC < wD < 1),
        "residual": mp.nstr(max(res, resh), 3),
    }


def report() -> dict:
    """Every number REVIEW_PHASE1.md quotes from this file (about 2 minutes)."""
    import time

    t0 = time.time()
    mp.dps = 60
    out: dict = {"route": "Gauss-Legendre panels over phi(u) u^(2x), dps 60 (80 from n = 1e5)"}
    ns = list(range(50, 3201, 25)) + [10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
    out["pade_rows"] = [_pade_row(n, 60 if n < 10 ** 5 else 80) for n in ns]
    rows = []
    for n in (50, 200, 800, 3200, 10 ** 4, 10 ** 5, 10 ** 6):
        lm, _ = log_moments([n + j for j in range(8)], dps=70)
        row = {"n": n}
        for k in range(2, 7):
            dk = mp.fsum((-1) ** (k - i) * mp.binomial(k, i) * lm[i] for i in range(k + 1))
            x = n + mpf(k) / 2
            Lx = script_L(x)
            rho = dk / ((-1) ** k * mp.factorial(k - 2) * (2 / Lx) / x ** (k - 1))
            row[f"rho_{k}"] = mp.nstr(rho, 6)
        rows.append(row)
    out["h_derivative_ratios"] = rows
    out["pade22"] = []
    for e in ("0.9", "0.5", "0.342", "0.1", "0.01", "1e-4", "1e-8"):
        eps = mpf(e)
        a1, b1, a2, b2 = [mp.re(v) for v in pade22(eps)]
        bs = betas(eps, [(a1, b1), (a2, b2)], 5)
        out["pade22"].append({"eps": e, "interlaced": bool(0 < a1 < b1 < a2 < b2 < 1),
                              "a1_over_eps": mp.nstr(a1 / eps, 8), "mid_gap_over_eps": mp.nstr((a2 - b1) / eps, 8),
                              "reflection_defect": mp.nstr(max(abs(a1 + b2 - 1), abs(b1 + a2 - 1)), 3),
                              "beta5_over_eps": mp.nstr(bs[4] / eps, 10)})
    out["seconds"] = round(time.time() - t0, 1)
    return out


if __name__ == "__main__":  # pragma: no cover - manual run
    import json
    import sys
    from pathlib import Path

    res = report()
    dest = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("results_review.json")
    dest.write_text(json.dumps(res, indent=1) + "\n", encoding="utf-8")
    print(f"wrote {dest} in {res['seconds']} s; E_S(6) < 0 at all {len(res['pade_rows'])} n:",
          all(r["n5_L_E_S6"].startswith("-") for r in res["pade_rows"]))
