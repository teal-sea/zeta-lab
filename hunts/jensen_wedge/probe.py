"""Hunt #135 phase 0: Holland's two sign facts, reproduced on two routes.

Run from the repository root:

    .venv/bin/python hunts/jensen_wedge/probe.py --time-unit   # time one unit first
    .venv/bin/python hunts/jensen_wedge/probe.py               # writes results.json

The objects, as read from Holland, arXiv:2608.08682v1 (sections 1 and 4 to 6) on
2026-10-18. Write R_j(n) = gamma(n+j)/gamma(n), so R_0 = 1, and

    q_k = R_{k+1}^2 / (R_k R_{k+2}),
    qq_k(U, V) = (U+k)(V+k+1) / ((V+k)(U+k+1)),

where qq_k(U, V) is the k-th quotient of the coefficient sequence
S^j (U)_j / (U^j (V)_j); U = infinity gives the Laguerre sequence S^j/(V)_j.

* Laguerre (Lemma 4.3). B_L = 1/(q_0 - 1), S_L = B_L R_1 match R_0, R_1, R_2.
  The defect at R_3 is D_n = log(R_3/R_3^L) = log(qq_1(inf, B_L)/q_1).
  Holland: D_n = 2/(n^2 L_n) (1 + O(1/L_n)), positive for large n.
* Jacobi (Lemmas 5.1 to 5.4). T = (q_0-1)/(q_1-1), A_J = 2 q_0/(T - q_0),
  1/B_J = q_0 (1 + 1/A_J) - 1, S_J = B_J R_1 match R_0..R_3. The defect at R_4
  is E_J(4) = log(R_4/R_4^J) = log(qq_2(A_J, B_J)/q_2). Holland:
  Q_n := -E_J(4) = 2/(n^3 L_n) (1 + O(1/L_n)), positive.
* Finite-free (Lemmas 6.1, 6.2). D = B_J/2 is fixed, (A, B, C) solve
  qq_k(A, B) qq_k(C, D) = q_k for k = 0, 1, 2, and S = B R_1; this matches
  R_0..R_4. Holland matches nothing further. The R_5 defect measured here is
  E_F(5) = log(R_5/R_5^F) = log(qq_3(A, B) qq_3(C, D)/q_3); it is the phase-1
  quantity, and its value depends on the free choice D = B_J/2, so the probe
  also reports it for D = theta B_J at a few theta.

L_n = L_{2n-2}, where L_x solves x = L_x (pi e^{L_x} + 3/4) (Holland eq. 16).

Route A, the exact table. zeta/li.py's Mellin route, gamma(m) = 8 m! b_m with
b_m = J_{m-1} - J_m/4, J_k = I_k/(4^k (2k)!), I_k = int_0^inf u^{2k} e^{u/4}
omega(e^u) du, evaluated one index at a time with breakpoints placed at the
saddle so that the peak (width about 0.03 at k = 3200) is resolved. It is
validated against zeta.li.xi_taylor_coefficients, whose integral and Cauchy
routes are pinned against each other in tests/test_li.py, before any large-n
number is produced, and it is re-run at a second working precision.

Route B, the saddle. In the single-term regime log I_y is the Laplace integral
of Psi(u) = 2y log u + u/4 - pi e^u, whose saddle is pi e^{u*} = 1/4 + 2y/u*
(hunts/gauss_positivity section 3). The Laplace series is carried to M
corrections (each a power of u*/y), giving log gamma(x) as an analytic function
of real x, and the saddle expansion of log R_j is its Taylor polynomial in j,

    log R_j = sum_{i=1}^{7} g_i(n) j^i,   g_i = (d/dn)^i log gamma(n) / i!.

It is carried with M = 6. Its stated error at each j is |g_8| j^8 + |g_9| j^9
(Taylor truncation) plus the larger of the last two Laplace increments,
|M6 - M5| and |M5 - M4|, evaluated directly at n + j. The rule first planned,
M = 4 with |M4 - M3|, missed at n = 150 and is still reported (M_PRESET).
Route B shares no quadrature with route A.

Grade: measured. Nothing here bears on RH.
"""

from __future__ import annotations

import argparse
import json
import platform
import subprocess
import sys
import time
from pathlib import Path

import mpmath
from mpmath import mp, mpf

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from zeta.core import omega  # noqa: E402

#: guard digits carried above the requested precision and discarded on return
GUARD = 15
#: zeta/li.py's _gamma_integral breakpoints, always included
PTS_LI = ("0", "0.5", "1", "2", "3", "5", "7")

N_LO, N_HI = 50, 3200
J_MAX = 5  # R_0..R_5 enter the three defects
SUBGRID = (50, 60, 70, 80, 100, 125, 150, 200, 250, 300, 400, 500, 600, 800,
           1000, 1250, 1600, 2000, 2400, 2800, 3200)
THETAS = ("0.125", "0.25", "0.5", "0.6", "0.7", "0.8", "0.82", "0.84", "0.86", "0.88", "0.9", "0.92", "0.95")
#: Laplace corrections carried by route B. The run of 2026-10-18 first used
#: M = 4 with |M4 - M3| as the Laplace part of the stated error; that rule missed
#: at n = 150 (RESULTS.md section 3), so route B now carries M = 6 and states the
#: larger of its last two increments, and the M = 4 rule is still reported.
M_ROUTE_B = 6
M_PRESET = 4
#: options for mp.taylor in route B (see saddle_expansion)
TAYLOR_OPTS = {"relative": True, "addprec": 60}
#: route B alone, beyond the exact table, to read the limiting constants
LARGE_NS = ("1e4", "1e5", "1e6", "1e8", "1e10", "1e12", "1e16", "1e20")
THETA_NS = (100, 400, 1600, 3200)


def s(x, digits: int = 15) -> str:
    return mpmath.nstr(x, digits)


# ---------------------------------------------------------------------------
# the saddle and Holland's L_x
# ---------------------------------------------------------------------------


def saddle(y):
    """u* with pi e^{u*} = 1/4 + 2y/u*, at the ambient precision."""
    y = mpf(y)
    g = mp.log(2 * y / mp.pi)
    guess = g - mp.log(g) if g > 2 else mpf(1)
    return mp.findroot(lambda u: mp.pi * mp.exp(u) - mpf(1) / 4 - 2 * y / u, guess)


def holland_L(x):
    """L_x with x = L_x (pi e^{L_x} + 3/4), Holland eq. (16), real x > 3."""
    x = mpf(x)
    g = mp.log(x / mp.pi)
    return mp.findroot(lambda L: L * (mp.pi * mp.exp(L) + mpf(3) / 4) - x, g - mp.log(g))


def script_L(n):
    """Holland's L_n := L_{2n-2}."""
    return holland_L(2 * n - 2)


# ---------------------------------------------------------------------------
# route A: the exact moments
# ---------------------------------------------------------------------------


def _omega_series(x):
    """omega(x) = sum_{n>=1} e^{-pi n^2 x}, the series zeta.core.omega sums, at the
    ambient precision, factored as e^{-pi x} (1 + sum_{n>=2} e^{-pi (n^2-1) x})."""
    eps = mpf(2) ** (-(mp.prec + 20))
    tot, n = mpf(1), 2
    while True:
        t = mp.exp(-mp.pi * (n * n - 1) * x)
        tot += t
        if t < eps:
            break
        n += 1
    return mp.exp(-mp.pi * x) * tot


def _log_f(k: int, t):
    """log of the integrand u^{2k} e^{u/4} omega(e^u) at u = t."""
    return 2 * k * mp.log(t) + t / 4 + mp.log(_omega_series(mp.exp(t)))


def _peak_width(k: int):
    u = saddle(k)
    return u, 1 / mp.sqrt(2 * mpf(k) / u**2 + mp.pi * mp.exp(u))


def window(k: int, decades) -> tuple:
    """[lo, hi] outside which the integrand is below its peak by `decades` decades.

    The integrand is unimodal for k >= 2 (its log-derivative 2k/u + 1/4 +
    d log omega(e^u)/du is positive below the saddle and negative above), so
    each side has exactly one crossing; both are found by bisection at 20 digits.
    """
    with mp.workdps(20):
        u, _ = _peak_width(k)
        level = _log_f(k, u) - decades * mp.log(10)
        g = lambda t: _log_f(k, t) - level  # noqa: E731
        lo = mp.findroot(g, (u * mpf(10) ** -12, u), solver="bisect")
        hi = mp.findroot(g, (u, u + 6), solver="bisect")
    return lo, hi


def moments_trapezoid(k0: int, k1: int, dps: int, rho: int = 8) -> tuple[dict, mpf]:
    """I_k for k0 <= k <= k1 by the trapezoid rule on one shared grid.

    The grid spans the union of the windows, with step sigma_min/rho where
    sigma_min = 1/sqrt(-Psi'') at k1 is the narrowest peak. The integrand is
    entire in a strip about the real axis and negligible at both ends, so the
    rule converges geometrically in 1/h; the weight e^{u/4} omega(e^u) is
    evaluated once per node and u^{2k} by one multiplication per index. The
    returned deviation is max_k |coarse/fine - 1|, the coarse rule using
    every other node (step 2h): it bounds the coarse error and so, a fortiori,
    the error of the fine rule, which is the one returned.
    """
    with mp.workdps(dps + GUARD):
        decades = dps + GUARD + 10
        lo = window(k0, decades)[0]
        hi = window(k1, decades)[1]
        _, sigma = _peak_width(k1)
        N = int(mp.ceil((hi - lo) * rho / sigma))
        N += N % 2
        h = (hi - lo) / N
        ts = [lo + i * h for i in range(N + 1)]
        W = [mp.exp(t / 4) * _omega_series(mp.exp(t)) for t in ts]
        t2 = [t * t for t in ts]
        pw = [mp.power(t, 2 * k0) * w for t, w in zip(ts, W)]
        out, worst = {}, mpf(0)
        for k in range(k0, k1 + 1):
            ends = (pw[0] + pw[-1]) / 2
            fine = h * (mp.fsum(pw) - ends)
            coarse = 2 * h * (mp.fsum(pw[::2]) - ends)
            out[k] = +fine
            worst = max(worst, abs(coarse / fine - 1))
            pw = [a * b for a, b in zip(pw, t2)]
        return out, worst


def moments(ks, dps: int, block: int = 64, log_every: int = 0) -> tuple[dict, mpf]:
    """Route A over a contiguous index range, block by block."""
    ks = list(ks)
    out, worst = {}, mpf(0)
    for i in range(0, len(ks), block):
        chunk = ks[i:i + block]
        part, dev = moments_trapezoid(chunk[0], chunk[-1], dps)
        out.update(part)
        worst = max(worst, dev)
        if log_every and (i // block) % log_every == 0:
            print(f"  [route A dps={dps}] k={chunk[0]}..{chunk[-1]} "
                  f"coarse/fine={s(dev, 3)}", flush=True)
    return out, worst


def moment_quad(k: int, dps: int):
    """Check route: I_k by adaptive tanh-sinh (mp.quad) over zeta.core.omega.

    Shares no node, no rule and no omega implementation with
    moments_trapezoid. Breakpoints: zeta/li.py's _gamma_integral points plus
    the saddle and u* +- {4, 12} peak widths; intervals whose nearer endpoint
    sits more than dps + GUARD + 10 decades below the peak are dropped, which
    the unimodality of the integrand makes safe.
    """
    with mp.workdps(dps + GUARD):
        u, w = _peak_width(k)
        pts = {mpf(p) for p in PTS_LI} | {u + c * w for c in (-12, -4, 0, 4, 12) if u + c * w > 0}
        top = max(mpf(7), u + 3)
        pts = sorted(p for p in pts if p < top) + [top]
        cut = (dps + GUARD + 10) * mp.log(10)
        lpeak = _log_f(k, u)
        kept = []
        for a, b in zip(pts[:-1], pts[1:]):
            near = b if b < u else a
            if a <= u <= b or (near > 0 and _log_f(k, near) > lpeak - cut):
                kept.append((a, b))

        def f(t):
            return mp.power(t, 2 * k) * mp.exp(t / 4) * omega(mp.exp(t), mp.dps)

        return +mp.fsum(mp.quad(f, [a, b]) for a, b in kept)


def log_gamma_from_moments(I: dict, m: int, dps: int):
    """log gamma(m) = log 8 + log m! + log(J_{m-1} - J_m/4), m >= 1."""
    with mp.workdps(dps + GUARD):
        def logJ(k):
            return mp.log(I[k]) - k * mp.log(4) - mp.loggamma(2 * k + 1)

        a, b = logJ(m - 1), logJ(m)
        return mp.log(8) + mp.loggamma(m + 1) + a + mp.log1p(-mp.exp(b - a) / 4)


# ---------------------------------------------------------------------------
# route B: the Laplace series and the saddle expansion of log R_j
# ---------------------------------------------------------------------------


def log_I_laplace(y, M: int):
    """Laplace series for log int exp(2y log u + u/4 - pi e^u) du, M corrections.

    With A = -Psi''(u*) and t = u - u*, expand exp(sum_{k>=3} Psi_k t^k/k!)
    with Psi_k weighted by s^{k-2}, keep total weight <= 2M, and take Gaussian
    moments E t^{2m} = (2m-1)!!/A^m. Weight 2 is 5 Psi_3^2/(24 A^3) +
    Psi_4/(8 A^2), the textbook first correction; each further even weight is
    one more power of u*/y.
    """
    y = mpf(y)
    u = saddle(y)
    eu = mp.exp(u)
    A = 2 * y / u**2 + mp.pi * eu
    psi = {
        k: 2 * y * (-1) ** (k - 1) * mp.factorial(k - 1) / u**k - mp.pi * eu
        for k in range(3, 2 * M + 3)
    }
    # p_w: (coefficient, t-degree) of Psi_{w+2} t^{w+2}/(w+2)!
    p = {w: (psi[w + 2] / mp.factorial(w + 2), w + 2) for w in range(1, 2 * M + 1)}
    e = [{0: mpf(1)}]
    for w in range(1, 2 * M + 1):
        acc: dict = {}
        for k in range(1, w + 1):
            c, deg = p[k]
            for d, v in e[w - k].items():
                acc[d + deg] = acc.get(d + deg, mpf(0)) + k * c * v
        e.append({d: v / w for d, v in acc.items()})
    corr = mpf(0)
    for w in range(2, 2 * M + 1, 2):
        for d, v in e[w].items():
            if d % 2 == 0:
                corr += v * mp.fac2(d - 1) / A ** (d // 2)
    psi0 = 2 * y * mp.log(u) + u / 4 - mp.pi * eu
    return psi0 + mp.log(2 * mp.pi / A) / 2 + mp.log1p(corr)


def log_gamma_saddle(x, M: int):
    """log gamma(x) for real x from the Laplace series of I_{x-1} and I_x."""
    def logJ(z):
        return log_I_laplace(z, M) - z * mp.log(4) - mp.loggamma(2 * z + 1)

    a, b = logJ(x - 1), logJ(x)
    return mp.log(8) + mp.loggamma(x + 1) + a + mp.log1p(-mp.exp(b - a) / 4)


def saddle_expansion(n: int, dps: int, order: int = 9, M: int = M_ROUTE_B) -> list:
    """[g_0, g_1, ..., g_order] with g_i = (d/dn)^i log gamma(n) / i!, route B."""
    with mp.workdps(dps + GUARD):
        # relative=True scales the difference step with n, without which the
        # high derivatives of a function of size n log n lose all their digits;
        # addprec=60 because the default 10 left the 9th derivative of log Gamma
        # at n = 1e20 good to 13 digits only (differentiation_check measures it)
        return [+c for c in mp.taylor(lambda x: log_gamma_saddle(x, M), mpf(n), order,
                                      **TAYLOR_OPTS)]


def differentiation_check(n: int, dps: int, order: int = 9) -> mpf:
    """The same mp.taylor call on log Gamma(x+1), against exact polygammas."""
    with mp.workdps(dps + GUARD):
        got = mp.taylor(lambda x: mp.loggamma(x + 1), mpf(n), order, **TAYLOR_OPTS)
        worst = mpf(0)
        for i in range(1, order + 1):
            exact = mp.polygamma(i - 1, n + 1) / mp.factorial(i)
            worst = max(worst, abs(got[i] / exact - 1))
        return worst


def log_R_from_expansion(g: list, j: int, top: int = 7):
    return mp.fsum(g[i] * mpf(j) ** i for i in range(1, top + 1))


# ---------------------------------------------------------------------------
# the three models and their defects (shared by both routes)
# ---------------------------------------------------------------------------


def log_qq(k: int, U, V):
    """log qq_k(U, V); U=None is the Laguerre limit U = infinity."""
    t = mp.log1p(1 / (V + k))
    if U is not None:
        t -= mp.log1p(1 / (U + k))
    return t


def log_q_from_log_R(lr: list) -> list:
    """log q_k = 2 log R_{k+1} - log R_k - log R_{k+2}, with lr[0] = 0."""
    return [2 * lr[k + 1] - lr[k] - lr[k + 2] for k in range(len(lr) - 2)]


def laguerre(lq: list) -> dict:
    BL = 1 / mp.expm1(lq[0])
    return {"B_L": BL, "D3": log_qq(1, None, BL) - lq[1],
            "match_residual": abs(log_qq(0, None, BL) - lq[0])}


def jacobi(lq: list) -> dict:
    q0 = mp.exp(lq[0])
    T = mp.expm1(lq[0]) / mp.expm1(lq[1])
    AJ = 2 * q0 / (T - q0)
    BJ = 1 / (q0 * (1 + 1 / AJ) - 1)
    res = max(abs(log_qq(k, AJ, BJ) - lq[k]) for k in (0, 1))
    return {"A_J": AJ, "B_J": BJ, "E_J4": log_qq(2, AJ, BJ) - lq[2], "match_residual": res}


def finite_free(lq: list, BJ, theta, guess) -> dict:
    """Solve qq_k(A,B) qq_k(C,D) = q_k (k = 0,1,2) with D = theta B_J.

    Newton runs in (log A, log B, log(C - D)), which scales the three unknowns
    (A ~ 10 B ~ 100 (C - D) at n = 3200) and keeps C > D by construction.
    """
    D = mpf(theta) * BJ

    def eqs(a, b, c):
        A, B, C = mp.exp(a), mp.exp(b), D + mp.exp(c)
        return [log_qq(k, A, B) + log_qq(k, C, D) - lq[k] for k in range(3)]

    gA, gB, gC = guess
    a, b, c = mp.findroot(eqs, (mp.log(gA), mp.log(gB), mp.log(gC - D)),
                          tol=mp.mpf(10) ** (-(mp.dps - 8)))
    A, B, C = mp.exp(a), mp.exp(b), D + mp.exp(c)
    res = max(abs(v) for v in eqs(a, b, c))
    return {"A": A, "B": B, "C": C, "D": D, "match_residual": res,
            "E_F5": log_qq(3, A, B) + log_qq(3, C, D) - lq[3]}


def ff_guess(jac: dict, n: int, Ln, theta="0.5") -> tuple:
    """Holland's asymptotic solution (Sec. 6): A ~ (6/5) A_J, B - B_J ~ n/(3 L_n),
    C - D ~ n/(24 L_n), stated for D = B_J/2."""
    D = mpf(theta) * jac["B_J"]
    return (mpf(6) / 5 * jac["A_J"], jac["B_J"] + n / (3 * Ln), D + n / (24 * Ln))


def defects(lr: list, n: int, Ln, guess=None, theta="0.5") -> dict:
    lq = log_q_from_log_R(lr)
    lag, jac = laguerre(lq), jacobi(lq)
    ff = finite_free(lq, jac["B_J"], theta, guess or ff_guess(jac, n, Ln, theta))
    return {"lq": lq, "lag": lag, "jac": jac, "ff": ff}


def theta_continuation(d: dict, theta, start=None, max_halvings: int = 30) -> dict:
    """The finite-free solve at D = theta B_J, reached from `start` = (theta0, ff0)
    (default Holland's theta = 1/2) by adaptive continuation in log theta: each
    step starts from the last solution with C - D extrapolated from the last two,
    a failed step is halved, a good one lengthened, and the walk raises after
    `max_halvings` consecutive halvings."""
    lq, BJ = d["lq"], d["jac"]["B_J"]
    th, ff = start if start is not None else (mpf(1) / 2, d["ff"])
    target = mpf(theta)
    path = [(th, ff)]
    step = (mp.log(target) - mp.log(th)) / 4
    halvings = 0
    while th != target:
        nxt = mp.exp(mp.log(th) + step)
        if (step > 0 and nxt > target) or (step < 0 and nxt < target):
            nxt = target
        gap = ff["C"] - ff["D"]
        if len(path) > 1:
            pth, pff = path[-2]
            slope = mp.log(gap / (pff["C"] - pff["D"])) / mp.log(th / pth)
            gap = gap * (nxt / th) ** slope
        try:
            new = finite_free(lq, BJ, nxt, (ff["A"], ff["B"], nxt * BJ + gap))
        except Exception:  # halve and retry; the walk raises below if it stalls
            halvings += 1
            if halvings > max_halvings:
                raise RuntimeError(f"continuation stalled at theta = {mp.nstr(th, 12)}")
            step /= 2
            continue
        halvings = 0
        th, ff = nxt, new
        path.append((th, ff))
        step *= mpf(3) / 2
    return ff


def theta_scan(d: dict, thetas, bisections: int = 40) -> dict:
    """E_F5 along a theta grid (continuation outward from 1/2 in each direction),
    and, where it changes sign between grid points, the crossing by bisection."""
    half = mpf(1) / 2
    sols = {half: d["ff"]}
    failed = {}
    for side in (sorted([mpf(t) for t in thetas if mpf(t) > half]),
                 sorted([mpf(t) for t in thetas if mpf(t) < half], reverse=True)):
        start = (half, d["ff"])
        for th in side:
            try:
                sols[th] = theta_continuation(d, th, start)
                start = (th, sols[th])
            except Exception as exc:  # recorded, and the walk on this side stops
                failed[th] = repr(exc)[:160]
                break
    order = sorted(sols)
    crossing = None
    for t0, t1 in zip(order[:-1], order[1:]):
        if (sols[t0]["E_F5"] > 0) != (sols[t1]["E_F5"] > 0):
            lo, hi, flo = t0, t1, sols[t0]
            for _ in range(bisections):
                mid = (lo + hi) / 2
                fm = theta_continuation(d, mid, (lo, flo))
                if (fm["E_F5"] > 0) == (flo["E_F5"] > 0):
                    lo, flo = mid, fm
                else:
                    hi = mid
            crossing = {"theta": (lo + hi) / 2, "ff": flo}
            break
    return {"solutions": sols, "failed": failed, "crossing": crossing}


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def validate_against_li(dps: int = 50, m_lo: int = 17, m_hi: int = 47) -> dict:
    """Route A must reproduce zeta/li.py's table before any large-n number.

    zeta/li.py's integral and Cauchy routes agree bit for bit (tests/test_li.py);
    its cached dps-50 table runs to n = 48. The trapezoid needs the integrand
    negligible at the window's ends, which u^{2k} gives once k is moderate, so
    the comparison starts at m = 17 (indices k >= 16) and the main range starts
    at k = 49; both checks, against the table and against moment_quad, raise.
    """
    from zeta.li import xi_taylor_coefficients

    table = xi_taylor_coefficients(m_hi + 1, dps=dps, cache=True)
    I, dev = moments(range(m_lo - 1, m_hi + 1), dps, block=16)
    worst = mpf(0)
    with mp.workdps(dps + GUARD):
        for m in range(m_lo, m_hi + 1):
            mine = log_gamma_from_moments(I, m, dps)
            worst = max(worst, abs(mine - mp.log(table[m])))
    if worst > mpf(10) ** (-(dps - 5)):
        raise RuntimeError(f"route A disagrees with zeta/li.py: max |d log gamma| = {worst}")
    return {"dps": dps, "m_range": [m_lo, m_hi], "max_abs_dlog_gamma": s(worst, 4),
            "coarse_fine_deviation": s(dev, 3)}


def git_head() -> str:
    try:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                              text=True, check=True).stdout.strip()
    except Exception as exc:  # recorded, not swallowed: the JSON says why it is missing
        return f"unavailable: {exc!r}"


def time_unit(dps: int, dps_check: int) -> None:
    for k0 in (49, 800, 3142):
        t0 = time.perf_counter()
        moments_trapezoid(k0, k0 + 63, dps)
        print(f"[unit] route A block k={k0}..{k0 + 63} dps={dps}: "
              f"{time.perf_counter() - t0:.2f} s")
    for k in (49, 3205):
        t0 = time.perf_counter()
        moment_quad(k, dps_check)
        print(f"[unit] check route k={k} dps={dps_check}: {time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    saddle_expansion(3200, dps)
    print(f"[unit] route B expansion n=3200 order 9 M={M_ROUTE_B} dps={dps}: "
          f"{time.perf_counter() - t0:.2f} s")


def run(dps: int, dps_check: int, out: Path) -> dict:
    t_start = time.perf_counter()
    report: dict = {
        "hunt": "jensen_wedge", "phase": 0, "grade": "measured",
        "source": "Holland, arXiv:2608.08682v1, Lemmas 4.3, 5.3, 5.4, 6.1, 6.2; eq. (16)",
        "git_head": git_head(), "python": platform.python_version(),
        "mpmath": mpmath.__version__, "dps": dps, "dps_check": dps_check,
        "n_range": [N_LO, N_HI],
    }

    print("[validate] route A against zeta/li.py", flush=True)
    # the dps-50 table to n = 48, and the dps-30 table to n = 128, which reaches
    # into the main range n >= 50
    report["validation_vs_li"] = [validate_against_li(50, 17, 47),
                                  validate_against_li(30, 17, 127)]
    print(f"  {report['validation_vs_li']}", flush=True)

    # --- route A: every index the dense scan needs -------------------------
    ks = range(N_LO - 1, N_HI + J_MAX + 1)
    t0 = time.perf_counter()
    I, worst_est = moments(ks, dps, log_every=10)
    t_moments = time.perf_counter() - t0
    with mp.workdps(dps + GUARD):
        ell = {m: log_gamma_from_moments(I, m, dps) for m in range(N_LO, N_HI + J_MAX + 1)}

    # the check route (tanh-sinh, zeta.core.omega, higher precision) on the subgrid
    ks_check = sorted({k for n in SUBGRID for k in range(n - 1, n + J_MAX + 1)})
    t0 = time.perf_counter()
    I2 = {k: moment_quad(k, dps_check) for k in ks_check}
    t_check = time.perf_counter() - t0
    moment_dev, prec_dev = mpf(0), mpf(0)
    with mp.workdps(dps_check + GUARD):
        for k in ks_check:
            moment_dev = max(moment_dev, abs(I[k] / I2[k] - 1))
        for n in SUBGRID:
            base2 = log_gamma_from_moments(I2, n, dps_check)
            for j in range(1, J_MAX + 1):
                lr2 = log_gamma_from_moments(I2, n + j, dps_check) - base2
                prec_dev = max(prec_dev, abs(lr2 - (ell[n + j] - ell[n])))
    if prec_dev > mpf(10) ** (-(dps - 10)):
        raise RuntimeError(f"route A and its check route disagree: max |d log R| = {prec_dev}")
    report["route_A"] = {
        "moments_computed": len(ks), "k_range": [ks[0], ks[-1]],
        "max_coarse_fine_deviation": s(worst_est, 3),
        "check_route_indices": len(ks_check),
        "max_rel_dev_vs_check_route": s(moment_dev, 3),
        "max_abs_dlogR_vs_check_route": s(prec_dev, 3),
        "check_seconds": round(t_check, 1),
        "seconds": round(t_moments, 1),
    }
    print(f"[route A] {report['route_A']}", flush=True)

    # --- dense scan on route A ---------------------------------------------
    dense = []
    guess = None
    with mp.workdps(dps + GUARD):
        for n in range(N_LO, N_HI + 1):
            lr = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, J_MAX + 1)]
            Ln = script_L(n)
            d = defects(lr, n, Ln, guess)
            ff = d["ff"]
            guess = (ff["A"], ff["B"], ff["C"])
            dense.append((n, Ln, d))

    def signs(vals):
        pos = sum(1 for v in vals if v > 0)
        neg = sum(1 for v in vals if v < 0)
        flips = [dense[i + 1][0] for i in range(len(vals) - 1)
                 if (vals[i] > 0) != (vals[i + 1] > 0)]
        return {"positive": pos, "negative": neg, "zero": len(vals) - pos - neg,
                "sign_changes_at_n": flips}

    D3 = [d["lag"]["D3"] for _, _, d in dense]
    EJ4 = [d["jac"]["E_J4"] for _, _, d in dense]
    EF5 = [d["ff"]["E_F5"] for _, _, d in dense]
    r3 = [n**2 * Ln * v / 2 for (n, Ln, _), v in zip(dense, D3)]
    r4 = [-(n**3) * Ln * v / 2 for (n, Ln, _), v in zip(dense, EJ4)]
    r5 = [n**4 * Ln * v for (n, Ln, _), v in zip(dense, EF5)]
    params_ok = all(
        d["jac"]["A_J"] > 0 and d["jac"]["B_J"] > 0 and d["ff"]["A"] > 0 and d["ff"]["B"] > 0
        and d["ff"]["C"] > d["ff"]["D"] > 0 for _, _, d in dense
    )
    report["dense_route_A"] = {
        "n_count": len(dense),
        "laguerre_D3": {**signs(D3), "min_n2L_D3_over_2": s(min(r3), 8),
                        "max_n2L_D3_over_2": s(max(r3), 8)},
        "jacobi_E_J4": {**signs(EJ4), "min_minus_n3L_EJ4_over_2": s(min(r4), 8),
                        "max_minus_n3L_EJ4_over_2": s(max(r4), 8)},
        "finite_free_E_F5": {**signs(EF5), "min_n4L_EF5": s(min(r5), 8),
                             "max_n4L_EF5": s(max(r5), 8)},
        "all_parameters_positive_and_C_gt_D": params_ok,
        "max_match_residual": s(max(max(d["lag"]["match_residual"], d["jac"]["match_residual"],
                                        d["ff"]["match_residual"]) for _, _, d in dense), 3),
    }
    print(f"[dense] {json.dumps(report['dense_route_A'], indent=1)}", flush=True)

    # --- the subgrid table, both routes ------------------------------------
    by_n = {n: (Ln, d) for n, Ln, d in dense}
    rows = []
    t0 = time.perf_counter()
    for n in SUBGRID:
        Ln, dA = by_n[n]
        with mp.workdps(dps + GUARD):
            g = saddle_expansion(n, dps, order=9, M=M_ROUTE_B)
            g_pre = saddle_expansion(n, dps, order=9, M=M_PRESET)
            lrA = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, J_MAX + 1)]
            lrB = [mpf(0)] + [log_R_from_expansion(g, j, 7) for j in range(1, J_MAX + 1)]
            lrB9 = [mpf(0)] + [log_R_from_expansion(g, j, 9) for j in range(1, J_MAX + 1)]
            lrBpre = [mpf(0)] + [log_R_from_expansion(g_pre, j, 7) for j in range(1, J_MAX + 1)]
            # the Laplace ladder, evaluated directly (no Taylor truncation)
            direct = {}
            for M in range(2, M_ROUTE_B + 1):
                base = log_gamma_saddle(mpf(n), M)
                direct[M] = [log_gamma_saddle(mpf(n + j), M) - base for j in range(J_MAX + 1)]

            def inc(M, j):
                return abs(direct[M][j] - direct[M - 1][j])

            tail = [abs(g[8]) * j**8 + abs(g[9]) * j**9 for j in range(J_MAX + 1)]
            stated = [tail[j] + max(inc(M_ROUTE_B, j), inc(M_ROUTE_B - 1, j))
                      for j in range(J_MAX + 1)]
            dev = [abs(lrA[j] - lrB[j]) for j in range(J_MAX + 1)]
            within = all(dev[j] <= stated[j] for j in range(1, J_MAX + 1))
            tail_pre = [abs(g_pre[8]) * j**8 + abs(g_pre[9]) * j**9 for j in range(J_MAX + 1)]
            stated_pre = [tail_pre[j] + inc(M_PRESET, j) for j in range(J_MAX + 1)]
            dev_pre = [abs(lrA[j] - lrBpre[j]) for j in range(J_MAX + 1)]
            within_pre = all(dev_pre[j] <= stated_pre[j] for j in range(1, J_MAX + 1))
            ladder = {str(M): [s(abs(lrA[j] - direct[M][j]), 3) for j in (1, J_MAX)]
                      for M in range(2, M_ROUTE_B + 1)}
            guess = (dA["ff"]["A"], dA["ff"]["B"], dA["ff"]["C"])
            dB = defects(lrB, n, Ln, guess)
            alt = [defects(lrB9, n, Ln, guess),
                   defects([mpf(0)] + direct[M_ROUTE_B][1:], n, Ln, guess),
                   defects([mpf(0)] + direct[M_ROUTE_B - 1][1:], n, Ln, guess)]

            def triple(d):
                return (d["lag"]["D3"], d["jac"]["E_J4"], d["ff"]["E_F5"])

            a3, a4, a5 = triple(dA)
            b3, b4, b5 = triple(dB)
            spread = [max(abs(x - triple(y)[i]) for y in alt)
                      for i, x in enumerate((b3, b4, b5))]
            ff, jac = dA["ff"], dA["jac"]
            rows.append({
                "n": n, "L_n": s(Ln, 12), "u_saddle": s(saddle(n), 12),
                "log_gamma_A": s(ell[n], 20), "log_gamma_B": s(g[0], 20),
                "q_minus_1": [s(mp.expm1(v), 12) for v in dA["lq"]],
                "g": [s(c, 12) for c in g[1:8]],
                "n_pow_i_minus_1_g_i": [s(mpf(n) ** (i - 1) * g[i], 10) for i in range(1, 8)],
                "g8": s(g[8], 4), "g9": s(g[9], 4),
                "logR_A_minus_B": [s(dev[j], 3) for j in range(1, J_MAX + 1)],
                "logR_B_stated_error": [s(stated[j], 3) for j in range(1, J_MAX + 1)],
                "route_B_within_stated_error": within,
                "preset_rule_M4": {
                    "logR_A_minus_B": [s(dev_pre[j], 3) for j in range(1, J_MAX + 1)],
                    "stated_error": [s(stated_pre[j], 3) for j in range(1, J_MAX + 1)],
                    "within": within_pre},
                "laplace_ladder_abs_dev_j1_j5": ladder,
                "D3_A": s(a3, 15), "D3_B": s(b3, 15), "D3_B_spread": s(spread[0], 3),
                "n2L_D3_over_2": s(n**2 * Ln * a3 / 2, 12),
                "E_J4_A": s(a4, 15), "E_J4_B": s(b4, 15), "E_J4_B_spread": s(spread[1], 3),
                "minus_n3L_EJ4_over_2": s(-(n**3) * Ln * a4 / 2, 12),
                "E_F5_A": s(a5, 15), "E_F5_B": s(b5, 15), "E_F5_B_spread": s(spread[2], 3),
                "n4L_EF5": s(n**4 * Ln * a5, 12),
                "signs_agree_A_B": [(a3 > 0) == (b3 > 0), (a4 > 0) == (b4 > 0),
                                    (a5 > 0) == (b5 > 0)],
                "B_resolves_sign": [spread[0] < abs(b3), spread[1] < abs(b4),
                                    spread[2] < abs(b5)],
                "A_J": s(jac["A_J"], 12), "B_J": s(jac["B_J"], 12),
                "ff_A": s(ff["A"], 12), "ff_B": s(ff["B"], 12),
                "ff_C": s(ff["C"], 12), "ff_D": s(ff["D"], 12),
                "A_over_A_J": s(ff["A"] / jac["A_J"], 10),
                "B_minus_B_J_times_L_over_n": s((ff["B"] - jac["B_J"]) * Ln / n, 10),
                "C_minus_D_times_L_over_n": s((ff["C"] - ff["D"]) * Ln / n, 10),
                "A_over_B": s(ff["A"] / ff["B"], 8),
                "C_minus_D_over_D": s((ff["C"] - ff["D"]) / ff["D"], 8),
            })
        print(f"[subgrid] n={n} D3={rows[-1]['D3_A']} EJ4={rows[-1]['E_J4_A']} "
              f"EF5={rows[-1]['E_F5_A']} B-within={within} "
              f"B-resolves={rows[-1]['B_resolves_sign']}", flush=True)
    report["subgrid"] = rows
    report["route_B_seconds"] = round(time.perf_counter() - t0, 1)

    # local exponent of |E_F5| between subgrid points (route A)
    slopes = []
    for a, b in zip(SUBGRID[:-1], SUBGRID[1:]):
        va, vb = by_n[a][1]["ff"]["E_F5"], by_n[b][1]["ff"]["E_F5"]
        slopes.append({"n_pair": [a, b],
                       "dlog_absEF5_dlog_n": s(mp.log(abs(vb / va)) / mp.log(mpf(b) / a), 6)})
    report["E_F5_local_exponent"] = slopes

    # dependence of the R_5 defect on Holland's free choice D = B_J/2, by
    # continuation in theta outward from Holland's solution, with the sign
    # crossing located where the grid brackets one
    theta_rows = []
    with mp.workdps(dps + GUARD):
        for n in THETA_NS:
            Ln, dA = by_n[n]
            scan = theta_scan(dA, THETAS)
            row = {"n": n, "B_J": s(dA["jac"]["B_J"], 12), "grid": {}, "failed": {
                s(t, 6): e for t, e in scan["failed"].items()}}
            for th, ff in sorted(scan["solutions"].items()):
                row["grid"][s(th, 6)] = {
                    "E_F5": s(ff["E_F5"], 12), "n4L_EF5": s(n**4 * Ln * ff["E_F5"], 10),
                    "A_over_B": s(ff["A"] / ff["B"], 8),
                    "C_minus_D": s(ff["C"] - ff["D"], 10),
                    "C_minus_D_over_D": s((ff["C"] - ff["D"]) / ff["D"], 8),
                    "match_residual": s(ff["match_residual"], 3)}
            c = scan["crossing"]
            if c is not None:
                ff = c["ff"]
                row["crossing"] = {"theta": s(c["theta"], 12),
                                   "C_minus_D_over_D": s((ff["C"] - ff["D"]) / ff["D"], 10),
                                   "A_over_B": s(ff["A"] / ff["B"], 10),
                                   "C_minus_D": s(ff["C"] - ff["D"], 10)}
            else:
                row["crossing"] = None
            theta_rows.append(row)
            print(f"[theta] n={n} crossing={row['crossing']} failed={list(row['failed'])}",
                  flush=True)
    report["theta_sensitivity"] = theta_rows

    # route B alone at large n: the limiting constants of Lemmas 4.3, 5.4 and Sec. 6
    large = []
    t0 = time.perf_counter()
    for n_str in LARGE_NS:
        n = int(mpf(n_str))
        dps_n = int(5 * mp.log10(n)) + 50
        with mp.workdps(dps_n + GUARD):
            Ln = script_L(n)
            g = saddle_expansion(n, dps_n, order=9, M=M_ROUTE_B)
            g3 = saddle_expansion(n, dps_n, order=9, M=M_ROUTE_B - 1)
            lr7 = [mpf(0)] + [log_R_from_expansion(g, j, 7) for j in range(1, J_MAX + 1)]
            lr9 = [mpf(0)] + [log_R_from_expansion(g, j, 9) for j in range(1, J_MAX + 1)]
            lr3 = [mpf(0)] + [log_R_from_expansion(g3, j, 7) for j in range(1, J_MAX + 1)]
            d = defects(lr7, n, Ln)
            guess = (d["ff"]["A"], d["ff"]["B"], d["ff"]["C"])
            alt = [defects(lr9, n, Ln, guess), defects(lr3, n, Ln, guess)]

            def spread(path):
                a, b = path
                return max(abs(d[a][b] - x[a][b]) for x in alt)

            ff, jac = d["ff"], d["jac"]
            large.append({
                "n": n_str, "dps": dps_n, "L_n": s(Ln, 12),
                "D3": s(d["lag"]["D3"], 12), "D3_spread": s(spread(("lag", "D3")), 3),
                "n2L_D3_over_2": s(mpf(n) ** 2 * Ln * d["lag"]["D3"] / 2, 10),
                "E_J4": s(jac["E_J4"], 12), "E_J4_spread": s(spread(("jac", "E_J4")), 3),
                "minus_n3L_EJ4_over_2": s(-mpf(n) ** 3 * Ln * jac["E_J4"] / 2, 10),
                "E_F5": s(ff["E_F5"], 12), "E_F5_spread": s(spread(("ff", "E_F5")), 3),
                "n4L_EF5": s(mpf(n) ** 4 * Ln * ff["E_F5"], 10),
                "n4_EF5": s(mpf(n) ** 4 * ff["E_F5"], 10),
                "A_over_A_J": s(ff["A"] / jac["A_J"], 10),
                "B_minus_B_J_times_L_over_n": s((ff["B"] - jac["B_J"]) * Ln / n, 10),
                "C_minus_D_times_L_over_n": s((ff["C"] - ff["D"]) * Ln / n, 10),
                "max_match_residual": s(max(d["lag"]["match_residual"],
                                            jac["match_residual"], ff["match_residual"]), 3),
            })
        print(f"[large n] {large[-1]}", flush=True)
    report["large_n_route_B"] = large
    report["large_n_seconds"] = round(time.perf_counter() - t0, 1)
    report["differentiation_check"] = {
        str(n): s(differentiation_check(n, 60), 3) for n in (50, 3200)}
    report["differentiation_check"]["1e20"] = s(differentiation_check(10**20, 150), 3)

    rB = report["subgrid"]
    report["verdict"] = {
        "laguerre_R3_positive_everywhere": report["dense_route_A"]["laguerre_D3"]["negative"] == 0
        and report["dense_route_A"]["laguerre_D3"]["zero"] == 0,
        "jacobi_R4_negative_everywhere": report["dense_route_A"]["jacobi_E_J4"]["positive"] == 0
        and report["dense_route_A"]["jacobi_E_J4"]["zero"] == 0,
        "route_B_agrees_in_sign_on_subgrid": all(all(r["signs_agree_A_B"][:2]) for r in rB),
        "route_B_within_stated_error_on_subgrid": all(r["route_B_within_stated_error"] for r in rB),
        "preset_rule_M4_misses_at_n": [r["n"] for r in rB if not r["preset_rule_M4"]["within"]],
        "E_F5_sign_changes_route_A": report["dense_route_A"]["finite_free_E_F5"]["sign_changes_at_n"],
    }
    report["total_seconds"] = round(time.perf_counter() - t_start, 1)
    out.write_text(json.dumps(report, indent=1) + "\n")
    print(f"[done] {json.dumps(report['verdict'])} in {report['total_seconds']} s; wrote {out}")
    return report


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--dps-check", type=int, default=80)
    ap.add_argument("--time-unit", action="store_true")
    ap.add_argument("--out", type=Path, default=HERE / "results.json")
    args = ap.parse_args()
    if args.time_unit:
        time_unit(args.dps, args.dps_check)
        return
    run(args.dps, args.dps_check, args.out)


if __name__ == "__main__":
    main()
