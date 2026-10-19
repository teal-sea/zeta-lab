"""Hunt #135 phase 1: the sixth coefficient (MISSION question Q1).

Run from the repository root:

    .venv/bin/python hunts/jensen_wedge/probe_phase1.py --time-unit   # time one unit first
    .venv/bin/python hunts/jensen_wedge/probe_phase1.py               # writes results_phase1.json

It reuses phase 0's two routes (`probe.py`) unchanged and adds four things.

(a) The R_5 defect of Holland's four-parameter family over (theta, n), where
    D = theta B_J. The unknowns are (w_A, log B, log(C - D)) with w_A = n/A, so
    the solution can be followed through A = infinity (w_A = 0), where it leaves
    the positive-root class; phase 0's solver, in log A, stalled there.
    theta_star(n) is the sign change of E_F(5), theta_inf(n) the point w_A = 0.

(b) The direct solve of the same family with D free: (A, B, C, D) matching
    q_0..q_3, i.e. R_0..R_5. At leading order in 1/n this is the [2/2] Pade
    approximant of a Stieltjes function (RESULTS.md section 10), and it starts
    from that approximant. Its R_6 defect E_S(6) = log(R_6/R_6^S) is the next
    quantity. Leading-order model computations (constant target density
    1 - 2/L on [0, 1]) sit beside it and are labelled as such: the two-factor
    configuration, the theta-family, and a scan of three-factor configurations
    for near-identity structure.

(c) Root geometry of the comparison polynomials at n = 3200 for d up to 96,
    Holland's model and the Pade model: real-rootedness by sign changes, the
    minimal root gap, critical points, and the derivative ratios
    T_k = y^k p^(k)(y)/p(y) that Holland's Proposition 2.2 needs bounded by
    r^k, beside the bound r <= y * sum_j 1/|y - y_j| (RESULTS.md section 11).
    The true Jensen polynomial is compared with each model. Every J^{d,n}
    used here is already known hyperbolic (GORTTW Cor. 1.3, d <= 9.36e20), so
    this part checks instruments and hypotheses, nothing about J^{d,n} itself.

Grade: measured. Nothing here bears on RH.
"""

from __future__ import annotations

import argparse
import itertools
import json
import platform
import sys
import time
from pathlib import Path

import mpmath
import numpy as np
from mpmath import mp, mpf

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from hunts.jensen_wedge import probe as p0  # noqa: E402

N_LO, N_HI = p0.N_LO, p0.N_HI
J6 = 6  # R_0..R_6 enter the R_6 defect
SUBGRID = p0.SUBGRID
#: steps of 0.01 above 0.8: past theta_inf the walk meets B = infinity within a few
#: hundredths, and a coarser grid (0.85, 0.9, 0.95 in the trial run) stepped over
#: theta_inf into that wall at n = 50..70 and n >= 500
THETA_MAP = ("0.05", "0.1", "0.125", "0.2", "0.25", "0.3", "0.4", "0.5", "0.6", "0.7",
             "0.75", "0.8") + tuple(f"0.{k}" for k in range(81, 100)) + ("0.995",)
THETA_LARGE = ("0.125", "0.25", "0.5", "0.7")
LARGE_NS = ("1e4", "1e5", "1e6", "1e8", "1e10", "1e12", "1e16", "1e20")
ROUTE_B_SUBGRID = (100, 200, 400, 800, 1600, 3200)
ROOT_N = 3200
ROOT_DS = (6, 12, 24, 48, 96)
#: moments for the dense table: every index the R_6 defect needs on 50..3200,
#: and enough above 3200 for the root-geometry part at d <= 96
K_LO, K_HI = N_LO - 1, ROOT_N + max(ROOT_DS)
LO_EPS = ("0.8", "0.661", "0.5", "0.342", "0.2", "0.1", "0.03", "0.01", "0.003", "0.001")
SCAN_EPS = (0.342, 0.1, 0.03, 0.01, 0.003, 0.001)


def s(x, digits: int = 15) -> str:
    return mpmath.nstr(x, digits)


# ---------------------------------------------------------------------------
# quotients with the first numerator parameter written as w = n/U
# ---------------------------------------------------------------------------


def log_qq_w(k: int, w, V, n):
    """log qq_k(U, V) with U = n/w: smooth through w = 0 (U = infinity) and
    defined for small negative w (U < 0, outside the positive-root class)."""
    return mp.log1p(1 / (V + k)) - mp.log1p(w / (n + k * w))


def family_solve(lq: list, n: int, BJ, theta, guess) -> dict:
    """Holland's family at D = theta B_J: (w_A, log B, log(C - D)) from q_0..q_2."""
    D = mpf(theta) * BJ

    def eqs(w, b, c):
        B, C = mp.exp(b), D + mp.exp(c)
        return [log_qq_w(k, w, B, n) + p0.log_qq(k, C, D) - lq[k] for k in range(3)]

    w, b, c = mp.findroot(eqs, guess, tol=mpf(10) ** (-(mp.dps - 8)))
    B, C = mp.exp(b), D + mp.exp(c)
    return {"x": (w, b, c), "w_A": w, "B": B, "C": C, "D": D, "theta": mpf(theta),
            "E_F5": log_qq_w(3, w, B, n) + p0.log_qq(3, C, D) - lq[3],
            "res": max(abs(v) for v in eqs(w, b, c))}


def family_from_holland(lq: list, n: int, BJ, ff: dict) -> dict:
    """Phase 0's theta = 1/2 solution, re-expressed in this solver's unknowns."""
    return family_solve(lq, n, BJ, mpf(1) / 2,
                        (n / ff["A"], mp.log(ff["B"]), mp.log(ff["C"] - ff["D"])))


def family_walk(lq: list, n: int, BJ, start: dict, theta_to, max_halvings: int = 40) -> dict:
    """Continuation in theta from `start` with linear extrapolation of the unknowns."""
    target = mpf(theta_to)
    path = [start]
    step = (target - start["theta"]) / 4
    halvings = 0
    while path[-1]["theta"] != target:
        cur = path[-1]
        nxt = cur["theta"] + step
        if (step > 0 and nxt > target) or (step < 0 and nxt < target):
            nxt = target
        if len(path) > 1:
            prev = path[-2]
            t = (nxt - cur["theta"]) / (cur["theta"] - prev["theta"])
            guess = tuple(a + t * (a - b) for a, b in zip(cur["x"], prev["x"]))
        else:
            guess = cur["x"]
        try:
            new = family_solve(lq, n, BJ, nxt, guess)
        except Exception:  # halve and retry; raises below once the walk stalls
            halvings += 1
            if halvings > max_halvings:
                raise RuntimeError(f"walk stalled at theta = {s(cur['theta'], 12)}")
            step /= 2
            continue
        halvings = 0
        path.append(new)
        step *= mpf(3) / 2
    return path[-1]


def family_map(lq: list, n: int, BJ, half: dict, thetas, bisections: int = 40) -> dict:
    """E_F5 on a theta grid, walking outward from theta = 1/2; theta_star (sign
    change of E_F5) and theta_inf (w_A = 0) located by bisection. The upward
    walk stops at the first grid point past theta_inf: beyond it A < 0."""
    sols = {half["theta"]: half}
    failed = {}
    for side in (sorted(mpf(t) for t in thetas if mpf(t) > half["theta"]),
                 sorted((mpf(t) for t in thetas if mpf(t) < half["theta"]), reverse=True)):
        cur = half
        for th in side:
            try:
                cur = family_walk(lq, n, BJ, cur, th)
            except Exception as exc:  # recorded; the walk on this side stops
                failed[s(th, 6)] = repr(exc)[:160]
                break
            sols[th] = cur
            if cur["w_A"] <= 0:
                break
    order = sorted(sols)

    def bisect(pred):
        for t0, t1 in zip(order[:-1], order[1:]):
            if pred(sols[t0]) != pred(sols[t1]):
                lo, flo, hi = t0, sols[t0], t1
                for _ in range(bisections):
                    mid = (lo + hi) / 2
                    fm = family_walk(lq, n, BJ, flo, mid)
                    if pred(fm) == pred(flo):
                        lo, flo = mid, fm
                    else:
                        hi = mid
                return (lo + hi) / 2, flo
        return None, None

    t_star, f_star = bisect(lambda f: f["E_F5"] > 0)
    t_inf, _ = bisect(lambda f: f["w_A"] > 0)
    return {"solutions": sols, "failed": failed, "theta_star": t_star, "at_star": f_star,
            "theta_inf": t_inf}


# ---------------------------------------------------------------------------
# the Pade model: Holland's family with D free, matching R_0..R_5
# ---------------------------------------------------------------------------


def lo_pade22(eps):
    """Leading-order model: the [2/2] Pade approximant of (1 - z)^(eps - 1),
    returned as the ordered numerator nodes (a1, a2) and pole nodes (b1, b2),
    i.e. w-coordinates n/U and n/V of the two Jacobi factors."""
    eps = mpf(eps)
    f = [mp.rf(1 - eps, k) / mp.factorial(k) for k in range(5)]
    q1, q2 = mp.lu_solve(mp.matrix([[f[2], f[1]], [f[3], f[2]]]), mp.matrix([-f[3], -f[4]]))
    p1, p2 = f[1] + q1, f[2] + q1 * f[1] + q2
    b = sorted(r.real for r in mp.polyroots([1, q1, q2]))
    a = sorted(r.real for r in mp.polyroots([1, p1, p2]))
    return a, b


def pade_solve(lq: list, n: int, guess) -> dict:
    """(w_A, log B, log C, log D) with qq_k(A, B) qq_k(C, D) = q_k, k = 0..3."""
    def eqs(w, b, c, d):
        B, C, D = mp.exp(b), mp.exp(c), mp.exp(d)
        return [log_qq_w(k, w, B, n) + p0.log_qq(k, C, D) - lq[k] for k in range(4)]

    x = mp.findroot(eqs, guess, tol=mpf(10) ** (-(mp.dps - 8)))
    w, b, c, d = x
    B, C, D = mp.exp(b), mp.exp(c), mp.exp(d)
    return {"x": tuple(x), "A": n / w, "w_A": w, "B": B, "C": C, "D": D,
            "E_S6": log_qq_w(4, w, B, n) + p0.log_qq(4, C, D) - lq[4],
            "res": max(abs(v) for v in eqs(w, b, c, d))}


def pade_guess(n: int, Ln) -> tuple:
    a, b = lo_pade22(2 / Ln)
    return (a[0], mp.log(n / b[0]), mp.log(n / a[1]), mp.log(n / b[1]))


def pade_row(n, Ln, sol: dict, BJ) -> dict:
    A, B, C, D = sol["A"], sol["B"], sol["C"], sol["D"]
    n = mpf(n)
    return {
        "A_over_nL": s(A / (n * Ln), 10), "B_minus_2n_L_over_n": s((B - 2 * n) * Ln / n, 10),
        "C_minus_2n_L_over_n": s((C - 2 * n) * Ln / n, 10),
        "D_minus_n_L_over_n": s((D - n) * Ln / n, 10),
        "theta_equiv_D_over_BJ": s(D / BJ, 12), "C_minus_D_over_D": s((C - D) / D, 10),
        "rho_AB": s(1 - B / A, 10), "rho_CD": s(1 - D / C, 10), "A_over_B": s(A / B, 10),
        "E_S6": s(sol["E_S6"], 12), "n5L_E_S6": s(n ** 5 * Ln * sol["E_S6"], 10),
        # total uncovered length of [0, 1] in w = n/parameter, times L: the L^1
        # distance of section 12.4's residual bound; 2 at leading order
        "gap_total_times_L": s((n / A + (n / C - n / B) + (1 - n / D)) * Ln, 10),
        "all_positive_and_U_gt_V": bool(A > B > 0 and C > D > 0),
        "match_residual": s(sol["res"], 3),
    }


# ---------------------------------------------------------------------------
# leading-order model computations (constant target density 1 - eps on [0, 1])
# ---------------------------------------------------------------------------


def lo_family(eps, theta) -> dict:
    """Leading order of the D-fixed family: pole b2 = w_D = (1 - eps/2)/theta,
    b1 and the numerator nodes from matching the first three moments; E5 is the
    first unmatched Taylor coefficient of target minus model (sign of E_F(5))."""
    eps, theta = mpf(eps), mpf(theta)
    f = [mp.rf(1 - eps, k) / mp.factorial(k) for k in range(5)]
    om = (1 - eps / 2) / theta
    b1 = (om * f[2] - f[3]) / (om * f[1] - f[2])
    q1, q2 = -(b1 + om), b1 * om
    p1, p2 = f[1] + q1, f[2] + q1 * f[1] + q2
    # ascending: w_A is the smaller numerator node, the one that crosses 0 (A =
    # infinity) and turns negative past theta_inf; w_C stays near w_D
    a = sorted(r.real for r in mp.polyroots([1, p1, p2]))
    return {"w_D": om, "b1": b1, "w_A": a[0], "w_C": a[1], "E5": f[4] + q1 * f[3] + q2 * f[2]}


def lo_bisect(eps, pred, lo="0.5", hi="0.9999", steps=60):
    lo, hi = mpf(lo), mpf(hi)
    plo = pred(lo_family(eps, lo))
    if pred(lo_family(eps, hi)) == plo:
        return None
    for _ in range(steps):
        mid = (lo + hi) / 2
        if pred(lo_family(eps, mid)) == plo:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def lo_tables() -> dict:
    out = []
    with mp.workdps(40):
        for e in LO_EPS:
            eps = mpf(e)
            a, b = lo_pade22(eps)
            # bracket_5 = 5 int t^4 (mu - tau): the R_6 defect's leading coefficient
            br5 = sum(x ** 5 for x in b) - sum(x ** 5 for x in a) - (1 - eps)
            out.append({
                "eps": e, "a": [s(x, 10) for x in a], "b": [s(x, 10) for x in b],
                "simpson_first_order": [s(eps / 6, 6), s(mpf(1) / 2 - eps / 3, 6),
                                        s(mpf(1) / 2 + eps / 3, 6), s(1 - eps / 6, 6)],
                "theta_star": s((1 - eps / 2) / b[1], 10),
                "one_minus_theta_star_times_L": s((1 - (1 - eps / 2) / b[1]) * 2 / eps, 8),
                "theta_inf": s(lo_bisect(eps, lambda f: f["w_A"] > 0), 10),
                "rho_CD": s(1 - a[1] / b[1], 8),
                "bracket5_over_eps": s(br5 / eps, 8),
                # n^4 L E_F(5) at theta = 1/2 = 24 L E5 (section 11.2); -12 as eps -> 0
                "n4L_E_F5_at_theta_half": s(24 * (2 / eps) * lo_family(eps, "0.5")["E5"], 8),
                "a1_plus_b2": s(a[0] + b[1], 12), "b1_plus_a2": s(b[0] + a[1], 12),
            })
    return {"pade22": out}


def _fco(eps: float, K: int = 5) -> list:
    a, f = 1 - eps, [1.0]
    for k in range(1, K + 1):
        f.append(f[-1] * (a + k - 1) / k)
    return f


def three_factor_scan(eps: float, n1: int = 500, n2: int = 120, wmax: float = 3.0) -> dict:
    """Leading order, three Jacobi factors matching four moments (R_0..R_5).

    Parametrized by two pole nodes (b1, b2); the third follows from the one
    linear constraint on the denominator, the numerator is the truncation of
    Q f. A configuration is admissible if every node is real, every pole lies
    in (0, wmax], every numerator node in [0, wmax) and some pairing has a_i < b_i
    (each factor U_i > V_i). rho_i = 1 - a_i/b_i is a factor's relative gap; the
    main factor is the one with the largest rho, and X = the largest rho among
    the others. Returned: the admissible configuration minimizing X on the grid.
    """
    f = _fco(eps)
    grid = np.concatenate([np.linspace(1e-4, 1.0, n1), np.linspace(1.0, wmax, n2)[1:]])
    best = None
    for i, b1 in enumerate(grid):
        for b2 in grid[i + 1:]:
            ss, pp = b1 + b2, b1 * b2
            den = -f[3] + ss * f[2] - pp * f[1]
            if den == 0:
                continue
            b3 = (-f[4] + ss * f[3] - pp * f[2]) / den
            if not 0 < b3 <= wmax:
                continue
            bs = np.array([b1, b2, b3])
            q = np.poly(bs)
            p1 = f[1] + q[1]
            p2 = f[2] + q[1] * f[1] + q[2]
            p3 = f[3] + q[1] * f[2] + q[2] * f[1] + q[3]
            ar = np.roots([1.0, p1, p2, p3])
            if np.max(np.abs(ar.imag)) > 1e-12:
                continue
            a = ar.real
            if a.min() < -1e-14 or a.max() >= wmax:
                continue
            for perm in itertools.permutations(range(3)):
                if not all(a[perm[k]] < bs[k] for k in range(3)):
                    continue
                rho = sorted(1 - max(a[perm[k]], 0.0) / bs[k] for k in range(3))
                if best is None or rho[1] < best[0]:
                    res = max(abs(np.sum(bs ** k) - np.sum(a ** k) - (1 - eps)) for k in range(1, 5))
                    best = (rho[1], rho, sorted(bs.tolist()), sorted(a.tolist()), res)
    if best is None:
        return {"eps": eps, "admissible_found": False}
    return {"eps": eps, "admissible_found": True, "X3": round(best[0], 6),
            "rho_sorted": [round(r, 6) for r in best[1]],
            "poles_b": [round(x, 6) for x in best[2]], "zeros_a": [round(x, 6) for x in best[3]],
            "X3_over_eps_cuberoot": round(best[0] / eps ** (1 / 3), 4),
            "moment_residual_s1_to_s4": float(f"{best[4]:.3g}")}


# ---------------------------------------------------------------------------
# root geometry of the comparison polynomials
# ---------------------------------------------------------------------------


def log_m(j: int, factors: list):
    """log of the y-coefficient multiplier of Holland's eq. (69), generalized:
    first factor (A)_j/(A^j (B)_j), each further factor (C)_j D^j/(C^j (D)_j)."""
    (A, B), rest = factors[0], factors[1:]
    v = mp.fsum(mp.log1p(i / A) - mp.log(B + i) for i in range(j))
    for C, D in rest:
        v += mp.fsum(mp.log1p(i / C) + mp.log(D) - mp.log(D + i) for i in range(j))
    return v


def model_coeffs(d: int, factors: list) -> list:
    """Coefficients c_j of p(y) = sum_j c_j y^j, roots near the first factor's B."""
    return [(-1) ** j * mp.binomial(d, j) * mp.exp(log_m(j, factors)) for j in range(d + 1)]


def jensen_coeffs(d: int, logR: list, S) -> list:
    """J^{d,n}(-y/S)/gamma(n) in the variable y, from log R_j."""
    return [(-1) ** j * mp.binomial(d, j) * mp.exp(logR[j] - j * mp.log(S)) for j in range(d + 1)]


def horner(c: list, y):
    v = mpf(0)
    for a in reversed(c):
        v = v * y + a
    return v


def deriv(c: list) -> list:
    return [j * c[j] for j in range(1, len(c))]


def real_roots(c: list, lo, hi, step, bisections: int = 120) -> list:
    """Sign changes of the polynomial on a grid, each refined by bisection."""
    roots = []
    N = int(mp.ceil((hi - lo) / step))
    y0, v0 = lo, horner(c, lo)
    for i in range(1, N + 1):
        y1 = lo + i * (hi - lo) / N
        v1 = horner(c, y1)
        if v0 == 0:
            roots.append(y0)
        elif (v0 > 0) != (v1 > 0):
            a, b, va = y0, y1, v0
            for _ in range(bisections):
                m = (a + b) / 2
                vm = horner(c, m)
                if (vm > 0) == (va > 0):
                    a, va = m, vm
                else:
                    b = m
            roots.append((a + b) / 2)
        y0, v0 = y1, v1
    return roots


def critical_points(c: list, roots: list, bisections: int = 120) -> list:
    dc = deriv(c)
    out = []
    for a, b in zip(roots[:-1], roots[1:]):
        lo, hi = a + (b - a) * mpf(10) ** -12, b - (b - a) * mpf(10) ** -12
        vlo = horner(dc, lo)
        for _ in range(bisections):
            m = (lo + hi) / 2
            vm = horner(dc, m)
            if (vm > 0) == (vlo > 0):
                lo, vlo = m, vm
            else:
                hi = m
        out.append((lo + hi) / 2)
    return out


def ratio_stats(roots: list, crits: list) -> dict:
    """At every critical point y: max_k |T_k|^(1/k), T_k = k! y^k e_k(1/(y - y_j)),
    and the Lemma A quantity y sum_j 1/|y - y_j|, which bounds it."""
    d = len(roots)
    worst_T, worst_A = mpf(0), mpf(0)
    for y in crits:
        x = [1 / (y - r) for r in roots]
        e = [mpf(1)] + [mpf(0)] * d
        for xi in x:
            for k in range(d, 0, -1):
                e[k] += xi * e[k - 1]
        for k in range(2, d + 1):
            Tk = abs(mp.factorial(k) * y ** k * e[k])
            if Tk > 0:
                worst_T = max(worst_T, Tk ** (mpf(1) / k))
        worst_A = max(worst_A, y * mp.fsum(abs(xi) for xi in x))
    return {"r_needed": worst_T, "r_lemma_A": worst_A}


def lmesh(roots: list):
    return min(b / a for a, b in zip(roots[:-1], roots[1:]))


def root_geometry(d: int, factors: list, logR: list, dps: int = 80) -> dict:
    """Roots, gaps and derivative ratios of the model p, and the Jensen polynomial
    P = J^{d,n}(-y/S)/gamma(n), S = B R_1, beside it. The first factor alone (a
    Jacobi polynomial) is solved too, to read Lemma B's gap bound and the
    log-mesh transfer of Lemma C on the actual polynomials."""
    with mp.workdps(dps):
        (A, B) = factors[0]
        S = B * mp.exp(logR[1])
        c = model_coeffs(d, factors)
        cP = jensen_coeffs(d, logR, S)
        c1 = model_coeffs(d, factors[:1])
        half = 6 * mp.sqrt(B * d) + 10 * d
        step = mp.sqrt(B / d) / 20
        rp = real_roots(c, B - half, B + half, step)
        rP = real_roots(cP, B - half, B + half, step)
        r1 = real_roots(c1, B - half, B + half, step)
        out = {"d": d, "B": s(B, 10), "A_over_B": s(A / B, 6),
               "lemma_B_hypotheses_A_ge_8B_and_B_ge_256d": bool(A >= 8 * B and B >= 256 * d),
               "model_real_roots": len(rp), "jensen_real_roots": len(rP),
               "first_factor_real_roots": len(r1)}
        if len(rp) == d and d > 1:
            g = min(b - a for a, b in zip(rp[:-1], rp[1:]))
            crits = critical_points(c, rp)
            st = ratio_stats(rp, crits)
            Hd = mp.harmonic(d)
            out.update({
                "root_hull_minus_B_over_sqrt_Bd": [s((rp[0] - B) / mp.sqrt(B * d), 6),
                                                   s((rp[-1] - B) / mp.sqrt(B * d), 6)],
                "min_gap_times_sqrt_d_over_B": s(g * mp.sqrt(d / B), 6),
                "r_needed_over_sqrt_Bd": s(st["r_needed"] / mp.sqrt(B * d), 6),
                "r_lemma_A_over_sqrt_Bd": s(st["r_lemma_A"] / mp.sqrt(B * d), 6),
                "r_explicit_over_sqrt_Bd": s(rp[-1] * (4 + 3 * Hd) / g / mp.sqrt(B * d), 6),
                "lemma_A_bounds_r_needed": bool(st["r_needed"] <= st["r_lemma_A"]),
            })
            if len(r1) == d:
                g1 = min(b - a for a, b in zip(r1[:-1], r1[1:]))
                out.update({
                    "first_factor_min_gap_over_sturm_bound": s(
                        g1 / (mp.pi * mp.sqrt(B / (mpf("2.47") * d + mpf("6.07")))), 6),
                    "lmesh_model_minus_1": s(lmesh(rp) - 1, 6),
                    "lmesh_first_factor_minus_1": s(lmesh(r1) - 1, 6),
                    "lmesh_transfer_holds": bool(lmesh(rp) >= lmesh(r1)),
                })
        if len(rp) == d and len(rP) == d:
            cm = [mp.exp(logR[j] - j * mp.log(S) - log_m(j, factors)) for j in range(d + 1)]
            cnt = 0
            for t in sorted(rp + rP):
                cnt = max(cnt, abs(sum(1 for r in rP if r <= t) - sum(1 for r in rp if r <= t)))
            g = min(b - a for a, b in zip(rp[:-1], rp[1:])) if d > 1 else mpf(1)
            out.update({
                "max_abs_c_minus_1": s(max(abs(v - 1) for v in cm), 6),
                "c_minus_1_vanishes_through_j": max(j for j in range(d + 1)
                                                    if all(abs(cm[i] - 1) < mpf(10) ** -40
                                                           for i in range(j + 1))),
                "max_root_shift_over_min_gap": s(max(abs(a - b) for a, b in zip(rp, rP)) / g, 6),
                "count_discrepancy": cnt,
            })
        return out


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def lr_route_B_direct(n, M: int, top: int = J6) -> list:
    base = p0.log_gamma_saddle(mpf(n), M)
    return [mpf(0)] + [p0.log_gamma_saddle(mpf(n) + j, M) - base for j in range(1, top + 1)]


def time_unit(dps: int) -> None:
    t0 = time.perf_counter()
    p0.moments_trapezoid(3233, 3296, dps)
    print(f"[unit] route A block k=3233..3296 dps={dps}: {time.perf_counter() - t0:.2f} s")
    n = 3200
    I, _ = p0.moments_trapezoid(n - 1, n + J6, dps)
    with mp.workdps(dps + p0.GUARD):
        ell = {m: p0.log_gamma_from_moments(I, m, dps) for m in range(n, n + J6 + 1)}
        lr = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, J6 + 1)]
        lq = p0.log_q_from_log_R(lr)
        Ln = p0.script_L(n)
        t0 = time.perf_counter()
        pade_solve(lq, n, pade_guess(n, Ln))
        print(f"[unit] Pade solve n={n}: {time.perf_counter() - t0:.2f} s")
        d0 = p0.defects(lr, n, Ln)
        half = family_from_holland(lq, n, d0["jac"]["B_J"], d0["ff"])
        t0 = time.perf_counter()
        family_walk(lq, n, d0["jac"]["B_J"], half, "0.85")
        print(f"[unit] family walk theta 0.5 -> 0.85 n={n}: {time.perf_counter() - t0:.2f} s")
    for nn in ("1e4", "1e20"):
        with mp.workdps(int(5 * mp.log10(mpf(nn))) + 50 + p0.GUARD):
            t0 = time.perf_counter()
            lr_route_B_direct(int(mpf(nn)), p0.M_ROUTE_B)
            print(f"[unit] route B direct log R_0..6 n={nn}: {time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    three_factor_scan(0.01, 150, 40)
    print(f"[unit] three-factor scan, 150+40 grid, eps=0.01: {time.perf_counter() - t0:.2f} s")


def run(dps: int, dps_check: int, out: Path) -> dict:
    t_start = time.perf_counter()
    report: dict = {
        "hunt": "jensen_wedge", "phase": 1, "grade": "measured",
        "source": "Holland, arXiv:2608.08682v1 (PDF, read 2026-10-18), Prop. 2.2, Lemmas 6.1, 7.1-7.3, "
                  "8.1, 9.1; Martinez-Finkelshtein, Morales, Perales, arXiv:2309.10970, Prop. 2.17",
        "git_head": p0.git_head(), "python": platform.python_version(),
        "mpmath": mpmath.__version__, "numpy": np.__version__, "dps": dps,
        "dps_check": dps_check,
    }

    print("[validate] route A against zeta/li.py", flush=True)
    report["validation_vs_li"] = [p0.validate_against_li(50, 17, 47),
                                  p0.validate_against_li(30, 17, 127)]

    # --- route A table ------------------------------------------------------
    ks = range(K_LO, K_HI + 1)
    t0 = time.perf_counter()
    I, worst = p0.moments(ks, dps, log_every=10)
    with mp.workdps(dps + p0.GUARD):
        ell = {m: p0.log_gamma_from_moments(I, m, dps) for m in range(N_LO, K_HI + 1)}
    t_mom = time.perf_counter() - t0
    check_ns = (50, 400, 3200)
    ks_check = sorted({k for n in check_ns for k in range(n - 1, n + J6 + 1)} | {K_HI - 1, K_HI})
    t0 = time.perf_counter()
    I2 = {k: p0.moment_quad(k, dps_check) for k in ks_check}
    with mp.workdps(dps_check + p0.GUARD):
        mdev = max(abs(I[k] / I2[k] - 1) for k in ks_check)
    if mdev > mpf(10) ** -(dps - 5):
        raise RuntimeError(f"route A and its check route disagree: {mdev}")
    report["route_A"] = {"k_range": [K_LO, K_HI], "moments_computed": len(ks),
                         "max_coarse_fine_deviation": s(worst, 3), "seconds": round(t_mom, 1),
                         "check_route_indices": ks_check, "max_rel_dev_vs_check_route": s(mdev, 3),
                         "check_seconds": round(time.perf_counter() - t0, 1)}
    print(f"[route A] {report['route_A']}", flush=True)

    def lr_A(n, top=J6):
        return [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, top + 1)]

    # --- (a) the R_5 defect over (theta, n), route A -------------------------
    t0 = time.perf_counter()
    maps = []
    with mp.workdps(dps + p0.GUARD):
        for n in SUBGRID:
            lr = lr_A(n)
            lq = p0.log_q_from_log_R(lr)
            Ln = p0.script_L(n)
            d0 = p0.defects(lr, n, Ln)
            BJ = d0["jac"]["B_J"]
            half = family_from_holland(lq, n, BJ, d0["ff"])
            m = family_map(lq, n, BJ, half, THETA_MAP)
            row = {"n": n, "L_n": s(Ln, 10), "grid": {}, "failed": m["failed"],
                   "theta_star": s(m["theta_star"], 12) if m["theta_star"] else None,
                   "theta_inf": s(m["theta_inf"], 12) if m["theta_inf"] else None}
            for th, f in sorted(m["solutions"].items()):
                row["grid"][s(th, 6)] = {
                    "E_F5": s(f["E_F5"], 12), "n4L_E_F5": s(n ** 4 * Ln * f["E_F5"], 8),
                    "A_positive": bool(f["w_A"] > 0), "w_A": s(f["w_A"], 8),
                    "C_minus_D_over_D": s((f["C"] - f["D"]) / f["D"], 8),
                    "match_residual": s(f["res"], 3)}
            if m["at_star"] is not None:
                f = m["at_star"]
                row["at_theta_star"] = {"C_minus_D_over_D": s((f["C"] - f["D"]) / f["D"], 10),
                                        "A_over_B": s(n / f["w_A"] / f["B"], 10)}
            maps.append(row)
            print(f"[map A] n={n} theta*={row['theta_star']} theta_inf={row['theta_inf']} "
                  f"failed={list(m['failed'])}", flush=True)
    report["theta_map_route_A"] = maps
    report["theta_map_seconds"] = round(time.perf_counter() - t0, 1)

    # --- (b) the Pade model on route A, every n --------------------------------
    t0 = time.perf_counter()
    dense, guess = [], None
    with mp.workdps(dps + p0.GUARD):
        for n in range(N_HI, N_LO - 1, -1):
            lr = lr_A(n)
            lq = p0.log_q_from_log_R(lr)
            Ln = p0.script_L(n)
            sol = pade_solve(lq, n, guess or pade_guess(n, Ln))
            guess = sol["x"]
            dense.append((n, Ln, sol, p0.jacobi(lq)["B_J"]))
    dense.reverse()
    E6 = [sol["E_S6"] for _, _, sol, _ in dense]
    report["pade_dense_route_A"] = {
        "n_count": len(dense),
        "E_S6_positive": sum(1 for v in E6 if v > 0), "E_S6_negative": sum(1 for v in E6 if v < 0),
        "E_S6_sign_changes_at_n": [dense[i + 1][0] for i in range(len(E6) - 1)
                                   if (E6[i] > 0) != (E6[i + 1] > 0)],
        "all_positive_and_U_gt_V": all(sol["A"] > sol["B"] > 0 and sol["C"] > sol["D"] > 0
                                       for _, _, sol, _ in dense),
        "max_match_residual": s(max(sol["res"] for _, _, sol, _ in dense), 3),
        "rows": {str(n): pade_row(n, Ln, sol, BJ) for n, Ln, sol, BJ in dense if n in SUBGRID},
        "seconds": round(time.perf_counter() - t0, 1),
    }
    print(f"[pade A] negative={report['pade_dense_route_A']['E_S6_negative']} "
          f"positive={report['pade_dense_route_A']['E_S6_positive']}", flush=True)

    # --- route B: the subgrid check and large n --------------------------------
    t0 = time.perf_counter()
    rb_sub = []
    by_n = {n: (Ln, sol, BJ) for n, Ln, sol, BJ in dense}
    with mp.workdps(dps + p0.GUARD):
        for n in ROUTE_B_SUBGRID:
            Ln, solA, BJ = by_n[n]
            vals = {}
            for M in (p0.M_ROUTE_B, p0.M_ROUTE_B - 1):
                lq = p0.log_q_from_log_R(lr_route_B_direct(n, M))
                vals[M] = pade_solve(lq, n, solA["x"])["E_S6"]
            e6 = vals[p0.M_ROUTE_B]
            sp6 = abs(e6 - vals[p0.M_ROUTE_B - 1])
            rb_sub.append({"n": n, "E_S6_B": s(e6, 12), "E_S6_A": s(solA["E_S6"], 12),
                           "E_S6_B_spread_M5_M6": s(sp6, 3),
                           "rel_dev_A_B": s(abs(e6 / solA["E_S6"] - 1), 3),
                           "B_resolves_sign": bool(sp6 < abs(e6)),
                           "signs_agree": bool((e6 > 0) == (solA["E_S6"] > 0))})
            print(f"[route B sub] {rb_sub[-1]}", flush=True)
    report["route_B_subgrid"] = rb_sub

    large = []
    for n_str in LARGE_NS:
        n = int(mpf(n_str))
        dps_n = int(5 * mp.log10(n)) + 50
        with mp.workdps(dps_n + p0.GUARD):
            Ln = p0.script_L(n)
            lrs = {M: lr_route_B_direct(n, M) for M in (p0.M_ROUTE_B, p0.M_ROUTE_B - 1)}
            row = {"n": n_str, "dps": dps_n, "L_n": s(Ln, 12)}
            per_M = {}
            for M, lr in lrs.items():
                lq = p0.log_q_from_log_R(lr)
                d0 = p0.defects(lr[:6], n, Ln)
                BJ = d0["jac"]["B_J"]
                sol = pade_solve(lq, n, pade_guess(n, Ln))
                half = family_from_holland(lq, n, BJ, d0["ff"])
                fam = {th: family_walk(lq, n, BJ, half, th) for th in THETA_LARGE}
                # theta_star ~ 1 - 2/(3L) and theta_inf ~ 1 - c/L at leading order, so
                # the grid is laid in units of 1/L; a fixed grid stepped over theta_inf
                top = tuple(1 - mpf(c) / 100 / Ln for c in range(120, 19, -5))
                star = family_map(lq, n, BJ, half, top)
                per_M[M] = (sol, BJ, fam, star)
            sol, BJ, fam, star = per_M[p0.M_ROUTE_B]
            sol5, _, fam5, star5 = per_M[p0.M_ROUTE_B - 1]
            row.update(pade_row(n, Ln, sol, BJ))
            row["E_S6_spread_M5_M6"] = s(abs(sol["E_S6"] - sol5["E_S6"]), 3)
            row["family"] = {
                th: {"n4L_E_F5": s(mpf(n) ** 4 * Ln * f["E_F5"], 10),
                     "first_order_prediction": s(-4 * (2 - mpf(th)) / mpf(th), 6),
                     "spread_M5_M6": s(abs(f["E_F5"] - fam5[th]["E_F5"]) / abs(f["E_F5"]), 3)}
                for th, f in fam.items()}
            row["theta_star"] = s(star["theta_star"], 14) if star["theta_star"] else None
            row["theta_inf"] = s(star["theta_inf"], 14) if star["theta_inf"] else None
            if star["theta_star"]:
                row["one_minus_theta_star_times_L"] = s((1 - star["theta_star"]) * Ln, 10)
            if star["theta_inf"]:
                row["one_minus_theta_inf_times_L"] = s((1 - star["theta_inf"]) * Ln, 10)
            large.append(row)
        print(f"[large n] {n_str}: theta*={row['theta_star']} n5L E_S6={row['n5L_E_S6']}", flush=True)
    report["large_n_route_B"] = large
    report["route_B_seconds"] = round(time.perf_counter() - t0, 1)

    # --- leading-order model --------------------------------------------------
    t0 = time.perf_counter()
    report["leading_order"] = lo_tables()
    report["leading_order"]["three_factor_scan"] = [three_factor_scan(e) for e in SCAN_EPS]
    for r in report["leading_order"]["three_factor_scan"]:
        print(f"[3-factor] {r}", flush=True)
    report["leading_order_seconds"] = round(time.perf_counter() - t0, 1)

    # --- (c) root geometry at n = 3200 -----------------------------------------
    # Evaluating a degree-d polynomial whose zeros cluster at B in the monomial
    # basis loses about d log10(2 sqrt(e) B/sqrt(Bd)) digits (about 77 at d = 48,
    # 140 at d = 96). The dps-60 table carries about 70, and in the trial run the
    # Jensen polynomial at d = 48 showed 6 spurious complex pairs for that reason
    # alone. So this part gets its own route A block at dps 260, with rho = 16 so
    # that the coarse/fine pair reads the error of the rho = 8 rule, checked
    # against the dps-60 table, and each polynomial is evaluated at dps 60 + 2d.
    t0 = time.perf_counter()
    n = ROOT_N
    dps_root = 260
    Ihp, dev_hp = p0.moments_trapezoid(n - 1, K_HI, dps_root, rho=16)
    with mp.workdps(dps_root + p0.GUARD):
        ell_hp = {m: p0.log_gamma_from_moments(Ihp, m, dps_root) for m in range(n, K_HI + 1)}
        agree = max(abs(ell_hp[m] - ell[m]) for m in range(n, K_HI + 1))
        if agree > mpf(10) ** -(dps + 5):
            raise RuntimeError(f"dps-{dps_root} block disagrees with the main table: {agree}")
        logR_all = [mpf(0)] + [ell_hp[n + j] - ell_hp[n] for j in range(1, max(ROOT_DS) + 1)]
    with mp.workdps(dps + p0.GUARD):
        Ln, solP, _ = by_n[n]
        lr = lr_A(n, 5)
        d0 = p0.defects(lr, n, Ln)
        ff = d0["ff"]
        models = {"holland_theta_half": [(ff["A"], ff["B"]), (ff["C"], ff["D"])],
                  "pade": [(solP["A"], solP["B"]), (solP["C"], solP["D"])]}
    geo = {"high_precision_block": {"dps": dps_root, "rho": 16, "k_range": [n - 1, K_HI],
                                    "coarse_fine_deviation": s(dev_hp, 3),
                                    "max_abs_dlog_gamma_vs_dps60_table": s(agree, 3)}}
    for name, fac in models.items():
        geo[name] = {"factors": [[s(U, 12), s(V, 12)] for U, V in fac], "by_d": []}
        for d in ROOT_DS:
            geo[name]["by_d"].append(root_geometry(d, fac, logR_all, dps=60 + 2 * d))
            print(f"[roots] {name} {geo[name]['by_d'][-1]}", flush=True)
    report["root_geometry_n3200"] = geo
    report["root_geometry_seconds"] = round(time.perf_counter() - t0, 1)

    report["total_seconds"] = round(time.perf_counter() - t_start, 1)
    out.write_text(json.dumps(report, indent=1) + "\n")
    print(f"[done] {report['total_seconds']} s; wrote {out}")
    return report


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--dps-check", type=int, default=80)
    ap.add_argument("--time-unit", action="store_true")
    ap.add_argument("--out", type=Path, default=HERE / "results_phase1.json")
    args = ap.parse_args()
    if args.time_unit:
        time_unit(args.dps)
        return
    run(args.dps, args.dps_check, args.out)


if __name__ == "__main__":
    main()
