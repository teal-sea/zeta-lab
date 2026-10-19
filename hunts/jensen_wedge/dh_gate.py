"""Hunt #135 rival gate: Holland's construction run on Davenport-Heilbronn.

Run from the repository root:

    .venv/bin/python hunts/jensen_wedge/dh_gate.py --time-unit   # time one unit first
    .venv/bin/python hunts/jensen_wedge/dh_gate.py               # writes results_dh.json

`MISSION.md`, "The rival gate", predicted before this ran that the construction of
phases 0 and 1 succeeds for the Davenport-Heilbronn (DH) function exactly as for
zeta, because it reads the weight only through its double-exponential decay. The
probe measures the prediction item by item on the DH gamma table:

* Holland's two sign facts: the Laguerre defect at R_3 positive and the Jacobi
  defect at R_4 negative (RESULTS.md sections 4 and 5);
* the sign map of E_F(5) over (theta, n) for D = theta B_J: negative below
  theta_star(n), positive up to theta_inf(n), where A passes infinity (section 10);
* the [2/2] Pade point: Holland's family with D free matches R_0..R_5 with every
  parameter positive, A > B and C > D, and its R_6 defect (sections 11.3, 11.4);

and, as the contrast, DH's own Jensen non-hyperbolicity at n = 0 near
d* = 20785 (`hunts/jensen_clock`), which the measured wedge region must not
overlap.

The DH table. `hunts/jensen_clock/probe.py` builds gamma(n) = n!/(2n)! M_{2n},
M_{2n} = int_0^inf u^{2n} Phi(u) du, Phi(u) = 4 e^{3u/2} omega(e^{2u}),
omega(x) = sum_m m a_m e^{-pi m^2 x/5}, a_m of period 5: (1, kappa, -kappa, -1, 0),
by composite Gauss-Legendre (`make_nodes`, `gammas_from_nodes`), and checks it with
two node sets. Its `omega_dh` drops every term below an absolute floor of
10^-(dps+8), so it returns exactly 0 once e^{-pi x/5} falls below the floor, which
at dps 75 is u > 2.86. That is harmless where jensen_clock uses the table (indices
to 400 at dps 130 to 180, measured below) and wrong here, where the peak of the
n = 3200 integrand sits at u = 3.62. This probe keeps jensen_clock's construction,
`make_nodes` and its two node sets, and replaces only the floor by a relative
cutoff (`omega_dh_rel`). The literal table is compared with this one in
`floor_record`, and `gammas_from_nodes` itself is reproduced on the same nodes.

Route A: that table for n = 50..3296 on both node sets, dps 60 + 15 guard.
Route B, no quadrature: in v = 2u, M_{2y} = 2^{1-2y} sum_m m a_m I_m(y) with
I_m(y) = int v^{2y} e^{3v/4 - (pi m^2/5) e^v} dv, each a Laplace integral with
saddle (pi m^2/5) e^v = 3/4 + 2y/v. Phase 0's series is carried with DH's
constants to M = 6 corrections for m = 1..4, and log gamma(n + j) is evaluated
directly at each j (phase 1's direct route B). The stated error is the larger of
the last two Laplace increments, |M6 - M5| and |M5 - M4|.

Normalisation. By the duplication formula, log gamma_DH(x) = -log Gamma(x + 1/2)
+ log I_1(x) + (linear in x) up to the m >= 2 terms, which is Holland's eq. (14)
shape with b = n + 1/2 and h = log I_1. Phase 1's leading-order reduction reads h
only through h''(x) ~ (2/L)/x, and for DH that L is the saddle of I_1(n),
(pi/5) e^L = 3/4 + 2n/L, written L_DH here. Every normalised column uses L_DH;
a choice differing from it by O(1/n) changes no limit.

Grade: measured. Nothing here bears on RH.
"""

from __future__ import annotations

import argparse
import json
import platform
import sys
import time
from pathlib import Path

import mpmath
from mpmath import mp, mpf

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(ROOT))

from hunts.jensen_clock import probe as jc  # noqa: E402
from hunts.jensen_wedge import probe as p0  # noqa: E402
from hunts.jensen_wedge import probe_phase1 as p1  # noqa: E402
from zeta.epstein import kappa  # noqa: E402

GUARD = p0.GUARD
N_LO, N_HI = p0.N_LO, p0.N_HI
J6 = p1.J6
SUBGRID = p0.SUBGRID
ROUTE_B_MAP_NS = p1.ROUTE_B_SUBGRID
LARGE_NS = p1.LARGE_NS
THETA_LARGE = p1.THETA_LARGE
ROOT_N, ROOT_DS = p1.ROOT_N, p1.ROOT_DS
#: the low end of the measured range, at degrees where the monomial basis is cheap
ROOT_N_LOW, ROOT_DS_LOW = 50, (6, 12, 24)
K_LO, K_HI = N_LO, ROOT_N + max(ROOT_DS)
#: jensen_clock's two node sets (its stage `validate`): (U, segments, Gauss-Legendre
#: level, which mpmath turns into 3 * 2^(level-1) nodes per segment)
QUADS = (("4.2", 16, 7), ("3.9", 13, 8))
#: the node set of the dps-275 root-geometry block; level 7 holds only 1e-183 there
QUAD_HP = ("4.2", 16, 8)
DPS_HP = 260
M_ROUTE_B = p0.M_ROUTE_B
#: theta terms carried by route B: a_5 = 0, and m = 6 is below 1e-100 relative
LAPLACE_TERMS = 4
#: the contrast: d either side of jensen_clock's d* = 20785.13 at n = 0, and n = 1
CONTRAST_CELLS = ((20000, 0), (22000, 0), (30000, 1))
FLOOR_NS = (50, 100, 200, 400, 800, 1600, 3200)
CLOCK_RESULTS = HERE.parent / "jensen_clock" / "results.json"


def s(x, digits: int = 15) -> str:
    return mpmath.nstr(x, digits)


_KAPPA: dict = {}


def kap_at(dps: int):
    if dps not in _KAPPA:
        _KAPPA[dps] = kappa(dps)
    return _KAPPA[dps]


# ---------------------------------------------------------------------------
# route A: jensen_clock's DH table, with a relative cutoff in omega
# ---------------------------------------------------------------------------


def omega_dh_rel(x, kap):
    """jensen_clock's omega_dh, summed as e^{-pi x/5} (1 + sum_{m>=2} m a_m
    e^{-pi (m^2-1) x/5}) until a term is below 2^-(prec+20) of the leading one."""
    a_pat = (mpf(1), kap, -kap, mpf(-1), mpf(0))
    eps = mpf(2) ** (-(mp.prec + 20))
    tot, m = mpf(1), 2
    while True:
        t = mp.exp(-mp.pi * (m * m - 1) * x / 5)
        a = a_pat[(m - 1) % 5]
        if a != 0:
            tot += m * a * t
        if m * t < eps:
            return mp.exp(-mp.pi * x / 5) * tot
        m += 1


def dh_nodes(dps: int, U, segs: int, gldeg: int, floor: bool = False) -> list:
    """jensen_clock's node table (make_nodes) for Phi_DH. floor=True puts the
    literal jc.omega_dh back, which is jc.dh_nodes exactly: for the record of the
    floor and for the planted-fault test."""
    kap = kap_at(dps)
    omega = jc.omega_dh if floor else omega_dh_rel
    with mp.workdps(dps):
        return jc.make_nodes(
            lambda u: 4 * mp.exp(mpf(3) / 2 * u) * omega(mp.exp(2 * u), kap), U, segs, gldeg, dps)


def moments(nodes: list, k_lo: int, k_hi: int, dps: int) -> dict:
    """M_{2k} = sum_i w_i u_i^{2k}, k_lo <= k <= k_hi: the sum gammas_from_nodes
    forms, with u^{2k} advanced by one multiplication per index."""
    with mp.workdps(dps):
        pw = [w * u ** (2 * k_lo) for u, w in nodes]
        u2 = [u * u for u, _ in nodes]
        out = {}
        for k in range(k_lo, k_hi + 1):
            out[k] = mp.fsum(pw)
            if k < k_hi:
                pw = [a * b for a, b in zip(pw, u2)]
    return out


def log_gamma_table(M: dict, dps: int) -> dict:
    """log gamma(m) = log m! - log (2m)! + log M_{2m}."""
    with mp.workdps(dps):
        return {m: mp.loggamma(m + 1) - mp.loggamma(2 * m + 1) + mp.log(v) for m, v in M.items()}


def route_A(dps: int, k_lo: int = K_LO, k_hi: int = K_HI, quads=QUADS, floor: bool = False):
    """log gamma on each node set, and the largest |difference| between them."""
    w = dps + GUARD
    tables = []
    for q in quads:
        tables.append(log_gamma_table(moments(dh_nodes(w, *q, floor=floor), k_lo, k_hi, w), w))
    with mp.workdps(w):
        dev = max(abs(tables[0][m] - t[m]) for t in tables[1:] for m in tables[0])
    return tables[0], dev


def check_two_quadratures(dev, dps: int) -> None:
    if dev > mpf(10) ** (-(dps - 5)):
        raise RuntimeError(f"the two DH node sets disagree: max |d log gamma| = {s(dev, 3)}")


# ---------------------------------------------------------------------------
# route B: Laplace series of each theta term, no quadrature
# ---------------------------------------------------------------------------


def saddle_gen(y, a, c):
    """v* with c e^{v*} = a + 2y/v*; (a, c) = (1/4, pi) is p0.saddle."""
    y = mpf(y)
    g = mp.log(2 * y / c)
    guess = g - mp.log(g) if g > 2 else mpf(1)
    return mp.findroot(lambda v: c * mp.exp(v) - a - 2 * y / v, guess)


def L_dh(n):
    """L_DH(n): the saddle of I_1(n), (pi/5) e^L = 3/4 + 2n/L."""
    return saddle_gen(n, mpf(3) / 4, mp.pi / 5)


def log_I_laplace_gen(y, M: int, a, c):
    """p0.log_I_laplace for log int exp(2y log v + a v - c e^v) dv; with
    (a, c) = (1/4, pi) it is phase 0's series exactly."""
    y = mpf(y)
    v = saddle_gen(y, a, c)
    ev = mp.exp(v)
    A = 2 * y / v**2 + c * ev
    psi = {k: 2 * y * (-1) ** (k - 1) * mp.factorial(k - 1) / v**k - c * ev
           for k in range(3, 2 * M + 3)}
    p = {w: (psi[w + 2] / mp.factorial(w + 2), w + 2) for w in range(1, 2 * M + 1)}
    e = [{0: mpf(1)}]
    for w in range(1, 2 * M + 1):
        acc: dict = {}
        for k in range(1, w + 1):
            cf, deg = p[k]
            for d, val in e[w - k].items():
                acc[d + deg] = acc.get(d + deg, mpf(0)) + k * cf * val
        e.append({d: val / w for d, val in acc.items()})
    corr = mpf(0)
    for w in range(2, 2 * M + 1, 2):
        for d, val in e[w].items():
            if d % 2 == 0:
                corr += val * mp.fac2(d - 1) / A ** (d // 2)
    psi0 = 2 * y * mp.log(v) + a * v - c * ev
    return psi0 + mp.log(2 * mp.pi / A) / 2 + mp.log1p(corr)


def log_gamma_saddle(x, M: int, terms: int = LAPLACE_TERMS) -> tuple:
    """(log gamma_DH(x), relative size of the m >= 2 theta terms) for real x."""
    x = mpf(x)
    kap = kap_at(mp.dps)
    coef = (mpf(1), 2 * kap, -3 * kap, mpf(-4))[:terms]
    logs = [log_I_laplace_gen(x, M, mpf(3) / 4, mp.pi * m * m / 5) for m in range(1, terms + 1)]
    rest = mp.fsum(cf * mp.exp(lg - logs[0]) for cf, lg in zip(coef[1:], logs[1:]))
    head = mp.loggamma(x + 1) - mp.loggamma(2 * x + 1) + (1 - 2 * x) * mp.log(2)
    return head + logs[0] + mp.log1p(rest), rest


def lr_B(n, M: int, top: int = J6) -> list:
    base = log_gamma_saddle(mpf(n), M)[0]
    return [mpf(0)] + [log_gamma_saddle(mpf(n) + j, M)[0] - base for j in range(1, top + 1)]


# ---------------------------------------------------------------------------
# the construction at one n, and what the prediction asks of it
# ---------------------------------------------------------------------------


def construction(lr: list, n, Ln, guess_ff=None, guess_pade=None) -> dict:
    """Holland's three fits (phase 0) and the Pade solve (phase 1) from log R_0..R_6."""
    lq = p0.log_q_from_log_R(lr)
    d = p0.defects(lr, n, Ln, guess_ff)
    pade = p1.pade_solve(lq, n, guess_pade or p1.pade_guess(n, Ln))
    return {"lq": lq, "lag": d["lag"], "jac": d["jac"], "ff": d["ff"], "pade": pade}


def prediction_at(c: dict) -> dict:
    """The items of the prediction that one value of n can decide."""
    ff, jac, pd = c["ff"], c["jac"], c["pade"]
    return {
        "laguerre_D3_positive": bool(c["lag"]["D3"] > 0),
        "jacobi_E_J4_negative": bool(jac["E_J4"] < 0),
        "E_F5_negative_at_theta_half": bool(ff["E_F5"] < 0),
        "holland_parameters_positive_C_gt_D": bool(
            jac["A_J"] > 0 and jac["B_J"] > 0 and ff["A"] > 0 and ff["B"] > 0
            and ff["C"] > ff["D"] > 0),
        "pade_positive_A_gt_B_C_gt_D": bool(pd["A"] > pd["B"] > 0 and pd["C"] > pd["D"] > 0),
    }


def normalised(c: dict, n, Ln) -> dict:
    """The columns of RESULTS.md sections 4, 5 and 11.3, with L = L_DH."""
    n = mpf(n)
    ff, jac = c["ff"], c["jac"]
    return {
        "n2L_D3_over_2": s(n ** 2 * Ln * c["lag"]["D3"] / 2, 10),
        "minus_n3L_EJ4_over_2": s(-(n ** 3) * Ln * jac["E_J4"] / 2, 10),
        "n4L_EF5": s(n ** 4 * Ln * ff["E_F5"], 10),
        "A_over_A_J": s(ff["A"] / jac["A_J"], 10),
        "B_minus_B_J_times_L_over_n": s((ff["B"] - jac["B_J"]) * Ln / n, 10),
        "C_minus_D_times_L_over_n": s((ff["C"] - ff["D"]) * Ln / n, 10),
    }


# ---------------------------------------------------------------------------
# the jensen_clock floor, and the n = 0 contrast
# ---------------------------------------------------------------------------


def floor_record(dps: int, rel: dict) -> dict:
    """Where jc.omega_dh's absolute floor cuts at this precision, the literal
    table against `rel` (route A on jensen_clock's default node set), and
    gammas_from_nodes reproduced by `moments` on the same nodes."""
    w = dps + GUARD
    kap = kap_at(w)
    with mp.workdps(w):
        # jc.omega_dh's first term passes its floor while e^{-pi x/5} >= 10^-(dps+8)
        x_cut = 5 * (w + 8) * mp.log(10) / mp.pi
        u_cut = mp.log(x_cut) / 2
        below = jc.omega_dh(mp.exp(2 * (u_cut - mpf("0.01"))), kap)
        above = jc.omega_dh(mp.exp(2 * (u_cut + mpf("0.01"))), kap)
        nd_lit, nd_rel = dh_nodes(w, *QUADS[0], floor=True), dh_nodes(w, *QUADS[0])
        zeroed = sum(1 for (_, a) in nd_lit if a == 0)
        lit = log_gamma_table(moments(nd_lit, FLOOR_NS[0], FLOOR_NS[-1], w), w)
        G = jc.gammas_from_nodes(nd_rel, 60, w)
        repro = max(abs(mp.log(G[m]) - rel[m]) for m in range(50, 61))
        return {
            "dps_work": w, "u_where_jc_omega_dh_turns_zero": s(u_cut, 6),
            "jc_omega_dh_just_below_and_above": [s(below, 3), s(above, 3)],
            "nodes_with_zero_weight_literal": zeroed, "nodes": len(nd_lit),
            "literal_minus_relative_log_gamma": {
                str(m): s(lit[m] - rel[m], 3) for m in FLOOR_NS},
            "gammas_from_nodes_reproduced_m50_60_max_abs_dlog": s(repro, 3),
        }


def contrast(dps: int = jc.DPS) -> dict:
    """DH's own Jensen non-hyperbolicity at n = 0, with jensen_clock's instrument
    (pair_delta on the damped series) on both tables at jensen_clock's precision."""
    t0 = time.perf_counter()
    jmax = jc.JMAX_DEFAULT + 8
    G_lit = jc.gammas_from_nodes(jc.dh_nodes(dps), jmax, dps)
    M = moments(dh_nodes(dps, *QUADS[0]), 0, jmax, dps)
    with mp.workdps(dps):
        G = [mp.factorial(m) / mp.factorial(2 * m) * M[m] for m in range(jmax + 1)]
        lit_dev = max(abs(a / b - 1) for a, b in zip(G_lit, G))
        x0 = jc.pair_x0(jc.flow_repair_pair1(), dps)
        cells = []
        for d, n in CONTRAST_CELLS:
            row = {"d": d, "n": n}
            for name, table in (("relative_cutoff", G), ("jensen_clock_literal", G_lit)):
                rec = jc.pair_delta(jc._shifted_coeffs(table, n, d, dps), mp.re(x0), 70, dps)
                delta = mp.re(rec["delta"])
                row[name] = {
                    "contour_count": s(mp.re(rec["count"]), 6), "delta": s(delta, 10),
                    "complex_pair_present": bool(abs(rec["count"] - 2) < mpf("1e-6") and delta < 0)}
            cells.append(row)
    # jensen_clock's largest table (stage pair2: dps 180, j <= 400, its node set),
    # to read whether the floor touches any number jensen_clock recorded
    dps2, jmax2, q2 = 180, 400, ("4.2", 18, 7)
    G2_lit = jc.gammas_from_nodes(jc.dh_nodes(dps2, U=q2[0], segs=q2[1], gldeg=q2[2]), jmax2, dps2)
    M2 = moments(dh_nodes(dps2, *q2), 0, jmax2, dps2)
    with mp.workdps(dps2):
        lit_dev2 = max(abs(a / (mp.factorial(m) / mp.factorial(2 * m) * M2[m]) - 1)
                       for m, a in enumerate(G2_lit))
    clock = json.loads(CLOCK_RESULTS.read_text())
    return {
        "dps": dps, "jmax": jmax,
        "table_max_rel_dev_literal_vs_relative_cutoff": s(lit_dev, 3),
        "pair2_table_dps180_j400_max_rel_dev_literal_vs_relative_cutoff": s(lit_dev2, 3),
        "cells": cells,
        "jensen_clock_record": {
            "pair1_dstar": clock["dstar"]["dstar"],
            "pair1_dstar_rel_spread_over_four_quadratures": clock["precision"]["dstar_max_rel_spread"],
            "pair2_dstar": clock["pair2"]["dstar"],
            "map2_cells": [{k: c[k] for k in ("d", "n", "detected", "contour_count")}
                           for c in clock["map2"]["cells"]],
        },
        "seconds": round(time.perf_counter() - t0, 1),
    }


# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------


def git_head() -> str:
    return p0.git_head()


def time_unit(dps: int) -> None:
    w = dps + GUARD
    t0 = time.perf_counter()
    nodes = dh_nodes(w, *QUADS[0])
    print(f"[unit] node set {QUADS[0]} at dps {w}: {len(nodes)} nodes, "
          f"{time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    M = moments(nodes, 3233, 3296, w)
    print(f"[unit] route A, 64 moments k=3233..3296: {time.perf_counter() - t0:.2f} s")
    n = 3200
    with mp.workdps(w):
        M = moments(nodes, n, n + J6, w)
        ell = log_gamma_table(M, w)
        lr = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, J6 + 1)]
        Ln = L_dh(n)
        t0 = time.perf_counter()
        c = construction(lr, n, Ln)
        print(f"[unit] construction (three fits + Pade) n={n}: {time.perf_counter() - t0:.2f} s")
        t0 = time.perf_counter()
        half = p1.family_from_holland(c["lq"], n, c["jac"]["B_J"], c["ff"])
        p1.family_walk(c["lq"], n, c["jac"]["B_J"], half, "0.85")
        print(f"[unit] family walk 0.5 -> 0.85 n={n}: {time.perf_counter() - t0:.2f} s")
        t0 = time.perf_counter()
        lr_B(n, M_ROUTE_B)
        print(f"[unit] route B direct log R_0..6 n={n}: {time.perf_counter() - t0:.2f} s")
    with mp.workdps(int(5 * mp.log10(mpf(10) ** 20)) + 50 + GUARD):
        t0 = time.perf_counter()
        lr_B(10 ** 20, M_ROUTE_B)
        print(f"[unit] route B direct log R_0..6 n=1e20: {time.perf_counter() - t0:.2f} s")
    t0 = time.perf_counter()
    jc.gammas_from_nodes(jc.dh_nodes(jc.DPS), 60, jc.DPS)
    print(f"[unit] literal jensen_clock table to j=60 at dps {jc.DPS}: "
          f"{time.perf_counter() - t0:.2f} s (the contrast needs j=328)")
    t0 = time.perf_counter()
    dh_nodes(DPS_HP + GUARD, *QUAD_HP)
    print(f"[unit] node set {QUAD_HP} at dps {DPS_HP + GUARD}: {time.perf_counter() - t0:.2f} s")


def run(dps: int, out: Path) -> dict:
    t_start = time.perf_counter()
    w = dps + GUARD
    report: dict = {
        "hunt": "jensen_wedge", "phase": "rival gate (Davenport-Heilbronn)", "grade": "measured",
        "prediction": "the construction succeeds for DH exactly as for zeta: Holland's sign facts "
                      "at R_3 and R_4, the sign map of E_F(5), and the [2/2] Pade match of R_5 "
                      "with all parameters positive (MISSION.md, 'The rival gate')",
        "git_head": git_head(), "python": platform.python_version(),
        "mpmath": mpmath.__version__, "dps": dps,
        "kappa": s(kap_at(w), 30),
    }

    # --- route A, both node sets -------------------------------------------
    t0 = time.perf_counter()
    ell, dev = route_A(dps)
    check_two_quadratures(dev, dps)
    report["route_A"] = {"m_range": [K_LO, K_HI], "node_sets": [list(q) for q in QUADS],
                         "max_abs_dlog_gamma_between_node_sets": s(dev, 3),
                         "seconds": round(time.perf_counter() - t0, 1)}
    print(f"[route A] {report['route_A']}", flush=True)

    print("[floor] jensen_clock's omega_dh at this precision", flush=True)
    report["jensen_clock_floor"] = floor_record(dps, ell)
    print(f"  {report['jensen_clock_floor']}", flush=True)

    def lr_A(n, top=J6):
        return [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, top + 1)]

    # --- every n on route A: the three fits upward, the Pade solve downward --
    t0 = time.perf_counter()
    dense, guess = {}, None
    with mp.workdps(w):
        for n in range(N_LO, N_HI + 1):
            Ln = L_dh(n)
            lr = lr_A(n)
            lq = p0.log_q_from_log_R(lr)
            d = p0.defects(lr, n, Ln, guess)
            guess = (d["ff"]["A"], d["ff"]["B"], d["ff"]["C"])
            dense[n] = {"Ln": Ln, "lq": lq, "lag": d["lag"], "jac": d["jac"], "ff": d["ff"]}
        guess = None
        for n in range(N_HI, N_LO - 1, -1):
            row = dense[n]
            row["pade"] = p1.pade_solve(row["lq"], n, guess or p1.pade_guess(n, row["Ln"]))
            guess = row["pade"]["x"]
    ns = list(range(N_LO, N_HI + 1))

    def signs(key):
        vals = [key(dense[n]) for n in ns]
        pos = sum(1 for v in vals if v > 0)
        neg = sum(1 for v in vals if v < 0)
        flips = [ns[i + 1] for i in range(len(vals) - 1) if (vals[i] > 0) != (vals[i + 1] > 0)]
        return {"positive": pos, "negative": neg, "zero": len(vals) - pos - neg,
                "sign_changes_at_n": flips}

    preds = {n: prediction_at(dense[n]) for n in ns}
    report["dense_route_A"] = {
        "n_count": len(ns),
        "laguerre_D3": signs(lambda r: r["lag"]["D3"]),
        "jacobi_E_J4": signs(lambda r: r["jac"]["E_J4"]),
        "finite_free_E_F5_theta_half": signs(lambda r: r["ff"]["E_F5"]),
        "pade_E_S6": signs(lambda r: r["pade"]["E_S6"]),
        "holland_parameters_positive_C_gt_D_at_every_n": all(
            p["holland_parameters_positive_C_gt_D"] for p in preds.values()),
        "pade_positive_A_gt_B_C_gt_D_at_every_n": all(
            p["pade_positive_A_gt_B_C_gt_D"] for p in preds.values()),
        "max_match_residual": s(max(max(r["lag"]["match_residual"], r["jac"]["match_residual"],
                                        r["ff"]["match_residual"], r["pade"]["res"])
                                    for r in dense.values()), 3),
        "seconds": round(time.perf_counter() - t0, 1),
    }
    print(f"[dense A] {json.dumps(report['dense_route_A'])}", flush=True)

    # --- the subgrid, both routes --------------------------------------------
    t0 = time.perf_counter()
    rows = []
    with mp.workdps(w):
        for n in SUBGRID:
            r = dense[n]
            Ln = r["Ln"]
            lrA = lr_A(n)
            lrBs = {M: lr_B(n, M) for M in (M_ROUTE_B, M_ROUTE_B - 1, M_ROUTE_B - 2)}
            stated = [max(abs(lrBs[M_ROUTE_B][j] - lrBs[M_ROUTE_B - 1][j]),
                          abs(lrBs[M_ROUTE_B - 1][j] - lrBs[M_ROUTE_B - 2][j])) for j in range(J6 + 1)]
            devAB = [abs(lrA[j] - lrBs[M_ROUTE_B][j]) for j in range(J6 + 1)]
            guess_ff = (r["ff"]["A"], r["ff"]["B"], r["ff"]["C"])
            cB = {M: construction(lrBs[M], n, Ln, guess_ff, r["pade"]["x"]) for M in lrBs}
            b = cB[M_ROUTE_B]
            keys = (("lag", "D3"), ("jac", "E_J4"), ("ff", "E_F5"), ("pade", "E_S6"))
            row = {"n": n, "L_DH": s(Ln, 12), "zeta_L_n": s(p0.script_L(n), 12),
                   "m_ge_2_theta_terms_relative": s(log_gamma_saddle(mpf(n), M_ROUTE_B)[1], 3),
                   "logR_A_minus_B": [s(v, 3) for v in devAB[1:]],
                   "logR_B_stated_error": [s(v, 3) for v in stated[1:]],
                   "route_B_within_stated_error": all(devAB[j] <= stated[j] for j in range(1, J6 + 1))}
            agree, resolve = [], []
            for a, k in keys:
                va, vb = r[a][k], b[a][k]
                spread = max(abs(vb - cB[M][a][k]) for M in lrBs if M != M_ROUTE_B)
                row[f"{k}_A"], row[f"{k}_B"], row[f"{k}_B_spread"] = s(va, 12), s(vb, 12), s(spread, 3)
                agree.append(bool((va > 0) == (vb > 0)))
                resolve.append(bool(spread < abs(vb)))
            row["signs_agree_A_B_D3_EJ4_EF5_ES6"] = agree
            row["B_resolves_sign_D3_EJ4_EF5_ES6"] = resolve
            row.update(normalised(r, n, Ln))
            row["n5L_E_S6"] = s(mpf(n) ** 5 * Ln * r["pade"]["E_S6"], 10)
            row["pade"] = p1.pade_row(n, Ln, r["pade"], r["jac"]["B_J"])
            row["prediction_items_A"] = preds[n]
            row["prediction_items_B"] = prediction_at(b)
            rows.append(row)
            print(f"[subgrid] n={n} D3={row['D3_A']} EJ4={row['E_J4_A']} EF5={row['E_F5_A']} "
                  f"ES6={row['E_S6_A']} agree={agree} resolve={resolve} "
                  f"within={row['route_B_within_stated_error']}", flush=True)
    report["subgrid"] = rows
    report["subgrid_seconds"] = round(time.perf_counter() - t0, 1)

    # --- the sign map of E_F(5) over (theta, n) --------------------------------
    t0 = time.perf_counter()
    maps = []
    with mp.workdps(w):
        for n in SUBGRID:
            r = dense[n]
            Ln, lq, BJ = r["Ln"], r["lq"], r["jac"]["B_J"]
            half = p1.family_from_holland(lq, n, BJ, r["ff"])
            m = p1.family_map(lq, n, BJ, half, p1.THETA_MAP)
            row = {"n": n, "L_DH": s(Ln, 10), "failed": m["failed"],
                   "theta_star": s(m["theta_star"], 12) if m["theta_star"] else None,
                   "theta_inf": s(m["theta_inf"], 12) if m["theta_inf"] else None,
                   "pade_D_over_B_J": s(r["pade"]["D"] / BJ, 12), "grid": {}}
            for th, f in sorted(m["solutions"].items()):
                row["grid"][s(th, 6)] = {
                    "E_F5": s(f["E_F5"], 12), "n4L_E_F5": s(n ** 4 * Ln * f["E_F5"], 8),
                    "A_positive": bool(f["w_A"] > 0), "match_residual": s(f["res"], 3)}
            if m["theta_star"] and m["theta_inf"]:
                row["one_minus_theta_star_times_L"] = s((1 - m["theta_star"]) * Ln, 8)
                row["one_minus_theta_inf_times_L"] = s((1 - m["theta_inf"]) * Ln, 8)
                row["window_times_L"] = s((m["theta_inf"] - m["theta_star"]) * Ln, 8)
            maps.append(row)
            print(f"[map A] n={n} theta*={row['theta_star']} theta_inf={row['theta_inf']} "
                  f"pade D/B_J={row['pade_D_over_B_J']} failed={list(m['failed'])}", flush=True)
    report["theta_map_route_A"] = maps

    maps_B = []
    with mp.workdps(w):
        for n in ROUTE_B_MAP_NS:
            r = dense[n]
            Ln = r["Ln"]
            lr = lr_B(n, M_ROUTE_B)
            c = construction(lr, n, Ln, (r["ff"]["A"], r["ff"]["B"], r["ff"]["C"]), r["pade"]["x"])
            BJ = c["jac"]["B_J"]
            half = p1.family_from_holland(c["lq"], n, BJ, c["ff"])
            m = p1.family_map(c["lq"], n, BJ, half, p1.THETA_MAP)
            rowA = {x["n"]: x for x in maps}[n]
            maps_B.append({
                "n": n, "failed": m["failed"],
                "theta_star_B": s(m["theta_star"], 12) if m["theta_star"] else None,
                "theta_inf_B": s(m["theta_inf"], 12) if m["theta_inf"] else None,
                "theta_star_A": rowA["theta_star"], "theta_inf_A": rowA["theta_inf"],
                "abs_theta_star_A_minus_B": s(abs(m["theta_star"] - mpf(rowA["theta_star"])), 3)
                if m["theta_star"] and rowA["theta_star"] else None})
            print(f"[map B] {maps_B[-1]}", flush=True)
    report["theta_map_route_B"] = maps_B
    report["theta_map_seconds"] = round(time.perf_counter() - t0, 1)

    # --- route B alone at large n ---------------------------------------------
    t0 = time.perf_counter()
    large = []
    for n_str in LARGE_NS:
        n = int(mpf(n_str))
        dps_n = int(5 * mp.log10(n)) + 50
        with mp.workdps(dps_n + GUARD):
            Ln = L_dh(n)
            per_M = {}
            for M in (M_ROUTE_B, M_ROUTE_B - 1):
                lr = lr_B(n, M)
                c = construction(lr, n, Ln)
                BJ = c["jac"]["B_J"]
                half = p1.family_from_holland(c["lq"], n, BJ, c["ff"])
                fam = {th: p1.family_walk(c["lq"], n, BJ, half, th) for th in THETA_LARGE}
                top = tuple(1 - mpf(k) / 100 / Ln for k in range(120, 19, -5))
                star = p1.family_map(c["lq"], n, BJ, half, top)
                per_M[M] = (c, fam, star)
            c, fam, star = per_M[M_ROUTE_B]
            c5, fam5, _ = per_M[M_ROUTE_B - 1]
            row = {"n": n_str, "dps": dps_n, "L_DH": s(Ln, 12), "zeta_L_n": s(p0.script_L(n), 12)}
            row.update(normalised(c, n, Ln))
            row["pade"] = p1.pade_row(n, Ln, c["pade"], c["jac"]["B_J"])
            row["prediction_items"] = prediction_at(c)
            row["spread_M5_M6_rel"] = {
                k: s(abs(c[a][k] - c5[a][k]) / abs(c[a][k]), 3)
                for a, k in (("lag", "D3"), ("jac", "E_J4"), ("ff", "E_F5"), ("pade", "E_S6"))}
            row["family"] = {
                th: {"n4L_E_F5": s(mpf(n) ** 4 * Ln * f["E_F5"], 10),
                     "first_order_prediction": s(-4 * (2 - mpf(th)) / mpf(th), 6),
                     "spread_M5_M6_rel": s(abs(f["E_F5"] - fam5[th]["E_F5"]) / abs(f["E_F5"]), 3)}
                for th, f in fam.items()}
            row["theta_star"] = s(star["theta_star"], 14) if star["theta_star"] else None
            row["theta_inf"] = s(star["theta_inf"], 14) if star["theta_inf"] else None
            row["theta_map_failed"] = star["failed"]
            if star["theta_star"]:
                row["one_minus_theta_star_times_L"] = s((1 - star["theta_star"]) * Ln, 10)
            if star["theta_inf"]:
                row["one_minus_theta_inf_times_L"] = s((1 - star["theta_inf"]) * Ln, 10)
            large.append(row)
        print(f"[large n] {n_str}: L_DH={row['L_DH']} theta*={row['theta_star']} "
              f"items={row['prediction_items']}", flush=True)
    report["large_n_route_B"] = large
    report["large_n_seconds"] = round(time.perf_counter() - t0, 1)

    # --- root geometry: the Jensen polynomials of DH at n = 3200 and n = 50 -----
    # same reason as phase 1 for a separate high-precision block (degree-96
    # polynomials in the monomial basis lose about 140 digits)
    t0 = time.perf_counter()
    whp = DPS_HP + GUARD
    hp_nodes = dh_nodes(whp, *QUAD_HP)
    geo = {"high_precision_block": {"dps": DPS_HP, "node_set": list(QUAD_HP)}}
    for n0, ds in ((ROOT_N, ROOT_DS), (ROOT_N_LOW, ROOT_DS_LOW)):
        ell_hp = log_gamma_table(moments(hp_nodes, n0, n0 + max(ds), whp), whp)
        with mp.workdps(whp):
            agree = max(abs(ell_hp[m] - ell[m]) for m in range(n0, n0 + max(ds) + 1))
            if agree > mpf(10) ** -(dps + 5):
                raise RuntimeError(f"dps-{DPS_HP} block disagrees with the main table at n={n0}: {agree}")
            logR_all = [mpf(0)] + [ell_hp[n0 + j] - ell_hp[n0] for j in range(1, max(ds) + 1)]
        r = dense[n0]
        models = {"holland_theta_half": [(r["ff"]["A"], r["ff"]["B"]), (r["ff"]["C"], r["ff"]["D"])],
                  "pade": [(r["pade"]["A"], r["pade"]["B"]), (r["pade"]["C"], r["pade"]["D"])]}
        block = {"max_abs_dlog_gamma_vs_dps60_table": s(agree, 3)}
        for name, fac in models.items():
            block[name] = {"factors": [[s(U, 12), s(V, 12)] for U, V in fac], "by_d": []}
            for d in ds:
                block[name]["by_d"].append(p1.root_geometry(d, fac, logR_all, dps=60 + 2 * d))
                print(f"[roots n={n0}] {name} {block[name]['by_d'][-1]}", flush=True)
        geo[f"n{n0}"] = block
    report["root_geometry"] = geo
    report["root_geometry_seconds"] = round(time.perf_counter() - t0, 1)

    # --- the contrast: DH non-hyperbolic at n = 0 --------------------------------
    print("[contrast] n = 0 and n = 1 with jensen_clock's instrument", flush=True)
    report["contrast_n0"] = contrast()
    print(f"  {report['contrast_n0']['cells']}", flush=True)

    report["verdict"] = verdict(report)
    report["total_seconds"] = round(time.perf_counter() - t_start, 1)
    out.write_text(json.dumps(report, indent=1) + "\n")
    print(f"[done] {json.dumps(report['verdict'], indent=1)} in {report['total_seconds']} s; wrote {out}")
    return report


def verdict(rep: dict) -> dict:
    """Grade the prediction from the record alone, so a test can re-grade it."""
    da = rep["dense_route_A"]
    sub = rep["subgrid"]
    large = rep["large_n_route_B"]
    maps = rep["theta_map_route_A"]
    maps_B = rep["theta_map_route_B"]

    def map_ok(r):
        ts, ti = r["theta_star"], r["theta_inf"]
        if r["failed"] or ts is None or ti is None or not float(ts) < float(ti):
            return False
        for th, g in r["grid"].items():
            t = float(th)
            if t < float(ts) and not (float(g["E_F5"]) < 0 and g["A_positive"]):
                return False
            if t > float(ti) and g["A_positive"]:
                return False
        return True

    items = {
        "laguerre_R3_positive_every_n_route_A": da["laguerre_D3"]["negative"] == 0
        and da["laguerre_D3"]["zero"] == 0,
        "jacobi_R4_negative_every_n_route_A": da["jacobi_E_J4"]["positive"] == 0
        and da["jacobi_E_J4"]["zero"] == 0,
        "sign_facts_route_B_agree_and_resolve_on_subgrid": all(
            all(r["signs_agree_A_B_D3_EJ4_EF5_ES6"][:2]) and all(r["B_resolves_sign_D3_EJ4_EF5_ES6"][:2])
            for r in sub),
        "sign_facts_route_B_large_n": all(
            r["prediction_items"]["laguerre_D3_positive"] and r["prediction_items"]["jacobi_E_J4_negative"]
            for r in large),
        "E_F5_negative_at_theta_half_every_n_both_routes": da["finite_free_E_F5_theta_half"]["positive"] == 0
        and da["finite_free_E_F5_theta_half"]["zero"] == 0
        and all(r["signs_agree_A_B_D3_EJ4_EF5_ES6"][2] and r["B_resolves_sign_D3_EJ4_EF5_ES6"][2] for r in sub)
        and all(r["prediction_items"]["E_F5_negative_at_theta_half"] for r in large),
        "theta_map_shape_route_A_every_subgrid_n": all(map_ok(r) for r in maps),
        "theta_star_route_B_matches_route_A": all(
            not r["failed"] and r["abs_theta_star_A_minus_B"] is not None
            and float(r["abs_theta_star_A_minus_B"]) < 1e-8 for r in maps_B),
        "theta_star_and_theta_inf_found_large_n": all(
            r["theta_star"] and r["theta_inf"] and float(r["theta_star"]) < float(r["theta_inf"])
            and not r["theta_map_failed"] for r in large),
        "pade_match_positive_every_n_route_A": da["pade_positive_A_gt_B_C_gt_D_at_every_n"],
        "pade_match_positive_large_n_route_B": all(
            r["prediction_items"]["pade_positive_A_gt_B_C_gt_D"] for r in large),
        "holland_parameters_positive_every_n": da["holland_parameters_positive_C_gt_D_at_every_n"]
        and all(r["prediction_items"]["holland_parameters_positive_C_gt_D"] for r in large),
    }
    further = {
        "pade_E_S6_negative_every_n_route_A": da["pade_E_S6"]["positive"] == 0
        and da["pade_E_S6"]["zero"] == 0,
        "pade_E_S6_route_B_agrees_and_resolves_on_subgrid": all(
            r["signs_agree_A_B_D3_EJ4_EF5_ES6"][3] and r["B_resolves_sign_D3_EJ4_EF5_ES6"][3] for r in sub),
        "route_B_within_stated_error_on_subgrid": all(r["route_B_within_stated_error"] for r in sub),
    }
    geo = rep.get("root_geometry", {})
    jensen_real = all(
        g["model_real_roots"] == g["d"] and g["jensen_real_roots"] == g["d"]
        for key in ("n3200", "n50") if key in geo
        for name in ("holland_theta_half", "pade") for g in geo[key][name]["by_d"])
    con = rep.get("contrast_n0", {})
    cells = {(c["d"], c["n"]): c for c in con.get("cells", [])}
    nonhyp = [(d, n) for (d, n), c in cells.items()
              if c["relative_cutoff"]["complex_pair_present"]]
    contrast_items = {
        "dh_complex_pair_at_n0_above_dstar": cells.get((22000, 0), {}).get(
            "relative_cutoff", {}).get("complex_pair_present") is True,
        "dh_pair_landed_at_n0_below_dstar": cells.get((20000, 0), {}).get(
            "relative_cutoff", {}).get("complex_pair_present") is False,
        "dh_pair_landed_at_n1": cells.get((30000, 1), {}).get(
            "relative_cutoff", {}).get("complex_pair_present") is False,
        "both_tables_agree_on_every_contrast_cell": all(
            c["relative_cutoff"]["complex_pair_present"] == c["jensen_clock_literal"]["complex_pair_present"]
            for c in cells.values()),
        "dh_jensen_polynomials_real_rooted_at_measured_wedge_cells": jensen_real,
        "non_hyperbolic_cells_found_at_n": sorted({n for _, n in nonhyp}),
        "smallest_n_of_the_wedge_measurement": N_LO,
    }
    contrast_items["no_overlap"] = bool(
        jensen_real and all(n < N_LO for _, n in nonhyp))
    held = all(items.values())
    return {"prediction_items": items, "prediction_held": held,
            "further_items_carried_over": further, "contrast": contrast_items}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--time-unit", action="store_true")
    ap.add_argument("--out", type=Path, default=HERE / "results_dh.json")
    args = ap.parse_args()
    if args.time_unit:
        time_unit(args.dps)
        return
    run(args.dps, args.out)


if __name__ == "__main__":
    main()
