"""Construction A: fake mass on attainable cells below the Mobius line.

Rows R_1..R_y of the T* matrix are unitriangular, so every attainable cell
q > y has the unique expansion R_q = sum_{s<=y} r^{(q)}_s R_s with integer
rates r^{(q)}_s = R_q(s) - R_q(s+1), R_q(t) = sum_{k<=y/t} mu(k) floor(q/(tk)).
Hence z_q := e_q - r^{(q)} is a zero-moment measure on Q_N of total mass
g_q := 1 - W_mu(q), and the zero-moment measures on Q_N are exactly the span
of {z_q : q in Q_N, q > y}.

Construction A.  For a set Q+ of attainable cells q > y with W_mu(q) < 1 and
weights theta_q >= 0, put delta = sum_q theta_q z_q.  Then

    support on Q_N, A^T delta = 0,
    m + delta >= 0   iff   sum_q theta_q r^{(q)}_s <= m_s for every s <= y,
    gain sum delta = sum_q theta_q (1 - W_mu(q))   (an exact rational).

It creates mass at q (which may carry no real prime power) by withdrawing it
from the prefix cells at the rates r^{(q)}.  This file evaluates:
  * single-cell bounds  theta_max(q) = min_{s : r_s > 0} m_s / r_s  and gains;
  * the additions-only LP over theta >= 0, rationalized and re-verified;
  * the constant-parameter version theta_q = t on Q+ ∩ (y, Y];
  * the two-sided LP (theta_q >= -m_q allowed), which must reproduce
    T*(y,N) - psi(N) exactly since the z_q span all zero-moment measures;
  * W_mu at the fake-only and emptied cells of the saved exact optimum.

Feasibility uses rigorous lower bounds on m_s (interval logs); gains that use
only theta and integers are exact rationals.  One thread; small sizes only.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

from dual_witness import build
from prefix_witness import mobius_table, prefix_rates


def construction_a(N: int, y: int, dps: int = 40, verbose: bool = True, greedy_steps: int = 25) -> dict:
    t0 = time.time()
    cells, idx, A, e, primes, ell = build(N, y)
    nq = cells.size
    mu = mobius_table(y)
    S0 = list(range(1, y + 1))
    if any(s not in idx for s in S0):
        raise RuntimeError("prefix cells not all attainable")
    # exact masses per cell as {p: count}
    mass_terms: dict[int, dict[int, int]] = {}
    for p in primes:
        for i, cnt in e[p].items():
            mass_terms.setdefault(i, {})[p] = cnt
    import mpmath

    iv = mpmath.iv
    iv.dps = dps
    mpmath.mp.dps = dps
    logs = {p: iv.log(iv.mpf(p)) for p in primes}

    def lo(x):
        return mpmath.mp.make_mpf(x._mpi_[0])

    def hi(x):
        return mpmath.mp.make_mpf(x._mpi_[1])

    def fr(x: Fraction):
        return iv.mpf(x.numerator) / iv.mpf(x.denominator)

    def mass_iv(i):
        tot = iv.mpf(0)
        for p, cnt in mass_terms.get(i, {}).items():
            tot += logs[p] * cnt
        return tot

    m_lo = {s: float(lo(mass_iv(idx[s]))) for s in S0}  # rigorous lower bounds
    m_f = {i: float(sum(math.log(p) * c for p, c in mt.items())) for i, mt in mass_terms.items()}

    above = [i for i in range(nq) if cells[i] > y]
    rates = {}
    g = {}
    for i in above:
        q = int(cells[i])
        r = prefix_rates(q, y, mu)  # integers as Fractions
        rates[i] = [int(x) for x in r]
        g[i] = 1 - sum(rates[i])  # = 1 - W_mu(q)
    Qplus = [i for i in above if g[i] > 0]
    Qminus = [i for i in above if g[i] < 0 and i in mass_terms]

    # single-cell rigorous bounds
    single = []
    for i in Qplus:
        pos = [(s, rates[i][s - 1]) for s in S0 if rates[i][s - 1] > 0]
        if not pos:
            theta_max, bind = float("inf"), None
        else:
            theta_max, bind = min((m_lo[s] / r, s) for s, r in pos)
        single.append({"q": int(cells[i]), "real_mass": m_f.get(i, 0.0), "gain_per_unit": g[i], "theta_max": theta_max, "binding_s": bind, "gain": theta_max * g[i] if theta_max != float("inf") else float("inf")})
    single.sort(key=lambda d: -d["gain"])

    # additions-only LP over theta >= 0
    def lp(cols, lower_bounds):
        obj = -np.array([g[i] for i in cols], dtype=float)
        M = np.array([[rates[i][s - 1] for i in cols] for s in S0], dtype=float)
        b = np.array([m_lo[s] for s in S0])
        res = linprog(obj, A_ub=M, b_ub=b, bounds=[(lb, None) for lb in lower_bounds], method="highs-ds")
        if res.status != 0:
            raise RuntimeError(res.message)
        return res

    den = 10**6
    if Qplus:
        resA = lp(Qplus, [0.0] * len(Qplus))
        gainA_f = float(-resA.fun)
        thetaA = {i: Fraction(int(math.floor(max(0.0, t) * den)), den) for i, t in zip(Qplus, resA.x)}
    else:
        gainA_f = 0.0
        thetaA = {}
    # rationalize theta downward and verify feasibility exactly-by-enclosure
    feasible = True
    min_slack = float("inf")
    for s in S0:
        drain = sum(thetaA[i] * rates[i][s - 1] for i in Qplus)
        slack = mass_iv(idx[s]) - fr(drain)
        min_slack = min(min_slack, float(lo(slack)))
        if lo(slack) < 0:
            feasible = False
    gainA = sum((thetaA[i] * g[i] for i in Qplus), Fraction(0))  # exact rational
    # moment identity of the rationalized delta, exact: sum_q delta_q floor(q/j) = 0
    ident = True
    for j in range(1, y + 1):
        tot = Fraction(0)
        for i in Qplus:
            if thetaA[i]:
                tot += thetaA[i] * (int(cells[i]) // j)
                tot -= thetaA[i] * sum(rates[i][s - 1] * (s // j) for s in S0)
        if tot != 0:
            ident = False
            break

    # ---------------- Construction B: pair exchanges a -> prefix -> b -------
    # delta = theta_b z_b - theta_a z_a with a a mass cell above y, b any other
    # cell above y.  Feasible iff theta_a <= m_a and, for every s <= y,
    # m_s + theta_a r^{(a)}_s - theta_b r^{(b)}_s >= 0.  Gain theta_b g_b - theta_a g_a.
    mass_above = [i for i in above if i in mass_terms]
    m_lo_cell = {i: float(lo(mass_iv(i))) for i in mass_above}

    def pair_lp(i_a, i_b, mcur_prefix, mcur_a):
        # variables (theta_a, theta_b)
        obj = np.array([g[i_a], -g[i_b]], dtype=float)  # minimise theta_a g_a - theta_b g_b
        rows = []
        rhs = []
        for s in S0:
            ra, rb = rates[i_a][s - 1], rates[i_b][s - 1]
            if ra != 0 or rb != 0:
                rows.append([-ra, rb])  # -theta_a ra + theta_b rb <= m_s
                rhs.append(mcur_prefix[s])
        res = linprog(obj, A_ub=np.array(rows) if rows else None, b_ub=np.array(rhs) if rows else None, bounds=[(0, mcur_a), (0, None)], method="highs-ds")
        if res.status != 0:
            return None
        return float(-res.fun), float(res.x[0]), float(res.x[1])

    # best single pairs from the real measure
    pairs = []
    for i_a in mass_above:
        for i_b in above:
            if i_b == i_a:
                continue
            r = pair_lp(i_a, i_b, m_lo, m_lo_cell[i_a])
            if r and r[0] > 1e-9:
                pairs.append({"a": int(cells[i_a]), "b": int(cells[i_b]), "b_has_mass": i_b in mass_terms, "gain": r[0], "theta_a": r[1], "theta_b": r[2], "g_a": g[i_a], "g_b": g[i_b]})
    pairs.sort(key=lambda d: -d["gain"])

    # greedy sequence of exchanges, masses updated after each; the sum is a witness
    mcur = dict(m_lo)
    mcur_cell = dict(m_lo_cell)
    greedy = []
    total = Fraction(0)
    delta_cells: dict[int, Fraction] = {}  # accumulated rational delta on cells (by cell value)
    for step in range(greedy_steps):
        best = None
        for i_a in mass_above:
            if mcur_cell[i_a] <= 1e-12:
                continue
            for i_b in above:
                if i_b == i_a:
                    continue
                r = pair_lp(i_a, i_b, mcur, mcur_cell[i_a])
                if r and r[0] > 1e-9 and (best is None or r[0] > best[0]):
                    best = (r[0], i_a, i_b, r[1], r[2])
        if best is None:
            break
        gain_f, i_a, i_b, ta, tb = best
        qa, qb = int(cells[i_a]), int(cells[i_b])
        # Rationalize and verify EXACTLY before accepting: shrink both amounts
        # by a common factor until the accumulated delta is feasible on every
        # touched cell (interval masses), since floor-rounding is not
        # sign-safe on the boundary of the pair LP.
        accepted = None
        for shrink in (1 - 1e-6, 1 - 1e-4, 1 - 1e-3, 0.99, 0.9):
            ta_r = Fraction(int(math.floor(ta * shrink * den)), den)
            tb_r = Fraction(int(math.floor(tb * shrink * den)), den)
            if ta_r < 0 or tb_r < 0:
                continue
            trial = dict(delta_cells)
            trial[qa] = trial.get(qa, Fraction(0)) - ta_r
            trial[qb] = trial.get(qb, Fraction(0)) + tb_r
            for s in S0:
                trial[s] = trial.get(s, Fraction(0)) + ta_r * rates[i_a][s - 1] - tb_r * rates[i_b][s - 1]
            ok_step = all(lo(mass_iv(idx[q]) + fr(dv)) >= 0 for q, dv in trial.items() if dv != 0)
            if ok_step:
                accepted = (ta_r, tb_r, trial)
                break
        if accepted is None:
            break
        ta_r, tb_r, delta_cells = accepted
        for s in S0:
            mcur[s] += float(ta_r * rates[i_a][s - 1] - tb_r * rates[i_b][s - 1])
        mcur_cell[i_a] -= float(ta_r)
        if i_b in mcur_cell:
            mcur_cell[i_b] += float(tb_r)
        step_gain = tb_r * g[i_b] - ta_r * g[i_a]
        total += step_gain
        greedy.append({"step": step + 1, "a": qa, "b": qb, "theta_a": str(ta_r), "theta_b": str(tb_r), "gain": float(step_gain), "cumulative": float(total)})
    # verify the accumulated greedy delta exactly: moments and feasibility
    gm_ident = all(sum(dv * (q // j) for q, dv in delta_cells.items()) == 0 for j in range(1, y + 1))
    gm_feasible = True
    gm_min = float("inf")
    for q, dv in delta_cells.items():
        i = idx[q]
        tot = mass_iv(i) + fr(dv)
        gm_min = min(gm_min, float(lo(tot)))
        if lo(tot) < 0:
            gm_feasible = False

    # constant-parameter version on Q+ ∩ (y, Y]
    const = []
    for Y in sorted({2 * y, 4 * y, 10 * y, N}):
        Ysel = [i for i in Qplus if cells[i] <= Y]
        if not Ysel:
            continue
        drains = {s: sum(rates[i][s - 1] for i in Ysel) for s in S0}
        pos = [(m_lo[s] / d, s) for s, d in drains.items() if d > 0]
        t_max, bind = min(pos) if pos else (float("inf"), None)
        const.append({"Y": Y, "cells": len(Ysel), "sum_gain_per_unit": sum(g[i] for i in Ysel), "t_max": t_max, "binding_s": bind, "gain": t_max * sum(g[i] for i in Ysel)})

    # two-sided LP: theta_q >= -m_q for cells with mass, additions anywhere
    cols2 = above
    lb2 = [-m_lo_cell[i] if i in mass_terms else 0.0 for i in cols2]
    res2 = lp(cols2, lb2)
    gain2 = float(-res2.fun)

    # what the saved exact optimum does, in terms of W_mu
    explain = {}
    try:
        with open(f"results/dual_witness_N{N}_y{y}.json") as fh:
            saved = json.load(fh)
        basis = set(saved["basis_cells"])
        kept = set(saved["cells_with_mass_kept"])
        fake_above = [q for q in sorted(basis - kept) if q > y]
        emptied_above = [q for q in saved["emptied_cells"] if q > y]
        Wmu = {int(cells[i]): 1 - g[i] for i in above}
        explain = {
            "fake_only_cells_above_y": {q: Wmu[q] for q in fake_above},
            "emptied_cells_above_y": {q: Wmu[q] for q in emptied_above},
            "fake_only_with_Wmu_below_1": sum(1 for q in fake_above if Wmu[q] < 1),
            "emptied_with_Wmu_above_1": sum(1 for q in emptied_above if Wmu[q] > 1),
            "T_star_minus_psi_saved": float(saved["gain_interval"][0]),
        }
    except FileNotFoundError:
        pass

    out = {
        "N": N, "y": y, "cells_above_y": len(above), "Q_plus": len(Qplus), "Q_minus_with_mass": len(Qminus),
        "single_cell_top": single[:12],
        "additions_lp_gain_float": gainA_f,
        "additions_rationalized_gain": str(gainA), "additions_rationalized_gain_float": float(gainA),
        "additions_rationalized_feasible": feasible, "additions_min_slack": min_slack, "additions_moments_exact": ident,
        "additions_cells_used": int(sum(1 for i in Qplus if thetaA[i] > 0)),
        "additions_theta": {int(cells[i]): str(thetaA[i]) for i in Qplus if thetaA[i] > 0},
        "constant_parameter": const,
        "pairs_top": pairs[:15],
        "pairs_count_positive": len(pairs),
        "greedy": greedy,
        "greedy_total_gain": str(total), "greedy_total_gain_float": float(total),
        "greedy_moments_exact": gm_ident, "greedy_feasible_by_enclosure": gm_feasible, "greedy_min_cell": gm_min,
        "two_sided_lp_gain_float": gain2,
        "explain_saved_optimum": explain,
        "seconds": time.time() - t0,
    }
    if verbose:
        print(f"Construction A at N={N} y={y}: {len(above)} cells above y, Q+ (W_mu<1) = {len(Qplus)}, Q- with mass = {len(Qminus)}")
        print("  best single cells (q, real mass, gain/unit, theta_max, binding s, gain):")
        for d in single[:6]:
            print(f"    q={d['q']:>5} m={d['real_mass']:7.3f} g={d['gain_per_unit']:>3d} theta_max={d['theta_max']:9.4f} at s={d['binding_s']}  gain={d['gain']:.4f}")
        print(f"  additions-only LP: {gainA_f:.6f}; rationalized {float(gainA):.6f} (exact {gainA}), feasible {feasible} (min slack {min_slack:.3e}), moments exact {ident}, cells used {out['additions_cells_used']}")
        for c in const:
            print(f"  constant theta on Q+ ∩ (y,{c['Y']}]: {c['cells']} cells, sum g = {c['sum_gain_per_unit']}, t_max = {c['t_max']:.5f} (binds at s={c['binding_s']}), gain = {c['gain']:.4f}")
        print(f"  Construction B, best single pairs (a -> b): " + "; ".join(f"{d['a']}->{d['b']}{'' if d['b_has_mass'] else '(fake)'}: {d['gain']:.3f}" for d in pairs[:6]))
        print(f"  greedy exchanges: {len(greedy)} steps, total {float(total):.4f} (exact {total}); moments exact {gm_ident}, feasible {gm_feasible} (min cell {gm_min:.3e})")
        for d in greedy[:10]:
            print(f"    step {d['step']:>2}: {d['a']:>5} -> {d['b']:>5}  theta_a={float(Fraction(d['theta_a'])):.4f} theta_b={float(Fraction(d['theta_b'])):.4f}  gain {d['gain']:.4f}  cum {d['cumulative']:.4f}")
        print(f"  two-sided LP (all z_q): {gain2:.6f}   [T*-psi saved: {explain.get('T_star_minus_psi_saved')}]")
        if explain:
            print(f"  saved optimum: fake-only cells above y with W_mu<1: {explain['fake_only_with_Wmu_below_1']}/{len(explain['fake_only_cells_above_y'])}; emptied above y with W_mu>1: {explain['emptied_with_Wmu_above_1']}/{len(explain['emptied_cells_above_y'])}")
            print(f"    W_mu at fake-only cells: {explain['fake_only_cells_above_y']}")
            print(f"    W_mu at emptied cells:   {explain['emptied_cells_above_y']}")
        print(f"  {time.time()-t0:.1f}s")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = construction_a(args.N, args.y)
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
