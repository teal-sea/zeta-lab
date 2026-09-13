#!/usr/bin/env python3
"""Joint signed-correction experiment for the reviewed factorial baseline.

Run from a zeta-lab checkout after PR #198. This is exploratory: the LP proposes
rational coefficients, and exact integer/rational checks decide whether they are
admissible. It does not establish optimality, novelty, an asymptotic family, RH,
or a bound on total CHHL E(N).
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
import argparse, importlib.util, json, math, sys

import mpmath as mp
import numpy as np
from scipy import sparse
from scipy.optimize import linprog

REPO = Path.cwd()
BASE = REPO / "hunts/prime_pair_error/frontier/2026-09-06/certificate_route_test"
if not BASE.is_dir():
    raise SystemExit(f"missing reviewed baseline package: {BASE}")

spec = importlib.util.spec_from_file_location("route_refine", BASE / "refine.py")
r = importlib.util.module_from_spec(spec); assert spec.loader; spec.loader.exec_module(r)
M, R = r.M, r.R
mp.mp.dps = 80


def add_coeff(c, other, factor=F(1)):
    out = defaultdict(F, c)
    for j, a in other.items():
        out[j] += factor * a
    return {j: a for j, a in out.items() if a}


def floor_array(c, size, den):
    t = np.arange(size, dtype=np.int64)
    out = np.zeros(size, dtype=np.int64)
    for j, a in c.items():
        q = a * den
        assert q.denominator == 1
        out += int(q) * (t // j)
    return out


def lifted(seed):
    t = np.arange(len(seed), dtype=np.int64)
    out = np.zeros_like(seed)
    s = 1
    while s < len(seed):
        out += seed[t // s]
        s *= M
    return out


def bump_lift(n):
    t = np.arange(R, dtype=np.int64)
    b = t // n - t // (n + 1) - t // (n * (n + 1))
    return lifted(b)


def extended_certificate_frac(c, H, star, N):
    value = r.certificate(c, N)
    x, k = N // R, 0
    while x >= 1:
        value += r.mpf(H) * (k + 1) * r.factorial_value(star, x)
        x //= M; k += 1
    return value


def main(out_path: Path):
    inp = json.loads((BASE / "inputs.json").read_text())
    agg = json.loads((BASE / "aggregate_results.json").read_text())
    initial = {int(j): F(a) for j, a in inp["starting_coefficients"].items()}
    star = {int(j): F(a) for j, a in inp["repair_coefficients"].items()}
    baseline = {int(j): F(a) for j, a in agg["new_coefficients"].items()}
    baseline_H = F(agg["tail_multiplier"])
    baseline_C = mp.mpf(agg["new_final_C"])

    # Existing repair cells are the allowed positive repair dictionary in this first joint test.
    repairs = defaultdict(F)
    for st in agg["stages"]:
        for n, a in st["repairs"]:
            repairs[int(n)] += F(a)
    repair_ns = sorted(repairs)

    # Target block: masked carries whose starts can revisit the first overcovered cells.
    candidates = list(range(13, 37))

    den0 = math.lcm(*(a.denominator for a in initial.values()))
    t = np.arange(R, dtype=np.int64)
    W0 = lifted(floor_array(initial, R, den0)).astype(float) / den0

    # Candidate masked-carry effects and exact tail suprema.
    Hcols = []
    kappas = []
    Hmax = []
    periods_checked = 0
    for q in candidates:
        hc = r.stencil_coeff(q)
        Hcols.append(lifted(floor_array(hc, R, den0))[1:].astype(float) / den0)
        kappas.append(float(r.kappa(hc)))
        period = math.prod(r.MASK) * q * (q + 1)
        hmax = int(r.stencil_array(q, period).max())
        assert hmax == 3
        Hmax.append(hmax)
        periods_checked += period
    Hmat = np.column_stack(Hcols)

    # Positive repair columns, using only cells already present in the reviewed baseline.
    rows, cols, data = [], [], []
    for ci, n in enumerate(repair_ns):
        L = bump_lift(n)[1:]
        nz = np.flatnonzero(L)
        rows.extend(nz.tolist()); cols.extend([ci] * len(nz)); data.extend(L[nz].astype(float).tolist())
    B = sparse.coo_matrix((data, (rows, cols)), shape=(R - 1, len(repair_ns))).tocsr()

    # W0 - sum y_q H_q + sum lambda_n B_n >= 1.
    A = sparse.hstack([sparse.csr_matrix(Hmat), -B], format="csr")
    rhs = W0[1:] - 1.0
    Cstar = r.kappa(star) / r.mpf(F(14, 15))
    tail_unit = float(Cstar) / R
    obj_y = np.array([-kappas[i] + Hmax[i] * tail_unit for i in range(len(candidates))])
    obj_l = np.array([float(r.kappa(r.bump_coeff(n))) for n in repair_ns])
    objective = np.concatenate([obj_y, obj_l])

    sol = linprog(objective, A_ub=A, b_ub=rhs,
                  bounds=[(0, None)] * len(objective), method="highs")
    if not sol.success:
        raise RuntimeError(sol.message)

    # Reconstruct all proposed rationals; the observed LP vertex is on a 1/108 grid.
    y = {q: F(float(sol.x[i])).limit_denominator(10_000)
         for i, q in enumerate(candidates) if sol.x[i] > 1e-10}
    lambdas = {n: F(float(sol.x[len(candidates) + i])).limit_denominator(10_000)
               for i, n in enumerate(repair_ns) if sol.x[len(candidates) + i] > 1e-10}
    assert all(a.denominator <= 108 for a in list(y.values()) + list(lambdas.values()))

    proposed = initial.copy()
    for q, a in y.items():
        proposed = add_coeff(proposed, r.stencil_coeff(q), -a)
    for n, a in lambdas.items():
        proposed = add_coeff(proposed, r.bump_coeff(n), a)
    tail_H = sum(F(3) * a for a in y.values())
    assert r.balanced(proposed)

    den = math.lcm(*(a.denominator for a in proposed.values()), tail_H.denominator)
    seed = floor_array(proposed, R, den)
    W = lifted(seed)
    assert int(W[1:].min()) >= den

    # Tail proof inputs: initial seed nonnegative; each selected masked carry <=3;
    # every repair is nonnegative; tail_H W_*(t/R) offsets the worst total subtraction.
    init_period, _ = r.floor_array(initial, inp["starting_L"])
    assert int(init_period.min()) >= 0
    for q in y:
        period = math.prod(r.MASK) * q * (q + 1)
        assert int(r.stencil_array(q, period).max()) == 3

    # Exact rational log enclosures establish a strict C improvement.
    Cstar_bounds = tuple(x / F(14, 15) for x in r.kappa_bounds(star))
    nb = r.kappa_bounds(proposed)
    bb = r.kappa_bounds(baseline)
    new_bounds = tuple((nb[i] + tail_H * F(1, R) * Cstar_bounds[i]) / F(14, 15) for i in (0, 1))
    old_bounds = tuple((bb[i] + baseline_H * F(1, R) * Cstar_bounds[i]) / F(14, 15) for i in (0, 1))
    assert new_bounds[1] < old_bounds[0]

    new_C = (r.kappa(proposed) + r.mpf(tail_H) * Cstar / R) / r.mpf(F(14, 15))
    new_mass = r.mass(proposed)
    old_mass = r.mass(baseline)

    comparisons = []
    for N in (10**4, 10**6, 10**8, 10**12):
        oldB = r.extended_certificate(baseline, int(baseline_H), star, N)
        newB = extended_certificate_frac(proposed, tail_H, star, N)
        oldU = baseline_C * N + r.mpf(old_mass) * r.first_budget(N) + r.mpf(baseline_H) * r.mpf(r.mass(star)) * r.second_budget(N)
        newU = new_C * N + r.mpf(new_mass) * r.first_budget(N) + r.mpf(tail_H) * r.mpf(r.mass(star)) * r.second_budget(N)
        assert newU < oldU
        comparisons.append({
            "N": N, "old_B": str(oldB), "new_B": str(newB),
            "old_U": str(oldU), "new_U": str(newU),
            "B_gain": str(oldB - newB), "U_gain": str(oldU - newU),
        })

    early = [18, 19, 20, 21, 24, 25, 32]
    base_seed = floor_array(baseline, R, 3); baseW = lifted(base_seed)
    early_weights = [{"t": n, "baseline": str(F(int(baseW[n]), 3)), "joint": str(F(int(W[n]), den))} for n in early]

    result = {
        "status": "joint finite correction candidate; exact feasibility checked; no asymptotic family rate, optimality, novelty, RH, or total-E claim",
        "baseline": {"C": agg["new_final_C"], "finite_mass": str(old_mass), "tail_H": str(baseline_H)},
        "candidate_range": candidates,
        "selected_masked_corrections": {str(q): str(a) for q, a in y.items()},
        "selected_repair_count": len(lambdas),
        "repair_coefficient_sum": str(sum(lambdas.values(), F())),
        "new_C": str(new_C), "new_C_interval": r.outward_summary(new_bounds),
        "strict_C_improvement_exact": True,
        "new_finite_mass": str(new_mass), "new_tail_H": str(tail_H),
        "new_coefficient_count": len(proposed), "negative_seed_cells_below_R": int(np.count_nonzero(seed < 0)),
        "lifted_prefix_min": str(F(int(W[1:].min()), den)),
        "early_weights": early_weights,
        "comparisons": comparisons,
        "checks": {"prefix_cells": R - 1, "candidate_period_positions": periods_checked,
                   "candidate_H_all_equal_3": True, "rational_grid_denominator": 108},
        "limitations": [
            "Positive repair variables were restricted to the 411 repair cells already appearing in the reviewed baseline.",
            "Candidate masked-carry starts were restricted to q=13..36.",
            "The LP is a proposal mechanism; exact reconstruction and feasibility are checked, but no exact LP optimality theorem is claimed.",
            "No iteration law or asymptotic rate for C-1 versus complexity is proved.",
        ],
        "new_coefficients": {str(j): str(a) for j, a in sorted(proposed.items())},
        "repair_coefficients": {str(n): str(a) for n, a in sorted(lambdas.items())},
    }
    out_path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["selected_masked_corrections", "selected_repair_count", "new_C", "new_finite_mass", "new_tail_H", "lifted_prefix_min"]}, indent=2))


if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--output", type=Path, default=Path("joint_results.json")); args = ap.parse_args()
    main(args.output)
