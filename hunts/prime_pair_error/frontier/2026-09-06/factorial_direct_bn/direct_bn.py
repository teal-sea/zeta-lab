#!/usr/bin/env python3
"""Minimize the factorial certificate B_N itself, and compare on B_N.

Third comparison on the pilot's seed family (2026-09-06), separate from and after
``../factorial_full_cost/`` whose record and conclusions are left unchanged. The two
earlier objectives were proxies: the leading constant C (the pilot) and the proved bound
U_N (``full_cost.py``). This one minimizes the certificate value itself,

    B_N(a) = sum_{k=0}^K sum_{j|L} a_j log(floor(N/(j M^k))!),   K = floor(log_M N),

which for fixed (L, M, N) is LINEAR in the coefficients a_j: B_N(a) = sum_j w_j a_j with
w_j = sum_k log(floor(N/(j M^k))!). Same constraints as the pilot, unchanged (j | L,
sum a_j/j = 0, g >= 0 on a full period, g >= 1 on [1, M)); same sizes (L in {30, 210,
2310}, M = 2..30); same cutoffs N in {10^4, 10^6, 10^8, 10^12}; the same 348 rows.

The LP proposes; ``Fraction(x).limit_denominator(10**6)`` reconstructs; every constraint
is rechecked exactly in integers (the checker is imported from ``full_cost.py`` so the
constraint set is literally the same code). Then all three seeds, the pilot's
leading-constant seed, the full-cost seed from ``full_cost_results.json``, and the
direct proposal, are evaluated on B_N at 50 digits from their exact rationals.

Fallback rule: the pilot's seed is the certificate of record. The direct proposal is
adopted only if it re-verifies exactly AND its B_N is strictly below the pilot seed's;
otherwise the pilot seed stands and the row says why. A worse certificate is never
accepted. No prime data is used or produced anywhere: B_N is a sum of log-factorials.

Nothing here is an asymptotic theorem, an LP-optimality proof, or an RH result.
Writes ``direct_bn_results.json`` next to itself.

Run from the repository root:
    .venv/bin/python hunts/prime_pair_error/frontier/2026-09-06/factorial_direct_bn/direct_bn.py
"""
from __future__ import annotations

import json
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
FULL_COST_DIR = HERE.parent / "factorial_full_cost"
sys.path.insert(0, str(FULL_COST_DIR))
from full_cost import (  # noqa: E402  (same constraint checker, same B_N, same reconstruction)
    B_N, CUTOFFS, DENOMINATOR_LIMIT, DPS, PERIODS, RADICES, K_of, evaluate, exact_verify,
    period_matrix, reconstruct, seed_str,
)

PILOT_RESULTS = HERE.parent / "factorial_certificate_pilot" / "results.json"
FULL_COST_RESULTS = FULL_COST_DIR / "full_cost_results.json"
OUT = HERE / "direct_bn_results.json"


def objective_weights(L: int, M: int, N: int) -> tuple[list[int], list[mp.mpf]]:
    """w_j = sum_{k=0}^K log(floor(N/(j M^k))!) at DPS digits, for every j | L."""
    div = [j for j in range(1, L + 1) if L % j == 0]
    K = K_of(N, M)
    weights = []
    with mp.workdps(DPS):
        for j in div:
            total = mp.mpf(0)
            power = 1
            for _ in range(K + 1):
                total += mp.loggamma(N // (j * power) + 1)
                power *= M
            weights.append(total)
    return div, weights


def solve_direct(L: int, M: int, N: int) -> dict[int, Fraction]:
    """Minimize B_N(a) = sum_j w_j a_j over the pilot's constraints; objective scaled by N."""
    div, matrix, jv = period_matrix(L)
    _, weights = objective_weights(L, M, N)
    with mp.workdps(DPS):
        objective = np.array([float(w / N) for w in weights])
    need = np.zeros(L)
    need[1:M] = 1
    res = linprog(objective, A_ub=-matrix, b_ub=-need, A_eq=[1 / jv], b_eq=[0],
                  bounds=[(None, None)] * len(div), method="highs",
                  options={"primal_feasibility_tolerance": 1e-10,
                           "dual_feasibility_tolerance": 1e-10})
    if not res.success:
        raise RuntimeError(f"direct LP failed at L={L}, M={M}, N={N}: {res.message}")
    return reconstruct(res.x, div)


def main() -> int:
    start = time.perf_counter()
    pilot = json.loads(PILOT_RESULTS.read_text(encoding="utf-8"))
    lead = {(c["period"], c["radix"]): {int(j): Fraction(a) for j, a in c["coefficients"].items()}
            for c in pilot["cases"]}
    full_record = json.loads(FULL_COST_RESULTS.read_text(encoding="utf-8"))
    full = {(r["L"], r["M"], r["N"]): {int(j): Fraction(a) for j, a in r["full_cost_seed"].items()}
            for r in full_record["rows"]}
    assert len(lead) == 87 and len(full) == 348

    rows: list[dict] = []
    rejected: list[dict] = []
    for L in PERIODS:
        for M in RADICES:
            seed_lead = lead[(L, M)]
            exact_verify(L, M, seed_lead)
            for N in CUTOFFS:
                seed_full = full[(L, M, N)]
                exact_verify(L, M, seed_full)
                proposal = solve_direct(L, M, N)
                try:
                    slack = exact_verify(L, M, proposal)
                    verified = True
                    why = ""
                except ValueError as exc:
                    verified, slack, why = False, None, str(exc)
                    rejected.append({"L": L, "M": M, "N": N, "why": why, "proposal": seed_str(proposal)})
                with mp.workdps(DPS):
                    b_lead = B_N(seed_lead, M, N)
                    b_full = B_N(seed_full, M, N)
                    b_direct = B_N(proposal, M, N) if verified else None
                    if not verified:
                        status = "fallback_rejected"
                    elif proposal == seed_lead:
                        status = "same_as_lead"
                    elif b_direct < b_lead:
                        status = "improves_lead"
                    elif b_direct == b_lead:
                        status = "fallback_tie_different_seed"
                    else:
                        status = "fallback_worse"
                    chosen = proposal if status == "improves_lead" else seed_lead
                    b_chosen = b_direct if status == "improves_lead" else b_lead
                    ev = evaluate(proposal, M, N) if verified else None
                    row = {
                        "L": L, "M": M, "N": N, "K": K_of(N, M),
                        "status": status,
                        "lead_seed": seed_str(seed_lead),
                        "full_cost_seed": seed_str(seed_full),
                        "direct_seed": seed_str(proposal) if verified else None,
                        "direct_rejected_why": why or None,
                        "direct_min_scaled_slack": slack,
                        "chosen_seed": seed_str(chosen),
                        "B_N_lead": mp.nstr(b_lead, 30),
                        "B_N_full_cost": mp.nstr(b_full, 30),
                        "B_N_direct": None if b_direct is None else mp.nstr(b_direct, 30),
                        "B_N_chosen": mp.nstr(b_chosen, 30),
                        "B_lead_minus_B_direct": None if b_direct is None else mp.nstr(b_lead - b_direct, 20),
                        "B_full_minus_B_direct": None if b_direct is None else mp.nstr(b_full - b_direct, 20),
                        "B_lead_minus_B_chosen": mp.nstr(b_lead - b_chosen, 20),
                        "relative_improvement_over_lead": mp.nstr((b_lead - b_chosen) / b_lead, 12),
                        "direct_A": None if ev is None else ev["A_exact"],
                        "direct_C": None if ev is None else mp.nstr(ev["C"], 20),
                        "direct_U_N": None if ev is None else mp.nstr(ev["U"], 30),
                        "direct_same_as_full_cost": verified and proposal == seed_full,
                    }
                rows.append(row)

    # ---- summaries ---------------------------------------------------------------
    by_status: dict[str, int] = {}
    for r in rows:
        by_status[r["status"]] = by_status.get(r["status"], 0) + 1
    improved = [r for r in rows if r["status"] == "improves_lead"]
    with mp.workdps(DPS):
        beats_full = [r for r in rows if r["B_N_direct"] is not None
                      and mp.mpf(r["B_full_minus_B_direct"]) > 0]
        worse_than_full = [r for r in rows if r["B_N_direct"] is not None
                           and mp.mpf(r["B_full_minus_B_direct"]) < 0]

    winners = []
    for L in PERIODS:
        for N in CUTOFFS:
            sub = [r for r in rows if r["L"] == L and r["N"] == N]
            with mp.workdps(DPS):
                wl = min(sub, key=lambda r: mp.mpf(r["B_N_lead"]))
                wf = min(sub, key=lambda r: mp.mpf(r["B_N_full_cost"]))
                wc = min(sub, key=lambda r: mp.mpf(r["B_N_chosen"]))
                winners.append({
                    "L": L, "N": N,
                    "lead_winner": {"M": wl["M"], "B_N": wl["B_N_lead"][:26]},
                    "full_cost_winner": {"M": wf["M"], "B_N": wf["B_N_full_cost"][:26]},
                    "chosen_winner": {"M": wc["M"], "seed": wc["chosen_seed"], "B_N": wc["B_N_chosen"][:26],
                                      "status": wc["status"]},
                    "B_lead_winner_minus_B_chosen_winner":
                        mp.nstr(mp.mpf(wl["B_N_lead"]) - mp.mpf(wc["B_N_chosen"]), 15),
                })

    persistence = []
    for L in PERIODS:
        for M in RADICES:
            sub = [r for r in rows if r["L"] == L and r["M"] == M]
            direct = [json.dumps(r["direct_seed"], sort_keys=True) for r in sub if r["direct_seed"]]
            persistence.append({
                "L": L, "M": M,
                "distinct_direct_seeds_across_cutoffs": len(set(direct)),
                "status_by_cutoff": {str(r["N"]): r["status"] for r in sub},
                "chosen_same_at_all_cutoffs": len({json.dumps(r["chosen_seed"], sort_keys=True) for r in sub}) == 1,
            })

    data = {
        "status": "direct minimization of the certificate value B_N over the pilot's seed family; "
                  "finite comparison, not an asymptotic theorem, no LP-optimality proof, no RH content",
        "python": platform.python_version(), "numpy": np.__version__,
        "scipy": __import__("scipy").__version__, "mpmath_dps": DPS,
        "denominator_limit": DENOMINATOR_LIMIT, "cutoffs": list(CUTOFFS),
        "rows_total": len(rows),
        "direct_proposals_rejected_by_exact_check": len(rejected),
        "rejections": rejected,
        "rows_by_status": by_status,
        "rows_direct_improves_lead": len(improved),
        "rows_direct_beats_full_cost_on_B_N": len(beats_full),
        "rows_direct_worse_than_full_cost_on_B_N": len(worse_than_full),
        "winners_per_L_and_N": winners,
        "pattern_persistence": persistence,
        "rows": rows,
        "elapsed_seconds": time.perf_counter() - start,
    }
    OUT.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    print(f"rows {len(rows)}: statuses {by_status}; rejected {len(rejected)}; "
          f"direct beats full-cost seed on B_N in {len(beats_full)}, worse in {len(worse_than_full)}; "
          f"{data['elapsed_seconds']:.1f}s -> {OUT.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
