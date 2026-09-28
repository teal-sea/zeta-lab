#!/usr/bin/env python3
"""Full-cost versus leading-constant optimization of the factorial-certificate seed.

Question (2026-09-06 follow-up to ``../factorial_certificate_pilot/``): does minimizing
the ENTIRE proved upper bound of PILOT.md section 3,

    U_N = kappa N (1 - M^{-K-1}) / (1 - 1/M) + A [(K+1)(1 + log N) - log(M) K(K+1)/2],

with kappa = -sum_j a_j log(j)/j, A = sum_j |a_j|, K = floor(log_M N) by integer powers,
give a better certificate than minimizing the leading constant C = kappa/(1 - 1/M) alone,
at the same L, M and N?

Everything else is held to the pilot exactly: indices j | L, balance sum a_j/j = 0,
g(r) >= 0 on 0 <= r < L, g(r) >= 1 on 1 <= r < M, with L in {30, 210, 2310} and M = 2..30.
N in {10^4, 10^6, 10^8, 10^12}. No prime data is used anywhere: the bound is a theorem
about floor sums and the search reads only the period matrix.

Method. U_N is linear in (a, u) once A is represented by auxiliaries u_j >= |a_j|, so the
full-cost problem is an LP. Writing c1 = N (1 - M^{-K-1})/(1 - 1/M) and
c2 = (K+1)(1 + log N) - log(M) K(K+1)/2 (both positive: K log M <= log N), the objective is
normalised to kappa + (c2/c1) A so the solver sees numbers of order one. The LP only
PROPOSES coefficients: each proposal is reconstructed as rationals
(``Fraction(x).limit_denominator(10**6)``, the pilot's rule) and every constraint is
rechecked exactly in integers; a proposal that fails is REJECTED and recorded, never
rounded toward feasibility. Baseline: the pilot's recorded leading-constant seed for the
same (L, M), read from ``../factorial_certificate_pilot/results.json`` and re-verified
here; the leading-constant LP is also re-solved as a consistency check. Both seeds are
then evaluated on the same U_N at 50 digits from their exact rationals.

Nothing here is an asymptotic theorem, an LP-optimality proof, a prime-counting record,
or an RH result. Writes ``full_cost_results.json`` next to itself.

Run from the repository root:
    .venv/bin/python hunts/prime_pair_error/frontier/2026-09-06/factorial_full_cost/full_cost.py
"""
from __future__ import annotations

import json
import math
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
PILOT_RESULTS = HERE.parent / "factorial_certificate_pilot" / "results.json"
OUT = HERE / "full_cost_results.json"

PERIODS = (30, 210, 2310)
RADICES = range(2, 31)
CUTOFFS = (10**4, 10**6, 10**8, 10**12)
DENOMINATOR_LIMIT = 1_000_000
DPS = 50


# ------------------------------------------------------------------ exact side ---

def divisors(L: int) -> list[int]:
    return [j for j in range(1, L + 1) if L % j == 0]


def exact_verify(L: int, M: int, seed: dict[int, Fraction]) -> int:
    """Balance and every period constraint in integers. Returns the minimum scaled slack.

    Raises ValueError on any failure; the caller records the rejection.
    """
    if not 2 <= M <= L:
        raise ValueError(f"need 2 <= M <= L, got L={L}, M={M}")
    if not seed:
        raise ValueError("empty seed")
    if any(j < 1 or L % j for j in seed):
        raise ValueError("an index does not divide the period")
    if sum((a / j for j, a in seed.items()), Fraction(0)) != 0:
        raise ValueError("balance sum a_j/j != 0")
    scale = math.lcm(*(a.denominator for a in seed.values()))
    nums = {j: int(a * scale) for j, a in seed.items()}
    worst = None
    for r in range(L):
        value = sum(a * (r // j) for j, a in nums.items())
        need = scale if 1 <= r < M else 0
        if value < need:
            raise ValueError(f"g({r}) = {value}/{scale} < {need}/{scale}")
        slack = value - need
        worst = slack if worst is None else min(worst, slack)
    return worst


def K_of(N: int, M: int) -> int:
    K, power = 0, M
    while power <= N:
        K += 1
        power *= M
    return K


def evaluate(seed: dict[int, Fraction], M: int, N: int) -> dict:
    """kappa, A, c1, c2 and U_N at DPS digits from the exact rationals."""
    K = K_of(N, M)
    A_exact = sum((abs(a) for a in seed.values()), Fraction(0))
    with mp.workdps(DPS):
        kappa = -sum((mp.mpf(a.numerator) / a.denominator) * mp.log(j) / j for j, a in seed.items())
        A = mp.mpf(A_exact.numerator) / A_exact.denominator
        Mm = mp.mpf(M)
        c1 = N * (1 - Mm ** (-K - 1)) / (1 - 1 / Mm)
        c2 = (K + 1) * (1 + mp.log(N)) - mp.log(Mm) * K * (K + 1) / 2
        assert c2 > 0
        U = c1 * kappa + c2 * A
        C = kappa / (1 - 1 / Mm)
        return {"K": K, "kappa": kappa, "A": A, "A_exact": str(A_exact), "C": C,
                "c1": c1, "c2": c2, "U": U}


def seed_str(seed: dict[int, Fraction]) -> dict[str, str]:
    return {str(j): str(a) for j, a in sorted(seed.items())}


def B_N(seed: dict[int, Fraction], M: int, N: int) -> mp.mpf:
    """The certificate value itself, sum_{k<=K} sum_j a_j log(floor(N/(j M^k))!), at DPS digits.

    Log-factorials only; no prime data. Recorded so a reader can see whether a seed that
    lowers the PROVED bound U_N also lowers the quantity the bound is about.
    """
    K = K_of(N, M)
    with mp.workdps(DPS):
        total = mp.mpf(0)
        power = 1
        for _ in range(K + 1):
            for j, a in seed.items():
                total += (mp.mpf(a.numerator) / a.denominator) * mp.loggamma(N // (j * power) + 1)
            power *= M
        return total


# --------------------------------------------------------------- numerical side ---

def period_matrix(L: int) -> tuple[list[int], np.ndarray, np.ndarray]:
    div = divisors(L)
    matrix = np.arange(L, dtype=np.int64)[:, None] // np.array(div, dtype=np.int64)[None, :]
    return div, matrix.astype(float), np.array(div, dtype=float)


def solve_leading(L: int, M: int) -> dict[int, Fraction]:
    """The pilot's LP: minimise C over the seed constraints, no auxiliaries."""
    div, matrix, jv = period_matrix(L)
    need = np.zeros(L)
    need[1:M] = 1
    objective = -np.log(jv) / jv / (1 - 1 / M)
    res = linprog(objective, A_ub=-matrix, b_ub=-need, A_eq=[1 / jv], b_eq=[0],
                  bounds=[(None, None)] * len(div), method="highs")
    if not res.success:
        raise RuntimeError(f"leading LP failed at L={L}, M={M}: {res.message}")
    return reconstruct(res.x, div)


def solve_full(L: int, M: int, ratio: float) -> dict[int, Fraction]:
    """Minimise kappa + ratio * A, ratio = c2/c1, with u_j >= |a_j| auxiliaries."""
    div, matrix, jv = period_matrix(L)
    d = len(div)
    need = np.zeros(L)
    need[1:M] = 1
    # variables: a_1..a_d, u_1..u_d
    objective = np.concatenate([-np.log(jv) / jv, np.full(d, ratio)])
    A_ub = np.zeros((L + 2 * d, 2 * d))
    b_ub = np.zeros(L + 2 * d)
    A_ub[:L, :d] = -matrix          # -matrix a <= -need
    b_ub[:L] = -need
    eye = np.eye(d)
    A_ub[L:L + d, :d] = eye         # a - u <= 0
    A_ub[L:L + d, d:] = -eye
    A_ub[L + d:, :d] = -eye         # -a - u <= 0
    A_ub[L + d:, d:] = -eye
    A_eq = np.concatenate([1 / jv, np.zeros(d)])[None, :]
    bounds = [(None, None)] * d + [(0, None)] * d
    res = linprog(objective, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=[0], bounds=bounds,
                  method="highs",
                  options={"primal_feasibility_tolerance": 1e-10,
                           "dual_feasibility_tolerance": 1e-10})
    if not res.success:
        raise RuntimeError(f"full-cost LP failed at L={L}, M={M}, ratio={ratio}: {res.message}")
    return reconstruct(res.x[:d], div)


def reconstruct(x: np.ndarray, div: list[int]) -> dict[int, Fraction]:
    seed = {j: Fraction(float(v)).limit_denominator(DENOMINATOR_LIMIT) for j, v in zip(div, x)}
    return {j: a for j, a in seed.items() if a}


# ------------------------------------------------------------------------ main ---

def main() -> int:
    start = time.perf_counter()
    pilot = json.loads(PILOT_RESULTS.read_text(encoding="utf-8"))
    recorded = {(c["period"], c["radix"]): {int(j): Fraction(a) for j, a in c["coefficients"].items()}
                for c in pilot["cases"]}
    assert len(recorded) == 87, len(recorded)

    rows: list[dict] = []
    rejected: list[dict] = []
    resolve_mismatch: list[dict] = []
    for L in PERIODS:
        for M in RADICES:
            base = recorded[(L, M)]
            base_slack = exact_verify(L, M, base)          # the baseline must re-verify too
            resolved = solve_leading(L, M)
            try:
                exact_verify(L, M, resolved)
                resolved_ok = True
            except ValueError as exc:
                resolved_ok = False
                resolve_mismatch.append({"L": L, "M": M, "why": f"re-solve rejected: {exc}"})
            if resolved_ok and resolved != base:
                with mp.workdps(DPS):
                    resolve_mismatch.append({
                        "L": L, "M": M, "why": "re-solved leading seed differs from the record",
                        "C_record": mp.nstr(evaluate(base, M, 10**4)["C"], 25),
                        "C_resolved": mp.nstr(evaluate(resolved, M, 10**4)["C"], 25),
                        "resolved": seed_str(resolved)})
            for N in CUTOFFS:
                ev_base = evaluate(base, M, N)
                ratio = float(ev_base["c2"] / ev_base["c1"])
                proposal = solve_full(L, M, ratio)
                try:
                    full_slack = exact_verify(L, M, proposal)
                except ValueError as exc:
                    rejected.append({"L": L, "M": M, "N": N, "why": str(exc),
                                     "proposal": seed_str(proposal)})
                    rows.append({"L": L, "M": M, "N": N, "K": ev_base["K"],
                                 "full_cost_seed": None, "full_cost_rejected": str(exc),
                                 "baseline_seed": seed_str(base),
                                 "U_baseline": mp.nstr(ev_base["U"], 30)})
                    continue
                ev_full = evaluate(proposal, M, N)
                with mp.workdps(DPS):
                    diff = ev_base["U"] - ev_full["U"]        # > 0 means full cost is better
                    rel = diff / ev_base["U"]
                    if proposal == base:
                        b_base = b_full = None
                    else:
                        b_base, b_full = B_N(base, M, N), B_N(proposal, M, N)
                rows.append({
                    "L": L, "M": M, "N": N, "K": ev_base["K"],
                    "c2_over_c1": mp.nstr(ev_base["c2"] / ev_base["c1"], 12),
                    "baseline_seed": seed_str(base),
                    "baseline_kappa": mp.nstr(ev_base["kappa"], 30),
                    "baseline_A": ev_base["A_exact"],
                    "baseline_C": mp.nstr(ev_base["C"], 30),
                    "U_baseline": mp.nstr(ev_base["U"], 30),
                    "full_cost_seed": seed_str(proposal),
                    "full_cost_kappa": mp.nstr(ev_full["kappa"], 30),
                    "full_cost_A": ev_full["A_exact"],
                    "full_cost_C": mp.nstr(ev_full["C"], 30),
                    "U_full_cost": mp.nstr(ev_full["U"], 30),
                    "U_baseline_minus_U_full_cost": mp.nstr(diff, 20),
                    "relative_improvement": mp.nstr(rel, 12),
                    "same_seed_as_baseline": proposal == base,
                    "min_scaled_slack_full_cost": full_slack,
                    "min_scaled_slack_baseline": base_slack,
                    "B_N_baseline": None if b_base is None else mp.nstr(b_base, 30),
                    "B_N_full_cost": None if b_full is None else mp.nstr(b_full, 30),
                    "B_N_baseline_minus_B_N_full_cost":
                        None if b_base is None else mp.nstr(b_base - b_full, 20),
                })

    # ---- summaries ---------------------------------------------------------------
    ok = [r for r in rows if r["full_cost_seed"] is not None]
    with mp.workdps(DPS):
        better = [r for r in ok if mp.mpf(r["U_baseline_minus_U_full_cost"]) > 0]
        worse = [r for r in ok if mp.mpf(r["U_baseline_minus_U_full_cost"]) < 0]
        tied = [r for r in ok if mp.mpf(r["U_baseline_minus_U_full_cost"]) == 0]
    same = [r for r in ok if r["same_seed_as_baseline"]]
    different = [r for r in ok if not r["same_seed_as_baseline"]]
    with mp.workdps(DPS):
        b_better = [r for r in different if mp.mpf(r["B_N_baseline_minus_B_N_full_cost"]) > 0]
        b_worse = [r for r in different if mp.mpf(r["B_N_baseline_minus_B_N_full_cost"]) < 0]

    winners = []
    for L in PERIODS:
        for N in CUTOFFS:
            sub = [r for r in ok if r["L"] == L and r["N"] == N]
            with mp.workdps(DPS):
                wf = min(sub, key=lambda r: mp.mpf(r["U_full_cost"]))
                wb = min(sub, key=lambda r: mp.mpf(r["U_baseline"]))
                winners.append({
                    "L": L, "N": N,
                    "full_cost_winner": {"M": wf["M"], "seed": wf["full_cost_seed"],
                                         "A": wf["full_cost_A"], "C": wf["full_cost_C"][:16],
                                         "U": wf["U_full_cost"][:24]},
                    "leading_constant_winner_by_U": {"M": wb["M"], "seed": wb["baseline_seed"],
                                                     "A": wb["baseline_A"], "C": wb["baseline_C"][:16],
                                                     "U": wb["U_baseline"][:24]},
                    "U_leading_winner_minus_U_full_winner":
                        mp.nstr(mp.mpf(wb["U_baseline"]) - mp.mpf(wf["U_full_cost"]), 15),
                })

    # pattern persistence: per (L, M), is the full-cost seed the same at every N?
    persistence = []
    for L in PERIODS:
        for M in RADICES:
            seeds = [r["full_cost_seed"] for r in ok if r["L"] == L and r["M"] == M]
            distinct = {json.dumps(s, sort_keys=True) for s in seeds}
            persistence.append({"L": L, "M": M, "cutoffs_with_a_seed": len(seeds),
                                "distinct_full_cost_seeds_across_cutoffs": len(distinct),
                                "same_as_baseline_at": [r["N"] for r in ok
                                                        if r["L"] == L and r["M"] == M and r["same_seed_as_baseline"]]})

    data = {
        "status": "finite comparison of two LP objectives on the pilot's seed family; "
                  "not an asymptotic theorem, not an LP-optimality proof, no RH content",
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": __import__("scipy").__version__,
        "mpmath_dps": DPS,
        "denominator_limit": DENOMINATOR_LIMIT,
        "cutoffs": list(CUTOFFS),
        "rows_total": len(rows),
        "rows_with_accepted_full_cost_seed": len(ok),
        "full_cost_proposals_rejected_by_exact_check": len(rejected),
        "rejections": rejected,
        "leading_constant_resolve_mismatches": len(resolve_mismatch),
        "resolve_mismatch_detail": resolve_mismatch,
        "rows_full_cost_strictly_better": len(better),
        "rows_full_cost_strictly_worse": len(worse),
        "rows_tied": len(tied),
        "rows_same_seed_as_baseline": len(same),
        "rows_different_seed_from_baseline": len(different),
        "rows_where_full_cost_seed_also_lowers_B_N": len(b_better),
        "rows_where_full_cost_seed_raises_B_N": len(b_worse),
        "winners_per_L_and_N": winners,
        "pattern_persistence": persistence,
        "rows": rows,
        "elapsed_seconds": time.perf_counter() - start,
    }
    OUT.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")
    print(f"rows {len(rows)}: accepted {len(ok)}, rejected {len(rejected)}; "
          f"full cost strictly better {len(better)}, worse {len(worse)}, tied {len(tied)}; "
          f"same seed as baseline {len(same)}, different {len(different)} "
          f"(of which B_N lower {len(b_better)}, higher {len(b_worse)}); "
          f"leading re-solve mismatches {len(resolve_mismatch)}; "
          f"{data['elapsed_seconds']:.1f}s -> {OUT.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
