"""Finite factorial ceilings on attainable quotients, measured LP grade.

Choose constraints without prime locations. Round candidate coefficients to
a common rational denominator and repair c_1 so feasibility is checked with
integer arithmetic. Evaluate the resulting bound independently at two
precisions. This proves no asymptotic estimate.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import time

from mpmath import mp
import numpy as np
from scipy.optimize import linprog
from scipy.special import gammaln


def quotient_cells(N: int) -> list[int]:
    """All floor(N/d) for 2 <= d <= N, enumerated in O(sqrt(N))."""
    if not isinstance(N, int) or isinstance(N, bool) or N < 2:
        raise ValueError("N must be an integer at least 2")
    r = math.isqrt(N)
    return sorted((set(range(1, r + 1)) | {N // d for d in range(1, r + 1)}) - {N})


def repair(c: list[float], cells: list[int], denominator: int) -> tuple[list[int], int]:
    """Round, then increase c_1 just enough for exact cell feasibility."""
    if not c or not cells or denominator < 1 or any(n < 1 for n in cells):
        raise ValueError("nonempty coefficients, positive cells and denominator required")
    nums = [round(float(v) * denominator) for v in c]
    delta = max(0, max(
        -((sum(a * (n // j) for j, a in enumerate(nums, 1)) - denominator) // n)
        for n in cells
    ))
    nums[0] += delta
    return nums, delta


def prime_powers(N: int) -> list[tuple[int, int]]:
    """Pairs (prime power, base prime), only for checking the solved bound."""
    flags = bytearray(b"\x01") * (N + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(N) + 1):
        if flags[p]:
            for n in range(p * p, N + 1, p):
                flags[n] = 0
    result = []
    for p in range(2, N + 1):
        if flags[p]:
            d = p
            while d <= N:
                result.append((d, p))
                d *= p
    return result


def evaluate(N: int, nums: list[int], denominator: int, dps: int) -> dict:
    """Independent factorial and weighted-prime evaluation at explicit precision."""
    with mp.workdps(dps):
        bound = mp.fsum(mp.mpf(a) * mp.loggamma(N // j + 1)
                        for j, a in enumerate(nums, 1)) / denominator
        # Aggregate exact rational excess weights by prime before taking logs.
        weights: dict[int, int] = {}
        counts: dict[int, int] = {}
        for d, p in prime_powers(N):
            n = N // d
            weight = sum(a * (n // j) for j, a in enumerate(nums, 1)) - denominator
            if weight < 0:
                raise ArithmeticError(f"negative excess at attained cell {n}")
            weights[p] = weights.get(p, 0) + weight
            counts[p] = counts.get(p, 0) + 1
        logs = {p: mp.log(p) for p in counts}
        psi = mp.fsum(counts[p] * logs[p] for p in counts)
        direct = mp.fsum(weights[p] * logs[p] for p in weights) / denominator
        defect = abs(bound - psi - direct)
        if defect > mp.power(10, -dps + 15) * N:
            raise ArithmeticError(f"factorial/prime identity failed: {defect}")
        return {"dps": dps, "bound": mp.nstr(bound, dps - 5),
                "psi": mp.nstr(psi, dps - 5), "excess": mp.nstr(direct, dps - 5),
                "identity_defect": mp.nstr(defect, 8),
                "prime_powers_checked": sum(counts.values())}


def solve(N: int, y: int, *, denominator: int = 10**12, time_limit: float = 30) -> dict:
    """Solve one finite LP, return exact feasibility plus measured objectives."""
    if not isinstance(y, int) or isinstance(y, bool) or not 1 <= y <= N:
        raise ValueError("support must be an integer between 1 and N")
    started = time.perf_counter()
    cells = quotient_cells(N)
    cols = np.arange(1, y + 1)
    A = (np.array(cells)[:, None] // cols).astype(float)
    L = gammaln(N // cols + 1)
    result = linprog(L, A_ub=-A, b_ub=-np.ones(len(cells)), bounds=(None, None),
                     method="highs-ds", options={"time_limit": time_limit})
    if not result.success:
        raise RuntimeError(f"N={N}, y={y}, solver status {result.status}: {result.message}")
    nums, delta = repair(result.x.tolist(), cells, denominator)
    heights = [sum(a * (n // j) for j, a in enumerate(nums, 1)) for n in cells]
    if min(heights) < denominator:
        raise ArithmeticError("rational repair failed")
    evaluations = [evaluate(N, nums, denominator, dps) for dps in (50, 80)]
    with mp.workdps(80):
        precision_defect = abs(mp.mpf(evaluations[0]["excess"]) -
                               mp.mpf(evaluations[1]["excess"]))
        if precision_defect > mp.mpf("1e-35") * N:
            raise ArithmeticError("excess moved under precision refinement")
    dual = -result.ineqlin.marginals
    return {
        "N": N, "y": y, "cells_checked": len(cells),
        "lp_value_measured": float(result.fun),
        "lp_duality_gap_measured": float(abs(result.fun - dual.sum())),
        "lp_dual_equation_residual_measured": float(np.max(np.abs(A.T @ dual - L))),
        "lp_dual_min_measured": float(dual.min()),
        "coefficient_numerators": nums, "denominator": denominator,
        "c1_repair_numerator": delta, "minimum_height_numerator": min(heights),
        "evaluations": evaluations, "seconds": time.perf_counter() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--N", type=int, nargs="+", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    record = {"started": datetime.now(timezone.utc).isoformat(), "status": "running",
              "requested": len(args.N), "completed": 0, "results": []}

    def save() -> None:
        args.output.write_text(json.dumps(record, indent=2) + "\n")

    save()
    try:
        for N in args.N:
            print(f"Starting N={N}, y={math.isqrt(N)}, completed={record['completed']}/{len(args.N)}", flush=True)
            row = solve(N, math.isqrt(N))
            record["results"].append(row)
            record["completed"] += 1
            save()
            print(f"Completed N={N}: {row['cells_checked']} exact cell checks, excess={row['evaluations'][-1]['excess']}, {row['seconds']:.2f}s", flush=True)
    except Exception as exc:
        record.update(status="failed", error=f"{type(exc).__name__}: {exc}",
                      finished=datetime.now(timezone.utc).isoformat())
        save()
        print(f"FAILED: completed={record['completed']}/{len(args.N)}: {exc}", flush=True)
        raise
    record.update(status="complete", finished=datetime.now(timezone.utc).isoformat())
    save()
    print(f"Complete: {record['completed']}/{len(args.N)} results saved to {args.output}", flush=True)


if __name__ == "__main__":
    main()
