"""Construct and check one rational sampling-null counterexample, without LPs."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import sys
import time

from sympy import Matrix, ilcm

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from hunts.quotient_certificate.finite_transfer import mass_factors, period_variance


def construct() -> dict:
    """A fixed 98 by 99 rational nullspace calculation at N=10000, y=100."""
    N, y = 10000, 100
    masses = mass_factors(N)
    P = [q for q, factors in masses.items() if factors]
    R = Matrix([[(q % j) - (P[0] % j) for j in range(2, y + 1)] for q in P[1:]])
    basis = R.nullspace()
    if not basis:
        raise ArithmeticError("the stated sampling nullspace is empty")
    z = min(basis, key=lambda v: sum(bool(a) for a in v))
    scale = int(ilcm(*[v.q for v in z]))
    tail = [int(v * scale) * j for j, v in enumerate(z, 2)]
    divisor = math.gcd(*tail)
    tail = [v // divisor for v in tail]
    # l1 normalization proves coverage at EVERY positive integer q:
    # q + sum_{j>=2} c_j floor(q/j) >= q - floor(q/2).
    denominator = sum(abs(v) for v in tail)
    nums = [denominator] + tail
    c = [Fraction(v, denominator) for v in nums]
    heights = {q: sum(v * (q // j) for j, v in enumerate(nums, 1)) for q in masses}
    saw = {q: sum((v * (Fraction(q % j, j) - Fraction(j - 1, 2 * j))
                  for j, v in enumerate(c, 1)), Fraction()) for q in P}
    A = sum((v / j for j, v in enumerate(c, 1)), Fraction())
    full = period_variance(c)
    if len(set(saw.values())) != 1 or full <= 0:
        raise ArithmeticError("sampling-null or positive-period witness failed")
    if min(heights.values()) < denominator or sum(abs(v) for v in c[1:]) != 1:
        raise ArithmeticError("exact coverage or normalization failed")
    if A != 1 or any(heights[q] != q * denominator for q in P):
        raise ArithmeticError("stated drift/prime-cell heights failed")
    source = json.loads(Path(__file__).with_name("results.json").read_text())
    saved = next(row for row in source["results"] if row["N"] == N)
    lower, upper = [], []
    for q in masses:
        slack = Fraction(sum(a * (q // j) for j, a in enumerate(
            saved["coefficient_numerators"], 1)) - saved["denominator"], saved["denominator"])
        slope = Fraction(heights[q], denominator) - q
        if slope > 0:
            lower.append((-slack / slope, q, slope))
        elif slope < 0:
            upper.append((-slack / slope, q, slope))
        elif slack < 0:
            raise ArithmeticError("saved vector is infeasible")
    lower_witness, upper_witness = max(lower), min(upper)
    if lower_witness[0] != 0 or upper_witness[0] != 0:
        raise ArithmeticError("stated saved-vector tangent interval changed")
    return {"status": "complete", "N": N, "y": y,
            "positive_mass_cells": P, "cells_checked": len(masses),
            "difference_matrix_shape": list(R.shape), "difference_matrix_rank": len(z) - len(basis),
            "coefficient_numerators": nums, "denominator": denominator,
            "tail_l1_exact": "1", "A_exact": str(A),
            "minimum_height_exact": str(Fraction(min(heights.values()), denominator)),
            "finite_saw_value_exact": str(next(iter(saw.values()))),
            "finite_saw_variance_exact": "0", "period_variance_exact": str(full),
            "saved_vector_tangent_interval": {
                "lower": str(lower_witness[0]), "upper": str(upper_witness[0]),
                "lower_cell": lower_witness[1], "upper_cell": upper_witness[1],
                "lower_slope": str(lower_witness[2]), "upper_slope": str(upper_witness[2])}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve() == Path(__file__).with_name("results.json").resolve():
        parser.error("the original results.json archive must remain unchanged")
    started = time.perf_counter()
    args.output.write_text(json.dumps({"status": "running", "completed": 0, "requested": 1}) + "\n")
    print("started: one exact sampling-null construction, zero optimizations", flush=True)
    try:
        report = construct()
    except Exception as exc:
        args.output.write_text(json.dumps({"status": "failed", "completed": 0,
                                          "requested": 1, "error": str(exc)}) + "\n")
        print(f"FAILED: {type(exc).__name__}: {exc}", file=sys.stderr, flush=True)
        raise
    report.update(completed=1, requested=1, seconds=time.perf_counter() - started)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"complete: 1/1, {report['seconds']:.3f}s", flush=True)


if __name__ == "__main__":
    main()
