"""Fixed exact transport-capacity controls, with no search or optimization."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
import time

from mpmath.ctx_iv import MPIntervalContext
from sympy import mobius

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from hunts.quotient_certificate.finite_transfer import mass_factors
from hunts.quotient_certificate.height_kernel import RELATION, enclosure, endpoint

HUNT = Path(__file__).resolve().parent
SOURCE_COMMIT = "3d8aa03034d5207cdab3129eb78534c0f77d2384"


def prefix_rates(q: int, y: int) -> list[int]:
    """True integer prefix rates, including R_q(y+1)=0 at the endpoint."""
    if not isinstance(q, int) or not isinstance(y, int) or y < 1 or q <= y:
        raise ValueError("integer q>y>=1 required")
    mu = [0] + [int(mobius(k)) for k in range(1, y + 1)]
    R = [0] * (y + 2)
    for s in range(1, y + 1):
        R[s] = sum(mu[k] * (q // (s * k)) for k in range(1, y // s + 1))
    return [R[s] - R[s + 1] for s in range(1, y + 1)]


def exchange(a: int, b: int, y: int) -> dict[int, int]:
    """Unit equal-mass exchange a to b through the prefix, as integer deltas."""
    if a == b:
        raise ValueError("distinct exchange endpoints required")
    ra, rb = prefix_rates(a, y), prefix_rates(b, y)
    delta = {a: -1, b: 1}
    delta.update({s: x - z for s, (x, z) in enumerate(zip(ra, rb), 1) if x != z})
    return delta


def moment_defects(delta: dict[int, int], y: int) -> list[int]:
    return [sum(value * (q // j) for q, value in delta.items()) for j in range(1, y + 1)]


def analyze() -> dict:
    N, y = 10000, 100
    factors = mass_factors(N)
    products = {q: math.prod(p ** k for p, k in counts.items()) for q, counts in factors.items()}
    if sum(RELATION.values()) != 1 or any(moment_defects(RELATION, y)):
        raise ArithmeticError("saved relation failed exact moment check")
    capacities = []
    for q, w in RELATION.items():
        if w >= 0:
            continue
        power = 97 ** (-w)
        if products[q] < power:
            raise ArithmeticError("log(97) exceeds a signed-relation capacity")
        capacities.append({"q": q, "withdrawal_coefficient": -w,
                           "mass_product": str(products[q]), "required_product": str(power),
                           "equal": products[q] == power})
    if [row["q"] for row in capacities if row["equal"]] != [103]:
        raise ArithmeticError("stated log(97) bottleneck failed")
    small = {1: 1, 102: 1, 103: -1}
    if not set(small) <= set(factors) or any(moment_defects(small, y)):
        raise ArithmeticError("three-cell control is unsupported or changes moments")
    if factors[103] != {97: 1} or factors[102]:
        raise ArithmeticError("three-cell source/destination masses changed")

    # One analytically specified pair, not a scan or a greedy proposal.
    a, b = 103, 101
    delta = exchange(a, b, y)
    ra, rb = prefix_rates(a, y), prefix_rates(b, y)
    if not set(delta) <= set(factors) or any(moment_defects(delta, y)):
        raise ArithmeticError("counterexample moment or support identity failed")
    if sum(delta.values()) != 2 or any(delta.get(s, 0) < 0 for s in range(51, 101)):
        raise ArithmeticError("gain or top-prefix hypothesis failed")
    if factors[33] or delta[33] != -1 or factors[b]:
        raise ArithmeticError("zero-capacity counterexample failed")
    # At theta=log97 every touched cell except33 is feasible, exactly.
    failed = [q for q, value in delta.items() if value < 0 and products[q] < 97 ** (-value)]
    if failed != [33]:
        raise ArithmeticError(f"unexpected failing cells: {failed}")
    withdrawals = sorted(q for q, value in delta.items() if value < 0)
    if any(delta[q] != -1 for q in withdrawals):
        raise ArithmeticError("stated exact minimum-capacity formula changed")
    # The true upper-prefix telescoping identity, including s=y.
    for q in (101, 103, 5000):
        r = prefix_rates(q, y)
        if any(sum(r[u - 1:]) != q // u for u in range(51, 101)):
            raise ArithmeticError("upper-prefix suffix identity failed")
    r5000 = prefix_rates(5000, y)
    if (r5000[50], r5000[99]) != (2, 50):
        raise ArithmeticError("non-indicator rate controls failed")

    payload = (HUNT / "height_kernel_results.json").read_bytes()
    saved = json.loads(payload)
    if saved["status"] != "complete" or (saved["N"], saved["y"]) != (N, y):
        raise ValueError("completed N10000 height input required")
    iv = MPIntervalContext()
    iv.dps = 80
    psi = iv.mpf(saved["enclosures"]["psi"])
    variance = iv.mpf(saved["enclosures"]["optimizer_variance"])
    ceiling = psi * iv.sqrt(iv.log(2) * variance / (psi - iv.log(2)))
    if endpoint(ceiling, 1) >= Fraction(17508, 1000):
        raise ArithmeticError("stated variance-procedure ceiling failed")
    return {"status": "complete", "N": N, "y": y, "source_commit": SOURCE_COMMIT,
            "height_input_sha256": hashlib.sha256(payload).hexdigest(),
            "relation_capacity_exact": "log(97)", "negative_capacity_checks": capacities,
            "three_cell_delta_per_log97": small, "three_cell_zero_mass_destination": 102,
            "log97_enclosure": enclosure(iv.log(97)),
            "optimizer_variance_enclosure": saved["enclosures"]["optimizer_variance"],
            "constant_variance_procedure_ceiling": enclosure(ceiling),
            "counterexample": {"a": a, "b": b, "W_mu_a": sum(ra), "W_mu_b": sum(rb),
                "delta_per_theta": delta, "gain_per_theta": sum(delta.values()),
                "top_prefix_negative_changes": [], "failing_cells_at_log97": failed,
                "initial_capacity_exact": "0", "zero_mass_cell": 33,
                "zero_mass_integer_interval": [N // 34 + 1, N // 33],
                "accumulated_measure_capacity_cells": withdrawals},
            "rate_controls": {"r51_at_5000": r5000[50], "r100_at_5000": r5000[99],
                              "upper_suffix_identities_checked": 150},
            "optimizations": 0}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve() in {HUNT / "results.json", HUNT / "height_kernel_results.json"}:
        parser.error("original input archives must remain unchanged")
    started = time.perf_counter()
    report = {"status": "running", "requested": 1, "completed": 0}
    args.output.write_text(json.dumps(report) + "\n")
    print("started: fixed capacity controls at N10000, zero searches or optimizations", flush=True)
    try:
        report = analyze()
        report.update(requested=1, completed=1)
    except Exception as exc:
        report.update(status="failed", error=f"{type(exc).__name__}: {exc}")
        print(f"FAILED: {report['error']}", file=sys.stderr, flush=True)
        raise
    finally:
        report["seconds"] = time.perf_counter() - started
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"complete: 1/1 in {report['seconds']:.3f}s; proposed capacity estimate refuted", flush=True)


if __name__ == "__main__":
    main()
