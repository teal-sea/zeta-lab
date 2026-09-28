"""Exact fixed compensated-fold check, with no bundle search or optimization."""
from __future__ import annotations

import argparse
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
from hunts.quotient_certificate.height_kernel import enclosure
from hunts.quotient_certificate.transport_capacity import moment_defects

HUNT = Path(__file__).resolve().parent
SOURCE_COMMIT = "f4ae24f027f07916037ca8fe6c56c95a29cbf4d7"


def fold(a: int, y: int) -> dict[int, int]:
    """Halving fold with the zero endpoint and merged prefix destination."""
    if not isinstance(a, int) or not isinstance(y, int) or y < 1 or a <= y:
        raise ValueError("integer a>y>=1 required")
    T = [0] * (y + 2)
    for i in range(1, y + 1):
        T[i] = sum(int(mobius(k)) * ((a // (i * k)) % 2)
                   for k in range(1, y // i + 1))
    result = {a: -1, a // 2: 2}
    for i in range(1, y + 1):
        result[i] = result.get(i, 0) + T[i] - T[i + 1]
    return {q: value for q, value in result.items() if value}


def analyze() -> dict:
    N, y = 1000, 31
    factors = mass_factors(N)
    products = {q: math.prod(p ** k for p, k in counts.items())
                for q, counts in factors.items()}
    if not set(range(1, y + 1)) <= set(factors):
        raise ArithmeticError("prefix not attainable")
    sources = (76, 200, 333)
    folds = {a: fold(a, y) for a in sources}
    for a, F in folds.items():
        if not factors[a] or not set(F) <= set(factors) or any(moment_defects(F, y)):
            raise ArithmeticError(f"fold support, source or moment check failed at {a}")
    if [sum(folds[a].values()) for a in sources] != [2, 4, 0]:
        raise ArithmeticError("fixed fold gains changed")
    seed = {q: folds[76].get(q, 0) + 2 * folds[200].get(q, 0) for q in factors}
    repair = folds[333]
    bundle = {q: seed[q] + repair.get(q, 0) for q in factors}
    if any(moment_defects(bundle, y)) or sum(bundle.values()) != 10:
        raise ArithmeticError("bundle moments or gain failed")
    empty = [q for q, counts in factors.items() if not counts]
    if [q for q in empty if seed[q] < 0] != [19, 25]:
        raise ArithmeticError("stated seed deficit block failed")
    if any(seed[q] != -1 or repair.get(q) != 1 for q in (19, 25)):
        raise ArithmeticError("one-unit joint repair failed")
    if any(repair.get(q, 0) < 0 or bundle[q] < 0 for q in empty):
        raise ArithmeticError("an empty cell is drained")

    actual_checks, envelope_checks = [], []
    for q, counts in factors.items():
        withdrawal = max(-bundle[q], 0)
        if withdrawal:
            if products[q] ** 3 < 7 ** withdrawal:
                raise ArithmeticError(f"actual capacity failed at {q}")
            actual_checks.append({"q": q, "withdrawal": withdrawal,
                                  "mass_product": str(products[q]),
                                  "equality": products[q] ** 3 == 7 ** withdrawal})
        # Empty cells use the repair lemma, not a positive-mass burden bound.
        if not counts:
            continue
        b0, b = max(-seed[q], 0), max(-repair.get(q, 0), 0)
        if b0 + b:
            if products[q] ** 3 < 7 ** (b0 + b):
                raise ArithmeticError(f"gross burden bound failed at {q}")
            envelope_checks.append({"q": q, "seed_burden": b0, "repair_burden": b,
                                    "mass_product": str(products[q]),
                                    "equality": products[q] ** 3 == 7 ** (b0 + b)})
    for rows in (actual_checks, envelope_checks):
        if [row["q"] for row in rows if row["equality"]] != [20]:
            raise ArithmeticError("unique cell-20 bottleneck failed")
    if factors[20] != {7: 1} or bundle[20] != -3:
        raise ArithmeticError("exact capacity identity failed")

    iv = MPIntervalContext()
    iv.dps = 80
    return {"status": "complete", "source_commit": SOURCE_COMMIT,
            "N": N, "y": y, "attainable_cells": len(factors),
            "empty_cells": empty,
            "folds": {a: {"gain": sum(F.values()), "vector": F} for a, F in folds.items()},
            "multiplicities": {76: 1, 200: 2, 333: 1},
            "seed_gain": sum(seed.values()), "repair_gain": sum(repair.values()),
            "seed_deficit_block": [19, 25],
            "empty_profiles": {q: {"seed": seed[q], "repair": repair.get(q, 0),
                                    "bundle": bundle[q]} for q in empty},
            "bundle": {q: value for q, value in bundle.items() if value},
            "unscaled_gain": sum(bundle.values()),
            "actual_capacity_checks": actual_checks,
            "positive_mass_envelope_checks": envelope_checks,
            "repair_lemma": {"P": [[0]], "d": [1], "p": [1], "rho": 0,
                             "t": [1], "S": 1, "ell": 0, "K_exact": "3/log(7)"},
            "scale_exact": "log(7)/3", "scale_enclosure": enclosure(iv.log(7) / 3),
            "gain_exact": "10*log(7)/3", "gain_enclosure": enclosure(10 * iv.log(7) / 3),
            "searches": 0, "optimizations": 0}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve().parent == HUNT and args.output.name != "compensated_repair_results.json":
        parser.error("inside this hunt, only the new compensated repair output may be written")
    started = time.perf_counter()
    report = {"status": "running", "requested_bundles": 1, "completed_bundles": 0}
    args.output.write_text(json.dumps(report) + "\n")
    print("started: one prescribed bundle at N1000, three folds, zero searches", flush=True)
    try:
        report = analyze()
        report.update(requested_bundles=1, completed_bundles=1)
    except Exception as exc:
        report.update(status="failed", error=f"{type(exc).__name__}: {exc}")
        print(f"FAILED: {report['error']}", file=sys.stderr, flush=True)
        raise
    finally:
        report["seconds"] = time.perf_counter() - started
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"complete: 1/1 bundle, all {report['attainable_cells']} cells checked, "
          f"gain 10*log(7)/3, {report['seconds']:.3f}s", flush=True)


if __name__ == "__main__":
    main()
