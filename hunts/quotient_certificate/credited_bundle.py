"""Fixed N10000 bundle with seed credits retained, without searching for repairs."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
import time

from mpmath.ctx_iv import MPIntervalContext

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from hunts.quotient_certificate.compensated_repair import fold
from hunts.quotient_certificate.finite_transfer import mass_factors
from hunts.quotient_certificate.height_kernel import enclosure
from hunts.quotient_certificate.transport_capacity import moment_defects

HUNT = Path(__file__).resolve().parent
SOURCE_COMMIT = "0eb39186334612b3e55db315758c49ab87a29763"
ADDITIONS = {163: 57, 232: 7, 270: 5, 434: 74,
             625: 40, 1250: 22, 2500: 12, 5000: 4}


def analyze() -> dict:
    N, y = 10000, 100
    factors = mass_factors(N)
    products = {q: math.prod(p ** k for p, k in counts.items())
                for q, counts in factors.items()}
    # Enumerate the prescribed seed rule at this one input, not new bundles.
    folds = {a: fold(a, y) for a in factors if a > y and factors[a]}
    sources = [a for a, F in folds.items() if sum(F.values()) > 0]
    if len(sources) != 28 or not set(ADDITIONS) <= set(folds):
        raise ArithmeticError("prescribed source domain changed")
    coefficients = {a: 2 for a in sources}
    for a, count in ADDITIONS.items():
        coefficients[a] = coefficients.get(a, 0) + count
    for a in coefficients:
        if not set(folds[a]) <= set(factors) or any(moment_defects(folds[a], y)):
            raise ArithmeticError(f"fold support or moments failed at {a}")
    U = {q: sum(folds[a].get(q, 0) for a in sources) for q in factors}
    H = {q: sum(count * folds[a].get(q, 0) for a, count in ADDITIONS.items())
         for q in factors}
    D = {q: 2 * U[q] + H[q] for q in factors}
    V = folds[103]
    R = {q: D[q] - V.get(q, 0) for q in factors}
    if (sum(U.values()), sum(H.values()), sum(D.values()), sum(V.values()), sum(R.values())) != (91, 433, 615, 3, 612):
        raise ArithmeticError("gain accounting failed")
    if any(moment_defects(D, y)) or any(moment_defects(R, y)):
        raise ArithmeticError("bundle or grouped repair moments failed")

    empty = [q for q, counts in factors.items() if not counts]
    V_empty = {q: V[q] for q in empty if V.get(q, 0)}
    if V_empty != {33: -1, 100: 1}:
        raise ArithmeticError("single-block seed profile failed")
    if any(D[q] < 0 or R[q] < 0 for q in empty) or R[33] != 1:
        raise ArithmeticError("empty-cell coverage or repair hypothesis failed")
    if [q for q in empty if H[q] < 0] != [54, 62]:
        raise ArithmeticError("original decomposition obstruction changed")
    for q, expected in {33: (-22, 22, 0), 54: (2, -2, 0), 62: (4, -4, 0)}.items():
        if (2 * U[q], H[q], D[q]) != expected:
            raise ArithmeticError(f"credit or cancellation failed at {q}")

    actual, envelope = [], []
    for q, counts in factors.items():
        withdrawal = max(-D[q], 0)
        if withdrawal:
            if products[q] ** 146 < 229 ** withdrawal:
                raise ArithmeticError(f"net capacity failed at {q}")
            actual.append({"q": q, "withdrawal": withdrawal,
                           "mass_product": str(products[q]),
                           "equality": products[q] ** 146 == 229 ** withdrawal})
        if not counts:
            continue
        b0, b = max(-V.get(q, 0), 0), max(-R[q], 0)
        if b0 + b:
            if products[q] ** 146 < 229 ** (b0 + b):
                raise ArithmeticError(f"component capacity envelope failed at {q}")
            envelope.append({"q": q, "seed_burden": b0, "repair_burden": b,
                             "mass_product": str(products[q]),
                             "equality": products[q] ** 146 == 229 ** (b0 + b)})
    for rows in (actual, envelope):
        if [row["q"] for row in rows if row["equality"]] != [43]:
            raise ArithmeticError("unique cell-43 bottleneck failed")
    if factors[43] != {229: 1} or D[43] != -146 or V.get(43, 0) != 0:
        raise ArithmeticError("exact maximal scale changed")
    gains = {a: sum(folds[a].values()) for a in ADDITIONS}
    positive_gain = sum(count * max(gains[a], 0) for a, count in ADDITIONS.items())
    gain_loss = sum(count * max(-gains[a], 0) for a, count in ADDITIONS.items())
    if (positive_gain, gain_loss) != (480, 47):
        raise ArithmeticError("negative-gain components were not fully accounted for")

    iv = MPIntervalContext()
    iv.dps = 80
    return {"status": "complete", "source_commit": SOURCE_COMMIT, "N": N, "y": y,
            "attainable_cells": len(factors), "empty_cells": empty,
            "source_candidates_in_prescribed_rule": len(folds), "seed_sources": sources,
            "seed_unit_gain": 91, "additional_multiplicities": ADDITIONS,
            "additional_unit_gains": gains, "additional_positive_gain": positive_gain,
            "additional_gain_loss": gain_loss, "additional_net_gain": 433,
            "bundle_coefficients": coefficients,
            "bundle": {q: value for q, value in D.items() if value}, "bundle_gain": 615,
            "empty_profiles": {q: {"twice_U": 2 * U[q], "H": H[q], "D": D[q],
                                    "V": V.get(q, 0), "R": R[q]} for q in empty},
            "net_capacity_checks": actual, "component_envelope_checks": envelope,
            "regrouping": {"seed_source": 103, "seed_gain": 3, "repair_gain": 612,
                           "blocks": [[33]], "p": [1], "C": [[0]], "rho": 0,
                           "d": [1], "t": [1], "S": 1, "ell": 0,
                           "K_exact": "146/log(229)",
                           "boxed_lemma_gain_only": "3*log(229)/146",
                           "positive_repair_gain_retained": "612*log(229)/146"},
            "original_seed_obstruction_cells": [54, 62],
            "scale_exact": "log(229)/146", "scale_enclosure": enclosure(iv.log(229) / 146),
            "gain_exact": "615*log(229)/146", "gain_enclosure": enclosure(615 * iv.log(229) / 146),
            "searches": 0, "optimizations": 0}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve().parent == HUNT and args.output.name != "credited_bundle_results.json":
        parser.error("inside this hunt, only the new credited bundle output may be written")
    started = time.perf_counter()
    report = {"status": "running", "requested_bundles": 1, "completed_bundles": 0}
    args.output.write_text(json.dumps(report) + "\n")
    print("started: supplied N10000 bundle, existing repair lemma, zero searches", flush=True)
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
    print(f"complete: 1/1 bundle, {report['attainable_cells']} cells checked, "
          f"gain 615*log(229)/146, {report['seconds']:.3f}s", flush=True)


if __name__ == "__main__":
    main()
