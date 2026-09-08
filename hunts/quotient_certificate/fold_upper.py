"""Fixed upper certificate and exact signed-fold coordinates, without optimization."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
from importlib.metadata import version
import json
from pathlib import Path
import shlex
import subprocess
import sys
import time

from mpmath.ctx_iv import MPIntervalContext

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from hunts.quotient_certificate.compensated_repair import fold
from hunts.quotient_certificate.finite_transfer import mass_factors
from hunts.quotient_certificate.height_kernel import endpoint, outward_bounds

HUNT = Path(__file__).resolve().parent
INPUT = HUNT / "fold_upper_input.json"


def signed_coordinates(delta: dict, cells: list[int], y: int) -> dict[int, Fraction]:
    """Exact coordinates for a supported rational zero-moment vector.

    The supplied cells must contain the prefix and every halved source.
    Missing parents in the descending recurrence have coefficient zero.
    """
    Q = set(cells)
    if len(Q) != len(cells) or not set(range(1, y + 1)) <= Q:
        raise ValueError("distinct cells containing the full prefix required")
    if y < 1 or any(q <= 0 or not isinstance(q, int) for q in Q):
        raise ValueError("positive integer cells and prefix length required")
    if any(q // 2 not in Q for q in Q if q > y):
        raise ValueError("halved source is missing")
    if not set(delta) <= Q or any(not isinstance(v, (int, Fraction)) for v in delta.values()):
        raise ValueError("supported integer or rational vector required")
    if any(sum(v * (q // j) for q, v in delta.items()) for j in range(1, y + 1)):
        raise ValueError("delta does not have zero moments")
    x = {}
    for q in sorted((q for q in Q if q > y), reverse=True):
        value = 2 * x.get(2 * q, 0) + 2 * x.get(2 * q + 1, 0) - Fraction(delta.get(q, 0))
        if value:
            x[q] = value
    return x


def check_columns(B: dict[int, int], denominator: int, cells: list[int], y: int) -> tuple[dict, list]:
    """Check nonnegative B and every exact fold-column inequality."""
    if denominator <= 0 or not set(B) <= set(cells):
        raise ValueError("positive denominator and supported B required")
    if any(not isinstance(v, int) or v < 0 for v in B.values()):
        raise ValueError("nonnegative integer B required")
    columns, rows = {}, []
    for a in cells:
        if a <= y:
            continue
        F = fold(a, y)
        if not set(F) <= set(cells):
            raise ArithmeticError("fold leaves attainable support")
        if any(sum(v * (q // j) for q, v in F.items()) for j in range(1, y + 1)):
            raise ArithmeticError("fold has nonzero moment")
        gain, dot = sum(F.values()), sum(B.get(q, 0) * v for q, v in F.items())
        slack = -denominator * gain - dot
        if slack < 0:
            raise ArithmeticError(f"upper inequality fails at source {a}: slack {slack}")
        columns[a] = F
        rows.append({"source": a, "gain": gain, "B_dot_fold": dot, "slack": slack})
    return columns, rows


def analyze() -> dict:
    payload = INPUT.read_bytes()
    source = json.loads(payload)
    N, y, den = source["N"], source["y"], source["denominator"]
    if (N, y, den) != (10000, 100, 1387):
        raise ValueError("only the prescribed N10000,y100 certificate is in scope")
    B = {int(q): v for q, v in source["B"].items()}
    factors = mass_factors(N)
    cells = list(factors)
    columns, rows = check_columns(B, den, cells, y)
    if len(cells) != 198 or len(columns) != 98:
        raise ArithmeticError("attainable domain changed")
    for row in rows:
        row["initially_empty_source"] = not bool(factors[row["source"]])
    # Exhaustive inverse check for these 98 basis columns. Orthogonal prefix
    # constructions and rational signed combinations are checked by pytest.
    for a, F in columns.items():
        if signed_coordinates(F, cells, y) != {a: Fraction(1)}:
            raise ArithmeticError(f"descending inverse failed for column {a}")
    log_coefficients = Counter()
    for q, b in B.items():
        for p, count in factors[q].items():
            log_coefficients[p] += b * count
    iv = MPIntervalContext()
    iv.dps = 90
    cost = sum((iv.log(p) * b for p, b in log_coefficients.items()), iv.mpf(0)) / den
    bounds = outward_bounds(endpoint(cost, 0), endpoint(cost, 1), 45)
    if bounds != source["coordinator_cost_enclosure"]:
        raise ArithmeticError("independent cost enclosure does not match supplied endpoints")
    if not endpoint(cost, 1) < Fraction(66339, 1000) < Fraction(source["comparison"]["gain"]):
        raise ArithmeticError("strict comparison with saved prefix gain failed")
    return {"status": "complete", "N": N, "y": y, "input_sha256": hashlib.sha256(payload).hexdigest(),
            "coefficient_domain": "nonnegative real x; every attainable source above y",
            "attainable_cells": len(cells), "allowed_sources": len(columns),
            "initially_empty_sources": sum(row["initially_empty_source"] for row in rows),
            "B_support_count": len(B), "positive_mass_B_cells": [q for q in B if factors[q]],
            "column_checks": rows, "tight_columns": sum(row["slack"] == 0 for row in rows),
            "strict_columns": sum(row["slack"] > 0 for row in rows),
            "largest_integer_slack": max(row["slack"] for row in rows),
            "cost_log_numerators": dict(sorted(log_coefficients.items())),
            "cost_denominator": den, "cost_enclosure": bounds,
            "comparison_gain": source["comparison"]["gain"],
            "signed_column_inverse_checks": len(columns),
            "optimizations": 0, "witness_coordinate_conversions": 0}


def write_manifest(path: Path, output: Path, report: dict, started: str) -> None:
    def git(*args):
        return subprocess.run(["git", *args], cwd=ROOT, check=True, text=True, capture_output=True).stdout.strip()

    code_inputs = [INPUT, Path(__file__), HUNT / "compensated_repair.py",
                   HUNT / "finite_transfer.py", HUNT / "height_kernel.py"]
    manifest = {
        "schema_version": 1, "claim_id": "nonnegative-halving-fold-upper-N10000-y100",
        "repository": {"commit": git("rev-parse", "HEAD"), "dirty": bool(git("status", "--porcelain"))},
        "command": "OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 "
                   + shlex.join([".venv/bin/python", "hunts/quotient_certificate/fold_upper.py",
                                 "--output", str(output), "--manifest", str(path)]),
        "environment": {"software": [f"Python {sys.version.split()[0]}"] +
                        [f"{name} {version(name)}" for name in ("mpmath", "sympy", "numpy", "python-flint")],
                        "hardware": "Not material to this bounded exact check; numerical libraries limited to one thread."},
        "mathematics": {
            "assertion_tested": "B>=0; F^T B<=-1387g on all 98 columns; cost<66.339; descending inverse for each column",
            "coefficient_domain": "Integer columns and B; rational coordinates; fresh 90-digit intervals for logarithms",
            "conventions": "All attainable sources above 100, including empty sources; T_(y+1)=0; merged prefix destination",
            "inputs": [{"path": str(p.relative_to(ROOT)), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in code_inputs],
            "bounds": {"N": 10000, "y": 100, "attainable_cells": 198, "columns": 98,
                       "numerical_threads": 1, "optimizer_calls": 0},
            "non_claims": ["No exact restricted optimum or matching lower certificate",
                           "No bound for arbitrary signed folds or general prefix exchanges",
                           "No upper bound for the full T* problem or growth estimate in N"]},
        "randomness": {"used": False, "generator": "none", "seed": None},
        "run": {"started_at": started, "runtime_seconds": report["seconds"],
                "exit_status": 0 if report["status"] == "complete" else 1},
        "outputs": [{"path": str(output), "sha256": hashlib.sha256(output.read_bytes()).hexdigest()}],
        "checks": [{"name": name, "status": "passed" if report["status"] == "complete" else "not completed"}
                   for name in ("Exact support, moments and 98 inequalities", "All 98 column inverse checks",
                                "Outward-rounded 45-decimal logarithmic cost", "Strict comparison with previously verified gain")],
        "result": report["status"],
        "residual_risks": ["Relies on integer/rational and interval arithmetic implementations; no formal proof artifact",
                           "The saved comparison witness is an accepted input, not rechecked here"]}
    path.write_text(json.dumps(manifest, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    for path, name in ((args.output, "fold_upper_results.json"), (args.manifest, "fold_upper_manifest.json")):
        if path.resolve().parent == HUNT and path.name != name:
            parser.error("previous hunt archives must remain unchanged")
    if args.output.resolve() == args.manifest.resolve():
        parser.error("output and manifest must be distinct")
    started, stamp = time.perf_counter(), datetime.now(timezone.utc).isoformat()
    report = {"status": "running", "requested_certificates": 1, "completed_certificates": 0}
    args.output.write_text(json.dumps(report) + "\n")
    print("started: one upper certificate, all 98 sources, zero optimizer calls", flush=True)
    try:
        report = analyze()
        report.update(requested_certificates=1, completed_certificates=1)
    except Exception as exc:
        report.update(status="failed", error=f"{type(exc).__name__}: {exc}")
        print(f"FAILED: {report['error']}", file=sys.stderr, flush=True)
        raise
    finally:
        report["seconds"] = time.perf_counter() - started
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        write_manifest(args.manifest, args.output, report, stamp)
    print(f"complete: 1/1, {report['allowed_sources']} inequalities and inverse checks, "
          f"cost<66.339, {report['seconds']:.3f}s", flush=True)


if __name__ == "__main__":
    main()
