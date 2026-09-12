#!/usr/bin/env python3
"""Fault injection for the n-point interval verifier (`verify_n.py`).

Why this exists. `verify_n.py` was validated by reproducing the published seven-point
run node for node. That establishes that two programs compute the same thing; it does
not establish that either is sound, and the same hunt holds the counterexample: the
published `verify_seven.py` reproduces its own committed certificate perfectly and is
unsound at raised targets, because its compactification prune is applied without
consulting the target (TRUST-MAP.md section 5.1). The Lean-side preflights were
fault-injected before they were trusted (FOUR-POINT.md section 4); this verifier was not.
A referee of the Pub 2 note said so, and was right.

What a soundness check of a verifier can be. A verifier is a decision procedure, so it
cannot be checked by feeding it a true instance: it accepts, and that is consistent with
being broken. The check is a *known-false* instance, a target strictly above the true
infimum of the functional, which a sound verifier must REFUSE. That refusal is the
harness. Fault injection then plants an unsoundness of a named shape and asks whether
the refusal flips to an acceptance: if it does, the harness detects that fault class; if
the verifier still refuses, the harness is blind to that class and this script says so.

The four planted fault classes mirror the four the Lean preflight was tested with, in
the verifier's own vocabulary:

  prune-ignores-target   the pressure prune is applied at a constant that does not
                         depend on the target (the published verifier's actual defect);
  inflated-kernel-table  every Arb lower bound on w is raised by a constant;
  inflated-coefficient   every pair coefficient 2/(n-s) is scaled up by one percent;
  dropped-box            the initial box containing the functional's minimiser is
                         silently removed from the search.

The false targets are the ones the hunt already refused and recorded: at n = 3,
13531/10^7 against an infimum of 0.0013530645... (RUNS.md 2026-08-23 validation
manifest); at n = 7, 38263/10^7 against the bracket 0.003826 <= inf F6 <= 0.0038262312
(RESULTS.md section 3). Both refusals were found at the configuration the float
minimiser found, which is the cell this script protects in the dropped-box fault.

Observability, as the house rule requires: this script prints every run it makes with
its node count and wall time, prints a verdict table, writes an artifact, and exits
non-zero unless (a) the true control is ACCEPTED, (b) the false control is REFUSED, and
(c) every planted fault flips the false control to ACCEPTED. A fault the harness cannot
see is reported by name; it is not swallowed.

Nothing here is a statement about zeta zeros. It is a statement about a program.

Usage (from the repository root, with python-flint installed in the venv):

    .venv/bin/python hunts/ainta_seven_point/verify_n_faults.py --n 3
    .venv/bin/python hunts/ainta_seven_point/verify_n_faults.py --n 7 --skip-true

The upstream verifier package is fetched at its pinned commit by `fetch_upstream.sh`
and `verify_n.py` is copied into it; both happen here automatically.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
UPSTREAM = REPO / ".upstream" / "zeta-simple-zeros"
ZSZ_SRC = UPSTREAM / "src" / "zeta_simple_zeros"
ARTIFACTS = HERE / "artifacts"

# (true target, false target, pressure, minimiser gaps) per point count. The false
# target is strictly above the recorded infimum; the minimiser is where the recorded
# refusal landed, to four decimals.
CASES: Dict[int, Dict[str, Any]] = {
    3: {
        "true": (1353, 10**6),
        "false": (13531, 10**7),
        "pressure": 3000,
        "minimiser": [1.05083108, 2.00247696],
        "recorded_infimum": "0.0013530645459787036",
    },
    7: {
        "true": (19, 5000),
        "false": (38263, 10**7),
        "pressure": 3000,
        "minimiser": [1.046, 1.990, 1.986, 1.042, 1.977, 1.045],
        "recorded_infimum": "0.003826 <= inf <= 0.0038262312115073",
    },
}


def ensure_upstream() -> None:
    """Fetch the pinned upstream clone if absent and install verify_n.py into it."""

    if not (UPSTREAM / ".git").is_dir():
        subprocess.run(["bash", str(HERE / "fetch_upstream.sh")], check=True,
                       stdout=subprocess.DEVNULL)
    src = HERE / "verify_n.py"
    dst = ZSZ_SRC / "verify_n.py"
    if not dst.exists() or src.read_bytes() != dst.read_bytes():
        shutil.copyfile(src, dst)
    sys.path.insert(0, str(ZSZ_SRC.parent))


def run_one(V: Any, n: int, num: int, den: int, pressure: int, grid: int,
            label: str, patch: Optional[Callable[[Any], Callable[[], None]]]) -> Dict[str, Any]:
    """Run verify_n once, unsharded, with an optional fault installed for the duration."""

    undo: Callable[[], None] = lambda: None
    if patch is not None:
        undo = patch(V)
    started = time.perf_counter()
    try:
        result = V.verify_n(n, num, den, grid=grid, pressure=pressure)
    finally:
        undo()
    wall = time.perf_counter() - started
    row = {
        "label": label,
        "target": f"{num}/{den}",
        "outcome": result["outcome"],
        "nodes": result["nodes"],
        "pressure_pruned": result["pressure_pruned"],
        "interval_pruned": result["interval_pruned"],
        "tangent_pruned": result["tangent_pruned"],
        "maximum_depth": result["maximum_depth"],
        "cutoff_cells": result["cutoff_cells"],
        "refuting_cell_gaps": result["refuting_cell_gaps"],
        "wall_seconds": round(wall, 1),
    }
    print(f"  {label:<24} {row['target']:<14} {row['outcome']:<9} nodes={row['nodes']:<8} "
          f"pruned p/i/t={row['pressure_pruned']}/{row['interval_pruned']}/{row['tangent_pruned']} "
          f"depth={row['maximum_depth']} cutoff={row['cutoff_cells']} {row['wall_seconds']}s",
          flush=True)
    return row


# ---------------------------------------------------------------- the four faults

def fault_prune_ignores_target(cutoff_cells: int) -> Callable[[Any], Callable[[], None]]:
    """The published verifier's defect: a prune constant that does not consult the target.

    `prepare` refuses a cutoff below the derived one, so the fault is planted where the
    real one lived, downstream of that check: the prepared object's cutoff is overwritten
    after preparation, which is what a hard-coded constant amounts to.
    """

    def install(V: Any) -> Callable[[], None]:
        original = V.prepare

        def patched(*args: Any, **kwargs: Any) -> Any:
            prepared = original(*args, **kwargs)
            prepared.cutoff_cells = cutoff_cells
            return prepared

        V.prepare = patched
        return lambda: setattr(V, "prepare", original)

    return install


def fault_inflated_kernel_table(delta: float) -> Callable[[Any], Callable[[], None]]:
    """Every Arb lower bound on w = k^2 raised by `delta`: the enclosure lies upward."""

    def install(V: Any) -> Callable[[], None]:
        original = V.build_kernel_table

        def patched(*args: Any, **kwargs: Any) -> Any:
            table = original(*args, **kwargs)
            return [value + delta for value in table]

        V.build_kernel_table = patched
        return lambda: setattr(V, "build_kernel_table", original)

    return install


def fault_inflated_coefficient(factor: Fraction) -> Callable[[Any], Callable[[], None]]:
    """Every pair coefficient 2/(n-s) scaled by `factor` > 1: the functional overstated."""

    def install(V: Any) -> Callable[[], None]:
        original = V._coefficient_bounds
        fmpq = V.fmpq

        def patched(n_points: int, span: int) -> Any:
            low, high, exact = original(n_points, span)
            f = float(factor)
            return low * f, high * f, exact * fmpq(factor.numerator, factor.denominator)

        V._coefficient_bounds = patched
        return lambda: setattr(V, "_coefficient_bounds", original)

    return install


def fault_dropped_box(minimiser: Sequence[float], grid: int) -> Callable[[Any], Callable[[], None]]:
    """The initial boxes containing the minimiser are removed before the search starts.

    Both of them: F is symmetric under reversing the gap vector, so every minimiser has a
    mirror image, and the first version of this fault dropped only one. The verifier then
    refused at the mirror, in the same 115 nodes as the control, and the harness reported
    itself blind to a fault that had not been fully planted. That run is kept in the
    artifact history as the reason this docstring exists.
    """

    images = [[int(g * grid) for g in minimiser], [int(g * grid) for g in reversed(minimiser)]]

    def contains(box: Sequence[Sequence[int]]) -> bool:
        return any(all(left <= cell <= right for (left, right), cell in zip(box, cells))
                   for cells in images)

    def install(V: Any) -> Callable[[], None]:
        original = V.shard_boxes

        def patched(boxes: Sequence[Any], shard_index: int, shard_count: int) -> List[Any]:
            kept = [box for box in original(boxes, shard_index, shard_count) if not contains(box)]
            dropped = len(original(boxes, shard_index, shard_count)) - len(kept)
            if dropped == 0:
                raise RuntimeError("dropped-box fault found no box containing the minimiser; "
                                   "the fault was not planted, refusing to report a result")
            return kept

        V.shard_boxes = patched
        return lambda: setattr(V, "shard_boxes", original)

    return install


# ---------------------------------------------------------------- main

def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--n", type=int, required=True, choices=sorted(CASES))
    ap.add_argument("--grid", type=int, default=4000)
    ap.add_argument("--skip-true", action="store_true",
                    help="skip the true-instance control (already reproduced and recorded)")
    args = ap.parse_args(argv)

    ensure_upstream()
    from zeta_simple_zeros import verify_n as V  # noqa: E402

    case = CASES[args.n]
    n, grid, p = args.n, args.grid, case["pressure"]
    tnum, tden = case["true"]
    fnum, fden = case["false"]
    derived = V.derived_cutoff_cells(grid, p, fnum, fden)
    # A cutoff that prunes the minimiser: its gap sum in cells, minus a margin, but never
    # below what the true target would derive, so the fault is "wrong target", not "absurd".
    min_sum_cells = int(sum(case["minimiser"]) * grid)
    bad_cutoff = min(min_sum_cells - grid // 20, derived - 1)

    print(f"verify_n fault injection: n={n} grid={grid} pressure={p}")
    print(f"  true target {tnum}/{tden}, false target {fnum}/{fden} "
          f"(recorded infimum {case['recorded_infimum']}), derived cutoff {derived} cells")
    rows: List[Dict[str, Any]] = []

    if not args.skip_true:
        rows.append(run_one(V, n, tnum, tden, p, grid, "control-true", None))
    rows.append(run_one(V, n, fnum, fden, p, grid, "control-false", None))

    faults = [
        ("prune-ignores-target", fault_prune_ignores_target(bad_cutoff)),
        ("inflated-kernel-table", fault_inflated_kernel_table(2e-4)),
        ("inflated-coefficient", fault_inflated_coefficient(Fraction(101, 100))),
        ("dropped-box", fault_dropped_box(case["minimiser"], grid)),
    ]
    for label, patch in faults:
        rows.append(run_one(V, n, fnum, fden, p, grid, label, patch))

    # ---- verdict
    by = {r["label"]: r for r in rows}
    problems: List[str] = []
    if "control-true" in by and by["control-true"]["outcome"] != "ACCEPTED":
        problems.append(f"control-true was {by['control-true']['outcome']}, expected ACCEPTED")
    if by["control-false"]["outcome"] != "REFUSED":
        problems.append(f"control-false was {by['control-false']['outcome']}, expected REFUSED: "
                        "the harness has no teeth and nothing below means anything")
    detected, blind = [], []
    for label, _ in faults:
        (detected if by[label]["outcome"] == "ACCEPTED" else blind).append(label)
    for label in blind:
        problems.append(f"fault '{label}' did not flip the refusal (got {by[label]['outcome']}): "
                        "the harness is blind to this fault class")

    print()
    print(f"verdict: controls {'ok' if not any('control' in q for q in problems) else 'FAILED'}; "
          f"faults detected {len(detected)}/{len(faults)}"
          + (f"; blind to: {', '.join(blind)}" if blind else ""))
    for q in problems:
        print(f"  PROBLEM: {q}")

    ARTIFACTS.mkdir(exist_ok=True)
    out = ARTIFACTS / f"verify-n-faults-n{n}-grid{grid}.json"
    payload = {
        "script": "hunts/ainta_seven_point/verify_n_faults.py",
        "verifier": "hunts/ainta_seven_point/verify_n.py, installed into the pinned upstream "
                    "clone (040c5e8) beside kernel.py and rounding.py",
        "n": n, "grid": grid, "pressure": p,
        "true_target": f"{tnum}/{tden}", "false_target": f"{fnum}/{fden}",
        "recorded_infimum": case["recorded_infimum"],
        "derived_cutoff_cells": derived, "planted_bad_cutoff_cells": bad_cutoff,
        "runs": rows,
        "faults_detected": detected, "faults_blind": blind, "problems": problems,
        "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    out.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"artifact: {out.relative_to(REPO)}")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
