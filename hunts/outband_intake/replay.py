"""Re-solve the cheap rungs behind this hunt's ladders and compare with the artifacts.

Issue #240: the runs behind RESULTS.md (and docs/35) were recorded in prose with
no `runmanifest`, so nothing pinned them. This script re-solves every
checkpointed solve that is cheap on a laptop, with the same `solve` call and
arguments `price_the_band.py` used, and compares the value with the one in
`artifacts/`. It writes nothing.

Not re-solved, because each costs minutes to hours: the out-of-band lane A rungs
at X = 120, 160 and 240 (recorded at 428 s, 2069 s and 10598 s), and the in-band
control at X = 240 and 320 from `lane-a-control-inband-long.json`. Those values
rest on the original artifacts alone.

Two tolerances, reported per row. EXACT (1e-9) is what a replay on the same
solver build would meet. SOLVER (1e-6) is what the LP's value is determined
to: HiGHS stops at feasibility tolerances of 1e-7, and on the 2026-10-10 replay
host its own three methods (`highs`, `highs-ds`, `highs-ipm`) disagreed by up to
7e-8 on the X = 40, reach 3.0 row. SOLVER was set after the first replay, run at
1e-9 alone, showed four out-of-band rows off by 7e-8 to 2e-7 (RUNS.md records
that run). Exit status is non-zero if any row misses SOLVER, or if nothing was
re-solved.

    .venv/bin/python hunts/outband_intake/replay.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "frontier_math"))

from configuration_lp import solve  # noqa: E402

ARTIFACTS = HERE / "artifacts"
SOURCES = ["lane-a-convergence.json", "lane-b-reach.json"]
EXACT = 1e-9
SOLVER = 1e-6


def _cheap(row):
    """Out-of-band rows up to X = 80 (40 s there, 428 s at X = 120); the
    in-band control is seconds at every rung up to X = 160."""
    if row.get("A_out") is None:
        return row["X"] <= 160
    return row["X"] <= 80


def main() -> int:
    checked, exact, failures, worst = 0, 0, 0, 0.0
    for name in SOURCES:
        for row in json.loads((ARTIFACTS / name).read_text()):
            if not row.get("feasible", True) or not _cheap(row):
                continue
            X, J, A_out = row["X"], row["J"], row.get("A_out")
            started = time.time()
            result = solve(J=J, X=X, eps=0.4 / X, A_out=A_out)
            elapsed = time.time() - started
            value = None if result is None else result["value"]
            diff = float("inf") if value is None else abs(value - row["value"])
            verdict = "exact" if diff <= EXACT else "solver" if diff <= SOLVER else "MISMATCH"
            checked += 1
            exact += verdict == "exact"
            failures += verdict == "MISMATCH"
            worst = max(worst, diff)
            reach = "none" if A_out is None else f"{A_out}"
            shown = "INFEASIBLE" if value is None else f"{value:.12f}"
            print(f"{name:26s} X={X:5.0f} J={J:4d} reach={reach:5s} "
                  f"artifact {row['value']:.12f}  re-solved {shown}  "
                  f"|diff| {diff:.1e}  {elapsed:.1f}s  {verdict}", flush=True)
    print(f"\nre-solved {checked} rows: {exact} within {EXACT:.0e}, "
          f"{checked - exact - failures} within {SOLVER:.0e} only, {failures} beyond; "
          f"worst |diff| {worst:.1e}")
    if checked == 0:
        print("nothing was re-solved: the artifacts are not what this script expects")
        return 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
