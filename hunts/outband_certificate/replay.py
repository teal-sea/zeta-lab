"""Re-solve the cheap rungs of the narrow-strip ladder and compare with the artifact.

Issue #240: the runs behind RESULTS.md (and docs/35) were recorded in prose with
no `runmanifest`, so nothing pinned them. This script re-solves every row of
`artifacts/ladder-narrow-strip.json` at X <= 160, with the same `solve` call and
arguments `ladder.py` used, and compares the value with the artifact. It writes
nothing.

Not re-solved, because together they cost about a quarter of an hour on a
laptop: the X = 240 and X = 320 rows (recorded at 61 s to 418 s each). Those
values, the lattice ladders and the `dual.py` and `signed_window.py` runs in
RUNS.md rest on the original artifacts and prose alone.

Two tolerances, reported per row, for the reason `../outband_intake/replay.py`
gives: EXACT (1e-9) for a replay on the same solver build, SOLVER (1e-6) for
what HiGHS's 1e-7 feasibility tolerances determine the value to. Exit status
is non-zero if any row misses SOLVER, or if nothing was re-solved.

    .venv/bin/python hunts/outband_certificate/replay.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "frontier_math"))

from configuration_lp import solve  # noqa: E402

ART = HERE / "artifacts" / "ladder-narrow-strip.json"
MAX_X = 160.0
EXACT = 1e-9
SOLVER = 1e-6


def main() -> int:
    checked, exact, failures, worst = 0, 0, 0, 0.0
    for row in json.loads(ART.read_text()):
        if not row["feasible"] or row["X"] > MAX_X:
            continue
        X, J, w = row["X"], row["J"], row["width"]
        started = time.time()
        result = solve(J=J, X=X, eps=0.4 / X, A_out=None if w is None else 1.0 + w)
        elapsed = time.time() - started
        value = None if result is None else result["value"]
        diff = float("inf") if value is None else abs(value - row["value"])
        verdict = "exact" if diff <= EXACT else "solver" if diff <= SOLVER else "MISMATCH"
        checked += 1
        exact += verdict == "exact"
        failures += verdict == "MISMATCH"
        worst = max(worst, diff)
        width = "none" if w is None else f"{w:.2f}"
        shown = "INFEASIBLE" if value is None else f"{value:.12f}"
        print(f"X={X:5.0f} J={J:4d} width={width:>4s}  artifact {row['value']:.12f}  "
              f"re-solved {shown}  |diff| {diff:.1e}  {elapsed:.1f}s  {verdict}", flush=True)
    print(f"\nre-solved {checked} rows: {exact} within {EXACT:.0e}, "
          f"{checked - exact - failures} within {SOLVER:.0e} only, {failures} beyond; "
          f"worst |diff| {worst:.1e}")
    if checked == 0:
        print("nothing was re-solved: the artifact is not what this script expects")
        return 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
