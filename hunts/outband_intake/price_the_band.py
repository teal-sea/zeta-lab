"""Price the unconditional out-of-band information, two lanes.

Lane A converges the configuration LP in the truncation X with BGSTB
out-of-band positivity switched on, and repeats it switched off as the
control. The discretisation restricts the adversary, so the class value
descends as X grows and the pair of ladders brackets what the information
is worth.

Lane B holds the grid fixed and sweeps the out-of-band reach A_out, which
prices the information slice by slice: how much of the gain arrives in the
first stretch past alpha = 1, and where it saturates.

Every solve is written to artifacts/ as it completes, so an interrupted run
keeps everything it paid for.

Run from the repo root:
    .venv/bin/python hunts/outband_intake/price_the_band.py
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

# (X, J) rungs. eps tracks 0.4/X, the truncation error floor, as the
# frontier_math ladder does.
LANE_A_RUNGS = [(40.0, 200), (80.0, 320), (120.0, 480), (160.0, 640), (240.0, 960)]

# Out-of-band reach. None is the control: bandwidth-one data alone.
LANE_B_REACH = [None, 1.25, 1.5, 2.0, 3.0, 5.0, 8.0]
LANE_B_GRID = (80.0, 320)


def run_one(X, J, A_out):
    started = time.time()
    result = solve(J=J, X=X, eps=0.4 / X, A_out=A_out)
    elapsed = time.time() - started
    if result is None:
        return {"X": X, "J": J, "A_out": A_out, "feasible": False,
                "wall_seconds": round(elapsed, 1)}
    return {
        "X": X,
        "J": J,
        "A_out": A_out,
        "feasible": True,
        "value": result["value"],
        "D": result["D"],
        "p": [float(v) for v in result["p"]],
        "q": float(result["q"]),
        "wall_seconds": round(elapsed, 1),
    }


def checkpoint(path, rows):
    path.write_text(json.dumps(rows, indent=1) + "\n")


def main():
    ARTIFACTS.mkdir(exist_ok=True)

    lane_a = []
    path_a = ARTIFACTS / "lane-a-convergence.json"
    for A_out in (3.0, None):
        label = "out-of-band to 3.0" if A_out else "control, in-band only"
        for X, J in LANE_A_RUNGS:
            row = run_one(X, J, A_out)
            row["lane"] = "A"
            row["label"] = label
            lane_a.append(row)
            checkpoint(path_a, lane_a)
            value = f"{row['value']:.7f}" if row["feasible"] else "INFEASIBLE"
            print(f"A  {label:24s} X={X:6.1f} J={J:5d}  {value}  "
                  f"{row['wall_seconds']}s", flush=True)

    lane_b = []
    path_b = ARTIFACTS / "lane-b-reach.json"
    X, J = LANE_B_GRID
    for A_out in LANE_B_REACH:
        row = run_one(X, J, A_out)
        row["lane"] = "B"
        lane_b.append(row)
        checkpoint(path_b, lane_b)
        value = f"{row['value']:.7f}" if row["feasible"] else "INFEASIBLE"
        reach = "none" if A_out is None else f"{A_out}"
        print(f"B  reach={reach:6s} X={X:6.1f} J={J:5d}  {value}  "
              f"{row['wall_seconds']}s", flush=True)

    print(f"\nartifacts: {path_a}\n           {path_b}")


if __name__ == "__main__":
    main()
