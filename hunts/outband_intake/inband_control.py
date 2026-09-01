"""The in-band control, which is also the calibration.

Lane A measures the out-of-band arm. This runs the same LP with the
out-of-band constraint switched off, at the same rungs, so the difference is
taken on one grid rather than against published values computed on another.

It is the calibration as well as the control: the in-band LP measures the
Montgomery-Taylor dual, whose limit is the standing record, so applying the
same extrapolation here recovers a known answer and the residual is the
method error. Any claim about the out-of-band limit is only as good as that
number.

`--extend` continues past the matched rungs. The in-band arm is roughly 240
times cheaper than the out-of-band one, so it can be pushed much further,
which sharpens the calibration.

Run from the repo root:
    .venv/bin/python hunts/outband_intake/inband_control.py
    .venv/bin/python hunts/outband_intake/inband_control.py --extend
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "frontier_math"))

from configuration_lp import solve  # noqa: E402

RECORD = 0.6725007036794116

MATCHED_RUNGS = [(40.0, 200), (80.0, 320), (120.0, 480), (160.0, 640)]
EXTENDED_RUNGS = [(240.0, 960), (320.0, 1280), (480.0, 1920), (640.0, 2560)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extend", action="store_true",
                        help="continue past the rungs lane A reached")
    args = parser.parse_args()

    rungs = EXTENDED_RUNGS if args.extend else MATCHED_RUNGS
    name = "lane-a-control-inband-long" if args.extend else "lane-a-control-inband"
    artifacts = HERE / "artifacts"
    artifacts.mkdir(exist_ok=True)
    out = artifacts / f"{name}.json"

    rows = []
    for X, J in rungs:
        started = time.time()
        result = solve(J=J, X=X, eps=0.4 / X, A_out=None)
        elapsed = round(time.time() - started, 1)
        rows.append({"X": X, "J": J, "A_out": None, "value": result["value"],
                     "D": result["D"], "wall_seconds": elapsed})
        out.write_text(json.dumps(rows, indent=1) + "\n")
        print(f"in-band X={X:6.1f} J={J:5d}  {result['value']:.7f}  "
              f"excess {result['value'] - RECORD:+.6f}  {elapsed}s", flush=True)

    print(f"\nartifact: {out}")


if __name__ == "__main__":
    main()
