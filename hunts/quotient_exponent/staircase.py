"""The full curve E(y) at fixed N, at every integer support.

The bisection found the transition to zero and, on the way, something the
diagonal could not show: the excess is constant over long runs of `y` and then
steps down.  A bisection sees only the values it happens to probe, so this
solves every integer support and reports the staircase, its step positions and
the length of the plateau immediately before zero.

A step in `y` means the column `floor(q/y)` added nothing to the programme at
all until the one that collapsed it.  That is a rank statement about the
constraint matrix, and it is the shape a reader should see before any law is
fitted through it.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import lp

ART = Path(__file__).resolve().parent / "artifacts"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y-max", type=int, default=None)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    N = args.N
    y_max = args.y_max or int(2.5 * math.isqrt(N))
    curve = []
    for y in range(2, y_max + 1):
        r = lp.solve(N, y, verbose=False)
        curve.append({"y": y, "excess": r["excess"],
                      "excess_direct": r["excess_direct"],
                      "min_e_direct": r["min_e_direct"],
                      "binding": r["n_binding_cells"],
                      "max_abs_c": r["max_abs_c"]})
    cells = int(lp.quotient_cells(N).size)

    steps, plateaus = [], []
    run_start, run_val = 0, curve[0]["excess"]
    for i, pt in enumerate(curve[1:], start=1):
        if abs(pt["excess"] - run_val) > 1e-9 * max(1.0, abs(run_val)):
            plateaus.append({"y_from": curve[run_start]["y"], "y_to": curve[i - 1]["y"],
                             "length": i - run_start, "excess": run_val})
            steps.append({"y": pt["y"], "from": run_val, "to": pt["excess"]})
            run_start, run_val = i, pt["excess"]
    plateaus.append({"y_from": curve[run_start]["y"], "y_to": curve[-1]["y"],
                     "length": len(curve) - run_start, "excess": run_val})

    zeros = [p for p in curve if p["excess"] <= 1e-9 * max(1.0, p["excess_direct"])]
    y_star = zeros[0]["y"] if zeros else None
    last_positive_plateau = None
    for p in plateaus:
        if p["excess"] > 0:
            last_positive_plateau = p

    out = {"N": N, "cells": cells, "y_max": y_max, "y_star": y_star,
           "n_distinct_values": len(plateaus), "n_steps": len(steps),
           "last_positive_plateau": last_positive_plateau,
           "plateaus": plateaus, "curve": curve}
    name = args.out or f"staircase_N{N}.json"
    ART.mkdir(exist_ok=True)
    (ART / name).write_text(json.dumps(out, indent=1), encoding="utf-8")
    print(f"N={N}  supports solved {len(curve)}  distinct values {len(plateaus)}  "
          f"y* = {y_star}  |Q_N| = {cells}")
    if last_positive_plateau:
        p = last_positive_plateau
        print(f"  last positive plateau: excess {p['excess']:.6f} held for "
              f"y = {p['y_from']}..{p['y_to']} ({p['length']} supports)")
    print(f"  longest plateau: " + str(max(plateaus, key=lambda p: p['length'])))
    print(f"-> {ART / name}")


if __name__ == "__main__":
    main()
