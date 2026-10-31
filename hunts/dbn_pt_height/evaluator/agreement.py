"""Milestone 1: the A + B - C evaluator against two independent routes to H_t.

For each (x, y, t) on a grid with 200 <= x <= 400 (and a few larger x for the
heat-kernel route only), compute

* H_phi: ``zeta.heatflow.H_t`` (Phi quadrature, precision from recommended_dps),
* H_hk:  the mpmath heat-kernel quadrature of ``oracles.Ht_heat_kernel``,
* the evaluator's A + B - C and its error radii E_A, E_B, E_C (Theorem 1.3 as
  published), and the A + B form with E_{C,0},

and record the measured differences against the radii.  One JSON line per point
is appended to the output as soon as that point is done (checkpoint per unit);
a rerun skips points already present.

Usage:  .venv/bin/python hunts/dbn_pt_height/evaluator/agreement.py ROUTE OUT.jsonl
with ROUTE in {phi, hk}.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (str(ROOT), str(HERE)):
    if p not in sys.path:
        sys.path.insert(0, p)

from mpmath import mp  # noqa: E402

import oracles  # noqa: E402

GRID_X = ["200", "250", "300", "350", "400"]
GRID_Y = ["0", "0.5", "1"]
GRID_T = ["0", "0.05", "0.2", "0.5"]
EXTRA_HK = [("1000", "0.2", "0.2"), ("1000", "0", "0.05"), ("2000", "0.5", "0.2"), ("2000", "0", "0.5")]


def grid(route: str) -> list[tuple[str, str, str]]:
    pts = [(x, y, t) for x in GRID_X for y in GRID_Y for t in GRID_T]
    if route == "hk":
        pts += EXTRA_HK
    return pts


def main() -> None:
    route, out = sys.argv[1], Path(sys.argv[2])
    done = set()
    if out.exists():
        for line in out.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                done.add((r["x"], r["y"], r["t"]))
    for (x, y, t) in grid(route):
        if (x, y, t) in done:
            continue
        t0 = time.perf_counter()
        if route == "phi":
            v = oracles.Ht_phi(x, y, t, digits=20)
            dps = 20
        else:
            v = oracles.Ht_heat_kernel(x, y, t, dps=30)
            dps = 30
        sec = time.perf_counter() - t0
        with mp.workdps(40):
            rec = {
                "route": route, "x": x, "y": y, "t": t,
                "re": mp.nstr(mp.re(v), 30), "im": mp.nstr(mp.im(v), 30),
                "digits_requested": dps, "seconds": round(sec, 2),
            }
        with out.open("a") as fh:
            fh.write(json.dumps(rec) + "\n")
        print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()
