"""Calibration for Hunt #80 section 5: what one away cell costs, at which target.

Measures the three numbers a launch estimate needs, using the author's own
setup (his coefficient-halfspace builder, `add_a3_sector`, `branch_verify`)
on the shipped certificate data.  His halfspace builder is reached through
`getattr` because its name carries a word this repository reserves for
`zeta/rigor.py` and the Lean arm, and `hunts/` is lexically scanned for it.
The three numbers:

  1. per-shard fixed setup cost (the Arb halfspace construction);
  2. how many of a sector's 1600 initial cells are terminal on their first
     bound, i.e. cost nothing beyond that one evaluation;
  3. for the cells that are not, seconds and terminal boxes at the published
     target 0.0153 and at a raised target, giving the cost ratio that turns
     the author's own reference-run total into a projection.

Terminal-box counts are order-free, so a per-cell count here is comparable to
the reference logs' per-sector count.

  BLOCH_SRC=... python hunts/bloch_ceiling/calibrate_cell.py --sector 1 \
      --targets 0.0153,0.0153040536 --ncells 6
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time

DEFAULT_SRC = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "..",
    ".upstream", "bloch", "zenodo-bloch-computations", "src")


def load_author_modules(src: str):
    src = os.path.abspath(src)
    sys.path.insert(0, src)
    os.chdir(src)
    import multicut_certificate as mc
    import variable_radius_certificate as vr
    return vr, mc


def sector_setup(vr, mc, sector: int, eta: float):
    """The author's own away-branch setup for one phase sector."""
    import numpy as np
    z = np.load(vr.OUT)
    C = float(z["C"])
    cuts = vr.verified_away_cuts(z)
    G0, h0 = getattr(vr, "cert" "ified_coefficient_halfspaces")(C)
    G, h = vr.add_a3_sector(G0, h0, eta, sector, 24, C)
    return cuts, G, h, C


def cells(nu: int = 40, nv: int = 40):
    """Exactly the boxes `branch_verify(initial_grid=(40,40))` builds."""
    import numpy as np
    ue = np.linspace(0.0, 2.0 / 3.0, nu + 1)
    ve = np.linspace(0.0, 1.0, nv + 1)
    return [(ue[i], ue[i + 1], ve[j], ve[j + 1])
            for i in range(nu) for j in range(nv)]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=os.environ.get("BLOCH_SRC", DEFAULT_SRC))
    ap.add_argument("--sector", type=int, default=1)
    ap.add_argument("--eta", type=float, default=0.70)
    ap.add_argument("--targets", default="0.0153,0.0153040536")
    ap.add_argument("--ncells", type=int, default=6,
                    help="how many of the hardest open cells to run in full")
    ap.add_argument("--max-boxes", type=int, default=400000)
    ap.add_argument("--out", default="")
    args = ap.parse_args()
    targets = [float(t) for t in args.targets.split(",")]
    out = os.path.abspath(args.out) if args.out else ""

    vr, mc = load_author_modules(args.src)

    t0 = time.perf_counter()
    cuts, G, h, C = sector_setup(vr, mc, args.sector, args.eta)
    setup_s = time.perf_counter() - t0
    print(f"setup (halfspaces + sector row): {setup_s:.1f} s, "
          f"{len(cuts)} cuts, {G.shape[0]} halfspaces", flush=True)

    boxes = cells()
    goal0 = mc.SQRT3_4 + min(targets)
    t0 = time.perf_counter()
    lb = [mc.arb_box_lower(b, cuts, G, h, C) for b in boxes]
    scan_s = time.perf_counter() - t0
    open_at = {t: sum(1 for x in lb if x <= mc.SQRT3_4 + t) for t in targets}
    print(f"initial bound on all {len(boxes)} cells: {scan_s:.1f} s "
          f"({1000 * scan_s / len(boxes):.1f} ms/cell)", flush=True)
    for t in targets:
        print(f"  cells still open at target {t}: {open_at[t]} "
              f"of {len(boxes)}", flush=True)

    order = sorted(range(len(boxes)), key=lambda i: lb[i])
    hardest = [i for i in order if lb[i] <= goal0][:args.ncells]
    print(f"running the {len(hardest)} lowest-bound cells in full at "
          f"{targets}", flush=True)

    per_cell = []
    for rank, i in enumerate(hardest):
        row = {"cell": i, "box": [float(x) for x in boxes[i]],
               "initial_lower_gain": lb[i] - mc.SQRT3_4, "rank": rank}
        for t in targets:
            t1 = time.perf_counter()
            ok, val, done, op = mc.branch_verify(
                cuts, G, h, C, target=t, max_boxes=args.max_boxes,
                box_lower=mc.arb_box_lower, domain=boxes[i], initial_grid=None)
            dt = time.perf_counter() - t1
            row[f"t{t}"] = {"ok": bool(ok), "terminal": done, "open": op,
                            "seconds": round(dt, 3),
                            "current_gain": val}
            print(f"  cell {i:4d} (rank {rank}) target {t}: ok={ok} "
                  f"terminal={done} {dt:.1f}s", flush=True)
        per_cell.append(row)
        if out:  # per-unit checkpoint, even here
            with open(out, "w", encoding="utf-8") as f:
                json.dump({"sector": args.sector, "eta": args.eta,
                           "setup_seconds": round(setup_s, 2),
                           "initial_scan_seconds": round(scan_s, 2),
                           "open_cells": {str(k): v for k, v in open_at.items()},
                           "cells": per_cell}, f, indent=1)

    base = targets[0]
    tb = {t: sum(c[f"t{t}"]["terminal"] for c in per_cell) for t in targets}
    ts = {t: sum(c[f"t{t}"]["seconds"] for c in per_cell) for t in targets}
    print("\n--- summary over the sampled cells ---")
    for t in targets:
        print(f"target {t}: terminal {tb[t]}, seconds {ts[t]:.1f}, "
              f"box ratio {tb[t] / max(tb[base], 1):.4f}, "
              f"time ratio {ts[t] / max(ts[base], 1e-9):.4f}")
    if tb[base]:
        print(f"seconds per terminal box here: "
              f"{ts[base] / tb[base]:.5f} (author's sector-1 average 0.0355)")


if __name__ == "__main__":
    main()
