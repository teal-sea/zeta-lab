"""Level 7, phase 2b: the full-ladder hardened penta scan.

Level 6a hardened the pentadiagonal caps at theta_full = 0.02 on the seven
probe depths only, and named the full ladder as compute.  This module runs
the same machinery, ``EnclosedPenta`` (ball kernels, directed endpoints,
DP total inflated 1 + 1e-9), over the complete level-4/5 geometric depth
ladder (60+ cells), with the pair-charge fraction eta taken one-sided per
cell: the maximum of the measured-optimal eta over every probe depth that
touches the cell's bracket (eta is measured on its adversary family, as at
level 6a; the configuration-free pair layer is the level-7 v-cell
certificate's job, not this scan's).

Per ladder cell (y1, y2): slack at the shallow lip y1 (lower endpoint),
hardened penta cap over the cell's sups at theta = 0.02 (min over the
delta ladder, each delta one-sided), and the verdict
``cap/slack + eta <= 1``.  The output is the first full-strip statement of
the level-6a assembly: every depth cell, hardened caps, stated margins.

Run ``.venv/bin/python hunts/frontier_math/full_ladder_scan.py``
(~30-60 min; writes a row per cell as it goes).
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pair_energy import PairEnergy  # noqa: E402
from penta_bound import _make_enclosed_penta, eta_optimal  # noqa: E402

ETA_GRID = (0.01, 0.02, 0.03, 0.05, 0.08, 0.15, 0.25, 0.35, 0.45, 0.49)


def eta_for_cell(etas: dict, y1: float, y2: float) -> float:
    """One-sided eta for a depth cell: max over probe depths bracketing it.

    The bracket is [largest grid depth <= y1, smallest grid depth >= y2]
    (falling back to the extremes), so the cell's eta is never read off a
    single interior probe.
    """
    grid = sorted(etas)
    lo = max([g for g in grid if g <= y1], default=grid[0])
    hi = min([g for g in grid if g >= y2], default=grid[-1])
    return max(eta for g, eta in etas.items() if lo <= g <= hi)


def run(theta: float = 0.02, nu_p: float = 1.0):
    EnclosedPenta = _make_enclosed_penta()
    ep = EnclosedPenta()
    pe = PairEnergy()
    print(f"= full-ladder hardened penta scan: theta = {theta}, nu_p = {nu_p} =",
          flush=True)
    etas = eta_optimal(pe, nu_p, y_grid=ETA_GRID)
    print("  eta (measured-optimal split) per probe depth:", flush=True)
    for y, eta in etas.items():
        print(f"    y={y}: eta = {eta:.4f}", flush=True)
    # the probe cells of level 6a were 1% wide; an 18%-wide cell dilates
    # cap/slack (worst y2 sups against shallow-lip slack) by ~(ratio)^2,
    # which is fatal at combined margins of a few percent, the ladder must
    # be fine enough that the cell dilation stays inside the margins.
    cells = ep.depth_ladder(ratio=1.05, deep_ratio=1.012, deep_from=0.09)
    print(f"  {len(cells)} depth cells", flush=True)
    worst = (float("inf"), None)
    t0 = time.time()
    all_closed = True
    for y1, y2 in cells:
        sups = ep.fine_sups(y1, y2)
        cap = min(
            ep.lambda_bar_from_sups(theta, sups, y2, d) for d in ep.delta_choices
        )
        slack = ep.slack(y1)
        eta = eta_for_cell(etas, y1, y2)
        combined = cap / slack + eta
        margin = 1.0 - combined
        if margin < worst[0]:
            worst = (margin, (y1, y2))
        closed = combined <= 1.0
        all_closed = all_closed and closed
        print(f"  cell [{y1:.4f}, {y2:.4f}]: cap/slack {cap / slack:.4f}  "
              f"eta {eta:.4f}  combined {combined:.4f}  "
              f"margin {margin:+.4f}  {'ok' if closed else 'FAILS'}  "
              f"[{time.time() - t0:.0f}s]", flush=True)
    print(f"= verdict: {'CLOSED on every cell' if all_closed else 'OPEN'} =",
          flush=True)
    print(f"  worst margin {worst[0]:+.5f} at cell {worst[1]}", flush=True)


if __name__ == "__main__":
    run()
