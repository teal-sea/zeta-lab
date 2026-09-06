"""The pinned-exponent table for the narrow-strip ladder, the instrument hunt #110 settled on.

A three-parameter fit through a handful of rungs does not pin a limit (refit.py in #110
shows two such fits landing on two different famous constants). So the exponent is pinned
and the answer is read as a range across exponents. For each strip width: the
difference-route limit of d(X) = v_strip - v_control at each pinned p, beside the control's
own fitted excess over the record at the same p, whose true limit is zero and which is
therefore the method error of that fit.

    .venv/bin/python hunts/outband_certificate/pinned.py
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ART = HERE / "artifacts" / "ladder-narrow-strip.json"
RECORD = 0.6725007036794116
OURS = 0.6728470197
LEADER = 0.6734164909714992949
NEED = LEADER - OURS


def pinned(x, y, p):
    design = np.vstack([np.ones_like(x), x ** (-p)]).T
    return float(np.linalg.lstsq(design, y, rcond=None)[0][0])


def main():
    rows = [r for r in json.loads(ART.read_text()) if r["feasible"]]
    ctrl = {r["X"]: r["value"] for r in rows if r["width"] is None}
    widths = sorted({r["width"] for r in rows if r["width"] is not None})
    print(f"control rungs X = {sorted(ctrl)}; record needs +{NEED:.5f} over this lab's {OURS}")
    print("\nraw gain per rung, d(X) = v_strip - v_control:")
    for w in widths:
        strip = {r["X"]: r["value"] for r in rows if r["width"] == w}
        xs = sorted(x for x in strip if x in ctrl)
        print(f"  width {w:.2f}: " + "  ".join(f"X={x:.0f}:{strip[x] - ctrl[x]:+.5f}" for x in xs))
    print("\npinned exponent p | control excess limit (true 0: method error) | difference limit per width, and limit/error")
    for p in (0.5, 0.75, 1.0, 1.5, 2.0):
        xs_c = np.array(sorted(ctrl), float)
        err = pinned(xs_c, np.array([ctrl[x] - RECORD for x in xs_c]), p)
        cells = []
        for w in widths:
            strip = {r["X"]: r["value"] for r in rows if r["width"] == w}
            xs = np.array(sorted(x for x in strip if x in ctrl), float)
            d = np.array([strip[x] - ctrl[x] for x in xs])
            lim = pinned(xs, d, p)
            cells.append(f"w={w:.2f}: {lim:+.5f} ({lim / abs(err):4.1f}x, {'takes the record' if lim > NEED else 'short'})")
        print(f"  p={p:<4}  err={err:+.5f}   " + "   ".join(cells))


if __name__ == "__main__":
    main()
