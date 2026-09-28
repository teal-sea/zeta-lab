"""How narrow a strip past the band still takes the record, calibrated.

Hunt #110 priced the whole strip (1, 1.5] and beyond. The fine sweep at one grid says the gain
is front-loaded: a fifth of it arrives by alpha = 1.05. But #110's calibrated method error is
about 1.8e-3 per fit, and a one-grid gain of 1.6e-3 is inside that. So: the same matched
ladder #110 used, for the control and for strips of width 0.05, 0.10 and 0.20, and the same
difference-route extrapolation a + b X^-p on d(X) = v_strip - v_control, whose limit is what
the strip is worth. The control's own excess over the record, whose true limit is zero, is the
method error printed beside it.

Every solve is written to artifacts/ as it completes.

    .venv/bin/python hunts/outband_certificate/ladder.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import curve_fit

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "frontier_math"))
from configuration_lp import solve  # noqa: E402

RECORD = 0.6725007036794116
RUNGS = [(40.0, 200), (80.0, 320), (120.0, 480), (160.0, 640), (240.0, 960), (320.0, 1280)]
WIDTHS = [None, 0.05, 0.10, 0.20]
# Width 0.20 is not run past X = 160: the question is how narrow a strip suffices, and its
# first four rungs already decay like the wider strips of hunt #110.
SKIP = {(240.0, 0.20), (320.0, 0.20)}
ART = HERE / "artifacts" / "ladder-narrow-strip.json"


def fit_limit(X, y):
    """a + b X^-p with free p; returns (a, p). Falls back to p = 1 if the fit does not converge."""
    X = np.asarray(X, float); y = np.asarray(y, float)
    f = lambda X, a, b, p: a + b * X ** (-p)
    try:
        (a, b, p), _ = curve_fit(f, X, y, p0=(y[-1], y[0] - y[-1], 1.0), maxfev=20000)
        return float(a), float(p)
    except Exception:
        (a, b), _ = curve_fit(lambda X, a, b: a + b / X, X, y, p0=(y[-1], y[0] - y[-1]))
        return float(a), 1.0


def main():
    ART.parent.mkdir(exist_ok=True)
    rows = json.loads(ART.read_text()) if ART.exists() else []
    have = {(r["X"], r["J"], r["width"]) for r in rows}
    for X, J in RUNGS:
        for w in WIDTHS:
            key = (X, J, w)
            if key in have or (X, w) in SKIP:
                continue
            t0 = time.time()
            r = solve(J=J, X=X, eps=0.4 / X, A_out=None if w is None else 1.0 + w)
            rows.append({"X": X, "J": J, "width": w, "feasible": r is not None,
                         "value": None if r is None else r["value"], "seconds": round(time.time() - t0, 1)})
            ART.write_text(json.dumps(rows, indent=1) + "\n")
            v = "INFEASIBLE" if r is None else f"{r['value']:.7f}"
            print(f"X={X:5.0f} J={J:4d} width={'none' if w is None else w:>5}  {v}  ({rows[-1]['seconds']}s)", flush=True)

    ctrl = {r["X"]: r["value"] for r in rows if r["width"] is None and r["feasible"]}
    Xs = sorted(ctrl)
    a_ctrl, p_ctrl = fit_limit(Xs, [ctrl[X] - RECORD for X in Xs])
    print(f"\ncontrol excess over the record, per rung: {['%.5f' % (ctrl[X] - RECORD) for X in Xs]}")
    print(f"  its extrapolated limit (true limit 0): {a_ctrl:+.5f}  <- the method error, p={p_ctrl:.2f}")
    print("\nwidth   gain per rung (X = " + ", ".join(f"{X:.0f}" for X in Xs) + ")            limit     limit/error   record needs")
    for w in WIDTHS[1:]:
        strip = {r["X"]: r["value"] for r in rows if r["width"] == w and r["feasible"]}
        d = [strip[X] - ctrl[X] for X in Xs if X in strip]
        a, p = fit_limit(Xs[:len(d)], d)
        ratio = a / abs(a_ctrl) if a_ctrl else float("inf")
        need = 0.6734164909714992949 - 0.6728470197
        print(f"{w:5.2f}   {['%+.5f' % v for v in d]}   {a:+.5f}   {ratio:6.1f}x       {'YES' if a > need else 'no '}  ({need:.5f} over our 0.6728470; p={p:.2f}; the free fit is unreliable, read pinned.py)")
    print(f"\nartifact: {ART}")


if __name__ == "__main__":
    main()
