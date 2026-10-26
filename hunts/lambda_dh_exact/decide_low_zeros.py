"""Decide the 21 low-screen zeros (t < 10^4, beta > 0.85) on both ball backends.

Hunt #119, resumption of 2026-10-26, resume-order step 2.  `stage_locate` on
the completed low screen (written to `deep_zeros_locate_20261026.json`, not
into the recorded `deep_zeros.json`) gave 21 float-grade zeros, one per
flagged window.  This module runs the instrument of `decide_deep_zero.py`
(chord-tube argument principle, Cauchy bound on |f''|) around each one, on
Arb and on the hand-rolled mpmath.iv route, so every depth y0 = beta - 1/2 in
the table is an exact rational enclosure of width 2^-26.

What it decides: each rectangle holds exactly one zero of f, and its depth
lies in the stated interval.  What it does not decide: that these are all the
zeros with beta > 0.85 below height 10^4.  That completeness statement rests on
the float screen and stays *measured*.

Run:  .venv/bin/python hunts/lambda_dh_exact/decide_low_zeros.py
"""
from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import decide_deep_zero as dd  # noqa: E402

SRC = os.path.join(_HERE, "deep_zeros_locate_20261026.json")
OUT = os.path.join(_HERE, "decide_low_zeros.json")

HALF = Fraction(1, 2**27)
R = Fraction(1, 2**13)


def main() -> None:
    zeros = json.load(open(SRC))["zeros"]
    rows = []
    t0 = time.time()
    for z in zeros:
        s_pol, fabs, fp = dd.polish(z["beta"], z["gamma"])
        centre = (dd.dyadic(float(s_pol.real), 40), dd.dyadic(float(s_pol.imag), 40))
        arb = dd.count_zeros(dd.ArbRoute(prec=128), centre, HALF, R)
        ivr = dd.IvRoute(prec=128, centre=centre, radius=Fraction(1, 2**12), K=14, log_every=0)
        ivc = dd.count_zeros(ivr, centre, HALF, R)
        y_lo = centre[0] - HALF - Fraction(1, 2)
        y_hi = centre[0] + HALF - Fraction(1, 2)
        decided = (arb.get("count") == 1 and ivc.get("count") == 1)
        row = {
            "gamma_float": z["gamma"], "beta_float": z["beta"],
            "rectangle_sigma": [str(centre[0] - HALF), str(centre[0] + HALF)],
            "rectangle_t": [str(centre[1] - HALF), str(centre[1] + HALF)],
            "abs_fprime_steering": abs(fp),
            "python-flint": {k: arb[k] for k in ("status", "count", "worst_clearance_over_tube", "seconds") if k in arb},
            "mpmath.iv": {k: ivc[k] for k in ("status", "count", "worst_clearance_over_tube", "seconds") if k in ivc},
            "both_backends_count_1": decided,
            "y0_enclosure": [str(y_lo), str(y_hi)],
            "y0_enclosure_float": [float(y_lo), float(y_hi)],
            "y0_above_0.40_decided": bool(y_lo > Fraction(2, 5)),
            "y0_below_0.40_decided": bool(y_hi < Fraction(2, 5)),
        }
        rows.append(row)
        print(f"gamma {z['gamma']:.4f}  y0 in [{float(y_lo):.10f}, {float(y_hi):.10f}]  "
              f"arb {arb.get('status')}/{arb.get('count')}  iv {ivc.get('status')}/{ivc.get('count')}",
              flush=True)
    out = {
        "what": "both-backend argument-principle counts around the 21 low-screen zeros (t < 1e4, beta > 0.85)",
        "date": "2026-10-26",
        "half_width": str(HALF), "R": str(R),
        "rows": rows,
        "all_decided": all(r["both_backends_count_1"] for r in rows),
        "max_y0_upper": max(r["y0_enclosure_float"][1] for r in rows),
        "seconds": round(time.time() - t0, 1),
    }
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=2)
    print("wrote", OUT, "all_decided", out["all_decided"], "max_y0_upper", out["max_y0_upper"])


if __name__ == "__main__":
    main()
