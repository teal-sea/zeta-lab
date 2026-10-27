"""The two-sided local gap model, as pre-registered in RESULTS.md section 8.10.

Hunt #119, unit 3 (2026-10-26).  For each of the 29 accounted, landed windows
(`census_1e4.json`, `census_deep4_1e5.json`), scan the line zeros on
[gamma - 4h, gamma + 4h], take d_L and d_R (nearest line zero below and
above gamma), and compare the ODE landing with

    t*_2 = int_0^{y0} y dy / (1 + 2 y^2 S2(y)),
    S2(y) = sum_{k<K} [1/((d_L + k h)^2 + y^2) + 1/((d_R + k h)^2 + y^2)],

which reduces to `theory.t_star_gap` at d_L = d_R = DBAR h.  Gate, metric and
pass/fail rule are the pre-registered ones and are applied here verbatim.

Grade: *measured* (float line scan, float integral, ODE landings measured).

Run:  .venv/bin/python hunts/lambda_dh_exact/twosided.py
"""
from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import census_1e4 as cz  # noqa: E402

OUT = os.path.join(HERE, "twosided.json")
K = 6000
GATE_TOL = 1e-4
RMS_FROZEN = 0.160
RMS_PASS = 0.080
BAND = (0.85, 1.25)


def h_mean(gamma: float) -> float:
    return 2 * math.pi / math.log(5 * gamma / (2 * math.pi))


def t_star_two(y0: float, d_l: float, d_r: float, h: float, k: int = K) -> float:
    a_l = d_l + h * np.arange(k)
    a_r = d_r + h * np.arange(k)
    S = lambda y: float(np.sum(1.0 / (a_l * a_l + y * y)) + np.sum(1.0 / (a_r * a_r + y * y)))
    return quad(lambda y: y / (1.0 + 2.0 * y * y * S(y)), 0.0, y0, limit=300)[0]


def windows():
    out = []
    for name in ("census_1e4.json", "census_deep4_1e5.json"):
        for r in json.load(open(os.path.join(HERE, name)))["rows"]:
            if r["landing_ode"] is not None and r["accounting_ok"]:
                out.append((name, r))
    return out


def rule(rms: float, ratios: list[float]) -> str:
    if rms <= RMS_PASS and all(BAND[0] <= q <= BAND[1] for q in ratios):
        return "PASS"
    if rms < RMS_FROZEN:
        return "IMPROVES"
    return "FAIL"


def main() -> None:
    t0 = time.time()
    rows = []
    for src, r in windows():
        g, y0, tode = r["gamma"], r["y0"], r["landing_ode"]
        h = h_mean(g)
        reals = cz.line_zeros(g - 4 * h, g + 4 * h)
        below = [x for x in reals if x < g]
        above = [x for x in reals if x > g]
        d_l, d_r = g - max(below), min(above) - g
        dists = sorted(abs(x - g) for x in reals)
        # the second-nearest overall is on the same side as the nearest iff it is
        # neither d_L nor d_R
        second_same_side = not (abs(dists[1] - d_l) < 1e-12 or abs(dists[1] - d_r) < 1e-12)
        gate = abs(min(d_l, d_r) / h - r["gap_ratio_d_over_h"])
        t2 = t_star_two(y0, d_l, d_r, h)
        rows.append({"source": src, "gamma": g, "y0": y0, "h": h, "landing_ode": tode,
                     "d_L_over_h": d_l / h, "d_R_over_h": d_r / h,
                     "gate_defect": gate, "second_nearest_same_side": second_same_side,
                     "n_line_scanned": len(reals), "model_two_sided": t2,
                     "ratio": tode / t2})
    gate_ok = all(x["gate_defect"] <= GATE_TOL for x in rows)
    ratios = [x["ratio"] for x in rows]
    rms = math.sqrt(sum((q - 1) ** 2 for q in ratios) / len(ratios))
    out = {
        "what": "two-sided local gap model vs 29 ODE landings, RESULTS.md section 8.10 PREREG",
        "date": "2026-10-26", "n": len(rows), "gate_tol": GATE_TOL, "gate_ok": gate_ok,
        "max_gate_defect": max(x["gate_defect"] for x in rows),
        "rms_dev_from_1": rms, "mean_ratio": sum(ratios) / len(ratios),
        "min_ratio": min(ratios), "max_ratio": max(ratios),
        "n_in_band": sum(BAND[0] <= q <= BAND[1] for q in ratios),
        "n_second_nearest_same_side": sum(x["second_nearest_same_side"] for x in rows),
        "verdict": rule(rms, ratios) if gate_ok else "VOID",
        "reference": {"frozen_rms": RMS_FROZEN, "plugin_rms": 0.393, "pass_rms": RMS_PASS,
                      "band": list(BAND)},
        "rows": rows, "seconds": round(time.time() - t0, 1),
    }
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps({k: v for k, v in out.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
