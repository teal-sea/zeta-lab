"""What n_max costs, and therefore where the ceiling is on this container.

The whole cost of this hunt is two numbers and how they move with the radius.
Writing N for the node count, w for the working precision, L = log10(1/r):

    w  =  dps + 2*guard + n_max * L,
    N  =  ceil(w * ln10 / ln(1/r)) + n_max + 8  =  (dps + 2*guard)/L + 2*n_max + 8,

so the node count is *linear* in n_max with slope 2 once the fixed part
(dps + 2*guard)/L is paid, while the precision is linear in n_max with slope L.
Raising r cuts the precision and buys back nodes, and because the evaluator cost
grows like w^2 (measured exponent 1.97 between 155 and 292 digits) and the node
cost only like N, there is an interior optimum in r.  That is the shape of the
door this file exists to price.

The evaluation cost is calibrated on this machine and the calibration is stated
so it can be redone elsewhere: warm, single-threaded, ``completed_dh_fast``
takes 0.0924 s at 142 working digits and 0.3226 s at 279.  The observed parallel
speedup was close to 1, because the container was carrying other tenants at a
load average of 8 to 13 against 4 vCPU, so three worker processes shared about
one core's worth of throughput.  Anyone running this on a quiet box should
divide by the number of cores they actually get.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dhli import disc_bounding_box

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")

C_REF, W_REF, C_EXP = 0.0924, 142.0, 1.97
D_REF, N_REF = 0.045, 5112.0   # seconds per coefficient at W_REF, N_REF nodes
D_EXP = 1.5
DPS, GUARD2 = 30, 20


def sizes(n_max: int, radius: float) -> tuple:
    L = math.log10(1.0 / radius)
    w = math.ceil(DPS + GUARD2 + n_max * L)
    N = math.ceil(w * math.log(10) / math.log(1.0 / radius)) + n_max + 8
    return w, N, L


def predict(n_max: int, radius: float, effective_cores: float = 1.0) -> dict:
    w, N, _ = sizes(n_max, radius)
    sample = N * C_REF * (w / W_REF) ** C_EXP
    dft = n_max * D_REF * (N / N_REF) * (w / W_REF) ** D_EXP
    left, right, half = disc_bounding_box(radius, sigma_cap=2.0)
    return {"n_max": n_max, "radius": radius, "work": w, "nodes": N,
            "rectangle_that_must_be_zero_free": [round(left, 5), right,
                                                 round(half, 3)],
            "distance_from_rectangle_to_critical_line": round(left - 0.5, 5),
            "sampling_s": sample / effective_cores,
            "extraction_s": dft / effective_cores,
            "total_s": (sample + dft) / effective_cores,
            "total_h": (sample + dft) / effective_cores / 3600.0}


def best_radius(n_max: int, radii) -> dict:
    rows = [predict(n_max, r) for r in radii]
    return min(rows, key=lambda r: r["total_s"])


def main() -> None:
    radii = [0.80, 0.85, 0.90, 0.95, 0.97, 0.98, 0.99]
    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "calibration": {"seconds_per_evaluation_at_142_digits": C_REF,
                        "seconds_per_evaluation_at_279_digits": 0.3226,
                        "cost_exponent_in_digits": C_EXP,
                        "effective_cores_observed": 1.0,
                        "note": "contended container, load average 8 to 13 on 4 vCPU"},
        "measured_runs": [
            {"n_max": 2000, "radius": 0.9, "work": 142, "nodes": 5112,
             "sampling_s": 503, "extraction_s": 124},
        ],
        "grid": [predict(n, r) for n in (2000, 5000, 10000, 20000, 50000)
                 for r in radii],
        "the_onset_index_directly": [predict(328997, r) for r in (0.95, 0.99)],
        "cheapest_radius": {str(n): best_radius(n, radii)
                            for n in (2000, 5000, 10000, 20000, 50000, 100000)},
    }
    for row in out["the_onset_index_directly"]:
        print(f"n_max=328997 r={row['radius']}: work={row['work']} "
              f"nodes={row['nodes']} total={row['total_h']:.0f} h")
    for n in (2000, 5000, 10000, 20000, 50000, 100000):
        b = out["cheapest_radius"][str(n)]
        print(f"n_max={n:>7} best r={b['radius']:.2f} work={b['work']:>6} "
              f"nodes={b['nodes']:>7} total={b['total_h']:.2f} h")
    os.makedirs(ART, exist_ok=True)
    p = os.path.join(ART, "ceiling.json")
    with open(p, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", p)


if __name__ == "__main__":
    main()
