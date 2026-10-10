"""Can an off-line quadruple this repository has not found beat pair 1?

The onset estimate is driven by one number, the growth rate

    R(rho) = |1 - 1/(1 - rho)| = sqrt( 1 + (2 beta - 1) / ((1 - beta)^2 + gamma^2) ),

and only by its largest value over the whole zero set.  Measured, the largest
among the fifteen off-line zeros this repository holds belongs to the lowest of
them, the pair at 0.80852 + 85.69935i, with R - 1 = 4.2006e-5.  An unfound
quadruple with a larger R would move the answer, so the question has to be
closed rather than hoped about, and it closes in three pieces.

*   **Below height 90.**  ``radius_scan.py``'s census compares argument-principle
    box counts against grid-refined sign-change counts on the critical line in
    every height window of 10 up to 90.  They agree everywhere except [80, 90],
    where the box exceeds the line by exactly 2: the two upper-half zeros of the
    known quadruple.  So there is no other off-line zero below height 90.

*   **Above height 189.**  f has no zero with Re s >= 2 (the coefficient bound,
    re-measured in ``radius_scan.py``), so 2 beta - 1 <= 3 and
    R - 1 <= 3/(2 gamma^2), which is below pair 1's 4.2006e-5 once
    gamma > sqrt(3 / (R_1^2 - 1)) = 188.97.

*   **Between them.**  What is left is a wedge: at height gamma, a rival needs
    2 beta - 1 > (R_1^2 - 1) ((1 - beta)^2 + gamma^2), which at gamma = 90 means
    beta > 0.8403 and gets harder as gamma rises.  One box count over
    [0.83, 2] x [90, 190] covers the whole wedge with margin, and it is far
    enough from the critical line that the contour is nowhere near a zero.

The output is the threshold curve and the box counts.  Nothing here is evidence
about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time

from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zeta.epstein import count_zeros_box

from zero_side import offline_quadruples, quadruple_growth

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")


def threshold_beta(gamma: float, r1_sq_minus_1: float) -> float:
    """Smallest beta at height gamma whose quadruple would out-grow pair 1.

    Solves 2b - 1 = k ((1-b)^2 + g^2) for the root in (1/2, 2], k the pair-1
    excess; above 2 the question is empty because f has no zero there.
    """
    k = r1_sq_minus_1
    # k b^2 - (2 + 2k) b + (1 + k + k g^2) = 0
    a, bq, cq = k, -(2 + 2 * k), 1 + k + k * gamma * gamma
    disc = bq * bq - 4 * a * cq
    if disc < 0:
        return float("inf")
    return (-bq - math.sqrt(disc)) / (2 * a)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sigma-lo", type=float, default=0.83)
    ap.add_argument("--t-lo", type=float, default=90.0)
    ap.add_argument("--t-hi", type=float, default=190.0)
    ap.add_argument("--window", type=float, default=20.0)
    args = ap.parse_args()

    quads = offline_quadruples()
    growth = [(q["label"], quadruple_growth(q["beta"], q["gamma"])) for q in quads]
    growth.sort(key=lambda kv: -float(kv[1]["R_minus_1"]))
    label, top = growth[0]
    R1 = float(top["R"])
    k = R1 * R1 - 1.0

    curve = [{"gamma": g, "threshold_beta": threshold_beta(g, k)}
             for g in (90, 100, 120, 150, 170, 185, 188, 189, 190)]
    gamma_safe = math.sqrt(3.0 / k)

    boxes = []
    t = args.t_lo
    while t < args.t_hi:
        hi = min(t + args.window, args.t_hi)
        t0 = time.time()
        n = count_zeros_box(mp.mpc(args.sigma_lo, t), mp.mpc(2.0, hi), dps=20)
        row = {"rect": [args.sigma_lo, 2.0, t, hi], "zeros": int(n),
               "seconds": round(time.time() - t0, 2)}
        print(row, flush=True)
        boxes.append(row)
        t = hi

    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "dominant_label": label,
        "dominant_R_minus_1": mp.nstr(top["R_minus_1"], 12),
        "gamma_above_which_the_strip_bound_suffices": gamma_safe,
        "threshold_curve": curve,
        "wedge_boxes": boxes,
        "wedge_clear": all(b["zeros"] == 0 for b in boxes),
    }
    os.makedirs(ART, exist_ok=True)
    p = os.path.join(ART, "dominance.json")
    with open(p, "w") as fh:
        json.dump(out, fh, indent=1)
    print("gamma_safe", gamma_safe, "wedge clear", out["wedge_clear"])
    print("wrote", p)


if __name__ == "__main__":
    main()
