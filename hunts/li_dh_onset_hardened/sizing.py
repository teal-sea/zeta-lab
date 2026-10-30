"""Step 3: the production node count and core-hours, from bounds not guesses.

Reads ``artifacts/admissibility.json`` (R_a) and ``artifacts/evaluator.json``
(seconds per node on the production circle), bounds M(rho) by the arc cover of
``trapezoid.bound_M`` on a few aliasing circles rho < R_a, and prices

    N >= ln( n_max M(rho) rho^{-n_max} / tol ) / ln(rho / r),   N > n_max,

rounded up to a power of two for ``acb.dft``, sampling only the upper half
(N/2 + 1 node evaluations), at r = sqrt(1 - 1/c) for several c.  Also rechecks
the judge's c = 1e4 statement: there rho must sit in (r, R_a), a window of
width 8e-6.

Usage: .venv/bin/python hunts/li_dh_onset_hardened/sizing.py
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction as Q

from flint import acb, arb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from balls import HERE, prec_guard, q_arb  # noqa: E402
from trapezoid import bound_M, plan  # noqa: E402

ART = os.path.join(HERE, "artifacts")
RHOS = (1 - Q(43, 10 ** 6), 1 - Q(44, 10 ** 6), 1 - Q(46, 10 ** 6), 1 - Q(50, 10 ** 6))
CS = (2000, 2500, 3000, 4000, 5000, 10000)
N_MAX = (400_000, 500_000)
TOL = 1e-10


def dft_seconds(n: int, prec: int) -> float:
    with prec_guard(prec):
        v = [acb(arb(k % 97) / 7, arb(k % 13) / 3) for k in range(n)]
        t0 = time.time()
        acb.dft(v)
        return time.time() - t0


def main() -> None:
    adm = json.load(open(os.path.join(ART, "admissibility.json")))
    ev = json.load(open(os.path.join(ART, "evaluator.json")))
    Ra = adm["radius"]["R_a_lower"]
    sec = {t["prec"]: t["seconds_per_node"] for t in ev["timing"]}
    out = {"generated": time.strftime("%Y-%m-%dT%H:%M:%S"), "R_a_lower": Ra, "tol": TOL,
           "seconds_per_node": sec, "M": {}, "plans": []}
    for rho in RHOS:
        assert float(rho) < Ra - 1e-9, "aliasing circle must lie inside R_a"
        t0 = time.time()
        with prec_guard(128):
            rb = q_arb(rho)
        bm = bound_M(rb, 128)
        bm["seconds"] = round(time.time() - t0, 1)
        out["M"][str(float(rho))] = bm
        print("rho", float(rho), bm["M_upper"], bm["closure_contains_0"], bm["seconds"], "s")
    for c in CS:
        r = math.sqrt(1 - 1 / c)
        for n_max in N_MAX:
            best = None
            for rho in RHOS:
                if float(rho) <= r:
                    continue
                M = out["M"][str(float(rho))]["M_upper"]
                p = plan(c, n_max, float(rho), M, TOL, sec[250])
                if best is None or p["N_power_of_two"] < best["N_power_of_two"]:
                    best = p
            if best is not None:
                out["plans"].append(best)
                print(c, n_max, best["N_aliasing"], best["N_power_of_two"], best["bits"],
                      round(best["core_hours_sampling"], 3))
    # the judge's c = 1e4 point: rho must lie in (r, R_a); report the window
    r4 = math.sqrt(1 - 1e-4)
    out["c_1e4"] = {"r": r4, "R_a": Ra, "window_width": Ra - r4,
                    "midpoint_circle": (1 + r4) / 2,
                    "midpoint_circle_inside_R_a": (1 + r4) / 2 < Ra}
    for k in (16, 17, 18):
        out.setdefault("dft_seconds_192_bits", {})[f"2^{k}"] = round(dft_seconds(2 ** k, 192), 2)
        print("dft 2^%d:" % k, out["dft_seconds_192_bits"][f"2^{k}"])
    with open(os.path.join(ART, "sizing.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
