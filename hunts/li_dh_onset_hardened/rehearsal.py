"""A dress rehearsal of the production pipeline on the production circle.

r = sqrt(1 - 1/5000), rho = 1 - 4.6e-5, N = 2^17 (one sixteenth of production).
At this N the aliasing bound (A) is far too large to decide anything, so the
lambda balls are uninformative by design; what the rehearsal measures is the
part production cannot afford to discover late: that the ball branch tracker
crosses the near-line stretch of the real circle (|Im s| up to about 140, the
circle within 1e-3 of the low zeros) and closes, what the cover costs per node,
and that the midpoints agree with hunt #128's float table, which is a measured
check of the plumbing at this geometry and nothing more.

Usage: .venv/bin/python hunts/li_dh_onset_hardened/rehearsal.py
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction as Q

from flint import arb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from balls import HERE, ROOT, prec_guard, q_arb  # noqa: E402
from trapezoid import DHModel, li_balls  # noqa: E402

ART = os.path.join(HERE, "artifacts")
C, N, N_MAX, PREC = 5000, 2 ** 17, 5000, 192
RHO = 1 - Q(46, 10 ** 6)


def main() -> None:
    sz = json.load(open(os.path.join(ART, "sizing.json")))
    M = sz["M"][str(float(RHO))]["M_upper"]
    old = json.load(open(os.path.join(ROOT, "hunts", "li_dh_onset", "artifacts",
                                      "lambda_dh_n5000_r0.95.json")))["lambda"]
    t0 = time.time()
    with prec_guard(PREC):
        r = (1 - 1 / q_arb(C)).sqrt()
        rho = q_arb(RHO)
    out = li_balls(DHModel(), r, N, N_MAX, PREC, rho, M)
    with prec_guard(PREC):
        lam = out["lambda"]
        diffs = [abs(lam[i].mid() - arb(str(old[i]))) for i in range(N_MAX)]
        worst = max(float(d.mid()) for d in diffs)
        worst_n = 1 + max(range(N_MAX), key=lambda i: float(diffs[i].mid()))
    res = {"generated": time.strftime("%Y-%m-%dT%H:%M:%S"), "c": C, "N": N,
           "n_max": N_MAX, "prec": PREC, "rho": str(RHO), "M_upper": M,
           "stats": out["stats"], "seconds_total": round(time.time() - t0, 1),
           "midpoint_vs_128_table_max_abs": worst, "at_n": worst_n,
           "radius_at_n_1": float(lam[0].rad()), "radius_at_n_max": float(lam[-1].rad())}
    print(json.dumps(res, indent=1))
    with open(os.path.join(ART, "rehearsal.json"), "w") as fh:
        json.dump(res, fh, indent=1)


if __name__ == "__main__":
    main()
