"""The radical capture bound at m = 4 on zeta's three largest windows.

Usage (from the repo root):

    .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/capture_m4.py [c:N ...]

Default cells (43, 128), (50, 128), (60, 128).  Per cell, the same quantities
as measure.py's capture_m2 with R_4 = span(r^(0..4)) in place of R_2: kappa =
bottom of the form on R_4, mu = bottom on R_4-perp, eta = ||(1 - P_R) A P_R||,
the perturbation bound eta / (mu - lambda_1) on dist(v_1, R_4) when
mu > lambda_1, and the actual distance.  Results go to data/capture_m4.json,
checkpointed after every cell; a rerun skips finished cells.

Grade: measured (float-grade eigenvector, midpoint arithmetic in capture()).
"""

from __future__ import annotations

import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ccm_common as C  # noqa: E402
import measure as M  # noqa: E402
from flint import ctx  # noqa: E402
from mpmath import mp  # noqa: E402

import wp_common as WP  # noqa: E402

CELLS = [(43, 128), (50, 128), (60, 128)]
OUT = os.path.join(M.DATA, "capture_m4.json")


def capture_cell(c, N, cache):
    t0 = time.time()
    prec = C.prec_for("zeta", c, N)
    A = C.matrix("zeta", c, N, prec)
    pairs = C.lowest_pairs(A, k=1)
    ctx.prec = prec
    lam1 = pairs[0][0].mid().str(20, radius=False)
    rec = {"c": WP.cstr(c), "N": N, "prec": prec, "lambda1_mid": lam1}
    with mp.workdps(M.MP_DPS["zeta"]):
        v = C.to_mp(pairs[0][1])
        rs = M.radical_vectors("zeta", c, N, cache)
        res4, qs = C.project_residual(v, rs[:5])
        rec["dist2_R4"] = mp.nstr(res4, 8)
        cap = M.capture(A, prec, qs, lam1)
    with mp.workdps(40):
        cap["actual_dist"] = mp.nstr(mp.sqrt(max(res4, 0)), 8)
    rec["capture_m4"] = cap
    rec["elapsed_s"] = round(time.time() - t0, 1)
    return rec


def main(argv):
    cells = CELLS
    if len(argv) > 1:
        cells = [(a.split(":")[0], int(a.split(":")[1])) for a in argv[1:]]
    store = WP.load(OUT, {"meta": {"kind": "zeta", "script": "capture_m4.py", "m": 4}, "cells": {}})
    cache = M.XiCache("zeta")
    for c, N in cells:
        key = f"{WP.cstr(c)}:{N}"
        if key in store["cells"]:
            continue
        rec = capture_cell(c, N, cache)
        store["cells"][key] = rec
        WP.save(OUT, store)
        cache.flush()
        print(f"zeta c={key} {rec['capture_m4']} dist2_R4={rec['dist2_R4']} t={rec['elapsed_s']}s", flush=True)


if __name__ == "__main__":
    main(sys.argv)
