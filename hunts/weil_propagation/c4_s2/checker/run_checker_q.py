"""Phase 1 numbers for Q (checker/), written to checker_q_cells.json.

Run from the worktree root:
    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/checker/run_checker_q.py
About 4 minutes on one core. Every number here is pinned by test_checker_q.py.
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")

from mpmath import mp  # noqa: E402

import checker_gate as CG  # noqa: E402
import checker_props as CP  # noqa: E402
import checker_q as CQ  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
CALIB = ["1.5", "1.9"]
NS = [8, 16, 32]
DPS = [40, 60]


def s(x, d=25):
    return mp.nstr(x, d)


def galerkin_dev(c, N, dps, M):
    sys.path.insert(0, WT)
    import galerkin as G  # oracle only

    with mp.workdps(dps):
        T = G.Truncation(mp.mpf(c), N)
        return max(abs(M[i, j] - T.entry(i - N, j - N)) for i in range(2 * N + 1) for j in range(2 * N + 1))


def main():
    t0 = time.time()
    out = {"meta": {"basis": "U_n, n=-N..N, index 0 is n=-N", "cells": CELLS, "calibration": CALIB,
                    "N": NS, "dps": DPS, "eigen": "mpmath eigsy (real) / eighe (complex), float grade"},
           "cells": {}}
    for c in CALIB + CELLS:
        rec = {"atoms": [n for n, _ in CQ.zeta_atoms(float(c))]}
        mats = {}
        for dps in DPS:
            R = CQ.q_parts(c, 32, dps, with_error=(dps == 40))
            mats[dps] = R["Q"]
            if dps == 40:
                rec["quad_err_dps40"] = s(R["quad_err"], 5)
                rec["galerkin_maxdev_N32_dps40"] = s(galerkin_dev(c, 32, 40, R["Q"]), 5)
        rec["drift_40_60_N32"] = s(CP.entry_drift(mats[40], mats[60]), 5)
        for N in NS:
            for dps in DPS:
                M = CQ.central_block(mats[dps], N) if N < 32 else mats[dps]
                ev = CQ.eigvals_hermitian(M, dps)
                rec[f"full_N{N}_dps{dps}"] = [s(x) for x in ev[:3]]
            bases = CP.class_bases(c, N, 40)
            M = CQ.central_block(mats[40], N) if N < 32 else mats[40]
            for cls in ("minus", "minus_zero"):
                ev = CQ.eigvals_hermitian(CQ.compress(M, bases[cls], 40), 40)
                rec[f"{cls}_N{N}_dps40"] = [s(x) for x in ev[:3]]
        out["cells"][c] = rec
        print(c, "done", round(time.time() - t0, 1), flush=True)
    out["gate"] = CG.run_gate()
    out["meta"]["runtime_s"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, "checker_q_cells.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
