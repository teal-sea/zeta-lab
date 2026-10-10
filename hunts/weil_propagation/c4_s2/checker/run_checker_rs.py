"""Phase 2 numbers (checker/): the routed kernel/ T_inf, the product-side
remainder Q - T_inf, Connes-Consani Thm 6.11 margins, and the shift form H.
Written to checker_rs_cells.json; pinned by test_checker_rs.py.

    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/checker/run_checker_rs.py

Estimate (measured 2026-09-23, one cell): T_inf N = 32 dps 40 8 s, N = 16
dps 60 about 20 s; about 5 minutes for the five c, single core.
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from mpmath import mp  # noqa: E402

import checker_glue as GLUE  # noqa: E402
import checker_props as CP  # noqa: E402
import checker_q as CQ  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
CALIB = ["1.5", "1.9"]


def s(x, d=25):
    return None if x is None else mp.nstr(x, d)


def main():
    t0 = time.time()
    out = {"meta": {"T_inf": "kernel/sonin.T_inf_matrix at af756a5", "Q": "checker_q",
                    "tol_rule": "10 x |dps40 - dps60| per eigenvalue where dps 60 exists (N <= 16), "
                                "else 1e-30 x max|entry|"},
           "cells": {}}
    for c in CALIB + CELLS:
        rec = {}
        Qd = {40: CQ.Q_matrix(c, 32, 40), 60: CQ.Q_matrix(c, 16, 60)}
        T32 = GLUE.T_inf(c, 32, 40)
        for N in (8, 16, 32):
            Q40 = CQ.central_block(Qd[40], N) if N < 32 else Qd[40]
            T40 = CQ.central_block(T32, N) if N < 32 else T32
            r = {"T_inf_herm_defect": s(CP.hermitian_defect(T40), 5),
                 "T_inf_low": [s(x) for x in CP.lowest(T40, 3, 40)]}
            R40 = Q40 - T40
            if N <= 16:
                Q60 = CQ.central_block(Qd[60], N) if N < 16 else Qd[60]
                T60 = GLUE.T_inf(c, N, 60)
                R60 = Q60 - T60
                r["T_inf_submatrix_defect_vs_N32"] = s(CP.submatrix_defect(GLUE.T_inf(c, N, 40), T32), 5)
            bases = CP.class_bases(c, N, 40)
            for cls in ("full", "minus", "minus_zero"):
                e40 = CQ.eigvals_hermitian(CQ.compress(R40, bases[cls], 40), 40)
                if N <= 16:
                    b60 = CP.class_bases(c, N, 60)[cls]
                    e60 = CQ.eigvals_hermitian(CQ.compress(R60, b60, 60), 60)
                    tol = max(10 * max(abs(x - y) for x, y in zip(e40, e60)), mp.mpf("1e-30"))
                else:
                    tol = mp.mpf("1e-30") * CP.max_abs(R40)
                r[f"R_{cls}_low"] = [s(x) for x in e40[:3]]
                r[f"R_{cls}_inertia"] = list(CQ.inertia(e40, tol))
                r[f"R_{cls}_tol"] = s(tol, 3)
            if c in CALIB and N <= 16:
                m40 = CP.cc611_margins(Q40, T40, c, N, 40)
                m60 = CP.cc611_margins(Q60, T60, c, N, 60)
                r["cc611"] = {k: s(v) for k, v in m40.items()}
                r["cc611_drift"] = {k: s(abs(m40[k] - m60[k]), 3) for k in m40 if m40[k] is not None}
            if c in CELLS:
                H = CQ.shift_form(c, N, 40)
                eh = CQ.eigvals_hermitian(H, 40)
                r["H_min"], r["H_max"] = s(eh[0]), s(eh[-1])
                r["H_count_above_quarter"] = sum(1 for x in eh if x > mp.mpf(1) / 4)
                r["H_count_below_minus_quarter"] = sum(1 for x in eh if x < -mp.mpf(1) / 4)
            rec[str(N)] = r
        out["cells"][c] = rec
        print(c, "done", round(time.time() - t0, 1), flush=True)
        with open(os.path.join(HERE, "checker_rs_cells.json"), "w") as fh:  # checkpoint per cell
            json.dump(out, fh, indent=1)
    out["meta"]["runtime_s"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, "checker_rs_cells.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
