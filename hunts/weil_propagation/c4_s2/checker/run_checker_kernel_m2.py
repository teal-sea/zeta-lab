"""Independent verification of kernel/ milestone 2 claims (routed by the
coordinator 2026-09-23), with the checker's own Q. Writes
checker_kernel_m2.json; pinned by test_checker_rs.py. About 3 minutes.

- kernel/ arch_matrix (A) against the checker's own arch block;
- the best Thm 6.11 constant kappa_star at c = 2.0 (kernel/: 12.43, 13.88,
  14.56 at N = 8, 16, 32);
- R_inf = P - E at c = 2.0 (kernel/: 2/1/0 negatives full/C1/C2);
- the archimedean-only remainder P - E on the mission cells (kernel/: C1
  negatives 1, 1, 2 and C2 negatives 0, 0, 1 at c = 2.2, 2.5, 2.9).
Inertia tolerance: 1e-30 x max|entry| (the dps 40/60 drift measured in
checker_rs_cells.json is below 1e-40 for these forms).
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


def s(x, d=25):
    return None if x is None else mp.nstr(x, d)


def main():
    t0 = time.time()
    sonin = GLUE._sonin()
    out = {"meta": {"kernel": "af756a5", "dps": 40}, "arch_dev": {}, "c2": {}, "PmE": {}}
    for c in ("1.5", "2.2", "2.9"):
        mine = CQ.q_parts(c, 32, 40)["arch"]
        theirs = sonin.arch_matrix(c, 32, 40)
        out["arch_dev"][c] = s(CP.entry_drift(mine, theirs), 5)
    for c in ("2.0", "2.2", "2.5", "2.9"):
        R = CQ.q_parts(c, 32, 40)
        QmP = R["pole"] + R["arch"]  # Q without the atom: Q_inf = P + A
        T32 = GLUE.T_inf(c, 32, 40)
        rec = {}
        for N in (8, 16, 32):
            Qi = CQ.central_block(QmP, N) if N < 32 else QmP
            T = CQ.central_block(T32, N) if N < 32 else T32
            X = Qi - T  # = P - E
            tol = mp.mpf("1e-30") * CP.max_abs(X)
            bases = CP.class_bases(c, N, 40)
            r = {}
            for cls in ("full", "minus", "minus_zero"):
                e = CQ.eigvals_hermitian(CQ.compress(X, bases[cls], 40), 40)
                r[f"{cls}_inertia"] = list(CQ.inertia(e, tol))
                r[f"{cls}_low"] = [s(x) for x in e[:2]]
            if c == "2.0":
                r["kappa_star"] = s(CP.cc611_margins(Qi, T, c, N, 40)["kappa_star"])
            rec[str(N)] = r
        out["c2" if c == "2.0" else "PmE"][c] = rec
        print(c, "done", round(time.time() - t0, 1), flush=True)
    out["meta"]["runtime_s"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, "checker_kernel_m2.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
