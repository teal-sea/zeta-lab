"""The 200 -> 240 mode step at N = 32 also moves Kmax (13 -> 14, kmax_for).
This builds (200, 2400, 32) at Kmax 14 and splits the step:
  Kmax response  ||T_S(200, K14) - T_S(200, K13)||_2
  mode response  ||T_S(240, K14) - T_S(200, K14)||_2
T_S(200, K13) and T_S(240, K14) are read from checker_ts_snapshot.json. Same
route and fail-closed guard as run_checker_ts.py. Writes checker_kmax.json.
Cloud container, 2026-09-24.

    PYTHONPATH=$PWD <venv python> .../run_checker_kmax.py
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402

import checker_glue as GLUE  # noqa: E402
import run_checker_ts as RT  # noqa: E402

OUT = os.path.join(HERE, "checker_kmax.json")


def main():
    digest = RT._guard()
    with open(RT.SNAP) as fh:
        snap = json.load(fh)
    if snap["meta"]["ts_inputs_digest"] != digest:
        raise SystemExit("refused: snapshot digest does not match the T_S inputs")
    ta_ts, _ = GLUE._ta()
    TP = GLUE._import(GLUE.TWO_ADIC, "ta_prolate")
    nv, S, N, K = 200, 2400, 32, 14
    t = time.time()
    prov = ta_ts.KernelProvider(nv, S)
    pm = TP.ProlateModes(nvec=nv, dps=20)
    out, diag = TP.delta_T_cells(pm, RT.CELLS, N, S=float(S), alpha=1.0, Kmax=K)
    RT._guard(digest)
    stray = GLUE.loaded_inputs_outside_key()
    if stray:
        raise SystemExit("refused: T_S loaded modules outside the key: " + ", ".join(stray))
    sec = round(time.time() - t, 1)
    hi = np.abs(np.arange(-N, N + 1)) > N // 2
    res = {"meta": {"ts_inputs_digest": digest, "seconds": sec, "unit": [nv, S, N], "kmax": K,
                    "kmax_default": TP.kmax_for(nv), "diag": diag}, "cells": {}}
    for c in RT.CELLS:
        dT = out[c][0]
        dT = ((dT + dT.conj().T) / 2).real
        T14 = prov.T_inf_matrix(c, N, 40) + dT
        T13 = np.array(snap["T_S"][RT.unit_key(c, N, 40, 200, 2400)])
        T240 = np.array(snap["T_S"][RT.unit_key(c, N, 40, 240, 2400)])
        r = {}
        for name, D in (("kmax_response", T14 - T13), ("mode_response", T240 - T14), ("combined", T240 - T13)):
            r[name] = {"full": RT.spec_norm(D), "central_N16": RT.spec_norm(D[np.ix_(~hi, ~hi)]),
                       "top_half": RT.spec_norm(D[np.ix_(hi, hi)])}
        r["T_S_200_K14_low3"] = [float(x) for x in np.linalg.eigvalsh(T14)[:3]]
        res["cells"][c] = r
        print(c, {k: round(v["full"], 6) for k, v in r.items() if isinstance(v, dict)}, flush=True)
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=1)
    print("seconds", sec)


if __name__ == "__main__":
    main()
