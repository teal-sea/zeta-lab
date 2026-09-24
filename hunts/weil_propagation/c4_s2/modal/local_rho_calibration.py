"""modal/ follow-up 2: the local half of the calibration unit (80, 1200, 8).

Builds checker/'s unit (nvec, S, N) = (80, 1200, 8) on this machine, exactly
as run_checker_ts.snapshot() builds it (build_unit with dps (40, 60) at
N = 8), inside run_checker_ts._guard before and after, and writes the rows to
modal/out_rho/local_checker_80_1200_8.json with the digest and the platform.
run_modal_rho.py's calibrate step compares the Modal build of the same unit
against this file (max abs difference, threshold 1e-10, BRIEF.md follow-up 2).

Writes only in modal/out_rho/. Computes no eigenvalue of T_S or R_S.

    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/modal/local_rho_calibration.py
"""

from __future__ import annotations

import json
import os
import platform
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CHK = os.path.normpath(os.path.join(HERE, "..", "checker"))
if CHK not in sys.path:
    sys.path.insert(0, CHK)

import checker_glue as G  # noqa: E402
import run_checker_ts as RC  # noqa: E402

NV, S, N = 80, 1200, 8
OUT = os.path.join(HERE, "out_rho", f"local_checker_{NV}_{S}_{N}.json")


def main():
    from importlib.metadata import version

    d0 = RC._guard()
    head = G._git("rev-parse", "HEAD").strip()
    t0 = time.time()
    rows, diag = RC.build_unit(NV, S, N, dps_list=(40, 60))
    secs = round(time.time() - t0, 1)
    RC._guard(d0)
    stray = G.loaded_inputs_outside_key()
    if stray:
        raise SystemExit("refused: T_S loaded modules outside the key: " + ", ".join(stray))
    kmax = G._import(G.TWO_ADIC, "ta_prolate").kmax_for(NV)
    meta = {"unit": f"checker_{NV}_{S}_{N}", "role": "calibration, local half (BRIEF.md follow-up 2)",
            "ts_inputs_digest": d0, "head": head, "seconds": secs, "kmax": kmax,
            "python": sys.version.split()[0], "platform": platform.platform(),
            "versions": {p: version(p) for p in ("numpy", "scipy", "mpmath", "python-flint", "sympy")},
            "route": "run_checker_ts.build_unit(80, 1200, 8, dps_list=(40, 60)), inside run_checker_ts._guard"}
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump({"meta": meta, "T_S": rows,
                   "units": {f"{NV}|{S}|{N}": {"role": meta["role"], "seconds": secs, "kmax": kmax, "diag": diag}}},
                  fh, indent=1)
    print(OUT, secs, "s", d0[:12], flush=True)


if __name__ == "__main__":
    main()
