"""Accuracy item of RESULTS s7 on the cheapest cell: ta_gram_probe.json.

Delta_T's band (3.5e-3 to 8.2e-3) was the Gram probe: the change of Delta_T
when the s-side Gram of the zeta_n (ta_prolate.gram_s, order-1/S tails) is
replaced by its exact value, the identity. This file measures, on c = 2.2,
N = 8, how that probe, Delta_T itself and T_S's lowest eigenvalue respond to
S and to nvec, one truncation (nvec, S) per process. Per run:
  dT                 Delta_T (both Grams s-side, as ta_run_prolate does);
  dT_probe_*         change of Delta_T when G_z^s is replaced by I (max entry, 2-norm);
  TS_low3            lowest eigenvalues of T_S = T_inf + Delta_T;
  gz_dev, gz_dev_diag_max   max |G_z^s - I| (the s-side Gram error, exact), all / diagonal.

The band, fixed before the S = 4800 runs were read (a spectral norm, so that
Weyl's inequality turns it into an eigenvalue error):
  band(80, 4800) = max( ||dT(80, 4800) - dT(80, 2400)||_2,     S-response
                        ||dT(100, 4800) - dT(80, 4800)||_2,    nvec-response
                        probe_2(80, 4800) ).
The target is Q's lowest eigenvalue on the same cell, read from
checker/checker_q_cells.json (2.5738e-4 at c = 2.2, N = 8; the 2.33e-4 quoted
for c = 2.2 is the N = 32 value). Float64: measured grade.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_mellin as TM  # noqa: E402
import ta_prolate as TP  # noqa: E402
import ta_run_prolate as R  # noqa: E402
import ta_ts as T  # noqa: E402

C, N, NVEC = "2.2", 8, 80
SS = (1200.0, 2400.0)


def q_low() -> float:
    """Q's lowest eigenvalue on (C, N), checker/'s dps-40 value (read-only)."""
    path = os.path.normpath(os.path.join(HERE, "..", "checker", "checker_q_cells.json"))
    with open(path) as fh:
        return float(json.load(fh)["cells"][C][f"full_N{N}_dps40"][0])



def grams(pm: TP.ProlateModes, S: float):
    s, sw = TM.s_grid(S, width=2.0, per_panel=8)
    Z, B = TP.hats_modes(pm, s, 1.0)
    jz, jb = TP.jumps(pm, 1.0)
    A = pm.derivs[:, 0] * pm.norm
    return s, sw, Z, B, TP.gram_s(Z, sw, jz, S, A, 1.0), TP.gram_s(B, sw, jb, S, A, 2.0)


def delta_T(s, sw, Z, B, Gz, Gb) -> np.ndarray:
    L = math.log(float(C))
    Mi = TM.T_from_rho(TM.rho(Z, Gz), s, sw, L, N)
    Ms = TM.T_from_rho(TM.rho(B, Gb), s, sw, L, N)
    return ((Mi - Ms) + (Mi - Ms).conj().T).real / 2


def run(nvec: int, S: float) -> dict:
    """One truncation (nvec, S) on the cell (C, N): Delta_T with both s-side
    Grams, the probe, T_S's lowest eigenvalue and the s-side error of G_z."""
    t0 = time.time()
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    Tinf = T.KernelProvider().T_inf_matrix(C, N, 40)
    s, sw, Z, B, Gz, Gb = grams(pm, S)
    dT = delta_T(s, sw, Z, B, Gz, Gb)
    dTI = delta_T(s, sw, Z, B, np.eye(nvec), Gb)
    return {
        "nvec": nvec, "S": S, "Kmax": TP.kmax_for(nvec),
        "dT": dT.tolist(),
        "dT_probe_maxentry": float(np.abs(dTI - dT).max()),
        "dT_probe_norm2": float(np.linalg.norm(dTI - dT, 2)),
        "TS_low3": [float(x) for x in np.linalg.eigvalsh(Tinf + dT)[:3]],
        "gz_dev": float(np.abs(Gz - np.eye(nvec)).max()),
        "gz_dev_diag_max": float(np.abs(np.diag(Gz).real - 1.0).max()),
        "seconds": round(time.time() - t0, 1),
    }


def main(argv=None) -> dict:
    """Arguments: nvec S (one truncation per process, merged into the JSON)."""
    argv = sys.argv[1:] if argv is None else argv
    path = os.path.join(HERE, "ta_gram_probe.json")
    try:
        with open(path) as fh:
            out = json.load(fh)
    except (OSError, ValueError):
        out = {}
    if "runs" not in out:
        out = {"c": C, "N": N, "runs": {}}
    out["Q_low"] = q_low()
    if argv:
        nvec, S = int(argv[0]), float(argv[1])
        out["runs"][f"{nvec},{int(S)}"] = run(nvec, S)
    else:
        pm = TP.ProlateModes(nvec=NVEC, dps=20)
        w = np.linspace(1.0, 1024.0, 20000)
        t1 = time.time()
        pm.zeta(w)
        out["zeta_seconds_per_node_80"] = (time.time() - t1) / w.size
        out["A_max_80"] = float(np.abs(pm.derivs[:, 0] * pm.norm).max())
        out["J_max_80"] = float(np.abs(pm.zeta(np.array([1.0]))[:, 0]).max())
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    return out


if __name__ == "__main__":
    o = main()
    for k, r in o["runs"].items():
        print(k, {a: b for a, b in r.items() if a != "dT"})
