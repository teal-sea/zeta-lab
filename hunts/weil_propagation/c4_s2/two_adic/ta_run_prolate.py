"""zeta's T_S = T_inf (kernel/) + Delta_T (this folder) on the mission cells: ta_ts_prolate.json.

Per truncation (nvec prolate modes, s in [-S, S]) the Mellin data are
computed once and reused for every (c, N). Recorded per (nvec, S, N, c):
  T_inf_eig_min/max            kernel/'s T_inf (moments, dps 40), float;
  T_S_eig_low3 / T_S_eig_max   T_S = T_inf + Delta_T;
  T_S_n_below_m002             eigenvalues of T_S below -0.02 (a PSD check);
  gram_sensitivity             max entry change of Delta_T when Q_inf's Gram
                               is replaced by the exact identity (the z_n are
                               orthonormal): the error scale of Delta_T;
  resid_top8                   the 8 eigenvalues of Delta_T + Wp largest in modulus;
  resid_n_above_01 / below     counts of eigenvalues of Delta_T + Wp beyond +-0.1.
Also zeta^ against kernel/'s closed-form Tate route (zeta_mellin_all).
Float64 throughout: measured grade. Runtime about 5 minutes.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_es as E  # noqa: E402
import ta_mellin as TM  # noqa: E402
import ta_prolate as TP  # noqa: E402
import ta_ts as T  # noqa: E402

CELLS = ("2.2", "2.5", "2.9")
CONFIGS = [(40, 800.0, (8,)), (80, 1200.0, (8, 16)), (120, 1600.0, (16,)), (130, 1800.0, (32,)), (200, 2400.0, (32,))]


def wp_matrix(c: str, N: int) -> np.ndarray:
    with mp.workdps(30):
        W = E.prime_block_from_C(mp.mpf(c), N, (1,), 30)
        return np.array([[float(mp.re(W[i, j])) for j in range(2 * N + 1)] for i in range(2 * N + 1)])


def tate_check(nvec: int = 40) -> float:
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    ss = np.array([0.0, 2.5, 30.0, 150.0])
    Z, _ = TP.hats_modes(pm, ss, 1.0, Kmax=10)
    err = 0.0
    for j, s0 in enumerate(ss):
        ref = TP.sonin.zeta_mellin_all(float(s0), 20, 0, nvec)
        err = max(err, max(abs(complex(ref[n]) - Z[n, j]) for n in range(nvec)))
    return err


def run_config(nvec: int, S: float, Ns, provider: T.KernelProvider) -> list[dict]:
    t0 = time.time()
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    s, sw = TM.s_grid(S, width=2.0, per_panel=8)
    Z, B = TP.hats_modes(pm, s, 1.0)
    jz, jb = TP.jumps(pm, 1.0)
    A = pm.derivs[:, 0] * pm.norm
    Gz = TP.gram_s(Z, sw, jz, S, A, 1.0)
    Gb = TP.gram_s(B, sw, jb, S, A, 2.0)
    rz, rzI, rb = TM.rho(Z, Gz), TM.rho(Z, np.eye(nvec)), TM.rho(B, Gb)
    t_hats = time.time() - t0
    rows = []
    for N in Ns:
        for c in CELLS:
            L = math.log(float(c))
            Mi = TM.T_from_rho(rz, s, sw, L, N)
            MiI = TM.T_from_rho(rzI, s, sw, L, N)
            Ms = TM.T_from_rho(rb, s, sw, L, N)
            dT = ((Mi - Ms) + (Mi - Ms).conj().T).real / 2
            dTI = ((MiI - Ms) + (MiI - Ms).conj().T).real / 2
            Tinf = provider.T_inf_matrix(c, N, 40)
            TS = Tinf + dT
            e0 = np.linalg.eigvalsh(Tinf)
            eS = np.linalg.eigvalsh(TS)
            ed = np.linalg.eigvalsh(dT + wp_matrix(c, N))
            top = ed[np.argsort(-np.abs(ed))][:8]
            rows.append(
                {
                    "nvec": nvec,
                    "S": S,
                    "N": N,
                    "c": c,
                    "T_inf_eig_min": float(e0.min()),
                    "T_inf_eig_max": float(e0.max()),
                    "T_S_eig_low3": [float(x) for x in eS[:3]],
                    "T_S_eig_max": float(eS.max()),
                    "T_S_n_below_m002": int((eS < -0.02).sum()),
                    "gram_sensitivity": float(np.abs(dTI - dT).max()),
                    "resid_top8": [float(x) for x in top],
                    "resid_n_above_01": int((ed > 0.1).sum()),
                    "resid_n_below_m01": int((ed < -0.1).sum()),
                    "Kmax": TP.kmax_for(nvec),
                    "seconds_hats": round(t_hats, 1),
                }
            )
            print(rows[-1], flush=True)
    return rows


def main(argv=None) -> None:
    """No argument: every configuration. With indices (0 .. 4) into CONFIGS:
    recompute only those and merge into the existing JSON, so that each
    process stays under the 10-minute local limit on a shared machine."""
    argv = sys.argv[1:] if argv is None else argv
    path = os.path.join(HERE, "ta_ts_prolate.json")
    t0 = time.time()
    prov = T.KernelProvider()
    if not argv:
        out = {"tate_check_max_abs": tate_check(), "rows": []}
        for nvec, S, Ns in CONFIGS:
            out["rows"].extend(run_config(nvec, S, Ns, prov))
        out["seconds_total"] = round(time.time() - t0, 1)
    else:
        with open(path) as fh:
            out = json.load(fh)
        for i in (int(a) for a in argv):
            nvec, S, Ns = CONFIGS[i]
            new = run_config(nvec, S, Ns, prov)
            keep = [r for r in out["rows"] if not (r["nvec"] == nvec and r["S"] == S)]
            out["rows"] = keep + new
        order = {(n, S): i for i, (n, S, _) in enumerate(CONFIGS)}
        out["rows"].sort(key=lambda r: (order[(r["nvec"], r["S"])], r["N"], r["c"]))
        out.setdefault("seconds_by_config", {})
        out["seconds_by_config"][",".join(argv)] = round(time.time() - t0, 1)
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
