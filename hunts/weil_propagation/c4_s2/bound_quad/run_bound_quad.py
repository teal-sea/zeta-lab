"""bound_quad/: the stored Gram spectra at the two builds with the smallest cond(F) (bound_quad_gram.json).

For (nvec, S) = (80, 1200) and (80, 1600), the stored route's own ingredients
(two_adic/ ta_prolate.delta_T_cells: hats, jumps, gram_factor_s with its two
order-1/S tail rows; read-only import), recorded per build:

  Gz_eig_min/max, Gb_eig_min/max   extreme eigenvalues of G_S = F* F (from the
                                    singular values of F, float64)
  Gz_minus_I_norm                   ||G_S^z - I||_2 (float64)
  leverage_sum_z / _b               sum over the s rows of w_s rho~(s) / 2 pi (A5)
  probe_norm[c][N]                  ||M_inf(G_S) - M_inf(I)||_2: the Q_inf part of
                                    Delta_T with the stored Gram against the identity,
                                    the Gram of exact prolates (two_adic/'s probe,
                                    spectral norm here)
  seconds

Float64, one route: measured. Used by DERIVATION s2.3 (Prop 3) for the two
builds where the recorded diagnostics alone do not show the obstruction.
About 2 minutes on the laptop.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
TWO_ADIC = os.path.normpath(os.path.join(HERE, "..", "two_adic"))
if TWO_ADIC not in sys.path:
    sys.path.insert(0, TWO_ADIC)

import ta_mellin as TM  # noqa: E402  (two_adic/, read-only)
import ta_prolate as TP  # noqa: E402  (two_adic/, read-only)

OUT = os.path.join(HERE, "bound_quad_gram.json")
BUILDS = [(80, 1200.0, (8, 16)), (80, 1600.0, (16,))]


def run(nvec: int, S: float, Ns) -> dict:
    t0 = time.time()
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    s, sw = TM.s_grid(S, width=1.0, per_panel=8)
    Z, B = TP.hats_modes(pm, s, 1.0)
    jz, jb = TP.jumps(pm, 1.0)
    A = pm.derivs[:, 0] * pm.norm
    Fz = TP.gram_factor_s(Z, sw, jz, S, A, 1.0)
    Fb = TP.gram_factor_s(B, sw, jb, S, A, 2.0)
    sz = np.linalg.svd(Fz, compute_uv=False)
    sb = np.linalg.svd(Fb, compute_uv=False)
    Gz = np.conj(Fz.T) @ Fz
    rz, rb = TM.rho(Z, factor=Fz), TM.rho(B, factor=Fb)
    probe = {}
    for c in ("2.2", "2.5", "2.9"):
        L = math.log(float(c))
        probe[c] = {}
        for N in Ns:
            Mi = TM.T_from_rho(rz, s, sw, L, N)
            MI = TM.T_from_rho(np.sum(np.abs(Z) ** 2, axis=0), s, sw, L, N)
            D = (Mi - MI + (Mi - MI).conj().T) / 2
            probe[c][str(N)] = float(np.abs(np.linalg.eigvalsh(D)).max())
    return {
        "nvec": nvec, "S": S, "s_nodes": int(s.size),
        "Gz_eig_min": float(sz[-1] ** 2), "Gz_eig_max": float(sz[0] ** 2),
        "Gb_eig_min": float(sb[-1] ** 2), "Gb_eig_max": float(sb[0] ** 2),
        "cond_Fz": float(sz[0] / sz[-1]), "cond_Fb": float(sb[0] / sb[-1]),
        "Gz_minus_I_norm": float(np.abs(np.linalg.eigvalsh(Gz - np.eye(nvec))).max()),
        "leverage_sum_z": float((rz * sw).sum() / (2 * math.pi)),
        "leverage_sum_b": float((rb * sw).sum() / (2 * math.pi)),
        "probe_norm": probe,
        "seconds": round(time.time() - t0, 1),
    }


def main() -> None:
    out = {"route": "two_adic/ta_prolate (hats_modes, jumps, gram_factor_s), ta_mellin (s_grid(S, 1, 8), rho, "
                    "T_from_rho); float64, measured", "rows": []}
    for nvec, S, Ns in BUILDS:
        out["rows"].append(run(nvec, S, Ns))
        print(out["rows"][-1], flush=True)
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
