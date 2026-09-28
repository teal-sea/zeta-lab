"""Kill-control 4 (optional, a LESION): bypass the gate and try to build T_S
with W_a's non-unitary data at 2 (a = 1/4, alpha = 2^{+1/4}, 2^{-1/4}).
Writes checker_lesion.json.

Three layers, recorded in order:
  1. the builder with the gate: ta_ts.T_S_matrix(c, N, dps, ta_data.W_A_QUARTER)
     (kill-control 2; expected NonUnitaryLocalData);
  2. gate bypassed, the routed provider: KernelProvider(nvec, S).delta_T(c, N,
     dps, alpha, "even"). Its exact exception, if any, is the finding for the
     construction as delivered;
  3. below both guards (LESION ONLY): ta_prolate.delta_T_cells with the
     non-unitary alpha, composed as the builder would:
     T_les = sum_j (T_inf + Delta_T(alpha_j)). two_adic/ never validated
     delta_T_cells off |alpha| = 1 (its Gram weight 1/(1 - |alpha|^2/2) was
     written for unitary alpha), so these numbers say what the unguarded
     formula does, not what a correct non-unitary T_S would be.
The Weil form with the same data at 2 is Q_les = 2 Q_inf - s_1(2) Wp,
s_1(2) = 2^{1/4} + 2^{-1/4}, Wp the zeta prime block (the prime block is
linear in real alpha). The archimedean factor of the real W_a (shifted
Gamma) is not modelled; only the data at 2 are lesioned.
N = 8, (nvec, S) = (80, 1200), kmax_for(80) = 10. About 3 minutes.
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
import checker_q as CQ  # noqa: E402

CELLS = ["2.2", "2.5", "2.9"]
N, NVEC, S = 8, 80, 1200
BAND = 6e-3  # two_adic/'s stated band for Delta_T at alpha = 1; no band exists off |alpha| = 1


def _layer(fn):
    try:
        out = fn()
    except Exception as e:  # recorded verbatim, not handled
        return {"outcome": "raised", "exception": f"{type(e).__module__}.{type(e).__name__}", "message": str(e)}
    return {"outcome": "returned", "type": type(out).__name__}


def spec(M):
    e = np.linalg.eigvalsh(M)
    return {"low3": [float(x) for x in e[:3]], "n_below_band": int((e < -BAND).sum()),
            "n_in_band": int((abs(e) <= BAND).sum()), "n_above_band": int((e > BAND).sum())}


def main():
    t0 = time.time()
    digest, dirty = GLUE.ts_key()
    ta_ts, ta_data = GLUE._ta()
    TP = GLUE._import(GLUE.TWO_ADIC, "ta_prolate")
    prov = ta_ts.KernelProvider(NVEC, S)
    a_plus, a_minus = 2 ** 0.25, 2 ** -0.25
    out = {"meta": {"N": N, "nvec": NVEC, "S": S, "kmax": TP.kmax_for(NVEC), "band": BAND,
                    "label": "LESION, kill-control 4", "ts_inputs_digest": digest, "dirty_inputs": dirty,
                    "head": GLUE._git("rev-parse", "HEAD").strip()},
           "layers": {
               "1_builder_with_gate": _layer(lambda: ta_ts.T_S_matrix("2.5", N, 40, ta_data.W_A_QUARTER, s_inf=prov)),
               "2_provider_gate_bypassed": _layer(lambda: prov.delta_T("2.5", N, 40, complex(a_plus), "even")),
               "2_provider_gate_bypassed_alpha_minus": _layer(lambda: prov.delta_T("2.5", N, 40, complex(a_minus), "even")),
           },
           "cells": {}}
    print(json.dumps(out["layers"], indent=1), flush=True)
    pm = TP.ProlateModes(nvec=NVEC, dps=20)
    dT = {}
    for name, a in (("1", 1.0), ("plus", a_plus), ("minus", a_minus)):
        o, diag = TP.delta_T_cells(pm, CELLS, N, S=float(S), alpha=a)
        dT[name] = {c: ((o[c][0] + o[c][0].conj().T) / 2).real for c in CELLS}
        out["meta"][f"diag_alpha_{name}"] = diag
    for c in CELLS:
        Tinf = prov.T_inf_matrix(c, N, 40)
        parts = CQ.q_parts(c, N, 40)
        f = lambda M: np.array([[float(M[i, j]) for j in range(2 * N + 1)] for i in range(2 * N + 1)])  # noqa: E731
        Qinf, prime = f(parts["pole"]) + f(parts["arch"]), f(parts["prime"])
        s1 = a_plus + a_minus
        T_z = Tinf + dT["1"][c]
        T_les = 2 * Tinf + dT["plus"][c] + dT["minus"][c]
        out["cells"][c] = {
            "T_zeta": spec(T_z), "T_les": spec(T_les),
            "R_zeta": spec(Qinf + prime - T_z),
            "R_les": spec(2 * Qinf + s1 * prime - T_les),
            "R_les_against_2Q_zeta": spec(2 * (Qinf + prime) - T_les),
            "dT_plus_minus_dT_1_maxabs": float(np.abs(dT["plus"][c] - dT["1"][c]).max()),
            "dT_minus_minus_dT_1_maxabs": float(np.abs(dT["minus"][c] - dT["1"][c]).max()),
        }
        print(c, "done", round(time.time() - t0, 1), flush=True)
    out["meta"]["seconds"] = round(time.time() - t0, 1)
    with open(os.path.join(HERE, "checker_lesion.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
