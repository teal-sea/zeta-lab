"""Mission cells for T_S_matrix: writes ta_ts_cells.json (outcome per cell and data set).

T_S_matrix never returns a number it cannot compute, so each entry records
the outcome class: "refused_nonunitary" (kill-control 2), "framework_limit"
(Gamma_C over Q with S = {inf, 2}), "awaiting_kernel" (S_inf not routed), or
"matrix" (checks passed; T_S_matrix builds it from kernel/'s data, values in
ta_ts_prolate.json). Uses dry_run, so it is fast. Also records ||P F_S P||_HS^2 partial sums.
"""

from __future__ import annotations

import json
import os
import sys

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_data as D  # noqa: E402
import ta_hs as H  # noqa: E402
import ta_ts as T  # noqa: E402

DATA = {
    "zeta": (D.ZETA, "Gamma_R"),
    "dedekind_Q_sqrt_m23": (D.DEDEKIND_Q_SQRT_M23, "Gamma_C"),
    "W_a_quarter": (D.W_A_QUARTER, "Gamma_R"),
    "epstein_116_tower": (("tower", D.EPSTEIN_116_TOWER[1], 2), "Gamma_C"),
    "place_2_off": (None, "Gamma_R"),
}


def outcome(c: str, N: int, name: str) -> dict:
    data, arch = DATA[name]
    try:
        M = T.T_S_matrix(c, N, 40, data, arch, dry_run=True)
    except D.NonUnitaryLocalData as e:
        return {"outcome": "refused_nonunitary", "message": str(e)}
    except T.FrameworkLimit as e:
        return {"outcome": "framework_limit", "message": str(e)}
    except T.KernelUnavailable as e:
        return {"outcome": "awaiting_kernel", "message": str(e)}
    return {"outcome": "matrix", "message": "built by T_S_matrix; values in ta_ts_prolate.json"}


def main() -> None:
    out = {"cells": []}
    for c in ("2.2", "2.5", "2.9"):
        for N in (8, 16, 32):
            row = {"c": c, "N": N, "dps": 40}
            for name in DATA:
                row[name] = outcome(c, N, name)
            out["cells"].append(row)
    with mp.workdps(30):
        out["hs2_P_FS_P"] = {
            "archimedean": mp.nstr(H.hs2_archimedean(), 15),
            "partial_sums": {str(K): mp.nstr(H.hs2_partial(K), 15) for K in (0, 8, 16, 24, 32, 40)},
            "asymptote": "K/2 + 1.0707867954",
        }
    with open(os.path.join(HERE, "ta_ts_cells.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out["cells"][0], indent=1)[:1500])


if __name__ == "__main__":
    main()
