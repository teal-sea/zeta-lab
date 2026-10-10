"""Mission cells for the E_S / theta_S matrices: writes ta_es_cells.json.

Per cell (c, N), at dps 40:
  theta_gram_eig_min/max : spectrum ends of Gram(Theta_1) on the window basis;
  prime_block_eig_min/max: spectrum ends of Wp (the atom n = 2), equal to
                           -log 2 (theta ends - 3/2) by the exact identity;
  identity_defect        : max entry of -Wp - log 2 (Gram(Theta_1) - 3/2 I);
  galerkin_dev           : max entry of Wp (from C) - Wp (galerkin.py).
The Cauchy-Schwarz bound for 2 < c < 4 (window and shifted window overlap in
less than half) puts the theta_S spectrum inside [3/2 - 1/sqrt 2, 3/2 + 1/sqrt 2].
Runtime is recorded.
"""

from __future__ import annotations

import json
import os
import sys
import time

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_es as E  # noqa: E402

CELLS_C = ("2.2", "2.5", "2.9")
CELLS_N = (8, 16, 32)
DPS = 40


def _ends(M):
    ev = mp.eigsy(M, eigvals_only=True)
    ev = sorted(ev)
    return ev[0], ev[-1]


def cell(c: str, N: int, dps: int = DPS) -> dict:
    t0 = time.time()
    with mp.workdps(dps):
        G = E.theta_gram(mp.mpf(c), N, (1,), dps)
        Wp = E.prime_block_from_C(mp.mpf(c), N, (1,), dps)
        Wg = E.galerkin_prime_block(mp.mpf(c), N, dps)
        n = G.rows
        Gr = mp.matrix([[mp.re(G[i, j]) for j in range(n)] for i in range(n)])
        # Gram(Theta_1) is real symmetric: C + C^* is real (q_nm), identity exact
        imag = max(abs(mp.im(G[i, j])) for i in range(n) for j in range(n))
        g0, g1 = _ends(Gr)
        Wr = mp.matrix([[mp.re(Wp[i, j]) for j in range(n)] for i in range(n)])
        w0, w1 = _ends(Wr)
        defect = E.identity_defect(mp.mpf(c), N, (1,), dps)
        gdev = max(abs(Wp[i, j] - Wg[i, j]) for i in range(n) for j in range(n))
        return {
            "c": c,
            "N": N,
            "dps": dps,
            "theta_gram_eig_min": mp.nstr(g0, 20),
            "theta_gram_eig_max": mp.nstr(g1, 20),
            "theta_gram_max_imag": mp.nstr(imag, 5),
            "prime_block_eig_min": mp.nstr(w0, 20),
            "prime_block_eig_max": mp.nstr(w1, 20),
            "identity_defect": mp.nstr(defect, 5),
            "galerkin_dev": mp.nstr(gdev, 5),
            "seconds": round(time.time() - t0, 2),
        }


def main() -> None:
    out = {
        "meta": {
            "what": "Gram(Theta_1) of theta_S and the Weil prime block on the CCM basis",
            "bound_lo": mp.nstr(mp.mpf(3) / 2 - 1 / mp.sqrt(2), 20),
            "bound_hi": mp.nstr(mp.mpf(3) / 2 + 1 / mp.sqrt(2), 20),
        },
        "cells": [],
    }
    for c in CELLS_C:
        for N in CELLS_N:
            r = cell(c, N)
            print(r, flush=True)
            out["cells"].append(r)
    with open(os.path.join(HERE, "ta_es_cells.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
