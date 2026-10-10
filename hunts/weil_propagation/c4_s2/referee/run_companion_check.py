"""referee/, phase 2 (written after routing): Lemma 1's measured companion by a second route.

bound_trunc/ s2.9 measures c_j = (1/2pi) int_{|s| <= 60} |f^(s)|^2 |zeta^_j(s)|^2 ds
for f = U_0 at c = 2.9 with kernel/'s closed-form Mellin transforms
(sonin.zeta_mellin_all, Tate's local functional equation), and reads the
partial sums P(n) = sum_{j < n} c_j as growing 0.99 per unit of log n. This
script recomputes c_j for j < 160 from two_adic/'s float64 route instead
(spherical Bessel samples, Gauss panels on [1, 2^Kmax], the asymptotic 1/w
tail: referee_lib.hats_knobs at two_adic/'s defaults), on its own s-grid
(Gauss-Legendre, width 1, 8 nodes per panel, on [-60, 60]), and writes
referee_companion.json with the agreement against bound_trunc/'s
lemma1_companion.json.

    PYTHONPATH=<worktree root> <venv python> run_companion_check.py
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402

import referee_lib as RL  # noqa: E402

NMAX = 160
S0 = 60.0
C = 2.9
OUT = os.path.join(HERE, "referee_companion.json")
THEIRS = os.path.join(RL.C4, "bound_trunc", "lemma1_companion.json")


def main():
    t = time.time()
    pm = RL.prolate_modes(NMAX)
    s, sw = RL.TM.s_grid(S0, width=1.0, per_panel=8)
    Z, _ = RL.hats_knobs(pm, s, RL.TP.kmax_for(NMAX))
    V0 = RL.TM.window_hat(math.log(C), 0, s)[0]
    cj = ((np.abs(V0) ** 2 * sw) @ (np.abs(Z) ** 2).T) / RL.TWO_PI
    theirs = RL.load_json(THEIRS)
    tc = np.array(theirs["c_j"][:NMAX])
    P = np.cumsum(cj)
    marks = [10, 20, 40, 80, 120, 160]
    slope = {f"{a}-{b}": float((P[b - 1] - P[a - 1]) / math.log(b / a)) for a, b in ((40, 80), (80, 160))}
    w_f = float((np.abs(V0) ** 2 * sw).sum() / RL.TWO_PI)
    doc = {
        "meta": {"what": "c_j of bound_trunc/ s2.9 by two_adic/'s float64 w-quadrature route", "c": C, "S0": S0,
                 "nmax": NMAX, "s_grid": "Gauss-Legendre width 1, 8 per panel", "Kmax": RL.TP.kmax_for(NMAX),
                 "seconds": round(time.time() - t, 1)},
        "w_f": w_f,
        "c_j": [float(x) for x in cj],
        "P": {str(m): float(P[m - 1]) for m in marks},
        "slope_per_log_n": slope,
        "max_abs_diff_c_j": float(np.abs(cj - tc).max()),
        "max_rel_diff_c_j": float((np.abs(cj - tc) / np.abs(tc)).max()),
        "diff_P160": float(P[NMAX - 1] - np.sum(tc)),
    }
    with open(OUT, "w") as fh:
        json.dump(doc, fh, indent=1)
    print({k: v for k, v in doc.items() if k != "c_j"})


if __name__ == "__main__":
    main()
