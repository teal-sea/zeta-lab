"""Which C2 condition does Epstein (1,1,6) break? Pole-free vs full spectra.

Theory s2.6: Q_e >= 0 iff (a) mu_2(Q°_e) >= 0 and (b) mu_1 >= 0 or the
pole-capacity Phi <= 0; Q_o >= 0 iff Q°_o >= 0 and 1 - 2<s,(A°_o)^-1 s> >= 0
(the odd pole block is negative). For Epstein at windows around its
crossings: ball LDL^T inertia of the pole-free and full matrices per sector,
and the lowest two approximate eigenvalues of each. Writes
epstein_polefree.json. N = 64, prec 400.
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402

OUT = os.path.join(W.HERE, "epstein_polefree.json")
N, PREC = 64, 400
CS = ["27", "28", "57/2", "29", "59/2", "30", "34", "40", "48"]


def main():
    d = {"meta": {"N": N, "prec": PREC, "note": __doc__.split("\n\n")[0]}, "cells": {}}
    for cs in CS:
        c = W.cq(Fraction(cs))
        full = W.epstein_matrices(c, N, PREC)
        free = W.epstein_matrices(c, N, PREC, with_pole=False)
        rec = {}
        for sector in ("even", "odd"):
            rec[sector] = {
                "full_inertia": list(W.ldl_signs(full[sector])),
                "polefree_inertia": list(W.ldl_signs(free[sector])),
                "full_lowest2": W.approx_spectrum(full[sector], 2),
                "polefree_lowest2": W.approx_spectrum(free[sector], 2),
            }
        d["cells"][cs] = rec
        W.save(OUT, d)
        e, o = rec["even"], rec["odd"]
        print(f"c={cs:>5} even full {e['full_inertia']} {[f'{x:.3e}' for x in e['full_lowest2']]} "
              f"free {e['polefree_inertia']} {[f'{x:.3e}' for x in e['polefree_lowest2']]} | "
              f"odd full {o['full_inertia']} {[f'{x:.3e}' for x in o['full_lowest2']]} "
              f"free {o['polefree_inertia']} {[f'{x:.3e}' for x in o['polefree_lowest2']]}", flush=True)


if __name__ == "__main__":
    main()
