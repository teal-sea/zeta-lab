"""Where does the pole-free even Epstein form get its second negative
eigenvalue (C2's condition (a) failing)? Bisection over dyadic c in
[29, 29.5] on the ball LDL^T inertia of the pole-free even matrix (1 -> 2
negative pivots), to 2^-10, at N = 64 and 128. Compare with the full-form
crossing in epstein_crossing.json. Writes epstein_mu2_cross.json.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402

OUT = os.path.join(W.HERE, "epstein_mu2_cross.json")


def nneg_free(c, N):
    M = W.epstein_matrices(W.cq(c), N, 400, with_pole=False)["even"]
    p, n, ok = W.ldl_signs(M)
    if not ok:
        raise ArithmeticError(f"inconclusive at {c}, {N}")
    return n


def main():
    full = json.load(open(os.path.join(W.HERE, "epstein_crossing.json")))["runs"]
    d = {"meta": {"note": __doc__.split("\n\n")[0]}, "runs": {}}
    for N in (64, 128):
        lo, hi = Fraction(29), Fraction(59, 2)
        assert nneg_free(lo, N) == 1 and nneg_free(hi, N) == 2
        for _ in range(10):
            mid = (lo + hi) / 2
            if nneg_free(mid, N) >= 2:
                hi = mid
            else:
                lo = mid
        fr = full[f"{N}|even"]
        d["runs"][str(N)] = {"mu2_last_nonneg_c": float(lo), "mu2_first_neg_c": float(hi),
                             "full_even_c_pos": fr["c_pos_float"], "full_even_c_neg": fr["c_neg_float"]}
        W.save(OUT, d)
        print(N, d["runs"][str(N)], flush=True)


if __name__ == "__main__":
    main()
