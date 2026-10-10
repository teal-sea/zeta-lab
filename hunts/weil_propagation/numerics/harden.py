"""Harden every grid cell's lambda_min, and check it IS the minimum.

Inverse iteration at shift 0 converges to the eigenvalue of smallest
MAGNITUDE. Where the form has a negative eigenvalue that is not the one
closest to 0, that is not lambda_min (it happens just above c = 32 at
N = 128: eigenvalues +7.3e-28 and -2.06e-25 at c = 32 + 1/256). So each
cell gets a Temple bracket whose LDL step also settles the ordering:
  lam1 > 0: ball LDL^T at shift s = sqrt(lam1 lam2) must show exactly one
            negative pivot (so lam1 < s <= lambda_2 and lam1 is the minimum);
  lam1 < 0: ball LDL^T at shift 0 must show exactly one negative pivot
            (so lambda_2 > 0, lam1 is the only negative eigenvalue).
Then Temple: lambda_min in [rho - eps^2/(s - rho), rho], rho = RQ(v) in balls.

Usage: harden.py KIND N  (reads grid_<kind>_N<N>.json, writes its
"hardened" block; checkpoint per cell).
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from mpmath import mp  # noqa: E402

KIND = sys.argv[1]
N = int(sys.argv[2])
PATH = os.path.join(W.HERE, f"grid_{KIND}_N{N}.json")


def main():
    d = W.load(PATH, None)
    hard = d.setdefault("hardened", {})
    t_run = time.time()
    for k in d["cells"]:
        if k in hard and hard[k].get("conclusive"):
            continue
        t0 = time.time()
        c = W.cq(Fraction(k))
        _, A = W.build(c, N, KIND)
        (r1, v1), (r2, _) = W.lowest_pairs(A, 2)
        if r1 > 0:
            shift = mp.nstr(mp.sqrt(mp.mpf(float(r1.mid())) * mp.mpf(float(r2.mid()))), 5)
        else:
            shift = "0"
        pb = W.ldl_prec(KIND, N)
        tb = None
        for _ in range(3):
            _, Ah = W.build(c, N, KIND, prec=pb)
            tb = W.temple_bracket(Ah, v1, shift)
            if tb["conclusive"]:
                break
            pb *= 2
        tb["ldl_prec"] = pb
        tb["elapsed_s"] = round(time.time() - t0, 2)
        hard[k] = tb
        W.save(PATH, d)
        print(f"{KIND} N={N} c={k:>7}: [{tb['lower'][:14] if tb['lower'] else None}, {tb['upper'][:14]}] "
              f"ldl {tb['ldl_inertia_at_shift']} concl={tb['conclusive']} [{time.time() - t_run:.0f}s]", flush=True)
    d["meta"]["hardened_all"] = all(h.get("conclusive") for h in hard.values()) and len(hard) == len(d["cells"])
    W.save(PATH, d)


if __name__ == "__main__":
    main()
