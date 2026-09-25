"""Task B (theory handoff C2): zeta's pole-free form against the full form.

Theory worker's Corollary (hunts/weil_propagation/theory/RESULTS.md s2.6,
commit 7d9636b): with Q = Q° + P and P = 2<f, c>^2 rank one on the even
sector, interlacing gives mu_1(Q°) <= lambda_1(Q) <= mu_2(Q°) <= lambda_2(Q),
and even-sector positivity needs mu_2(Q°) >= 0 plus a pole-capacity condition.
The asked measurement: mu_2 of the pole-free even form against lambda_1,
lambda_2 of the full even form, c in [2, 60].

Per window c (step 1/2), band N, even sector, zeta:
  E  = full matrix (weil_trunc assembly), lambda_1, lambda_2 by inverse
       iteration (E is positive definite here; checked by ball LDL at 0);
  E° = E - W02 (the pole block, from the same assembly), mu_1 by shifted
       inverse iteration at -20, mu_2 = its eigenvalue of smallest magnitude;
       ball LDL^T of E° at 0 gives its number of negative eigenvalues.
Ball Rayleigh quotients (upper bounds) for all four; interlacing checked on
midpoints. Usage: zeta_pole.py N   (writes zeta_pole_N<N>.json)
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from flint import arb, arb_mat, ctx  # noqa: E402

N = int(sys.argv[1])
OUT = os.path.join(W.HERE, f"zeta_pole_N{N}.json")
PREC = 900 if N <= 128 else 1400
LDLP = W.ldl_prec("zeta", N)


def key(c: Fraction) -> str:
    return str(c.numerator) if c.denominator == 1 else f"{c.numerator}/{c.denominator}"


def main():
    d = W.load(OUT, {"meta": {"kind": "zeta", "N": N, "sector": "even", "prec": PREC, "ldl_prec": LDLP,
                              "grid": "c in [2, 60] step 1/2"}, "cells": {}})
    t_run = time.time()
    c = Fraction(2)
    while c <= 60:
        k = key(c)
        if k not in d["cells"]:
            t0 = time.time()
            bt, E = W.build(W.cq(c), N, "zeta", prec=PREC)
            ctx.prec = PREC
            pole = W.components(bt, check=False)["pole"]
            E0 = E - pole
            (l1, v1), (l2, _) = W.lowest_pairs(E, 2)
            m1, _ = W.eig_near(E0, W.approx_spectrum(E0, 1)[0], iters=8)  # a fixed shift at -20 converged to the wrong eigenvalue at small c
            (m2, w2), = W.lowest_pairs(E0, 1)
            _, Eh = W.build(W.cq(c), N, "zeta", prec=LDLP)
            ctx.prec = LDLP
            poleh = W.components(W.EN.BallTruncation(W.cq(c), N, kind="zeta", prec=LDLP), check=False)["pole"]
            inE = W.ldl_signs(Eh)
            inE0 = W.ldl_signs(Eh - poleh)
            f = lambda x: float(x.mid())  # noqa: E731
            rec = {
                "c": k, "c_float": float(c),
                "lam1": W.as_str(l1, 12), "lam2": W.as_str(l2, 8),
                "mu1": W.as_str(m1, 10), "mu2": W.as_str(m2, 10),
                "inertia_full_at_0": list(inE), "inertia_polefree_at_0": list(inE0),
                "mu2_over_lam2": f(m2 / l2), "mu2_over_lam1": f(m2 / l1),
                "interlacing_mid": bool(f(m1) <= f(l1) <= f(m2) <= f(l2)),
                "elapsed_s": round(time.time() - t0, 2),
            }
            d["cells"][k] = rec
            W.save(OUT, d)
            print(f"N={N} c={k:>5}: lam1 {rec['lam1'][:14]} lam2 {rec['lam2'][:12]} mu1 {rec['mu1'][:10]} "
                  f"mu2 {rec['mu2'][:14]} mu2/lam2 {rec['mu2_over_lam2']:.4f} inter {rec['interlacing_mid']} "
                  f"inertia {inE0} [{time.time() - t_run:.0f}s]", flush=True)
        c += Fraction(1, 2)


if __name__ == "__main__":
    main()
