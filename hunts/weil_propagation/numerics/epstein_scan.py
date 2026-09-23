"""Task A (theory handoff C2): the Epstein (1,1,6) window floor on c in [2, 48].

zeta_Q for Q = x^2 + xy + 6y^2 (discriminant -23, class number 3) has a pole,
off-line zeros (Davenport-Heilbronn), a Gamma(s) factor with positive Levy
density, and Lambda_Q(n) >= 0 for every n <= 47 (first negative at n = 48,
checked against zeta.epstein.log_derivative_coefficients). So on every window
c < 48 it satisfies the hypotheses of the theory worker's candidate C2
("Markov + one pole"). If its form goes negative below 48, C2-type mechanisms
are refuted.

Per window c (step 1/2), band N, sector in {even, odd}:
  - ball LDL^T inertia at shift 0 (hardened sign: n_neg);
  - lambda_1, lambda_2 from the approximate spectrum, refined by shifted
    inverse iteration to an exact vector, ball Rayleigh quotient;
  - Temple bracket with an LDL^T at the midpoint shift (lambda_1 + lambda_2)/2;
  - localization of the ground vector: peak mode k and its frequency
    2 pi k / L, and the coefficient mass near the peak.
Usage: epstein_scan.py N [dedekind]   (writes epstein_N<N>.json, or
dedekind_N<N>.json for the control: the Dedekind zeta of Q(sqrt(-23)),
zeta(s) L(s, chi_-23), which has the SAME completion, pole and archimedean
block and a genuine Euler product, so under GRH its form is positive on every
window; a composition error in the shared blocks would show up there.)
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from flint import arb  # noqa: E402

N = int(sys.argv[1])
CONTROL = len(sys.argv) > 2 and sys.argv[2] == "dedekind"
FORM = "dedekind-23" if CONTROL else W.EPSTEIN_FORM
PREC = 400
OUT = os.path.join(W.HERE, f"{'dedekind' if CONTROL else 'epstein'}_N{N}.json")


def key(c: Fraction) -> str:
    return str(c.numerator) if c.denominator == 1 else f"{c.numerator}/{c.denominator}"


def sector_record(A, L):
    npos, nneg, concl = W.ldl_signs(A)
    l1, l2 = W.approx_spectrum(A, 2)
    r1, v1 = W.eig_near(A, l1)
    s = (l1 + l2) / 2
    tb = W.temple_bracket(A, v1, repr(s))
    mass = [float(v1[i, 0].mid()) ** 2 for i in range(v1.nrows())]
    k = max(range(len(mass)), key=lambda i: mass[i])
    near = sum(mass[max(0, k - 3):k + 4])
    return {
        "inertia_at_0": [npos, nneg, bool(concl)],
        "lam1_approx": l1, "lam2_approx": l2,
        "lam1_rq": W.as_str(r1, 14),
        "temple": {q: tb[q] for q in ("lower", "upper", "ldl_inertia_at_shift", "conclusive")},
        "peak_mode": k,
        "peak_freq": 2 * 3.141592653589793 * k / L,
        "mass_within_3_modes_of_peak": near,
    }


def main():
    d = W.load(OUT, {"meta": {"kind": "dedekind zeta Q(sqrt -23)" if CONTROL else "epstein (1,1,6)", "N": N, "prec": PREC,
                              "grid": "c in [2, 48] step 1/2"}, "cells": {}})
    t_run = time.time()
    c = Fraction(2)
    while c <= 48:
        k = key(c)
        if k not in d["cells"]:
            t0 = time.time()
            M = W.epstein_matrices(W.cq(c), N, PREC, form=FORM)
            L = float(c.numerator / c.denominator)
            import math
            L = math.log(L)
            rec = {"c": k, "c_float": float(c), "band_edge": 2 * math.pi * N / L}
            for sector in ("even", "odd"):
                rec[sector] = sector_record(M[sector], L)
            rec["elapsed_s"] = round(time.time() - t0, 2)
            d["cells"][k] = rec
            W.save(OUT, d)
            e, o = rec["even"], rec["odd"]
            print(f"N={N} c={k:>5}: even n_neg={e['inertia_at_0'][1]} lam1 {e['lam1_approx']:+.4e} peak {e['peak_freq']:.1f} | "
                  f"odd n_neg={o['inertia_at_0'][1]} lam1 {o['lam1_approx']:+.4e} peak {o['peak_freq']:.1f} "
                  f"[{time.time() - t_run:.0f}s]", flush=True)
        c += Fraction(1, 2)


if __name__ == "__main__":
    main()
