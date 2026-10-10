"""Edge-amplitude probe: does d lambda / dL track the ground state's edge value?

The transport grid showed d lambda/dL ~ -kappa mu_0^2 with kappa = O(1),
where mu_0 = v_0 + sqrt2 sum_k v_k = sqrt(L) f_v(0) is the value of the
band-N ground state at the window's edge (f_v(0) = f_v(L) in this basis).
This script measures kappa = -(d lambda/dL) / mu_0^2 along N-ladders at a
few windows, for zeta and DH, to see whether kappa is an N-stable and
kind-independent number (a structural law) or a basis artifact.

Usage: edge.py KIND   (writes edge_<kind>.json, checkpoint per cell)
"""

from __future__ import annotations

import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402

KIND = sys.argv[1]
OUT = os.path.join(W.HERE, f"edge_{KIND}.json")
CS = {"dh": ["27/2", "41/2", "61/2", "63/2"], "zeta": ["27/2", "41/2", "61/2"]}[KIND]
NS = [32, 64, 96, 128, 192, 256]


def main():
    d = W.load(OUT, {"meta": {"kind": KIND, "sector": "even",
                              "kappa": "-(d lambda/dL)/mu0^2, HF derivative at fixed coefficients"},
                     "cells": {}})
    t_run = time.time()
    for cs in CS:
        for N in NS:
            k = f"{cs}|{N}"
            if k in d["cells"]:
                continue
            t0 = time.time()
            c = W.cq(Fraction(cs))
            _, A = W.build(c, N, KIND)
            (r1, v1), (r2, _) = W.lowest_pairs(A, 2)
            res = W.residual_norm(A, v1, r1)
            m0 = W.mu0(v1)
            hf = W.hf_derivative(c, N, KIND, v1)
            kappa = -hf["total"] / (m0 * m0)
            rec = {
                "c": cs, "N": N, "lam1": W.as_str(r1, 14), "lam2": W.as_str(r2, 6),
                "residual": res.str(3), "mu0": m0.str(12),
                "hf_total": hf["total"].str(12),
                "hf_parts": {n: hf[n].str(10) for n in ("pole", "arch", "prime") if n in hf},
                "kappa": kappa.str(8),
                "neg_dlogLam_dL": (-hf["total"] / r1).str(8),
                "hf_eps": f"2^-{hf['_eps_pow2']}", "hf_prec": hf["_prec"],
                "elapsed_s": round(time.time() - t0, 1),
            }
            d["cells"][k] = rec
            W.save(OUT, d)
            print(f"{KIND} c={cs} N={N}: lam {rec['lam1'][:20]} mu0 {rec['mu0'][:16]} "
                  f"kappa {rec['kappa'][:14]} [{rec['elapsed_s']}s, total {time.time() - t_run:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
