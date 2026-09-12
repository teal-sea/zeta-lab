"""Finite checks for SHARP_EXPONENT.md.

Two measurements at fixed N, neither a test of an asymptotic statement.

(1) The decay in theta of I_beta(theta) = int_1^N t^(beta-1) e(t theta) dt for a real
    beta = 1 - kappa/sqrt(log N): the document uses |I_beta(theta)| <= C N^beta / (N|theta|)
    for 1/N <= |theta| <= R/N, with C absorbing (N|theta|)^(1-beta) <= e^(kappa sigma).
    Reports the largest observed C over a grid of theta.
(2) The per-arc integral behind the ceiling: int over |theta| <= R/(rN) of
    |K_N(theta)|^2 |I_beta(theta)|^2 dtheta against N^(2 beta + 1), for several r and R,
    showing no growth in R (the old bookkeeping charged a factor R here).

Run from the repository root with .venv/bin/python. Writes
results_sharp_exponent_probe.json next to this file. A few seconds.
"""
from __future__ import annotations

import json
import math
import os
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "results_sharp_exponent_probe.json")

_GL_X, _GL_W = np.polynomial.legendre.leggauss(24)


def I_beta(beta: float, theta: float, N: int) -> complex:
    n_osc = abs(theta) * (N - 1)
    panels = int(4 * n_osc) + 64
    edges = np.exp(np.linspace(0.0, math.log(N), panels + 1))
    a = edges[:-1][:, None]
    b = edges[1:][:, None]
    t = 0.5 * (b - a) * _GL_X[None, :] + 0.5 * (b + a)
    w = 0.5 * (b - a) * _GL_W[None, :]
    return complex(np.sum(w * np.exp((beta - 1) * np.log(t) + 2j * math.pi * theta * t)))


def K_N(theta: float, N: int) -> complex:
    if abs(theta) < 1e-15:
        return complex(N)
    return (np.exp(2j * math.pi * theta * (N + 1)) - np.exp(2j * math.pi * theta)) / (
        np.exp(2j * math.pi * theta) - 1.0
    )


def main():
    t0 = time.time()
    out = {}
    # ------------------------------------------------------------- (1) decay of I_beta
    rows = []
    for N in (10**4, 10**6):
        ell = math.log(N)
        for kappa in (0.1, 0.3, 1.0):
            beta = 1 - kappa / math.sqrt(ell)
            worst = 0.0
            for Ntheta in np.geomspace(1.0, 200.0, 40):
                theta = Ntheta / N
                val = abs(I_beta(beta, theta, N))
                C = val / (N**beta / Ntheta)
                worst = max(worst, C)
            rows.append({"N": N, "kappa": kappa, "beta": beta,
                         "worst_C_in_abs_I_le_C_Nbeta_over_Ntheta": worst,
                         "e_kappa_sigma_at_sigma_log200_over_sqrt_ell": math.exp(kappa * math.log(200) / math.sqrt(ell)),
                         "abs_I_at_theta_0": abs(I_beta(beta, 0.0, N)), "Nbeta": N**beta})
    out["decay_of_I_beta"] = rows

    # ------------------------------------------------------ (2) per-arc integral, no R growth
    N = 10**4
    ell = math.log(N)
    arc_rows = []
    for kappa in (0.3, 1.0):
        beta = 1 - kappa / math.sqrt(ell)
        for r in (1, 3, 7):
            for R in (5, 20, 80):
                half = R / (r * N)
                # composite Gauss-Legendre in theta with fine panels near 0
                edges = np.concatenate([-np.geomspace(half, 1e-3 / N, 60), [0.0], np.geomspace(1e-3 / N, half, 60)])
                total = 0.0
                for a_, b_ in zip(edges[:-1], edges[1:]):
                    x = 0.5 * (b_ - a_) * _GL_X + 0.5 * (b_ + a_)
                    w = 0.5 * (b_ - a_) * _GL_W
                    vals = np.array([abs(K_N(th, N)) ** 2 * abs(I_beta(beta, th, N)) ** 2 for th in x])
                    total += float(np.sum(w * vals))
                arc_rows.append({"kappa": kappa, "beta": beta, "r": r, "R": R,
                                 "int_arc_K2_I2": total, "over_N_2beta_plus_1": total / N ** (2 * beta + 1)})
    out["per_arc_integral"] = {"N": N, "rows": arc_rows}
    out["elapsed_s"] = time.time() - t0
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    print(json.dumps(out, indent=1, default=float))


if __name__ == "__main__":
    main()
