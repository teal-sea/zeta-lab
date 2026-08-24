#!/usr/bin/env python3
"""Structure of the window axis: is H(v) maximised by the harmonics or by nothing?

H(v) = 2 - 1/c1 with c1 = (u.c)^2 / (c^T M c), so H is a Rayleigh quotient in the
17 window coefficients and its maximum over the whole coefficient space has the
closed form  H_max = 2 - 1/(u^T M^{-1} u), attained at c ~ M^{-1} u.

This probe asks what that maximiser is, and how much window constant each
harmonic actually costs.
"""
from __future__ import annotations

import numpy as np

from family import (H_of, amtopa_coeffs, frequencies, window_ceiling,
                    window_matrices)

np.set_printoptions(precision=6, suppress=False, linewidth=140)


def main() -> int:
    for n in (1, 2, 3, 7, 13, 17, 25):
        w = frequencies(n)
        u, Cm, Am, M = window_matrices(w)
        hmax, cbest = window_ceiling(u, M)
        eig = np.linalg.eigvalsh(M)
        print(f"nterms={n:3d}  H_max={hmax:.20f}  min_eig(M)={eig.min():.3e}  "
              f"|c_rest|_inf={np.abs(cbest[1:]).max() if n > 1 else 0.0:.3e}")

    print("\n-- the 17-term case in detail --")
    w = frequencies(17)
    u, Cm, Am, M = window_matrices(w)
    print(f"u = sinc(w_j/2):  u[0]={u[0]:.17f}  max|u[1:]|={np.abs(u[1:]).max():.3e}")
    print(f"M[0,1:] (coupling of sqrt(2) to the harmonics): max abs = "
          f"{np.abs(M[0,1:]).max():.3e}")
    print(f"M[0,1:] first six = {M[0,1:7]}")

    e0 = np.zeros(17)
    e0[0] = 1.0
    print(f"\nH(single sqrt(2) term)        = {H_of(e0, u, M):.20f}")
    print(f"Anthropic Theorem D  HD(1)    = 0.6725007036794116457")
    c = amtopa_coeffs()
    print(f"H(AMTOPA 17-term window)      = {H_of(c, u, M):.20f}")
    print(f"AMTOPA give up                  {H_of(e0,u,M) - H_of(c,u,M):.6e} of window constant")

    print("\n-- cost of switching on one harmonic at a time, from the pure sqrt(2) window --")
    for j in (1, 2, 3, 8, 16):
        for amp in (1e-3, 1e-2):
            cc = e0.copy()
            cc[j] = amp
            print(f"  c_{j:2d} = {amp:<7g}  H = {H_of(cc, u, M):.18f}  "
                  f"dH = {H_of(cc,u,M) - H_of(e0,u,M):+.3e}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
