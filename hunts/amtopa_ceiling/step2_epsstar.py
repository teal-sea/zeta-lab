#!/usr/bin/env python3
"""Step 2: converge eps*(B) at AMTOPA's own window, and read the shadow prices."""
from __future__ import annotations

import sys
import time

import numpy as np

from ceiling import family_bound
from epsstar import eps_star
from family import (H_of, amtopa_b, amtopa_coeffs, frequencies, kernel,
                    window_matrices)

AMTOPA_EPS = 79107 / 10000000
AMTOPA_FLOATMIN = 0.007911105155226424
AMTOPA_BOUND = 0.6734164909714992949
AMTOPA_H_FLOOR = 336094079 / 500000000


def main() -> int:
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    c = amtopa_coeffs()
    w = frequencies(len(c))
    u, _, _, M = window_matrices(w)
    H = H_of(c, u, M)
    k0 = float(kernel(0.0, c, w)[0])
    B0 = float(amtopa_b().sum())

    print(f"window = AMTOPA 17-term;  H = {H:.18f}")
    print(f"B0 = {B0:.18f} = 93/23000\n")

    t0 = time.time()
    r = eps_star(B0, c, w, k0, rounds=rounds, verbose=True, seed=7)
    dt = time.time() - t0
    print(f"\n  elapsed {dt:.1f}s over {rounds} rounds "
          f"({dt/max(rounds,1):.2f} s/round)")
    print(f"  eps*(B0) in [{r['lower']:.12f}, {r['upper']:.12f}]")
    print(f"  AMTOPA float min          {AMTOPA_FLOATMIN:.12f}")
    print(f"  AMTOPA accepted eps      {AMTOPA_EPS:.12f}")
    lo_v, lo_m = family_bound(H, r["lower"], B0)
    up_v, up_m = family_bound(H, r["upper"], B0)
    print(f"\n  assembled bracket [{lo_v:.16f} (m={lo_m}), {up_v:.16f} (m={up_m})]")
    print(f"  AMTOPA headline    {AMTOPA_BOUND:.16f}")

    np.save("/tmp/amtopa/eps_star_a.npy", r["a"])
    np.save("/tmp/amtopa/eps_star_b.npy", r["b"])
    np.save("/tmp/amtopa/eps_star_cuts.npy", r["cuts"])

    print("\n-- shadow prices of the assembly at their operating point --")
    base, m = family_bound(H, AMTOPA_EPS, B0)
    dh = 1e-7
    dH = (family_bound(H + dh, AMTOPA_EPS, B0)[0] - base) / dh
    de = (family_bound(H, AMTOPA_EPS + dh, B0)[0] - base) / dh
    dB = (family_bound(H, AMTOPA_EPS, B0 + dh)[0] - base) / dh
    print(f"  d(bound)/dH   = {dH:+.6f}")
    print(f"  d(bound)/deps = {de:+.6f}")
    print(f"  d(bound)/dB   = {dB:+.6f}")
    print(f"  break-even  d(eps)/dB  = {-dB/de:.6f}  "
          "(more pressure pays only above this)")
    print(f"  break-even  d(eps)/d(-H) = {dH/de:.6f}  "
          "(a harmonic pays only if it buys this much floor per unit of H)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
