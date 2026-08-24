#!/usr/bin/env python3
"""Step 1 of the ceiling: how much is left on the PAIR-WEIGHT axis alone?

Hold AMTOPA's window and their exact pressure vector fixed.  Optimise the pair
weights over their own polytope.  Their 21 weights were found by a trust-region
LP against the final bound plus differential-evolution stress; this asks what
the polytope's true optimum is.
"""
from __future__ import annotations

import time

import numpy as np

from ceiling import eps_star, family_bound, global_min_F
from family import (amtopa_a, amtopa_b, amtopa_coeffs, frequencies, H_of,
                    kernel, window_matrices, eps_diag)

AMTOPA_H_FLOOR = 336094079 / 500000000
AMTOPA_EPS = 79107 / 10000000
AMTOPA_BOUND = 0.6734164909714992949


def main() -> int:
    c = amtopa_coeffs()
    w = frequencies(len(c))
    u, _, _, M = window_matrices(w)
    a0 = amtopa_a()
    b0 = amtopa_b()
    B0 = float(b0.sum())
    k0 = float(kernel(0.0, c, w)[0])
    H = H_of(c, u, M)

    print("== reference point ==")
    v, m = family_bound(AMTOPA_H_FLOOR, AMTOPA_EPS, B0)
    print(f"assembly at their published (H_floor, eps, B): {v:.19f} at m={m}")
    print(f"  their published headline                     {AMTOPA_BOUND:.19f}")

    t0 = time.time()
    lo0, g0 = global_min_F(a0, b0, c, w, k0, coarse=200000, keep=140, seed=1)
    t_unit = time.time() - t0
    print(f"\n-- one global_min_F unit: {t_unit:.1f} s --")
    print(f"true min of F at THEIR pair weights = {lo0:.15f}")
    print(f"  their observed floating minimum     0.007911105155226424")
    print(f"  argmin {np.round(g0, 9)}")
    print(f"  their basin (1.978079145369, 1.044055102239, 1.973013931233,")
    print(f"               1.045981098706, 1.974452906922, 1.042299648208)")

    ed, tstar = eps_diag(B0, c, w, k0=k0)
    print(f"\na-free equal-gap cap  eps_diag = {ed:.12f}")
    vd, md = family_bound(H, ed, B0)
    print(f"  assembling that cap gives      {vd:.16f} at m={md}")

    print(f"\n-- pair-weight polytope optimum at their window and pressure --")
    t0 = time.time()
    val, aopt, lower, G = eps_star(b0, c, w, k0, rounds=18, verbose=True,
                                   coarse=150000, keep=100)
    print(f"  elapsed {time.time()-t0:.1f} s, cuts held {G.shape[0]}")
    print(f"  eps* upper (LP)   = {val:.12f}")
    print(f"  eps* lower (true) = {lower:.12f}")
    print(f"  their accepted eps = {AMTOPA_EPS:.12f}")
    print(f"  their own float min = 0.007911105155226424")
    print(f"  headroom on the pair-weight axis: {lower - 0.007911105155226424:+.6e}")

    vb, mb = family_bound(H, lower, B0)
    print(f"\n  assembled at the polytope optimum: {vb:.19f} at m={mb}")
    print(f"  against their headline             {AMTOPA_BOUND:.19f}")
    print(f"  delta                              {vb - AMTOPA_BOUND:+.6e}")

    np.save("/tmp/amtopa/aopt_theirwindow.npy", aopt)
    print(f"\n  optimal a (rounded): {np.round(aopt, 6)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
