#!/usr/bin/env python3
"""Step 5: the two-sided bracket on eps*, redone after the minimiser fix.

Epistemics, stated once and carried through every number this prints:

  ``upper``  the LP optimum over the accumulated cut set.  Every cut is a real
             gap vector, so every LP row is a true constraint on the family,
             so this is a genuine UPPER bound on eps*(B, window) -- the largest
             floor the pair-weight polytope and the pressure simplex can have.
  ``lower``  the smallest value of F seen at a feasible (a, b), over the union
             of the cut pool and a multistart.  This is an ESTIMATE, exactly the
             status AMTOPA give their own "observed floating minimum": it is an
             upper estimate of min_g F, hence an optimistic floor.  It becomes a
             certificate only when their six-dimensional interval verifier
             accepts a rational target beneath it.

The gap between the two is what this hunt can honestly say the family has left.
"""
from __future__ import annotations

import json
import os
import sys
import time

import numpy as np

from ceiling import family_bound
from epsstar import eps_star
from family import (H_of, amtopa_a, amtopa_b, amtopa_coeffs, frequencies,
                    kernel, window_matrices, eps_diag)
from epsstar import harvest

AMTOPA_EPS = 79107 / 10000000
AMTOPA_FLOATMIN = 0.007911105155226424
AMTOPA_BOUND = 0.6734164909714992949
AMTOPA_H_FLOOR = 336094079 / 500000000


def load_pool():
    for p in ("artifacts/cut_pool.npy", "/tmp/amtopa/pool_bsweep.npy",
              "/tmp/amtopa/eps_star_cuts.npy"):
        try:
            return np.load(p)
        except OSError:
            continue
    return None


def main() -> int:
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    coarse = int(sys.argv[2]) if len(sys.argv) > 2 else 80000
    keep = int(sys.argv[3]) if len(sys.argv) > 3 else 80
    c = amtopa_coeffs()
    w = frequencies(len(c))
    u, _, _, M = window_matrices(w)
    H = H_of(c, u, M)
    k0 = float(kernel(0.0, c, w)[0])
    B0 = float(amtopa_b().sum())
    pool = load_pool()
    print(f"pool: {0 if pool is None else pool.shape[0]} cuts")

    # ---- their own point, evaluated against the pool -----------------------
    a0, b0 = amtopa_a(), amtopa_b()
    rng = np.random.default_rng(99)
    hv, g, _ = harvest(a0, b0, c, w, k0, rng, coarse=coarse, keep=keep)
    from ceiling import W_matrix
    pv = (pool @ b0 + W_matrix(pool, c, w, k0) @ a0).min() if pool is not None else np.inf
    theirs = min(hv, float(pv))
    print(f"\nAMTOPA's own (a,b): min F = {theirs:.15f}")
    print(f"  their published float minimum 0.007911105155226424  "
          f"(delta {theirs - AMTOPA_FLOATMIN:+.3e})")

    # ---- the polytope optimum at their window and their B ------------------
    t0 = time.time()
    r = eps_star(B0, c, w, k0, rounds=rounds, seed=2027,
                 cut_pool=pool.copy() if pool is not None else None,
                 coarse=coarse, keep=keep, verbose=True)
    print(f"  ({time.time()-t0:.0f}s, {r['cuts'].shape[0]} cuts)")
    print(f"\neps*(B0, their window) bracketed:")
    print(f"  lower (best point found) {r['lower']:.12f}")
    print(f"  upper (LP over cuts)     {r['upper']:.12f}")
    print(f"  AMTOPA achieve           {theirs:.12f}")
    print(f"  headroom on the floor, at most {r['upper'] - theirs:+.3e}")
    if "inconsistent" in r:
        print(f"  !! inconsistent by {r['inconsistent']:.3e}")

    v_lo, m_lo = family_bound(H, theirs, B0)
    v_hi, m_hi = family_bound(H, r["upper"], B0)
    v_mid, m_mid = family_bound(H, r["lower"], B0)
    print(f"\nassembled with the true H (not their conservative floor):")
    print(f"  at AMTOPA's floor      {v_lo:.16f}  (m={m_lo})")
    print(f"  at our best point      {v_mid:.16f}  (m={m_mid})")
    print(f"  at the LP upper bound  {v_hi:.16f}  (m={m_hi})")
    print(f"  AMTOPA headline (their conservative H floor) {AMTOPA_BOUND:.16f}")
    print(f"\n  CEILING of the (a,b) axes at this window and this B: "
          f"{v_hi:.16f}")
    print(f"  that is {v_hi - AMTOPA_BOUND:+.3e} against their headline")

    ed, _ = eps_diag(B0, c, w, k0=k0)
    print(f"\n  for scale, the one-point a-free cap eps_diag = {ed:.10f} "
          f"(loose by {ed - r['upper']:.2e})")

    os.makedirs("/tmp/amtopa", exist_ok=True)
    np.save("/tmp/amtopa/pool_headroom.npy", r["cuts"])
    np.save("/tmp/amtopa/hr_a.npy", r["a"])
    np.save("/tmp/amtopa/hr_b.npy", r["b"])
    with open("headroom.json", "w") as fh:
        json.dump({"H": H, "B0": B0, "amtopa_floor": theirs,
                   "eps_star_lower": r["lower"], "eps_star_upper": r["upper"],
                   "bound_at_amtopa_floor": v_lo,
                   "bound_at_lower": v_mid, "bound_at_upper": v_hi,
                   "amtopa_headline": AMTOPA_BOUND,
                   "eps_diag": ed, "cuts": int(r["cuts"].shape[0])}, fh, indent=2)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
