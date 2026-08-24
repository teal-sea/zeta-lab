#!/usr/bin/env python3
"""Step 3: the saturation curve on the pressure axis, at AMTOPA's own window.

Total pressure B is the one scalar that trades directly against the bound: it
costs d(bound)/dB per unit and buys d(eps*)/dB * d(bound)/deps.  The break-even
slope is printed by step2.  This sweep measures the real d(eps*)/dB curve and
locates the B at which the family stops paying.

Unit cost, measured before the run: one eps* solve is ~1.1 s per cutting-plane
round and converges in <= 20 rounds warm, so ~12 s per B value; 17 values is
about 3.5 minutes.
"""
from __future__ import annotations

import json
import os
import time

import numpy as np

from ceiling import family_bound
from epsstar import eps_star
from family import H_of, amtopa_b, amtopa_coeffs, frequencies, kernel, window_matrices

AMTOPA_BOUND = 0.6734164909714992949


def main() -> int:
    c = amtopa_coeffs()
    w = frequencies(len(c))
    u, _, _, M = window_matrices(w)
    H = H_of(c, u, M)
    k0 = float(kernel(0.0, c, w)[0])
    B0 = float(amtopa_b().sum())

    pool = None
    for p in ("artifacts/cut_pool.npy", "/tmp/amtopa/pool_headroom.npy",
              "/tmp/amtopa/pool_bsweep.npy", "/tmp/amtopa/eps_star_cuts.npy"):
        try:
            pool = np.load(p)
            break
        except OSError:
            continue

    factors = [0.0, 0.25, 0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 1.75, 2.0,
               2.5, 3.0, 4.0, 6.0]
    rows = []
    print(f"H = {H:.18f}   B0 = {B0:.12f}")
    print(f"{'B/B0':>6} {'B':>12} {'eps*_lo':>14} {'eps*_up':>14} "
          f"{'bound':>20} {'m':>5} {'vs AMTOPA':>12}")
    t0 = time.time()
    for f in factors:
        B = B0 * f
        if B <= 0:
            # no pressure at all: F has no linear term, and W -> 0 at large gaps
            e_lo = e_up = 0.0
            v, m = -np.inf, 0
            print(f"{f:>6.2f} {B:>12.8f} {'0':>14} {'0':>14} "
                  f"{'-inf (no floor)':>20} {'-':>5} {'-':>12}")
            rows.append(dict(factor=f, B=B, eps_lo=0.0, eps_up=0.0,
                             bound=None, m=None))
            continue
        r = eps_star(B, c, w, k0, rounds=14, seed=11,
                     cut_pool=pool.copy() if pool is not None else None)
        pool = r["cuts"]
        v, m = family_bound(H, r["lower"], B)
        print(f"{f:>6.2f} {B:>12.8f} {r['lower']:>14.10f} {r['upper']:>14.10f} "
              f"{v:>20.16f} {m:>5d} {v - AMTOPA_BOUND:>+12.3e}")
        rows.append(dict(factor=f, B=B, eps_lo=r["lower"], eps_up=r["upper"],
                         bound=v, m=m,
                         missed=r.get("harvest_missed")))
    print(f"\nelapsed {time.time()-t0:.1f} s")

    print("\n-- marginal floor per unit pressure, d(eps*)/dB, vs break-even 1.4998 --")
    ok = [r for r in rows if r["bound"] is not None]
    for p, q in zip(ok, ok[1:]):
        slope = (q["eps_lo"] - p["eps_lo"]) / (q["B"] - p["B"])
        flag = "pays" if slope > 1.4998 else "COSTS"
        print(f"  B/B0 {p['factor']:>5.2f} -> {q['factor']:>5.2f}: "
              f"d(eps*)/dB = {slope:>8.4f}   {flag}")

    with open("bsweep.json", "w") as fh:
        json.dump(rows, fh, indent=2)
    os.makedirs("/tmp/amtopa", exist_ok=True)
    np.save("/tmp/amtopa/pool_bsweep.npy", pool)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
