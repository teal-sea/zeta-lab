#!/usr/bin/env python3
"""Step 4: the window axis, which is where the whole family's ceiling lives.

The window is the only free parameter that moves H, and H is worth 1.0076 of
bound per unit while the floor eps is worth only 0.643.  The 2*j*pi harmonics
cannot raise H -- probe_window.py shows they are exactly M-orthogonal to the
sqrt(2) term, so H_max over the whole coefficient space is the pure sqrt(2)
value 0.6725007036794117 -- so every harmonic is H spent to buy floor.  The
break-even is 1.5674 units of floor per unit of window constant.  This step asks
what the best available exchange rate is.

Search strategy.  eps*(B, c) costs about a second; a 17-dimensional search cannot
afford it.  Instead a fixed pool of gap vectors gives an LP upper bound on
eps*(B, c) in tens of milliseconds (sweep.lp_upper), the search maximises that
upper bound, and each epoch the pool is refreshed at the winners with their real
basins.  Maximising an upper bound and then tightening it at the argmax is a
search for the ceiling FROM ABOVE: it cannot miss a good window, it can only
propose one that the refreshed pool then knocks down.

Constraint carried from their own check_window.py: v(s) > 0 on [-1/2, 1/2].
"""
from __future__ import annotations

import json
import os
import sys
import time

import numpy as np
from scipy.optimize import differential_evolution

from ceiling import family_bound
from epsstar import eps_star
from family import H_of, amtopa_b, amtopa_coeffs, frequencies, kernel, window_matrices
from sweep import Pool, ceiling_upper, lp_upper, refresh_pool

AMTOPA_BOUND = 0.6734164909714992949
NTERM = 17
SGRID = np.linspace(-0.5, 0.5, 1201)


def window_min(c, w):
    """min of v(s) over [-1/2,1/2] on a fine grid (their positivity constraint)."""
    return float((np.cos(np.outer(SGRID, w)) @ c).min())


def make_objective(w, u, M, pool, B_fixed=None, B0=None):
    def obj(z):
        c = np.empty(NTERM)
        c[0] = 1.0
        c[1:] = z[:NTERM - 1]
        B = B_fixed if B_fixed is not None else B0 * np.exp(z[NTERM - 1])
        if window_min(c, w) <= 1e-3:
            return 1.0            # infeasible window: positivity fails
        v = ceiling_upper(c, w, u, M, B, pool)
        return -v if np.isfinite(v) else 1.0
    return obj


def main() -> int:
    epochs = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    maxiter = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    c0 = amtopa_coeffs()
    w = frequencies(NTERM)
    u, _, _, M = window_matrices(w)
    B0 = float(amtopa_b().sum())
    shard = int(os.environ.get("ZETA_WINDOW_SEED", "0"))
    rng = np.random.default_rng(2026 + 1000 * shard)

    pool = None
    for p in ("artifacts/cut_pool.npy", "/tmp/amtopa/pool_headroom.npy",
              "/tmp/amtopa/pool_bsweep.npy"):
        if os.path.exists(p):
            pool = Pool(np.load(p))
            break
    if pool is None:
        pool = Pool(np.array(np.meshgrid(*[(1.0, 2.0, 3.0)] * 6)).reshape(6, -1).T)
    pool.dedupe(cap=1800)
    print(f"pool starts at {pool.G.shape[0]} cuts")

    # -- reference points -----------------------------------------------
    e0 = np.zeros(NTERM)
    e0[0] = 1.0
    print("\n-- the two ends of the window trade --")
    for name, cc in (("pure sqrt(2)", e0), ("AMTOPA 17-term", c0)):
        H = H_of(cc, u, M)
        refresh_pool(cc, w, B0, pool, rng, rounds=4)
        r = eps_star(B0, cc, w, rounds=20, seed=5, cut_pool=pool.G.copy())
        pool.add(r["cuts"][-400:])
        pool.dedupe(cap=1800)
        v, m = family_bound(H, r["lower"], B0)
        print(f"  {name:<16} H={H:.16f}  eps*={r['lower']:.10f}  "
              f"bound={v:.16f} (m={m})")

    best = {"bound": -np.inf}
    lb = np.concatenate([np.full(NTERM - 1, -0.06), [-0.7]])
    ub = np.concatenate([np.full(NTERM - 1, 0.06), [0.7]])
    x0 = np.concatenate([c0[1:], [0.0]])

    t0 = time.time()
    for ep in range(epochs):
        obj = make_objective(w, u, M, pool, B0=B0)
        res = differential_evolution(
            obj, list(zip(lb, ub)), seed=100 + ep + 977 * shard, maxiter=maxiter,
            popsize=18, tol=1e-12, mutation=(0.35, 1.0), recombination=0.85,
            init="sobol", polish=True, x0=x0 if ep == 0 else best.get("z", x0),
            workers=1, updating="immediate")
        z = res.x
        c = np.empty(NTERM)
        c[0] = 1.0
        c[1:] = z[:NTERM - 1]
        B = B0 * np.exp(z[NTERM - 1])
        surrogate = -res.fun
        # tighten: give this window its real basins, then solve eps* properly
        refresh_pool(c, w, B, pool, rng, rounds=6)
        r = eps_star(B, c, w, rounds=24, seed=31 + ep + 977 * shard,
                     cut_pool=pool.G.copy())
        pool.add(r["cuts"][-500:])
        n = pool.dedupe(cap=1800)
        H = H_of(c, u, M)
        v, m = family_bound(H, r["lower"], B)
        print(f"\nepoch {ep}: surrogate {surrogate:.16f} -> true {v:.16f} (m={m})")
        print(f"  H={H:.16f}  B/B0={B/B0:.4f}  eps*={r['lower']:.10f} "
              f"[LPup {r['upper']:.10f}]  vmin={window_min(c,w):.4f}  pool={n}")
        print(f"  vs AMTOPA {v - AMTOPA_BOUND:+.4e}")
        if v > best["bound"]:
            best = {"bound": v, "m": m, "H": H, "B": B, "eps": r["lower"],
                    "eps_up": r["upper"], "c": c.tolist(), "z": z,
                    "a": r["a"].tolist(), "b": r["b"].tolist()}
        x0 = z
    print(f"\nelapsed {time.time()-t0:.1f}s")

    print("\n== best window found ==")
    print(f"  bound {best['bound']:.19f} at m={best['m']}")
    print(f"  AMTOPA {AMTOPA_BOUND:.19f}")
    print(f"  delta  {best['bound'] - AMTOPA_BOUND:+.6e}")
    print(f"  H={best['H']:.18f}  B={best['B']:.12f} (B/B0={best['B']/B0:.5f})")
    print(f"  eps*={best['eps']:.12f}")
    out = {k: v for k, v in best.items() if k != "z"}
    with open(f"window_search_{shard}.json", "w") as fh:
        json.dump(out, fh, indent=2)
    os.makedirs("/tmp/amtopa", exist_ok=True)
    np.save("/tmp/amtopa/pool_window.npy", pool.G)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
