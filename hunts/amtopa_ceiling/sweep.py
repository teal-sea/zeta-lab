#!/usr/bin/env python3
"""Fast surrogate for the family ceiling, and the sweeps built on it.

The expensive object is eps*(B, c) -- a cutting-plane solve costing about a
second.  But for ANY window, an LP over a FIXED pool of gap vectors is a valid
upper bound on eps*(B, c), because every row of the pool is a real constraint
     b.g + sum_p a_p W(d_p(g)) >= t.
So with a pool assembled once (from every basin any window has produced), a
single LP solve gives an upper bound on eps* in tens of milliseconds, and

     ceiling_upper(c, B) = max_m assembly( H(c), lp_upper(c, B), B )

is an upper bound on everything the family can reach at that window and total
pressure.  Maximising that surrogate over the 16 free window coefficients and
over B is a search for the family ceiling FROM ABOVE; every candidate it likes
is then re-checked with the full cutting-plane solve and the true minimiser.
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import linprog

from ceiling import W_matrix, _span_blocks, family_bound
from epsstar import harvest
from family import Q, H_of, kernel, window_matrices

BLOCKS = _span_blocks()
NPAIR = 21


class Pool:
    """A growing set of gap vectors used as LP cuts."""

    def __init__(self, G: np.ndarray):
        self.G = np.asarray(G, dtype=float)

    def add(self, rows):
        rows = np.atleast_2d(np.asarray(rows, dtype=float))
        if rows.size:
            self.G = np.vstack([self.G, rows])

    def dedupe(self, tol=1e-6, cap=6000):
        G = np.round(self.G / tol).astype(np.int64)
        _, idx = np.unique(G, axis=0, return_index=True)
        self.G = self.G[np.sort(idx)]
        if self.G.shape[0] > cap:
            self.G = self.G[-cap:]
        return self.G.shape[0]


def _lp_pieces(B):
    n = NPAIR + Q + 1
    A_eq = np.zeros((Q + 1, n))
    for s, cols in enumerate(BLOCKS):
        A_eq[s, cols] = 1.0
    A_eq[Q, NPAIR:NPAIR + Q] = 1.0
    b_eq = np.concatenate([np.full(Q, 2.0), [B]])
    bounds = [(0.0, 2.0)] * NPAIR + [(0.0, B)] * Q + [(None, None)]
    cost = np.zeros(n)
    cost[-1] = -1.0
    return cost, A_eq, b_eq, bounds


def lp_upper(c, w, B, pool: Pool, k0=None, want_xy=False):
    """Upper bound on eps*(B, c) from the fixed cut pool."""
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    if not np.isfinite(k0) or abs(k0) < 1e-9:
        return (-np.inf, None, None) if want_xy else -np.inf
    G = pool.G
    Wm = W_matrix(G, c, w, k0)
    A_ub = np.hstack([-Wm, -G, np.ones((G.shape[0], 1))])
    b_ub = np.zeros(G.shape[0])
    cost, A_eq, b_eq, bounds = _lp_pieces(B)
    res = linprog(cost, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=bounds, method="highs")
    if not res.success:
        return (-np.inf, None, None) if want_xy else -np.inf
    val = float(res.x[-1])
    if want_xy:
        return val, res.x[:NPAIR], res.x[NPAIR:NPAIR + Q]
    return val


def ceiling_upper(c, w, u, M, B, pool: Pool):
    """Upper bound on the assembled proportion at this window and pressure."""
    k0 = float(kernel(0.0, c, w)[0])
    if abs(k0) < 1e-6:
        return -np.inf
    H = H_of(c, u, M)
    if not np.isfinite(H):
        return -np.inf
    e = lp_upper(c, w, B, pool, k0)
    if e <= 0:
        return -np.inf
    v, _ = family_bound(H, e, B)
    return v


def refresh_pool(c, w, B, pool: Pool, rng, rounds=6, coarse=40000, keep=32):
    """Add the basins this window actually has, so the surrogate stops lying."""
    k0 = float(kernel(0.0, c, w)[0])
    for _ in range(rounds):
        val, a, b = lp_upper(c, w, B, pool, k0, want_xy=True)
        if a is None:
            break
        bs = np.where(b > 1e-14, b, 1e-14)
        _, _, mins = harvest(a, bs, c, w, k0, rng, coarse=coarse, keep=keep,
                             hi=min(0.02 / (B / Q), 40.0))
        if not mins:
            break
        pool.add(np.array(mins))
    pool.dedupe()
    return pool
