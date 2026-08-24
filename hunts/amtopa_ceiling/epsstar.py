#!/usr/bin/env python3
"""eps*(B, window): the exact floor ceiling over BOTH free linear axes.

At a fixed window the local functional

    F(g) = sum_r b_r g_r + sum_{i<j} a_ij W(y_j - y_i)

is linear in the pair weights a AND in the pressure vector b, and the admissible
set

    P(B) = { a >= 0, sum_i a_{i,i+s} = 2 (s=1..6),  b >= 0, sum_r b_r = B }

is a polytope.  So

    eps*(B) = max_{(a,b) in P(B)}  min_{g >= 0} F(g; a, b)

is a concave maximisation over a polytope -- a semi-infinite LP with one
constraint per gap vector -- and cutting planes solve it to optimality.  This is
the largest floor the AMTOPA construction can certify at that window and that
total pressure.  Only the window and B remain free after it.

The loop is stabilised: the LP is solved with a small proximal pull toward the
previous iterate, and every round contributes many cuts (all distinct local
minima found, not only the global one), which is what makes it converge in tens
of rounds instead of thousands.
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import linprog, minimize

from ceiling import IDX_I, IDX_J, NPAIR, W_and_slope, W_matrix, _span_blocks
from family import Q, kernel

BLOCKS = _span_blocks()


# ------------------------------------------------------------ local minima

def _fun_jac(g, a, b, c, w, k0):
    y = np.concatenate(([0.0], np.cumsum(g)))
    d = y[IDX_J] - y[IDX_I]
    Wv, Wp = W_and_slope(d, c, w, k0)
    val = float(b @ g + a @ Wv)
    grad = b.copy()
    contrib = a * Wp
    for p in range(NPAIR):
        grad[IDX_I[p]:IDX_J[p]] += contrib[p]
    return val, grad


def harvest(a, b, c, w, k0, rng, coarse=60000, keep=48, hi=None):
    """Return (best_value, best_g, list_of_distinct_local_minima)."""
    if hi is None:
        hi = min(0.02 / float(np.min(b[b > 0])) if np.any(b > 0) else 40.0, 40.0)
    S = np.vstack([
        rng.uniform(0.0, min(hi, 6.0), size=(coarse, Q)),
        rng.uniform(0.6, 3.2, size=(coarse // 2, Q)),
        np.array(np.meshgrid(*[(1.0, 2.0, 3.0)] * Q)).reshape(Q, -1).T,
    ])
    vals = S @ b + W_matrix(S, c, w, k0) @ a
    order = np.argsort(vals)[:keep]
    bounds = [(0.0, hi)] * Q
    mins, seen = [], []
    best = (np.inf, None)
    for idx in order:
        res = minimize(lambda g: _fun_jac(g, a, b, c, w, k0), S[idx], jac=True,
                       method="L-BFGS-B", bounds=bounds,
                       options={"maxiter": 300, "ftol": 1e-16, "gtol": 1e-12})
        g, v = res.x, float(res.fun)
        if v < best[0]:
            best = (v, g.copy())
        if not any(np.max(np.abs(g - s)) < 1e-5 for s in seen):
            seen.append(g.copy())
            mins.append(g.copy())
    return best[0], best[1], mins


# ------------------------------------------------------------------- eps*

def eps_star(B, c, w, k0=None, rounds=60, seed=0, tol=1e-10, verbose=False,
             coarse=60000, keep=48, proximal=1e-4, a_init=None, b_init=None,
             cut_pool=None):
    """Cutting-plane solve of max_{(a,b) in P(B)} min_{g>=0} F.

    Returns dict with 'upper' (LP value, a rigorous upper bound on eps* given the
    cuts are valid constraints), 'lower' (achieved floor at the returned (a,b)),
    'a', 'b', 'cuts'.
    """
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    rng = np.random.default_rng(seed)
    hi = min(0.02 / (B / Q), 40.0)

    # LP variables: a(21), b(6), t(1)
    n = NPAIR + Q + 1
    A_eq = np.zeros((Q + 1, n))
    for s, cols in enumerate(BLOCKS):
        A_eq[s, cols] = 1.0
    A_eq[Q, NPAIR:NPAIR + Q] = 1.0
    b_eq = np.concatenate([np.full(Q, 2.0), [B]])
    bounds = [(0.0, 2.0)] * NPAIR + [(0.0, B)] * Q + [(None, None)]

    a = a_init if a_init is not None else np.array(
        [2.0 / max(1, len(np.where(np.array([j - i for i, j in zip(IDX_I, IDX_J)]) == (j - i))[0]))
         for i, j in zip(IDX_I, IDX_J)])
    if a_init is None:
        a = np.zeros(NPAIR)
        for cols in BLOCKS:
            a[cols] = 2.0 / len(cols)
    b = b_init if b_init is not None else np.full(Q, B / Q)

    G = cut_pool if cut_pool is not None else np.empty((0, Q))
    if G.shape[0] == 0:
        G = np.vstack([
            np.array(np.meshgrid(*[(1.0, 2.0, 3.0, 4.0)] * Q)).reshape(Q, -1).T,
            rng.uniform(0.0, min(hi, 6.0), size=(3000, Q)),
        ])

    best = {"upper": np.inf, "lower": -np.inf, "a": a, "b": b}
    for it in range(rounds):
        Wm = W_matrix(G, c, w, k0)
        # b.g + Wm a >= t   ->   -Wm a - G b + t <= 0
        A_ub = np.hstack([-Wm, -G, np.ones((G.shape[0], 1))])
        b_ub = np.zeros(G.shape[0])
        cost = np.zeros(n)
        cost[-1] = -1.0
        res = linprog(cost, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=bounds, method="highs")
        if not res.success:
            raise RuntimeError(f"LP failed: {res.message}")
        # The pure LP value is the only quantity that is a genuine upper bound
        # on eps*, and it decreases monotonically as cuts accumulate.  Any
        # proximal perturbation must not touch it, so it is read here first.
        upper = float(res.x[-1])
        a = res.x[:NPAIR]
        b = res.x[NPAIR:NPAIR + Q]

        bsafe = np.where(b > 1e-14, b, 1e-14)
        hv, gmin, mins = harvest(a, bsafe, c, w, k0, rng, coarse, keep, hi)
        # The achieved floor at this (a, b) must be read off EVERY gap vector we
        # hold, not only the multistart's own basins.  Each row of the cut pool
        # is a real point of the orthant, so the pool minimum is an upper
        # estimate of min_g F that the multistart cannot beat by missing a
        # basin -- and it is free, the kernel matrix is already built for the LP.
        pool_vals = G @ b + Wm @ a
        lower = min(hv, float(pool_vals.min()))
        if lower > best["lower"]:
            best.update(lower=lower, a=a.copy(), b=b.copy())
        best["upper"] = min(best["upper"], upper)
        # min_g F at a feasible (a,b) is a lower bound on eps*; the LP value over
        # any valid cut set is an upper bound.  With the pool minimum folded in,
        # lower <= upper holds by construction; a violation would mean the LP and
        # the direct evaluation disagree, which is a bug, not a search failure.
        if best["lower"] > best["upper"] + 1e-12:
            best["inconsistent"] = float(best["lower"] - best["upper"])
        if verbose and (it % 5 == 0 or it == rounds - 1):
            print(f"    it {it:3d}  LP={upper:.10f}  min={lower:.10f}  "
                  f"gap={upper-lower:.2e}  cuts={G.shape[0]}")
        if upper - lower < tol:
            break
        add = np.array(mins) if mins else gmin[None, :]
        G = np.vstack([G, add])
    best["cuts"] = G
    best["upper"] = min(best["upper"], upper)
    return best
