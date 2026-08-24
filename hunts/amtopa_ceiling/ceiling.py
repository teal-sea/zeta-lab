#!/usr/bin/env python3
"""The ceiling of the AMTOPA exact-pressure family.

Three instruments, in increasing tightness:

1. ``eps_diag``            (in family.py) a one-point, pair-weight-free cap on
                           the acceptable floor.
2. ``eps_star``            the exact optimum of the floor over the whole
                           pair-weight polytope at a fixed window and pressure
                           vector, by cutting-plane linear programming.  At
                           convergence this is the *largest floor the family can
                           have* at that window and pressure -- not an estimate.
3. ``family_bound``        the assembled proportion at (H, eps, B), maximised
                           over the block length m.

The outer problem -- sup over window coefficients c and pressure vector b -- is
then a 22-dimensional smooth maximisation whose objective is instrument 3
composed with instrument 2.

Why the pair-weight axis is exactly solvable.  eps(a) = min_{g>=0} F(g;a,b) is a
minimum of functions linear in a, hence concave in a, and the admissible set

    P = { a >= 0 : sum_i a_{i,i+s} = 2 for s = 1..6 }

is a product of six scaled simplices.  So max_{a in P} eps(a) is a concave
maximisation and equals the value of the semi-infinite LP

    max t  s.t.  b.g + sum_p a_p W(d_p(g)) >= t  for all g >= 0,  a in P,

which cutting planes solve to optimality: each round solves the LP over a finite
set of gap vectors (an upper bound on the true value), then finds the global
minimiser of F at the LP's own a (a lower bound), and adds it as a cut.
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import linprog, minimize

from family import (PAIR_LIST, PAIR_SPAN, Q, kernel, frequencies)

IDX_I = np.array([i for i, _ in PAIR_LIST])
IDX_J = np.array([j for _, j in PAIR_LIST])
NPAIR = len(PAIR_LIST)


# ------------------------------------------------------------ kernel + slope

def _sinc(z):
    return np.sinc(np.asarray(z) / np.pi)


def _dsinc(z):
    """d/dz sin(z)/z = (z cos z - sin z)/z^2, stable at 0."""
    z = np.asarray(z, dtype=float)
    out = np.empty_like(z)
    small = np.abs(z) < 1e-4
    zs = z[small]
    out[small] = -zs / 3.0 + zs**3 / 30.0
    zb = z[~small]
    out[~small] = (zb * np.cos(zb) - np.sin(zb)) / zb**2
    return out


def kernel_and_slope(x, c, w):
    x = np.atleast_1d(np.asarray(x, dtype=float))
    half = w / 2.0
    lo = half[None, :] - np.pi * x[:, None]
    hi = half[None, :] + np.pi * x[:, None]
    k = 0.5 * ((_sinc(lo) + _sinc(hi)) * c[None, :]).sum(axis=1)
    kp = 0.5 * np.pi * ((_dsinc(hi) - _dsinc(lo)) * c[None, :]).sum(axis=1)
    return k, kp


def W_and_slope(x, c, w, k0):
    k, kp = kernel_and_slope(x, c, w)
    return (k / k0) ** 2, 2.0 * k * kp / (k0 * k0)


def W_matrix(G, c, w, k0, chunk=20000):
    """G is (N,Q).  Returns (N, 21) matrix of W at every pair distance.

    Chunked on purpose: the intermediate is N x 21 x len(w) doubles, so an
    unchunked call at N = 4e5 with a 17-term window allocates about 1.1 GB.
    That allocation is what killed the first attempt at this hunt's candidate
    generation on the authoring host.
    """
    G = np.atleast_2d(np.asarray(G, dtype=float))
    out = np.empty((G.shape[0], len(IDX_I)))
    for s in range(0, G.shape[0], chunk):
        blk = G[s:s + chunk]
        y = np.concatenate([np.zeros((blk.shape[0], 1)), np.cumsum(blk, axis=1)], axis=1)
        d = y[:, IDX_J] - y[:, IDX_I]
        k, _ = kernel_and_slope(d.ravel(), c, w)
        out[s:s + chunk] = ((k / k0) ** 2).reshape(d.shape)
    return out


# ---------------------------------------------------------------- global min

def _grad_F(g, a, b, c, w, k0):
    y = np.concatenate(([0.0], np.cumsum(g)))
    d = y[IDX_J] - y[IDX_I]
    Wv, Wp = W_and_slope(d, c, w, k0)
    val = float(b @ g + a @ Wv)
    grad = b.copy()
    contrib = a * Wp
    for p in range(NPAIR):
        grad[IDX_I[p]:IDX_J[p]] += contrib[p]
    return val, grad


def global_min_F(a, b, c, w, k0=None, coarse=200000, keep=140, seed=0,
                 lattice=(1.0, 2.0, 3.0, 4.0, 5.0)):
    """Apparent global minimum of F over the nonnegative orthant.

    Not rigorous: this is a float minimiser, exactly the status AMTOPA give
    their own 'observed floating minimum'.  The box is the one their verifier
    uses, gap <= target/min(b), outside which the pressure term alone exceeds
    any target of interest.
    """
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    rng = np.random.default_rng(seed)
    hi = 0.02 / float(np.min(b))          # generous: >> any target we consider
    hi = min(hi, 40.0)

    starts = [np.array(np.meshgrid(*[lattice] * Q)).reshape(Q, -1).T]
    starts.append(rng.uniform(0.0, min(hi, 8.0), size=(coarse, Q)))
    starts.append(rng.uniform(0.0, 3.0, size=(coarse // 2, Q)))
    S = np.vstack(starts)

    vals = S @ b + W_matrix(S, c, w, k0) @ a
    order = np.argsort(vals)[:keep]
    best_val = float(vals[order[0]])
    best_g = S[order[0]].copy()

    bounds = [(0.0, hi)] * Q
    for idx in order:
        g0 = S[idx]
        res = minimize(lambda g: _grad_F(g, a, b, c, w, k0), g0, jac=True,
                       method="L-BFGS-B", bounds=bounds,
                       options={"maxiter": 400, "ftol": 1e-16, "gtol": 1e-12})
        if res.fun < best_val:
            best_val = float(res.fun)
            best_g = res.x.copy()
    return best_val, best_g


# ------------------------------------------------------- pair-weight optimum

def _span_blocks():
    """Column index lists, one per span."""
    return [np.where(PAIR_SPAN == s)[0] for s in range(1, Q + 1)]


def eps_star(b, c, w, k0=None, rounds=24, seed=0, verbose=False,
             coarse=120000, keep=80):
    """max over the pair-weight polytope of min over the orthant of F.

    Returns (value, a_opt, lower_bracket, cuts).  ``value`` is the LP optimum
    over the accumulated cut set, an UPPER bound on the family's floor at this
    (b, c); ``lower_bracket`` is the true global minimum of F at ``a_opt``, a
    LOWER bound.  They meet at convergence.
    """
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    blocks = _span_blocks()
    rng = np.random.default_rng(seed)

    hi = min(0.02 / float(np.min(b)), 40.0)
    G = np.vstack([
        np.array(np.meshgrid(*[(1.0, 2.0, 3.0, 4.0)] * Q)).reshape(Q, -1).T,
        rng.uniform(0.0, min(hi, 8.0), size=(4000, Q)),
    ])

    # LP variables: [a (21), t (1)].  maximise t.
    n = NPAIR + 1
    cost = np.zeros(n)
    cost[-1] = -1.0
    A_eq = np.zeros((Q, n))
    for s, cols in enumerate(blocks):
        A_eq[s, cols] = 1.0
    b_eq = np.full(Q, 2.0)
    bounds = [(0.0, 2.0)] * NPAIR + [(None, None)]

    a_opt = None
    value = np.inf
    lower = -np.inf
    for it in range(rounds):
        Wm = W_matrix(G, c, w, k0)
        lin = G @ b
        # constraint:  -(Wm a) + t <= lin      i.e.   Wm a - t >= -lin  ->  b.g + Wm a >= t
        A_ub = np.hstack([-Wm, np.ones((Wm.shape[0], 1))])
        res = linprog(cost, A_ub=A_ub, b_ub=lin, A_eq=A_eq, b_eq=b_eq,
                      bounds=bounds, method="highs")
        if not res.success:
            raise RuntimeError(f"LP failed: {res.message}")
        a_opt = res.x[:NPAIR]
        value = float(res.x[-1])
        lower, gmin = global_min_F(a_opt, b, c, w, k0, coarse=coarse,
                                   keep=keep, seed=seed + it)
        if verbose:
            print(f"    cut {it:2d}: LP={value:.10f}  true_min={lower:.10f}  "
                  f"gap={value - lower:.2e}")
        if value - lower < 1e-11:
            break
        G = np.vstack([G, gmin[None, :]])
        # a few extra cuts near the found basin keep the LP honest
        G = np.vstack([G, np.clip(gmin[None, :] + rng.normal(0, 0.02, size=(6, Q)), 0, hi)])
    return value, a_opt, lower, G


# --------------------------------------------------------------- assembly

def family_bound(H, eps, B, q=Q, m_hi=4000):
    """max over m of the AMTOPA scalar-Gram projection.  Float, for search.

    When H <= B/eps the projection is decreasing in R and its maximum sits at
    small m, just under H; that is a real (bad) value, not an error, so it is
    returned rather than masked.
    """
    if eps <= 0:
        return -np.inf, 0
    m = np.arange(q + 1, m_hi + 1, dtype=float)
    A = eps * (m - q)
    thr = m / (m - 1.0)
    R = np.where(A <= thr, A, A / m + 2.0 * np.sqrt((m - 1.0) * A / m) - 1.0)
    den = m - R
    ok = den > 0
    v = np.where(ok, (m * H - B * R / eps) / np.where(ok, den, 1.0), -np.inf)
    k = int(np.argmax(v))
    return float(v[k]), int(m[k])
