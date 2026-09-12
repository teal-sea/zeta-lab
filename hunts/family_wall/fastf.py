"""Batched evaluation and minimisation of the n-point functional F_{n-1}.

Same functional as modal_npoint_sweep.py / modal_family_wall.py:

  F(g) = (1/p) sum g_i + sum_{s=1}^{n-1} (2/(n-s)) sum_{i} w(g_i + ... + g_{i+s-1}),
  w(x) = k(x)^2,  k(x) = K(x)/K(0),  K(x) = int_{-1/2}^{1/2} cos(sqrt2 t) cos(2 pi x t) dt,

but evaluated for a whole batch of gap vectors in one numpy call, with the exact
analytic gradient, so that every seed of a cell (all 2^(n-1) or 4^(n-1) kernel-zero
words plus random starts) is driven into its basin simultaneously by projected Adam,
and only the best few hundred are polished to machine precision by L-BFGS-B.

Nothing here is rigorous. Float values of F at a point are UPPER bounds on inf F;
the Arb enclosure at the winning point stays the rigorous step, as before.

`reference_F` is the original pure-python evaluator, kept so `selftest()` can prove
the batched one agrees with it to rounding.
"""
from __future__ import annotations

import math

import numpy as np
from scipy.optimize import minimize

S2 = math.sqrt(2.0)
K0 = S2 * math.sin(1 / S2)
KERNEL_ZEROS = (1.057278, 2.030068, 3.020243, 4.015236)


# ---------------------------------------------------------------- reference
def reference_F(n_points: int, p: float):
    def sinc(x):
        return 1.0 if abs(x) < 1e-12 else math.sin(x) / x

    def w(x):
        f = 2 * math.pi * x
        return (((sinc((S2 - f) / 2) + sinc((S2 + f) / 2)) / 2) / K0) ** 2

    n = n_points
    C = {s: 2.0 / (n - s) for s in range(1, n)}

    def F(g):
        if min(g) < 0:
            return float("inf")
        v = sum(g) / p
        for s in range(1, n):
            for i in range(n - s):
                v += C[s] * w(sum(g[i : i + s]))
        return v

    return F


# ---------------------------------------------------------------- geometry
class Geo:
    """Window index tables for n points (k = n-1 gaps), built once per n."""

    def __init__(self, n_points: int):
        n = n_points
        k = n - 1
        I, J, C = [], [], []
        for s in range(1, n):
            for i in range(n - s):
                I.append(i)
                J.append(i + s)
                C.append(2.0 / (n - s))
        self.n, self.k = n, k
        self.I = np.array(I)
        self.J = np.array(J)
        self.C = np.array(C)
        # membership: window w contains gap j iff I[w] <= j < J[w]
        M = np.zeros((len(I), k))
        for widx, (a, b) in enumerate(zip(I, J)):
            M[widx, a:b] = 1.0
        self.M = M
        self.W = len(I)


def _sinc(x):
    return np.sinc(x / np.pi)  # sin(x)/x with the removable singularity handled


def _dsinc(x):
    # (x cos x - sin x) / x^2, with the series -x/3 + x^3/30 near 0
    small = np.abs(x) < 1e-4
    xs = np.where(small, 1.0, x)
    d = (xs * np.cos(xs) - np.sin(xs)) / (xs * xs)
    return np.where(small, -x / 3.0 + x**3 / 30.0, d)


def w_and_dw(x):
    f = 2 * np.pi * x
    a = (S2 - f) / 2
    b = (S2 + f) / 2
    kx = ((_sinc(a) + _sinc(b)) / 2) / K0
    # dk/dx = (pi/2) (sinc'(b) - sinc'(a)) / K0
    dk = (np.pi / 2) * (_dsinc(b) - _dsinc(a)) / K0
    return kx * kx, 2 * kx * dk


def F_batch(G: np.ndarray, p: float, geo: Geo):
    """F for every row of G (B x k). Rows with a negative gap get +inf."""
    G = np.atleast_2d(G)
    S = np.concatenate([np.zeros((G.shape[0], 1)), np.cumsum(G, axis=1)], axis=1)
    sums = S[:, geo.J] - S[:, geo.I]
    w, _ = w_and_dw(sums)
    F = G.sum(axis=1) / p + (geo.C * w).sum(axis=1)
    return np.where((G < 0).any(axis=1), np.inf, F)


def F_and_grad_batch(G: np.ndarray, p: float, geo: Geo):
    G = np.atleast_2d(G)
    S = np.concatenate([np.zeros((G.shape[0], 1)), np.cumsum(G, axis=1)], axis=1)
    sums = S[:, geo.J] - S[:, geo.I]
    w, dw = w_and_dw(sums)
    F = G.sum(axis=1) / p + (geo.C * w).sum(axis=1)
    grad = 1.0 / p + (geo.C * dw) @ geo.M  # (B x W) @ (W x k)
    return F, grad


# ---------------------------------------------------------------- optimisers
def adam_batch(G0: np.ndarray, p: float, geo: Geo, iters: int = 400, lr: float = 0.02):
    """Projected Adam over a whole batch of starts. Gets every start into its
    basin to ~1e-7 in F; ranking basins is all this step is for."""
    G = np.array(G0, dtype=float)
    m = np.zeros_like(G)
    v = np.zeros_like(G)
    b1, b2, eps = 0.9, 0.999, 1e-12
    for t in range(1, iters + 1):
        F, g = F_and_grad_batch(G, p, geo)
        m = b1 * m + (1 - b1) * g
        v = b2 * v + (1 - b2) * g * g
        mh = m / (1 - b1**t)
        vh = v / (1 - b2**t)
        step = lr * (0.5 if t > iters * 0.6 else 1.0) * (0.25 if t > iters * 0.85 else 1.0)
        G = np.maximum(G - step * mh / (np.sqrt(vh) + eps), 0.0)
    F = F_batch(G, p, geo)
    return G, F


def polish(x0, p: float, geo: Geo):
    """L-BFGS-B with the exact gradient, to machine precision."""

    def fg(x):
        F, g = F_and_grad_batch(x[None, :], p, geo)
        return float(F[0]), g[0]

    r = minimize(fg, np.asarray(x0, dtype=float), jac=True, method="L-BFGS-B",
                 bounds=[(0.0, None)] * geo.k,
                 options={"ftol": 1e-16, "gtol": 1e-13, "maxiter": 2000, "maxcor": 20})
    x = np.maximum(r.x, 0.0)
    return x, float(F_batch(x[None, :], p, geo)[0])


def words(k: int, alphabet: int) -> np.ndarray:
    """All alphabet^k words over the first `alphabet` kernel zeros, as a (alphabet^k x k) array."""
    zs = np.array(KERNEL_ZEROS[:alphabet])
    idx = np.arange(alphabet**k)
    out = np.empty((len(idx), k))
    for j in range(k):
        out[:, j] = zs[idx % alphabet]
        idx //= alphabet
    return out


def minimise_cell(n_points: int, p: float, seeds: np.ndarray, top: int = 300,
                  adam_iters: int = 400):
    """Batched descent over every seed, then L-BFGS-B polish of the `top` best
    distinct basins. Returns (best_x, best_F, ranked list of (F, x) after polish)."""
    geo = Geo(n_points)
    G, F = adam_batch(seeds, p, geo, iters=adam_iters)
    order = np.argsort(F)
    # keep the best `top`, skipping near-duplicates in F (same basin)
    chosen, last = [], -1.0
    for i in order:
        if not np.isfinite(F[i]):
            continue
        if not chosen or F[i] - last > 1e-9:
            chosen.append(i)
            last = F[i]
        if len(chosen) >= top:
            break
    polished = [polish(G[i], p, geo) for i in chosen]
    polished.sort(key=lambda t: t[1])
    best_x, best_F = polished[0]
    return best_x, best_F, [(f, x) for x, f in polished]


# ---------------------------------------------------------------- selftest
def selftest(verbose: bool = True) -> bool:
    rng = np.random.default_rng(0)
    ok = True
    # 1. batched F equals the reference to rounding
    for n in (7, 9, 12):
        geo = Geo(n)
        ref = reference_F(n, 3000.0)
        G = rng.uniform(0.5, 4.0, size=(50, n - 1))
        Fb = F_batch(G, 3000.0, geo)
        err = max(abs(Fb[i] - ref(list(G[i]))) / Fb[i] for i in range(50))
        ok &= err < 1e-13
        if verbose:
            print(f"F agreement n={n}: max rel err {err:.2e}")
    # 2. gradient equals central differences
    for n in (7, 12):
        geo = Geo(n)
        x = rng.uniform(0.8, 2.5, size=n - 1)
        _, g = F_and_grad_batch(x[None, :], 3000.0, geo)
        h = 1e-6
        num = np.array([(F_batch((x + h * e)[None, :], 3000.0, geo)[0] - F_batch((x - h * e)[None, :], 3000.0, geo)[0]) / (2 * h)
                        for e in np.eye(n - 1)])
        err = np.max(np.abs(num - g[0]) / (np.abs(num) + 1e-12))
        ok &= err < 1e-5
        if verbose:
            print(f"grad agreement n={n}: max rel err {err:.2e}")
    # 3. control: n=7 p=3000 over all 4^6 words reproduces the Arb floor
    x, F, _ = minimise_cell(7, 3000.0, words(6, 4), top=100)
    target, argmin = 0.0038262312115073, np.array([1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002])
    arg_ok = min(np.max(np.abs(x - argmin)), np.max(np.abs(x[::-1] - argmin))) < 2e-5
    ok &= abs(F - target) < 1e-9 and arg_ok
    if verbose:
        print(f"control n=7 p=3000: F={F:.16f} (target {target}), diff={F - target:.2e}, argmin ok={arg_ok}")
    return bool(ok)


if __name__ == "__main__":
    import sys
    sys.exit(0 if selftest() else 1)
