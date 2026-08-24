#!/usr/bin/env python3
"""Independent reimplementation of the AMTOPA exact-pressure family.

Nothing here imports AMTOPA code.  Everything is written from the mathematical
description in their ``proof.md`` and re-derived against their ``candidate.json``
numbers, so agreement is evidence and disagreement is a finding.

The family, in the notation of AMTOPA ``proof.md``:

    window        v(s) = sum_j c_j cos(w_j s),  w_0 = sqrt(2), w_j = 2*pi*j
    window const  H(v) = 2 - 1/c1,   c1 = I1^2 / (I2 + J)
    kernel        K(x) = int_{-1/2}^{1/2} v(s) cos(2 pi x s) ds
                       = sum_j c_j [ sinc(w_j/2 - pi x) + sinc(w_j/2 + pi x) ] / 2
    pair weight   W(x) = (K(x)/K(0))^2                       (>= 0 everywhere)
    functional    F(g) = sum_r b_r g_r + sum_{i<j} a_ij W(y_j - y_i),  y_j = g_1+..+g_j
    floor         eps  = inf_{g >= 0} F(g)
    assembly      see exact_assembly.py

Free parameters: c (17 numbers, scale-invariant so 16 free), a (21 numbers on the
polytope a >= 0, sum_i a_{i,i+s} = 2 for each span s), b (6 numbers >= 0).

``sinc`` here is the unnormalised sin(z)/z, as in AMTOPA's source.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np

Q = 6                      # gaps per local window
NPT = Q + 1                # points

# --------------------------------------------------------------- their point

HERE = Path(__file__).resolve().parent
AMTOPA_NUMERATORS = [
    1000000000, 12378982, -12602495, 4164033, 5741405, -1724025, 6219280,
    -8047828, 6321519, -5241981, -892658, 560544, -431207, 357969, -310433,
    100000, -100000,
]
AMTOPA_DEN = 1000000000
AMTOPA_PAIRS = [
    (0, 1, 244109993), (0, 2, 0), (0, 3, 254223074), (0, 4, 1000000000),
    (0, 5, 1000000000), (0, 6, 2000000000), (1, 2, 346264551),
    (1, 3, 368129744), (1, 4, 745776926), (1, 5, 0), (1, 6, 1000000000),
    (2, 3, 409625456), (2, 4, 1263740512), (2, 5, 745776926),
    (2, 6, 1000000000), (3, 4, 409625456), (3, 5, 368129744),
    (3, 6, 254223074), (4, 5, 346264551), (4, 6, 0), (5, 6, 244109993),
]
AMTOPA_PAIR_DEN = 1000000000
AMTOPA_PRESSURE = [22420713, 32878293, 37700994, 37700994, 32878293, 22420713]
AMTOPA_PRESSURE_DEN = 46000000000


def amtopa_coeffs() -> np.ndarray:
    return np.array(AMTOPA_NUMERATORS, dtype=float) / AMTOPA_DEN


def amtopa_a() -> np.ndarray:
    """21-vector of pair weights in the canonical (i<j) order of pair_index()."""
    a = np.zeros(len(PAIR_LIST))
    lookup = {(i, j): n / AMTOPA_PAIR_DEN for i, j, n in AMTOPA_PAIRS}
    for k, (i, j) in enumerate(PAIR_LIST):
        a[k] = lookup[(i, j)]
    return a


def amtopa_b() -> np.ndarray:
    return np.array(AMTOPA_PRESSURE, dtype=float) / AMTOPA_PRESSURE_DEN


PAIR_LIST = [(i, j) for i in range(NPT) for j in range(i + 1, NPT)]
PAIR_SPAN = np.array([j - i for i, j in PAIR_LIST])

# ------------------------------------------------------------------- window


def frequencies(nterms: int) -> np.ndarray:
    w = np.empty(nterms)
    w[0] = np.sqrt(2.0)
    w[1:] = 2.0 * np.pi * np.arange(1, nterms)
    return w


def _sinc(z):
    """sin(z)/z, vectorised, exact at z = 0."""
    return np.sinc(np.asarray(z) / np.pi)


def kernel(x, c: np.ndarray, w: np.ndarray) -> np.ndarray:
    """K(x) = sum_j c_j [sinc(w_j/2 - pi x) + sinc(w_j/2 + pi x)] / 2."""
    x = np.atleast_1d(np.asarray(x, dtype=float))
    half = w / 2.0
    arg_lo = half[None, :] - np.pi * x[:, None]
    arg_hi = half[None, :] + np.pi * x[:, None]
    return 0.5 * ((_sinc(arg_lo) + _sinc(arg_hi)) * c[None, :]).sum(axis=1)


def Wfun(x, c: np.ndarray, w: np.ndarray, k0: float | None = None) -> np.ndarray:
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    k = kernel(x, c, w)
    return (k / k0) ** 2


# --- H(v) as a Rayleigh quotient -------------------------------------------
#
# I1 = u . c        (linear)
# I2 = c^T Cmat c   (quadratic)
# J  = c^T Amat c   (quadratic, Amat is the symmetrised A)
# c1 = (u.c)^2 / (c^T M c),  M = Cmat + Amat_sym   ->   H = 2 - 1/c1
#
# Therefore max_c H = 2 - 1/(u^T M^{-1} u), attained at c propto M^{-1} u.
# That closed form is the exact ceiling of the window axis for a fixed
# frequency set, and it is what `window_ceiling` returns.


def _sinc_scalar(z: float) -> float:
    return float(np.sinc(z / np.pi))


def window_matrices(w: np.ndarray):
    n = len(w)
    u = np.array([_sinc_scalar(wi / 2.0) for wi in w])
    Cm = np.empty((n, n))
    Am = np.empty((n, n))
    for i in range(n):
        for j in range(n):
            a, b = w[i], w[j]
            Cm[i, j] = 0.5 * (_sinc_scalar((a - b) / 2.0) + _sinc_scalar((a + b) / 2.0))
            Am[i, j] = (
                (np.sin(a / 2.0) / a + 2.0 * np.cos(a / 2.0) / a**2) * _sinc_scalar(b / 2.0)
                - 2.0 * Cm[i, j] / a**2
            )
    M = Cm + 0.5 * (Am + Am.T)
    return u, Cm, Am, M


def H_of(c: np.ndarray, u: np.ndarray, M: np.ndarray) -> float:
    i1 = float(u @ c)
    denom = float(c @ M @ c)
    c1 = i1 * i1 / denom
    return 2.0 - 1.0 / c1


def window_ceiling(u: np.ndarray, M: np.ndarray):
    """Exact maximum of H over the whole coefficient space for this frequency set."""
    sol = np.linalg.solve(M, u)
    c1max = float(u @ sol)
    return 2.0 - 1.0 / c1max, sol / sol[0]


# --------------------------------------------------------------- functional


def F_of(g: np.ndarray, a: np.ndarray, b: np.ndarray, c: np.ndarray,
         w: np.ndarray, k0: float | None = None) -> float:
    g = np.asarray(g, dtype=float)
    y = np.concatenate(([0.0], np.cumsum(g)))
    d = np.array([y[j] - y[i] for i, j in PAIR_LIST])
    return float(b @ g + a @ Wfun(d, c, w, k0))


def F_batch(G: np.ndarray, a: np.ndarray, b: np.ndarray, c: np.ndarray,
            w: np.ndarray, k0: float | None = None) -> np.ndarray:
    """G is (N, Q).  Returns the N functional values."""
    G = np.atleast_2d(G)
    y = np.concatenate([np.zeros((G.shape[0], 1)), np.cumsum(G, axis=1)], axis=1)
    idx_i = np.array([i for i, _ in PAIR_LIST])
    idx_j = np.array([j for _, j in PAIR_LIST])
    d = y[:, idx_j] - y[:, idx_i]
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    Wv = Wfun(d.ravel(), c, w, k0).reshape(d.shape)
    return G @ b + Wv @ a


def gap_upper(b: np.ndarray, target: float) -> float:
    """Any g with F(g) < target has every gap below this."""
    return target / float(np.min(b))


# ------------------------------------------------- a-free ceiling instrument
#
# For the equal-gap test vector g = t * 1, every pair of index span s sits at the
# same distance s*t, so   F(t*1) = B*t + sum_s (sum_i a_{i,i+s}) W(s t)
#                                = B*t + 2 * sum_{s=1..6} W(s t)
# using the span capacity  sum_i a_{i,i+s} = 2  that the construction imposes.
# The right-hand side does not depend on a at all.  Hence for EVERY admissible
# pair-weight vector,
#
#       eps  <=  eps_diag(B)  :=  min_{t >= 0} [ B t + 2 sum_{s=1..6} W(s t) ].
#
# That is a hard cap on the floor the family can certify at a given window and a
# given total pressure, and it is the instrument this hunt uses to bracket the
# family ceiling.


def eps_diag(B: float, c: np.ndarray, w: np.ndarray, spans: int = Q,
             tmax: float | None = None, n: int = 200001,
             k0: float | None = None) -> tuple[float, float]:
    if k0 is None:
        k0 = float(kernel(0.0, c, w)[0])
    if tmax is None:
        tmax = 12.0 / max(B, 1e-12) / 1000.0 + 8.0
    t = np.linspace(0.0, tmax, n)
    tot = B * t
    for s in range(1, spans + 1):
        tot = tot + 2.0 * Wfun(s * t, c, w, k0)
    k = int(np.argmin(tot))
    # local golden refinement
    lo = t[max(k - 1, 0)]
    hi = t[min(k + 1, n - 1)]
    for _ in range(200):
        m1 = lo + (hi - lo) * 0.381966
        m2 = hi - (hi - lo) * 0.381966
        f1 = B * m1 + sum(2.0 * float(Wfun(s * m1, c, w, k0)[0]) for s in range(1, spans + 1))
        f2 = B * m2 + sum(2.0 * float(Wfun(s * m2, c, w, k0)[0]) for s in range(1, spans + 1))
        if f1 < f2:
            hi = m2
        else:
            lo = m1
    tstar = 0.5 * (lo + hi)
    val = B * tstar + sum(2.0 * float(Wfun(s * tstar, c, w, k0)[0]) for s in range(1, spans + 1))
    return min(val, float(tot[k])), tstar


def main() -> int:
    c = amtopa_coeffs()
    w = frequencies(len(c))
    u, Cm, Am, M = window_matrices(w)
    a = amtopa_a()
    b = amtopa_b()
    B = float(b.sum())

    print("== independent replay of AMTOPA's published quantities ==")
    print(f"H(v)            = {H_of(c, u, M):.20f}")
    print("  theirs          0.67218815811823458517 (mpmath, 80 dps)")
    hmax, cmax = window_ceiling(u, M)
    print(f"H ceiling (17 freqs, exact Rayleigh) = {hmax:.20f}")
    print(f"  they sit below it by {hmax - H_of(c, u, M):.6e}")

    print(f"\nB               = {B:.20f}   (93/23000 = {93/23000:.20f})")
    print(f"span capacities  = {[float(a[PAIR_SPAN == s].sum()) for s in range(1, Q+1)]}")
    print(f"K(0)             = {float(kernel(0.0, c, w)[0]):.17f}")
    print(f"W(0)             = {float(Wfun(0.0, c, w)[0]):.17f}")

    gstar = np.array([1.978079145369, 1.044055102239, 1.973013931233,
                      1.045981098706, 1.974452906922, 1.042299648208])
    print(f"\nF at their recorded basin = {F_of(gstar, a, b, c, w):.18f}")
    print("  theirs                    0.007911105155226424")

    ed, tstar = eps_diag(B, c, w)
    print(f"\na-free equal-gap cap eps_diag(B) = {ed:.12f}  at t = {tstar:.9f}")
    print(f"  their accepted eps = 0.0079107 ; cap is above it: {ed > 0.0079107}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
