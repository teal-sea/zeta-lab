"""Constructive check of strong duality for the out-of-band envelope (float64).

Theory: RESULTS.md section 2. For L with every comb prime p < e^{2L},
write s(k) = sum_i k_i log p_i on Z^r. The window comb operator P on
L^2[-L, L] has top of spectrum lambda_max. Theorem 2 says
inf_H sup_t (P_L - H)(t) = lambda_max, the infimum over real even
trigonometric polynomials H with all frequencies >= 2L in absolute value.

This script follows the proof step by step and measures the result:
  1. lambda_max from the finite components of the window graph (valid when
     every component is finite, which holds for L <= 0.8; see RESULTS.md).
  2. The partial Toeplitz matrix M[j, j'] = psi(j - j') on the box
     F_N = {-N..N}^r, specified where |s(j) - s(j')| < 2L, with
     psi(0) = t, psi(+-m e_i) = -Lambda(p_i^m)/p_i^{m/2}, psi = 0 elsewhere.
  3. Positive semidefinite completion, one point at a time in s-order
     (the pattern is a unit interval graph, hence chordal).
  4. Weighted averaging over the box with product cosine weights, giving a
     positive definite c on Z^r, hence mu(theta) = sum_k c(k) e^{ik.theta} >= 0.
  5. H = the part of mu with |s(k)| >= 2L. Then P_L - H <= t + error, and
     the script evaluates sup(Phi - H) and min(mu) on a grid of the torus.

Everything here is float64, one route: measured grade. It is a check of a
proof, not a replacement for it.
"""
import math
import sys

import numpy as np


def comb_terms(L):
    """[(p, m, w)] for prime powers n = p^m with log n < 2L, w = log p / p^{m/2}."""
    out = []
    for p in range(2, int(math.exp(2 * L)) + 1):
        if any(p % q == 0 for q in range(2, int(math.isqrt(p)) + 1)):
            continue
        m = 1
        while m * math.log(p) < 2 * L:
            out.append((p, m, math.log(p) / p ** (m / 2)))
            m += 1
    return out


def window_lambda_max(L, terms, samples=4000, tol=1e-9, cap=5000, seed=0):
    """Max top eigenvalue over components of the window graph (x ~ x +- log n)."""
    steps = [(m * math.log(p), w) for p, m, w in terms]
    rng = np.random.default_rng(seed)
    best, sizes = 0.0, {}
    for x0 in rng.uniform(-L, L, samples):
        pos = [x0]
        edges = []
        queue = [0]
        while queue:
            i = queue.pop()
            x = pos[i]
            for s, w in steps:
                for y in (x + s, x - s):
                    if -L <= y <= L:
                        j = next((k for k, z in enumerate(pos) if abs(z - y) < tol), None)
                        if j is None:
                            pos.append(y)
                            j = len(pos) - 1
                            queue.append(j)
                            if len(pos) > cap:
                                raise RuntimeError("component too large: percolating regime")
                        if i < j:
                            edges.append((i, j, w))
        A = np.zeros((len(pos), len(pos)))
        for i, j, w in edges:
            A[i, j] += w
            A[j, i] += w
        lam = float(np.linalg.eigvalsh(A)[-1])
        sizes[len(pos)] = max(sizes.get(len(pos), 0.0), lam)
        best = max(best, lam)
    return best, sizes


def completion(points_s, psi_of, twoL):
    """PSD completion of the partial matrix, specified iff |s_i - s_j| < 2L.

    points are pre-sorted by s. Adds one point at a time; the specified
    earlier neighbours of the new point form a contiguous block B, and the
    unspecified entries are filled by u = M[U, B] M[B, B]^{-1} v.
    """
    n = len(points_s)
    M = np.zeros((n, n))
    M[0, 0] = psi_of(0, 0)
    lo = 0
    for k in range(1, n):
        while points_s[k] - points_s[lo] >= twoL:
            lo += 1
        B = np.arange(lo, k)
        v = np.array([psi_of(k, j) for j in B])
        M[k, k] = psi_of(k, k)
        M[k, B] = v
        M[B, k] = v
        if lo > 0:
            U = np.arange(0, lo)
            if len(B):
                z = np.linalg.solve(M[np.ix_(B, B)], v)
                u = M[np.ix_(U, B)] @ z
            else:
                u = np.zeros(len(U))
            M[k, U] = u
            M[U, k] = u
    return M


def run(L, N, grid=256, delta=1e-9):
    terms = comb_terms(L)
    primes = sorted({p for p, _, _ in terms})
    ell = np.array([math.log(p) for p in primes])
    r = len(primes)
    lam, sizes = window_lambda_max(L, terms)
    t = lam + delta

    psi = {tuple([0] * r): t}
    for p, m, w in terms:
        e = [0] * r
        e[primes.index(p)] = m
        psi[tuple(e)] = -w
        psi[tuple(-x for x in e)] = -w

    rng1 = np.arange(-N, N + 1)
    pts = np.array(np.meshgrid(*([rng1] * r), indexing="ij")).reshape(r, -1).T
    s = pts @ ell
    order = np.argsort(s)
    pts, s = pts[order], s[order]

    def psi_of(i, j):
        return psi.get(tuple(pts[i] - pts[j]), 0.0)

    M = completion(s, psi_of, 2 * L)
    eig_min = float(np.linalg.eigvalsh(M)[0])

    # weighted average over the box: alpha_j = prod_i cos(pi j_i / (2N + 2))
    alpha = np.prod(np.cos(math.pi * pts / (2 * N + 2)), axis=1)
    Z = float(alpha @ alpha)
    W = (alpha[:, None] * alpha[None, :]) * M / Z
    size = 4 * N + 1
    c = np.zeros([size] * r)
    diff = (pts[:, None, :] - pts[None, :, :]) + 2 * N
    np.add.at(c, tuple(diff[..., i] for i in range(r)), W)

    # split c into in-slab (must reproduce t - Phi, damped) and out-of-band H
    ks = np.array(np.meshgrid(*([np.arange(-2 * N, 2 * N + 1)] * r), indexing="ij"))
    sk = np.tensordot(ell, ks, axes=1)
    inband = np.abs(sk) < 2 * L
    H_coef = np.where(inband, 0.0, c)
    # check in-band coefficients against psi times damping
    worst_inband = 0.0
    for idx in zip(*np.nonzero(inband)):
        k = tuple(int(x) - 2 * N for x in idx)
        target = psi.get(k, 0.0)
        if target == 0.0:
            worst_inband = max(worst_inband, abs(c[idx]))

    # evaluate on the torus grid by FFT (coefficient of e^{ik.theta})
    def synth(coef):
        full = np.zeros([grid] * r, dtype=complex)
        for idx in zip(*np.nonzero(coef)):
            k = tuple((int(x) - 2 * N) % grid for x in idx)
            full[k] += coef[idx]
        return np.real(np.fft.ifftn(full) * grid ** r)

    mu = synth(c)
    Hval = synth(H_coef)
    thetas = np.meshgrid(*([2 * math.pi * np.arange(grid) / grid] * r), indexing="ij")
    Phi = np.zeros([grid] * r)
    for p, m, w in terms:
        Phi += 2 * w * np.cos(m * thetas[primes.index(p)])

    n2 = 2 * N + 2

    def rho(m):
        return ((n2 - 1 - m) * math.cos(math.pi * m / n2) + math.sin(math.pi * (m + 1) / n2) / math.sin(math.pi / n2)) / n2

    bound = t + sum(2 * w * (1 - rho(m)) for p, m, w in terms)
    sep = 0.0
    for p in primes:
        ts = [math.log(p) / p ** (m / 2) for q, m, w in terms if q == p]
        T = np.array([[0.0 if i == j else ts[abs(i - j) - 1] for j in range(len(ts) + 1)] for i in range(len(ts) + 1)])
        sep += float(np.linalg.eigvalsh(T)[-1])
    return {
        "L": L, "N": N, "primes": primes, "A_L": sum(2 * w for _, _, w in terms),
        "S_sep": sep, "lambda_max": lam, "component_types": {k: round(v, 9) for k, v in sorted(sizes.items())},
        "completion_min_eig": eig_min, "worst_inband_leak": worst_inband,
        "min_mu_grid": float(mu.min()), "sup_Phi_minus_H_grid": float((Phi - Hval).max()),
        "proof_bound": bound, "H_l1": float(np.abs(H_coef).sum()),
        "H_max_freq": float(np.abs(np.where(inband, 0.0, sk)).max()),
    }


if __name__ == "__main__":
    for L, N in [(0.6, 6), (0.6, 12), (0.6, 20), (0.8, 6), (0.8, 12), (0.8, 20)]:
        res = run(L, N)
        print({k: (float('%.7g' % v) if isinstance(v, float) else v) for k, v in res.items()})
        sys.stdout.flush()
