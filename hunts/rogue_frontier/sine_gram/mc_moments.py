"""Monte Carlo estimate of the sine-kernel Gram spectral moments m_k(lambda).

The object: for the sine process of density 1 and band-width lambda, let
G_ij = K_lambda(x_i - x_j) with K_lambda(x) = sin(pi lambda x)/(pi x).
The paper of 10 August 2026 (Remark 7.5(f)) records the normalised moments
m_k(lambda) = lim tr G^k / (d * ell_1^k), d = lambda * N, and states
m_k(1) = 1, 4/3, 2, 13/4 for k = 1..4.

Circular model.  On a circle of circumference N carrying N points of unit
density, the band-limited kernel is the Dirichlet kernel
D_M(x) = sum_{|m|<=M} e(m x / N), so D_M = N * K_lambda with d = 2M+1 = lambda N.
Then G = V^* V for V_{m,j} = e(m x_j / N), so tr G^k = tr T^k / N^k with
T the (2M+1)x(2M+1) Toeplitz matrix T_{m,m'} = sum_j e((m-m') x_j / N).
For the CUE, x_j = N theta_j / (2 pi), so T_{m,m'} = Tr(U^{m-m'}).

This module estimates m_k by sampling the CUE.  It is a control on the exact
combinatorial engine, not the engine itself.
"""

from __future__ import annotations

import numpy as np


def cue_eigenangles(n: int, rng: np.random.Generator) -> np.ndarray:
    """Eigenangles of a Haar-random n x n unitary matrix."""
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2.0)
    q, r = np.linalg.qr(z)
    d = np.diagonal(r)
    q = q * (d / np.abs(d))
    return np.angle(np.linalg.eigvals(q))


def gram_moments_one_sample(
    theta: np.ndarray, n: int, half_band: int, k_max: int
) -> np.ndarray:
    """tr G^k / (d N^0) for k = 1..k_max on one configuration.

    Returns the raw traces tr T^k / N^k, i.e. tr G^k in the continuum
    normalisation.
    """
    m = np.arange(-half_band, half_band + 1)
    # power sums Tr(U^h) for every h that can occur as m - m'
    h_max = 2 * half_band
    powers = np.arange(-h_max, h_max + 1)
    trace_u = np.array([np.sum(np.exp(1j * h * theta)) for h in powers])
    toeplitz = trace_u[(m[:, None] - m[None, :]) + h_max]
    out = np.empty(k_max, dtype=float)
    mat = np.eye(len(m), dtype=complex)
    for k in range(1, k_max + 1):
        mat = mat @ toeplitz
        out[k - 1] = np.trace(mat).real / n ** k
    return out


def estimate(
    n: int = 240,
    lam: float = 1.0,
    k_max: int = 6,
    samples: int = 200,
    seed: int = 20260817,
) -> dict:
    """Monte Carlo estimate of m_k(lambda), k = 1..k_max, with standard errors."""
    half_band = int(round((lam * n - 1) / 2))
    d = 2 * half_band + 1
    rng = np.random.default_rng(seed)
    acc = np.zeros((samples, k_max))
    for s in range(samples):
        theta = cue_eigenangles(n, rng)
        acc[s] = gram_moments_one_sample(theta, n, half_band, k_max)
    normalised = acc / d
    return {
        "n": n,
        "lambda_effective": d / n,
        "d": d,
        "samples": samples,
        "mean": normalised.mean(axis=0).tolist(),
        "stderr": (normalised.std(axis=0, ddof=1) / np.sqrt(samples)).tolist(),
    }


if __name__ == "__main__":
    res = estimate()
    print("N =", res["n"], " d =", res["d"], " lambda_eff =", res["lambda_effective"])
    target = {1: 1.0, 2: 4 / 3, 3: 2.0, 4: 13 / 4}
    for i, (mu, se) in enumerate(zip(res["mean"], res["stderr"]), start=1):
        ref = target.get(i)
        if ref is None:
            tag = ""
        elif se > 0:
            tag = f"   paper: {ref:.6f}  dev: {(mu - ref) / se:+.1f} se"
        else:
            tag = f"   paper: {ref:.6f}  (deterministic)"
        print(f"m_{i} = {mu:.6f} +- {se:.6f}{tag}")
