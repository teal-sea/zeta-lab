"""Separable (per-prime) out-of-band majorant for Zhu's envelope constant.

For each prime p <= e^{2L}: phi_p(theta) = sum_{k<=m_p} c_{p,k} cos(k theta),
c_{p,k} = 2 log p / p^{k/2}, m_p = max{k : k log p < 2L}.  Frequencies k >= m_p+1
correspond to t-frequencies k log p >= 2L, invisible to Q on window [-L, L].
inf_h sup(phi_p - h_p) = lambda_max(Toeplitz(0, t_1..t_m)), t_k = c_{p,k}/2
(Caratheodory-Toeplitz duality on the circle).  Finite-degree version: Fejer
kernels of degree D, t_k -> t_k / (1 - k/(D+1)).  This script computes the
constants and VERIFIES the finite-D certificate Phi_p >= 0 numerically.
"""
import math
import numpy as np


def primes_upto(x):
    return [p for p in range(2, int(x) + 1) if all(p % q for q in range(2, int(math.isqrt(p)) + 1))]


def toep(first):
    n = len(first)
    return np.array([[first[abs(i - j)] for j in range(n)] for i in range(n)])


def prime_block(p, L, D=None):
    m = 0
    while (m + 1) * math.log(p) < 2 * L:
        m += 1
    t = [math.log(p) / p ** (k / 2) for k in range(1, m + 1)]
    if D is not None:
        t = [tk / (1 - k / (D + 1)) for k, tk in enumerate(t, start=1)]
    T = toep([0.0] + t)
    return m, t, float(np.linalg.eigvalsh(T)[-1]), T


def fejer(theta, D):
    k = np.arange(-D, D + 1)
    return np.real(np.exp(1j * np.outer(theta, k)) @ (1 - np.abs(k) / (D + 1)))


def certificate(p, L, D):
    """Build Phi_p = sum_j a_j K_D(theta - theta_j) >= 0 with the required low
    coefficients; return (M_p(D), min Phi on grid, max low-coefficient error)."""
    m, tD, M, TD = prime_block(p, L, D)
    A = M * np.eye(m + 1) - TD                      # PSD Toeplitz, singular
    w, V = np.linalg.eigh(A)
    u = V[:, 0]                                     # kernel vector
    roots = np.roots(u[::-1])                       # poly sum u_k z^k
    th = np.angle(roots)
    # weights from first column: A[k,0] = sum_j a_j e^{i k th_j}
    Vd = np.exp(1j * np.outer(np.arange(m + 1), th))
    a = np.linalg.lstsq(Vd, A[:, 0].astype(complex), rcond=None)[0]
    grid = np.linspace(-math.pi, math.pi, 20001)
    Phi = sum(np.real(aj) * fejer(grid - tj, D) for aj, tj in zip(a, th))
    # low coefficients of Phi should be M (k=0), -t_k (1<=k<=m)
    c = [np.trapezoid(Phi * np.cos(k * grid), grid) / (2 * math.pi) for k in range(m + 1)]
    _, t, _, _ = prime_block(p, L)
    target = [M] + [-tk for tk in t]
    return M, float(Phi.min()), max(abs(x - y) for x, y in zip(c, target)), float(np.min(np.real(a))), float(np.max(np.abs(np.abs(roots) - 1)))

def main():
    print(f"{'L':>6} {'c=e^2L':>7} {'A_L':>8} {'sep(inf)':>9} {'sep(D=64)':>9} {'T1 Zhu':>10} {'T1 sep':>9} {'T*':>7}")
    for L in [0.8, 1.0, 1.19, 1.2825, 1.4, 1.6, 1.7169, 2.0]:
        ps = primes_upto(math.exp(2 * L))
        AL = sum(2 * math.log(p) / p ** (k / 2) for p in ps for k in range(1, 60) if k * math.log(p) < 2 * L)
        sep = sum(prime_block(p, L)[2] for p in ps)
        sep64 = sum(prime_block(p, L, 64)[2] for p in ps)
        print(f"{L:6.4f} {math.exp(2*L):7.2f} {AL:8.4f} {sep:9.4f} {sep64:9.4f} {2*math.pi*math.exp(AL):10.4g} {2*math.pi*math.exp(sep64):9.4g} {2*math.pi*math.exp(2*L):7.1f}")

    print("\ncertificate check (D=64): p, L, M_p(D), min Phi, coeff err, min weight, max |root|-1")
    for L in [0.8, 1.19]:
        for p in primes_upto(math.exp(2 * L)):
            print(p, L, *[f"{v:.3e}" for v in certificate(p, L, 64)])


if __name__ == "__main__":
    main()
