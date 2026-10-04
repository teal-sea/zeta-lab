"""Probe: how far can an out-of-band term lower the prime-comb envelope in
Zhu's one-stroke reduction (arXiv:2608.24827)?

For supp f in [-L, L], |F|^2 has spectrum in [-2L, 2L], so adding
H(t) = sum_w b_w cos(t*lambda_w) with every lambda_w >= 2L leaves Q(f)
unchanged.  The envelope constant becomes sup_t (P_L - H)(t) instead of
A_L = sup_t P_L(t).  Weak duality: sup(P_L - H) >= lambda_max of the
windowed comb operator (P phi)(x) = sum_n w_n [phi(x-log n)+phi(x+log n)]
on L^2[-L, L], w_n = Lambda(n)/sqrt(n).  This script computes that floor
(float64, piecewise-constant Galerkin, a probe not a certificate) and an
explicit LP upper bound on the 2-torus at L = 0.8.
"""
import math, sys
import numpy as np


def mangoldt_upto(X):
    out = []
    for n in range(2, int(X) + 1):
        m, p = n, None
        for q in range(2, int(math.isqrt(n)) + 1):
            if m % q == 0:
                p = q
                break
        if p is None:
            p = n
        while m % p == 0:
            m //= p
        if m == 1:
            out.append((n, math.log(p)))
    return out


def comb(L):
    return [(n, lam / math.sqrt(n)) for n, lam in mangoldt_upto(math.exp(2 * L)) if math.log(n) < 2 * L]


def A_L(L):
    return sum(2 * w for _, w in comb(L))


def lam_max(L, M):
    h = 2 * L / M
    left = -L + h * np.arange(M)
    A = np.zeros((M, M))
    for n, w in comb(L):
        s = math.log(n)
        for sgn in (1, -1):
            # overlap of cell i with cell j shifted by sgn*s
            a0 = left[:, None]
            b0 = a0 + h
            a1 = left[None, :] + sgn * s
            b1 = a1 + h
            ov = np.clip(np.minimum(b0, b1) - np.maximum(a0, a1), 0, None)
            A += w * ov / h
    A = 0.5 * (A + A.T)
    return float(np.linalg.eigvalsh(A)[-1])


def main():
    print(f"{'L':>5} {'A_L':>8} {'lmax(P_L)':>10} {'ratio':>6} {'T1=2pi e^A':>11} {'T1eff':>9} {'T*=2pi e^2L':>11}")
    for L in [0.8, 1.0, 1.19, 1.2825, 1.4, 1.6, 2.0]:
        lm = [lam_max(L, M) for M in (400, 800, 1600)]
        a = A_L(L)
        T1 = 2 * math.pi * math.exp(a)
        T1e = 2 * math.pi * math.exp(lm[-1])
        Ts = 2 * math.pi * math.exp(2 * L)
        print(f"{L:5.3f} {a:8.4f} {lm[-1]:10.4f} {lm[-1]/a:6.3f} {T1:11.4g} {T1e:9.4g} {Ts:11.4g}   (M=400/800/1600: {lm[0]:.4f} {lm[1]:.4f} {lm[2]:.4f})")
    sys.stdout.flush()


if __name__ == "__main__":
    main()
