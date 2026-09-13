"""Finite checks for RANK3_Z_COMPONENT.md at q = 1.

For N in a short ladder: T_N (UPPER_BOUND (29)), the arc-restricted U_1 and
Z_(1) = int_{|beta|<=Q/N} |F_N - K_N|^4 (FFT grid, two resolutions), the
Cauchy-Schwarz pin 3 U_1^2 / (2N^3 + N), and the short-interval variance
V_H = sum_x (window sum of Lambda(n) - 1 over x < n <= x+H)^2 with
H = N/(2Q), which is what Gallagher's lemma bounds int_arc |D|^2 by.
Reports Z_(1)/(N V_H) and Z_(1)/N^3. Nothing asymptotic is asserted.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def mangoldt(N):
    lam = np.zeros(N + 1)
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, N + 1):
        if sieve[p]:
            sieve[p * p::p] = False
            pk = p
            while pk <= N:
                lam[pk] = math.log(p)
                pk *= p
    return lam


def arc_integrals(d, N, Q, mult):
    """Return (U_1, Z_1, T_N(2,1)-style full circle check) on a grid of mult*N points."""
    M = mult * N
    pad = np.zeros(M, dtype=complex)
    pad[1:N + 1] = 1.0
    K = M * np.fft.ifft(pad)
    pad[1:N + 1] = d[1:]
    D = M * np.fft.ifft(pad)
    beta = np.arange(M) / M
    dist = np.minimum(beta, 1 - beta)
    arc = dist <= Q / N
    U1 = float((np.abs(K[arc]) ** 2 * np.abs(D[arc]) ** 2).sum() / M)
    Z1 = float((np.abs(D[arc]) ** 4).sum() / M)
    Zfull = float((np.abs(D) ** 4).sum() / M)
    return U1, Z1, Zfull


def main():
    rows = []
    for N in (1000, 5000, 20000, 60000):
        lam = mangoldt(N)
        L = math.log(N)
        Q = math.isqrt(N) // 3
        d = lam.copy(); d[1:] -= 1.0
        # T_N exactly from partial sums
        S = np.cumsum(d[1:])
        T_N = float(np.sum(S ** 2) + np.sum((S[-1] - S[:-1]) ** 2))
        U1a, Z1a, Zfa = arc_integrals(d, N, Q, 32)
        U1b, Z1b, Zfb = arc_integrals(d, N, Q, 64)
        pin = 3 * U1b ** 2 / (2 * N ** 3 + N)
        # short-interval variance of the truncated sequence, window H = N/(2Q)
        H = max(1, round(N / (2 * Q)))
        P = np.concatenate([[0.0], S])  # P[t] = sum_{n<=t} d(n), t = 0..N
        # window sums for x from -H to N: sum_{x<n<=x+H, 1<=n<=N} d(n) = P[min(x+H,N)] - P[max(x,0)]
        xs = np.arange(-H, N + 1)
        hi = np.clip(xs + H, 0, N); lo = np.clip(xs, 0, N)
        W = P[hi] - P[lo]
        V_H = float(np.sum(W ** 2))
        rows.append({
            "N": N, "Q": Q, "H": H, "T_N": T_N, "U_1_arc": U1b, "U_1_grid32": U1a,
            "Z_1_arc": Z1b, "Z_1_grid32": Z1a, "Z_1_full_circle": Zfb,
            "pin_3U1sq_over_2N3": pin, "pin_holds": bool(Z1b >= pin),
            "Z1_over_pin": Z1b / pin, "V_H": V_H,
            "Z1_over_N_VH": Z1b / (N * V_H), "Z1_over_N3": Z1b / N ** 3,
            "Z1_over_N52": Z1b / N ** 2.5, "Zfull_over_N3": Zfb / N ** 3,
            "U1_over_TN": U1b / T_N,
        })
        r = rows[-1]
        print(f"N={N:6d} Q={Q:3d} H={H:4d} Z1/N^3={r['Z1_over_N3']:.4g} Z1/N^2.5={r['Z1_over_N52']:.4g} "
              f"Zfull/N^3={r['Zfull_over_N3']:.3f} pin={r['pin_holds']} Z1/pin={r['Z1_over_pin']:.3g} "
              f"Z1/(N V_H)={r['Z1_over_N_VH']:.4f} grid32/64 Z1 rel diff={abs(Z1a-Z1b)/Z1b:.1e}")
    (HERE / "results_rank3_z_component_probe.json").write_text(json.dumps(rows, indent=2) + "\n")


if __name__ == "__main__":
    main()
