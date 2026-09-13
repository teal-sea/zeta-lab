"""Finite checks for ARC_SPLIT_BUDGET.md.

Everything here is a measurement at fixed N, without an exceptional zero (none
exists at reachable N, so the correction C_N is zero and E_corr = E). It checks

(1) the pointwise identity G_y = (|F|^2 - |H|^2) + R_mod - kappa for a toy sieve
    model at Z = 7, which pins the sign of the constant kappa = d_N - sum a(n)^2;
(2) the arc split of the centered mean square at the arcs of UPPER_BOUND.md (7):
    the shares of the major and minor arcs, the minor-arc fourth moment I_Q, and
    the minor-arc energy of the main-term polynomial V_y + a_0(N, y), measured
    against N^3/Q and N^3/Q^2;
(3) the mean square of the singular-series tail S(h) - S_R(h) against
    N * T(R), T(R) = sum_{q > R} mu(q)^2 / phi(q)^3, which is what the large sieve
    bounds by 2 N T(R) in the document.

Run from the repository root with .venv/bin/python. Writes
results_arc_split_probe.json next to this file. Roughly a minute.
"""
from __future__ import annotations

import json
import math
import os
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "results_arc_split_probe.json")

C2 = 0.6601618158468695739278121100145557784326233602847334133194484233354056423


def sieve_lambda(n_max: int):
    """von Mangoldt Lambda(n), 1 <= n <= n_max, and the primes."""
    spf = np.zeros(n_max + 1, dtype=np.int64)
    primes = []
    for i in range(2, n_max + 1):
        if spf[i] == 0:
            primes.append(i)
            spf[i::i][spf[i::i] == 0] = i
    lam = np.zeros(n_max + 1, dtype=np.float64)
    for p in primes:
        pk = p
        while pk <= n_max:
            lam[pk] = math.log(p)
            pk *= p
    return lam, primes


def mobius_phi(n_max: int):
    mu = np.ones(n_max + 1, dtype=np.int64)
    phi = np.arange(n_max + 1, dtype=np.int64)
    is_p = np.ones(n_max + 1, dtype=bool)
    is_p[:2] = False
    for p in range(2, n_max + 1):
        if not is_p[p]:
            continue
        is_p[2 * p::p] = False
        mu[p::p] *= -1
        mu[p * p::p * p] = 0
        phi[p::p] = phi[p::p] // p * (p - 1)
    return mu, phi


def singular_series(n_max: int, primes):
    """S(h) = 2 C2 prod_{p | h, p > 2} (p-1)/(p-2) for even h, 0 for odd h."""
    s = np.zeros(n_max + 1, dtype=np.float64)
    s[2::2] = 2.0 * C2
    for p in primes:
        if p == 2:
            continue
        s[p::p] *= (p - 1.0) / (p - 2.0)
    return s


def ramanujan_truncation(n_max: int, z: int, mu, phi):
    """S_z(h) = sum_{q <= z} mu(q)^2 c_q(h) / phi(q)^2 for 0 <= h <= n_max."""
    s = np.zeros(n_max + 1, dtype=np.float64)
    for q in range(1, z + 1):
        if mu[q] == 0:
            continue
        cq = np.zeros(n_max + 1, dtype=np.float64)
        # c_q(h) = sum_{d | q, d | h} mu(q/d) d
        for d in range(1, q + 1):
            if q % d == 0 and mu[q // d] != 0:
                cq[0::d] += mu[q // d] * d
        s += cq / float(phi[q]) ** 2
    return s


def psi2(lam: np.ndarray, n_max: int):
    """psi_2(N, h) = sum_{n <= N-h} Lambda(n) Lambda(n+h) for 1 <= h <= N, via FFT."""
    m = 1
    while m < 2 * n_max + 2:
        m *= 2
    f = np.fft.rfft(lam, m)
    corr = np.fft.irfft(np.abs(f) ** 2, m)[: n_max + 1]
    return corr  # index h; corr[0] = sum Lambda^2


def grid_transform(coeffs_pm: np.ndarray, m: int):
    """Values on the grid alpha_j = j/m of sum_{|h|<=N} c(|h|) e(h alpha), c even."""
    v = np.zeros(m, dtype=np.float64)
    n = len(coeffs_pm) - 1
    v[0] = coeffs_pm[0]
    v[1 : n + 1] += coeffs_pm[1:]
    v[m - n :] += coeffs_pm[1:][::-1]
    return np.fft.fft(v)


def main():
    t0 = time.time()
    out = {"note": "measured at fixed N without an exceptional zero; C_N = 0 and E_corr = E"}

    # ---------------------------------------------------------------- (1) identity
    N1 = 2000
    lam, primes = sieve_lambda(N1)
    Z = 7
    P = 2 * 3 * 5
    b = P / (1 * 2 * 4)
    n = np.arange(N1 + 1)
    nu = np.where((n >= 1) & (np.gcd(n, P) == 1), b, 0.0)
    m1 = 1 << 14
    F = np.fft.fft(lam, m1)
    H = np.fft.fft(nu, m1)
    dN = float(np.sum(lam**2))
    sa2 = float(np.sum(nu**2))
    kappa = dN - sa2
    y1 = int(math.isqrt(N1))
    mu, phi = mobius_phi(max(N1, 4096))
    Sy = ramanujan_truncation(N1, y1, mu, phi)
    wts = (N1 - np.arange(N1 + 1)).astype(np.float64) * Sy
    Vy = grid_transform(wts, m1).real
    a0 = dN - N1 * Sy[0]
    Gy = np.abs(F) ** 2 - Vy - a0
    # R_mod = C(|H|^2 - V_y): remove constant coefficients of both
    Rmod = (np.abs(H) ** 2 - sa2) - (Vy - N1 * Sy[0])
    lhs = Gy
    rhs = (np.abs(F) ** 2 - np.abs(H) ** 2) + Rmod - kappa
    out["identity_G_equals_FF_minus_HH_plus_Rmod_minus_kappa"] = {
        "N": N1,
        "Z": Z,
        "max_abs_defect": float(np.max(np.abs(lhs - rhs))),
        "max_abs_G": float(np.max(np.abs(Gy))),
        "kappa": kappa,
        "sign_convention": "kappa = d_N - sum a(n)^2, entering with a minus sign",
    }

    # ---------------------------------------------------------------- (2) arc split
    N = 8000
    lam, primes = sieve_lambda(N)
    m = 1 << 19
    F = np.fft.fft(lam, m)
    F2 = np.abs(F) ** 2
    F4 = F2**2
    y = int(math.isqrt(N))
    Sy = ramanujan_truncation(N, y, mu, phi)
    S = singular_series(N, primes)
    wts = (N - np.arange(N + 1)).astype(np.float64) * Sy
    Vy = grid_transform(wts, m).real
    dN = float(np.sum(lam**2))
    a0 = dN - N * Sy[0]
    Gy = F2 - Vy - a0
    corr = psi2(lam, N)
    E_h = 2.0 * float(np.sum((corr[1:] - (N - np.arange(1, N + 1)) * S[1:]) ** 2))
    J_h = 2.0 * float(np.sum((corr[1:] - (N - np.arange(1, N + 1)) * Sy[1:]) ** 2))
    J_grid = float(np.mean(Gy**2))
    Dtail = 2.0 * float(np.sum(((N - np.arange(1, N + 1)) ** 2) * (S[1:] - Sy[1:]) ** 2))
    alpha = np.arange(m) / m
    L = math.log(N)
    splits = []
    for Q in (3, 6, 12, 24, 48):
        major = np.zeros(m, dtype=bool)
        for q in range(1, Q + 1):
            rad = Q / (q * N)
            for a in range(q):
                if math.gcd(a, q) != 1:
                    continue
                d = np.abs(alpha - a / q)
                d = np.minimum(d, 1.0 - d)
                major |= d <= rad
        minor = ~major
        main_poly = Vy + a0
        splits.append(
            {
                "Q": Q,
                "measure_major": float(np.mean(major)),
                "measure_major_over_2Q2_over_N": float(np.mean(major) / (2 * Q * Q / N)),
                "int_major_G2": float(np.mean(Gy[major] ** 2 * 1.0) * np.mean(major)) if major.any() else 0.0,
                "int_minor_G2": float(np.sum(Gy[minor] ** 2) / m),
                "int_minor_F4": float(np.sum(F4[minor]) / m),
                "int_minor_F4_over_N3_over_Q": float(np.sum(F4[minor]) / m / (N**3 / Q)),
                "int_minor_F4_over_N3_L6_over_Q": float(np.sum(F4[minor]) / m / (N**3 * L**6 / Q)),
                "int_minor_mainpoly2": float(np.sum(main_poly[minor] ** 2) / m),
                "int_minor_mainpoly2_over_N3_over_Q2": float(np.sum(main_poly[minor] ** 2) / m / (N**3 / Q**2)),
                "sup_minor_F2_over_N2_over_Q": float(np.max(F2[minor]) / (N**2 / Q)),
            }
        )
    # fix the major integral (mean over major set times measure = sum/m)
    for s in splits:
        s["int_major_G2"] = J_grid - s["int_minor_G2"]
    out["arc_split"] = {
        "N": N,
        "grid": m,
        "y": y,
        "E_from_h_space": E_h,
        "J_ms_from_h_space": J_h,
        "J_ms_from_grid": J_grid,
        "parseval_relative_defect": abs(J_h - J_grid) / J_h,
        "D_tail_N_y": Dtail,
        "D_tail_over_N2": Dtail / N**2,
        "sqrtE_minus_sqrtJ_over_sqrtDtail": (math.sqrt(E_h) - math.sqrt(J_h)) / math.sqrt(Dtail),
        "N3": float(N**3),
        "splits": splits,
    }

    # ---------------------------------------------------------------- (3) tail mean square
    tails = []
    for R in (5, 10, 20, 40, 80):
        SR = ramanujan_truncation(N, R, mu, phi)
        ms = float(np.sum((S[1:] - SR[1:]) ** 2))
        qs = np.arange(R + 1, 200001)
        # T(R) = sum_{q > R} mu^2 / phi^3, tail beyond 2e5 is below 1e-11
        mu2, phi2 = mobius_phi(200000)
        TR = float(np.sum((mu2[R + 1 :] ** 2) / phi2[R + 1 :].astype(np.float64) ** 3))
        tails.append(
            {
                "R": R,
                "sum_h_tail_sq": ms,
                "N_times_T_R": N * TR,
                "ratio_to_N_T_R": ms / (N * TR),
                "ratio_to_large_sieve_bound_2N_T_R": ms / (2 * N * TR),
            }
        )
    out["tail_mean_square"] = {"N": N, "rows": tails}
    out["elapsed_s"] = time.time() - t0
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
