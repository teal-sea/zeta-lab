"""Finite checks for MAJOR_ARC_EXPLICIT.md.

Three measurements at fixed N, none of them a test of an asymptotic statement.

(1) The oscillatory integrals I_rho(theta) = int_1^N t^(rho-1) e(t theta) dt for the
    first zeros of zeta, against the two bounds the document uses: N^beta/sqrt|gamma|
    when |gamma| < 4 pi N |theta| (stationary regime) and N^beta/|gamma| otherwise.
    Reports the largest ratio observed in each regime.
(2) The exponential-sum explicit formula: F(theta) = sum_{n<=N} Lambda(n) e(n theta)
    against K_N(theta) - sum_{|gamma|<=T} I_rho(theta), for small theta and moderate T,
    with the defect compared to (N/T) log^2 N (1 + N|theta|).
(3) The Plancherel identity behind the major-arc lemma: for a prime modulus r,
    sum over reduced a of |W(a/r + theta)|^2 equals (r/phi(r)) sum over chi of
    |V_chi(theta)|^2 up to the residue classes not coprime to r, checked with a toy
    model at Z = 7 and every character mod 7.

Run from the repository root with .venv/bin/python. Writes
results_major_arc_explicit_probe.json next to this file. About a minute; the
zeros of zeta come from mpmath.zetazero.
"""
from __future__ import annotations

import cmath
import json
import math
import os
import time

import mpmath as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "results_major_arc_explicit_probe.json")


def sieve_lambda(n_max: int):
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
    return lam


_GL_X, _GL_W = np.polynomial.legendre.leggauss(24)


def I_rho(rho, theta, N):
    """int_1^N t^(rho-1) exp(2 pi i theta t) dt by composite Gauss-Legendre.

    Panels are chosen so that each carries at most about a quarter of an
    oscillation of either phase (2 pi theta t and gamma log t); 24 nodes per
    panel then give far better than the 1e-6 relative accuracy the ratios need.
    """
    gamma = abs(rho.imag)
    n_osc = abs(theta) * (N - 1) + gamma * math.log(N) / (2 * math.pi)
    panels = int(4 * n_osc) + 64
    edges = np.exp(np.linspace(0.0, math.log(N), panels + 1))
    a = edges[:-1][:, None]
    b = edges[1:][:, None]
    t = 0.5 * (b - a) * _GL_X[None, :] + 0.5 * (b + a)
    w = 0.5 * (b - a) * _GL_W[None, :]
    vals = np.exp((rho - 1) * np.log(t) + 2j * math.pi * theta * t)
    return complex(np.sum(w * vals))


def main():
    t0 = time.time()
    out = {}

    # ------------------------------------------------------------- (1) I_rho bounds
    zeros = []
    with mp.workdps(25):
        for k in range(1, 61):
            zeros.append(complex(mp.zetazero(k)))
    rows = []
    worst_stat, worst_far = 0.0, 0.0
    for N in (10**4, 10**6):
        for Ntheta in (0.0, 1.0, 10.0, 100.0):
            theta = Ntheta / N
            for rho in zeros:
                beta, gamma = rho.real, abs(rho.imag)
                val = abs(I_rho(rho, theta, N))
                stationary = gamma < 4 * math.pi * Ntheta
                if stationary:
                    ratio = val / (N**beta / math.sqrt(gamma))
                    worst_stat = max(worst_stat, ratio)
                else:
                    ratio = val / (N**beta / gamma)
                    worst_far = max(worst_far, ratio)
                rows.append({"N": N, "N_theta": Ntheta, "gamma": gamma, "abs_I": val,
                             "regime": "stationary" if stationary else "far", "ratio_to_bound": ratio})
    out["I_rho_bounds"] = {
        "zeros_used": len(zeros),
        "gamma_max": max(abs(z.imag) for z in zeros),
        "worst_ratio_stationary_regime_vs_Nbeta_over_sqrt_gamma": worst_stat,
        "worst_ratio_far_regime_vs_Nbeta_over_gamma": worst_far,
        "n_rows": len(rows),
        "sample_rows": rows[:6] + rows[-6:],
    }

    # ---------------------------------------------------- (2) exponential-sum explicit formula
    N = 2000
    lam = sieve_lambda(N)
    Tz = 400.0
    zs = []
    with mp.workdps(25):
        k = 1
        while True:
            z = complex(mp.zetazero(k))
            if z.imag > Tz:
                break
            zs.append(z)
            k += 1
    ef_rows = []
    for Ntheta in (0.0, 0.5, 2.0, 5.0):
        theta = Ntheta / N
        F = sum(lam[n] * cmath.exp(2j * math.pi * n * theta) for n in range(1, N + 1))
        K = sum(cmath.exp(2j * math.pi * n * theta) for n in range(1, N + 1))
        Z = 0j
        for z in zs:
            Iv = I_rho(z, theta, N)
            Z += Iv + I_rho(z.conjugate(), theta, N)
        pred = K - Z
        defect = abs(F - pred)
        scale = (N / Tz) * math.log(N) ** 2 * (1 + N * theta)
        ef_rows.append({"N_theta": Ntheta, "abs_F": abs(F), "abs_pred": abs(pred),
                        "abs_defect": defect, "defect_over_scale": defect / scale,
                        "abs_zero_sum": abs(Z)})
    out["explicit_formula"] = {"N": N, "T": Tz, "zeros_with_gamma_le_T": len(zs), "rows": ef_rows}

    # ---------------------------------------------------------- (3) Plancherel identity
    N = 3000
    lam = sieve_lambda(N)
    P = 2 * 3 * 5
    b = P / 8
    n = np.arange(N + 1)
    nu = np.where((n >= 1) & (np.gcd(n, P) == 1), b, 0.0)
    w = lam - nu
    r = 7
    g = 3  # primitive root mod 7
    # characters chi_j(g^k) = e(jk/6)
    log_table = {}
    x = 1
    for k in range(6):
        log_table[x] = k
        x = (x * g) % r
    theta = 3.0 / (r * N)
    lhs = 0.0
    for a in range(1, r):
        Wa = sum(w[m] * cmath.exp(2j * math.pi * m * (a / r + theta)) for m in range(1, N + 1))
        lhs += abs(Wa) ** 2
    rhs = 0.0
    for j in range(6):
        V = 0j
        for m in range(1, N + 1):
            if m % r == 0:
                continue
            chi = cmath.exp(2j * math.pi * j * log_table[m % r] / 6)
            V += w[m] * chi * cmath.exp(2j * math.pi * m * theta)
        rhs += abs(V) ** 2
    rhs *= r / (r - 1)
    # residue class 0 mod r carries Lambda at powers of 7 only
    W0 = sum(w[m] * cmath.exp(2j * math.pi * m * theta) for m in range(r, N + 1, r))
    # exact identity: sum over ALL a mod r of |W(a/r+theta)|^2 = r sum over ALL classes b of |W_b|^2,
    # and the coprime classes give (r/phi(r)) sum_chi |V_chi|^2; so
    #   sum_{(a,r)=1} |W|^2 + |W(theta)|^2 = (r/phi(r)) sum_chi |V_chi|^2 + r |W_0|^2.
    # In the toy, Z = 7 does not exceed r = 7, so class 0 carries model mass and is not small;
    # in the document's setting r < Z and the class is O(log^2 N).
    Wfull0 = sum(w[m] * cmath.exp(2j * math.pi * m * theta) for m in range(1, N + 1))
    lhs_all = lhs + abs(Wfull0) ** 2
    rhs_all = rhs + r * abs(W0) ** 2
    out["plancherel"] = {
        "N": N, "r": r, "theta_times_rN": theta * r * N,
        "sum_reduced_a_abs_W_sq": lhs,
        "r_over_phi_times_sum_chi_abs_V_sq": rhs,
        "abs_W_at_theta_sq": abs(Wfull0) ** 2,
        "r_times_abs_W_class0_sq": r * abs(W0) ** 2,
        "identity_lhs_all": lhs_all,
        "identity_rhs_all": rhs_all,
        "identity_relative_defect": abs(lhs_all - rhs_all) / rhs_all,
        "note": "exact identity over all a and all classes; the toy's Z = 7 does not exceed r, so class 0 mod 7 is not small here, unlike the document's setting r < Z",
    }
    out["elapsed_s"] = time.time() - t0
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    print(json.dumps({k: v for k, v in out.items() if k != "I_rho_bounds"}, indent=1, default=float))
    print(json.dumps({k: v for k, v in out["I_rho_bounds"].items() if k != "sample_rows"}, indent=1))


if __name__ == "__main__":
    main()
