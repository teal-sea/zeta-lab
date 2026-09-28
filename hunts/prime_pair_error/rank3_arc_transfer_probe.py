"""Numeric check for RANK3_ARC_TRANSFER.md.

Checks, for small N and several q, by direct evaluation of F_N, K_N,
P_{q,a}, R_{q,a} as finite exponential sums (no asymptotics):

1. Monotonicity: for every (q,a), the arc integral
   int_{I_{q,a}} |P_{q,a}|^2 |R_{q,a}|^2 is <= the full-circle integral
   T_N(q,a) = int_T |P_{q,a}|^2 |R_{q,a}|^2. This is the elementary fact
   the write-up leans on (nonnegative integrand, arc subset of the circle).

2. The exact Parseval identity (D7) of RANK3_ROUTE_D.md: summed over
   reduced a mod q, int_T |K_N|^2 |R1_{q,a}|^2 equals
   Sigma_diag(q) + Sigma_cross(q), computed independently from T(q,b),
   X(b,b') via (D5)-(D6). This cross-checks that the definitions used in
   the write-up match RANK3_ROUTE_D.md's, since the monotonicity argument
   is only useful if T_N(q,a) really is the object (D10) bounds.

All integrals are over trigonometric polynomials of bounded degree, so a
uniform grid of M points computes them exactly (DC term recovered exactly
whenever M exceeds twice the max frequency present, so no nonzero frequency
aliases to 0); the arc integral uses plain numerical quadrature (quad) since
it is not a full-circle average.
"""
import json

import numpy as np
import sympy
from scipy import integrate


def Lambda(n):
    if n < 2:
        return 0.0
    f = sympy.factorint(n)
    if len(f) == 1:
        p = next(iter(f))
        return float(sympy.log(p))
    return 0.0


def run_check(N, qs_as, verbose=True):
    Lam = np.array([Lambda(n) for n in range(0, N + 1)])

    def K(alpha):
        n = np.arange(1, N + 1)
        return np.sum(np.exp(2j * np.pi * n * alpha))

    def F(alpha):
        n = np.arange(1, N + 1)
        return np.sum(Lam[1:N + 1] * np.exp(2j * np.pi * n * alpha))

    def mu(q):
        return int(sympy.mobius(q))

    def phi(q):
        return int(sympy.totient(q))

    results = []
    for (q, a) in qs_as:
        m, ph = float(mu(q)), float(phi(q))

        def P(alpha):
            return (m / ph) * K(alpha - a / q)

        def R(alpha):
            return F(alpha) - P(alpha)

        def integrand(alpha):
            return abs(P(alpha)) ** 2 * abs(R(alpha)) ** 2

        M = 16 * N + 5
        grid = np.arange(M) / M
        n = np.arange(1, N + 1)
        Fg = (Lam[1:N + 1][None, :] * np.exp(2j * np.pi * np.outer(grid, n))).sum(axis=1)
        Kg_shifted = np.exp(2j * np.pi * np.outer(grid - a / q, n)).sum(axis=1)
        Pg = (m / ph) * Kg_shifted
        Rg = Fg - Pg
        T_full = np.mean(np.abs(Pg) ** 2 * np.abs(Rg) ** 2).real

        Q = max(1, int(np.floor(np.sqrt(N) / 3)))
        delta_q = Q / (q * N)
        lo, hi = a / q - delta_q, a / q + delta_q
        arc_val, err = integrate.quad(integrand, lo, hi, limit=200)

        ok = bool(arc_val <= T_full + 1e-9)
        results.append((q, a, N, arc_val, T_full, ok))
        if verbose:
            print(
                "N=%4d q=%3d a=%3d  arc=%14.4f  T_full=%14.4f  arc<=T_full: %s"
                % (N, q, a, arc_val, T_full, ok)
            )
    return results


def check_D7_identity(N, q, verbose=True):
    Lam = np.array([Lambda(n) for n in range(0, N + 1)])
    reduced = [b for b in range(q) if sympy.gcd(b, q) == 1]
    ph = len(reduced)

    def Delta(t, b):
        s = sum(Lam[n] for n in range(1, t + 1) if n % q == b)
        return s - t / ph

    def T_qb(b):
        s1 = sum(Delta(t, b) ** 2 for t in range(1, N + 1))
        s2 = sum((Delta(N, b) - Delta(t, b)) ** 2 for t in range(1, N))
        return s1 + s2

    def X_bb(b, bp):
        s1 = sum(Delta(t, b) * Delta(t, bp) for t in range(1, N + 1))
        s2 = sum(
            (Delta(N, b) - Delta(t, b)) * (Delta(N, bp) - Delta(t, bp))
            for t in range(1, N)
        )
        return s1 + s2

    Tvals = {b: T_qb(b) for b in reduced}
    Sigma_diag = ph * sum(Tvals.values())

    def c_q(k):
        return sum(
            np.exp(2j * np.pi * a * k / q) for a in reduced if sympy.gcd(a, q) == 1
        ).real

    Sigma_cross = 0.0
    for b in reduced:
        for bp in reduced:
            if b == bp:
                continue
            Sigma_cross += c_q((b - bp) % q) * X_bb(b, bp)

    lhs_total = Sigma_diag + Sigma_cross

    def K(alpha):
        n = np.arange(1, N + 1)
        return np.sum(np.exp(2j * np.pi * n * alpha))

    M = 16 * N + 5
    grid = np.arange(M) / M
    n = np.arange(1, N + 1)
    Kg = np.exp(2j * np.pi * np.outer(grid, n)).sum(axis=1)

    direct_total = 0.0
    for a in reduced:
        R1 = np.zeros(M, dtype=complex)
        for b in reduced:
            coeff = np.exp(2j * np.pi * a * b / q)
            mask = (n % q == b)
            d_coeffs = Lam[1:N + 1] * mask - (1.0 / ph)
            Db = (d_coeffs[None, :] * np.exp(2j * np.pi * np.outer(grid, n))).sum(axis=1)
            R1 += coeff * Db
        direct_total += np.mean(np.abs(Kg) ** 2 * np.abs(R1) ** 2).real

    if verbose:
        match = abs(direct_total - lhs_total) < 1e-6 * max(1, abs(lhs_total))
        print(
            "N=%d q=%d: D7 lhs(direct)=%.6f  Sigma_diag+Sigma_cross=%.6f  match: %s"
            % (N, q, direct_total, lhs_total, match)
        )
    return direct_total, lhs_total


if __name__ == "__main__":
    print("=== Monotonicity check: arc integral <= full-circle T_N(q,a) ===")
    qas = [(2, 1), (3, 1), (3, 2), (5, 1), (5, 3), (6, 1)]
    res = run_check(120, qas)
    all_ok = bool(all(r[5] for r in res))
    print("ALL MONOTONICITY CHECKS PASS:", all_ok)

    print()
    print("=== (D7) exact identity cross-check ===")
    d7ok = []
    for N, q in [(80, 2), (80, 3), (60, 4), (60, 5)]:
        direct, formula = check_D7_identity(N, q)
        d7ok.append(bool(abs(direct - formula) < 1e-6 * max(1, abs(formula))))
    print("ALL D7 IDENTITY CHECKS PASS:", all(d7ok))

    with open(
        "hunts/prime_pair_error/results_rank3_arc_transfer_probe.json", "w"
    ) as f:
        json.dump(
            {
                "monotonicity_checks": [
                    {
                        "N": r[2],
                        "q": r[0],
                        "a": r[1],
                        "arc": r[3],
                        "T_full": r[4],
                        "ok": r[5],
                    }
                    for r in res
                ],
                "all_monotonicity_ok": all_ok,
                "all_D7_identity_ok": all(d7ok),
            },
            f,
            indent=2,
        )
