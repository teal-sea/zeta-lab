#!/usr/bin/env python3
"""Independent check of the factorial-certificate pilot (review side, 2026-09-06).

This file is a NEW output of the review. It shares no code with ``../pilot.py``: it
reads the preserved ``../results.json`` as data and re-derives every claim it can
touch with its own arithmetic. What it establishes is finite and exact; what it does
not establish (the general argument in ``../PILOT.md`` sections 1 to 3) is reviewed
by hand in ``../REVIEW.md``. Nothing here is a prime-counting record and nothing
bears on RH.

Checks, in order:

1. Every recorded seed (period L, radix M, coefficients a_j): balance sum a_j/j = 0,
   g(r) >= 0 for r = 0..L-1 and g(r) >= 1 for r = 1..M-1, in Fractions only. This
   is the same finite check the pilot ran, redone from scratch.
2. The leading constant C = kappa / (1 - 1/M), kappa = -sum a_j log(j)/j, at 40
   digits (mpmath), against the recorded float, for all 87 seeds.
3. The pilot's lower bound C - 1 >= [1/(L+1) - 1/(L+2)] / (1 - 1/M) for all 87 seeds.
4. The integral representation kappa = int_1^inf g(t)/t^2 dt: the truncated integral
   has the closed form sum_j a_j [H_{floor(R/j)}/j - floor(R/j)/R]; at R = 10^7 it
   must agree with kappa to O(1/R) (checked for the three selected seeds).
5. The factorial inequality |log(floor(y)!) - (y log y - y)| <= 1 + log^+(y) on a
   grid of 20,000 reals in [0, 10^4] plus every integer to 10^5.
6. The certificate itself for all 87 seeds at N in {10^3, 10^4, 10^5} and for the
   three selected seeds at N = 10^6: psi(N) <= B_N <= C N + A (K+1)(1 + log N), with
   psi from an independent sieve of von Mangoldt and B_N from log-factorials at 30
   digits; also the sharper two-sided budget with the (1 - M^{-K-1}) factor and the
   -log(M) K(K+1)/2 term.
7. The identity B_N = sum_d Lambda(d) W_N(N/d) in integers only, for the three
   selected seeds at N = 10^4: for every prime p <= N the exponent of p in
   prod_{k,j} floor(N/(j M^k))!^{a_j} (Legendre) equals sum_{p^i <= N} W_N(N/p^i),
   and every W_N(N/p^i) is >= 1.

Run from this directory:  ../../../../../../.venv/bin/python check_pilot.py
Writes check_pilot.json next to itself.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
RESULTS = HERE.parent / "results.json"
OUT = HERE / "check_pilot.json"


# ---------------------------------------------------------------- helpers ---

def seed_of(case: dict) -> dict[int, Fraction]:
    return {int(j): Fraction(a) for j, a in case["coefficients"].items()}


def g_at(seed: dict[int, Fraction], t: Fraction) -> Fraction:
    return sum((a * (t // j) for j, a in seed.items()), Fraction(0))


def check_period(L: int, M: int, seed: dict[int, Fraction]) -> dict:
    assert 2 <= M <= L, (L, M)
    assert all(L % j == 0 for j in seed), "an index does not divide the period"
    balance = sum((a / j for j, a in seed.items()), Fraction(0))
    assert balance == 0, f"balance {balance}"
    worst_nonneg = None
    worst_one = None
    for r in range(L):
        v = g_at(seed, Fraction(r))
        need = 1 if 1 <= r < M else 0
        assert v >= need, f"g({r}) = {v} < {need}"
        slack = v - need
        if need == 0:
            worst_nonneg = slack if worst_nonneg is None else min(worst_nonneg, slack)
        else:
            worst_one = slack if worst_one is None else min(worst_one, slack)
    # periodicity, as a computed fact rather than a remembered one
    for r in (0, 1, M - 1, L - 1):
        assert g_at(seed, Fraction(r + L)) == g_at(seed, Fraction(r))
        assert g_at(seed, Fraction(r) + Fraction(1, 3)) == g_at(seed, Fraction(r))
    return {"min_slack_nonneg": str(worst_nonneg), "min_slack_one": str(worst_one)}


def constant(seed: dict[int, Fraction], M: int) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    with mp.workdps(40):
        kappa = -sum(mp.mpf(a.numerator) / a.denominator * mp.log(j) / j for j, a in seed.items())
        C = kappa / (1 - mp.mpf(1) / M)
        A_exact = sum((abs(a) for a in seed.values()), Fraction(0))
        A = mp.mpf(A_exact.numerator) / A_exact.denominator
        return kappa, C, A


def lifted(seed: dict[int, Fraction], M: int, N: int) -> tuple[dict[int, Fraction], int]:
    """Coefficients of W_N at indices j*M^k, and K = floor(log_M N) by integer powers."""
    out: dict[int, Fraction] = {}
    power, K = 1, -1
    while power <= N:
        K += 1
        for j, a in seed.items():
            out[j * power] = out.get(j * power, Fraction(0)) + a
        power *= M
    return {j: a for j, a in out.items() if a}, K


def W_N(seed: dict[int, Fraction], M: int, N: int, t: Fraction) -> Fraction:
    coeffs, _ = lifted(seed, M, N)
    return sum((a * (t // j) for j, a in coeffs.items()), Fraction(0))


def mangoldt_sieve(N: int) -> tuple[list[int], list[float]]:
    """Smallest prime factor table; returns (spf, log Lambda(n)) with Lambda as float logs."""
    spf = list(range(N + 1))
    for i in range(2, math.isqrt(N) + 1):
        if spf[i] == i:
            for k in range(i * i, N + 1, i):
                if spf[k] == k:
                    spf[k] = i
    return spf


def psi_exact(spf: list[int], N: int) -> mp.mpf:
    """psi(N) = sum_{p^i <= N} log p, at 30 digits."""
    with mp.workdps(30):
        total = mp.mpf(0)
        for n in range(2, N + 1):
            p = spf[n]
            m = n
            while m % p == 0:
                m //= p
            if m == 1:
                total += mp.log(p)
        return total


def B_N(seed: dict[int, Fraction], M: int, N: int) -> mp.mpf:
    coeffs, _ = lifted(seed, M, N)
    with mp.workdps(30):
        return sum(
            (mp.mpf(a.numerator) / a.denominator) * mp.loggamma(N // j + 1)
            for j, a in coeffs.items()
        )


def legendre(n: int, p: int) -> int:
    v, m = 0, n
    while m:
        m //= p
        v += m
    return v


# ---------------------------------------------------------------- checks ----

def main() -> int:
    data = json.loads(RESULTS.read_text(encoding="utf-8"))
    cases = data["cases"]
    best = data["best_in_numerical_search"]
    report: dict = {
        "note": "review-side rerun, independent code; see check_pilot.py docstring",
        "cases_in_record": len(cases),
    }

    # 1 + 2 + 3: every seed
    per_case = []
    max_C_gap = mp.mpf(0)
    for case in cases:
        L, M = case["period"], case["radix"]
        seed = seed_of(case)
        slack = check_period(L, M, seed)
        kappa, C, A = constant(seed, M)
        gap = abs(C - mp.mpf(case["leading_constant_float"]))
        max_C_gap = max(max_C_gap, gap)
        lower = (Fraction(1, L + 1) - Fraction(1, L + 2)) / (1 - Fraction(1, M))
        assert C - 1 >= mp.mpf(lower.numerator) / lower.denominator, (L, M)
        assert kappa >= 1 - mp.mpf(1) / M, (L, M)
        assert sum((abs(a) for a in seed.values()), Fraction(0)) == Fraction(case["coefficient_l1"]), (L, M)
        per_case.append({"L": L, "M": M, "C_40dps": mp.nstr(C, 20), "A": str(A),
                         "C_minus_1_lower_bound": str(lower), **slack})
    report["all_87_seeds_exact_feasible"] = True
    report["max_abs_gap_C_40dps_vs_recorded_float"] = mp.nstr(max_C_gap, 5)
    assert max_C_gap < 1e-12
    report["per_case"] = per_case

    # 4: integral representation of kappa, three selected seeds, R = 10^7
    R = 10**7
    integral_rows = []
    for case in best:
        L, M = case["period"], case["radix"]
        seed = seed_of(case)
        kappa, C, A = constant(seed, M)
        with mp.workdps(40):
            trunc = mp.mpf(0)
            for j, a in seed.items():
                n = R // j
                trunc += (mp.mpf(a.numerator) / a.denominator) * (mp.harmonic(n) / j - mp.mpf(n) / R)
            gap = abs(trunc - kappa)
        assert gap < 10 * A / R, (L, M, gap)
        integral_rows.append({"L": L, "M": M, "R": R, "kappa": mp.nstr(kappa, 20),
                              "truncated_integral": mp.nstr(trunc, 20), "abs_gap": mp.nstr(gap, 5)})
    report["kappa_integral_representation"] = integral_rows

    # 5: the factorial inequality
    with mp.workdps(30):
        worst = mp.mpf(0)
        ys = [mp.mpf(i) / 2 for i in range(0, 2 * 10**4 + 1)]  # half-integers to 10^4
        ys += [mp.mpf(k) * mp.sqrt(2) for k in range(0, 7072)]  # irrationals to 10^4
        for y in ys:
            m = int(mp.floor(y))
            lhs = abs(mp.loggamma(m + 1) - (y * mp.log(y) - y if y > 0 else 0))
            rhs = 1 + (mp.log(y) if y >= 1 else 0)
            assert lhs <= rhs, y
            worst = max(worst, lhs / rhs)
        for m in range(0, 10**5 + 1):
            y = mp.mpf(m)
            lhs = abs(mp.loggamma(m + 1) - (y * mp.log(y) - y if m else 0))
            assert lhs <= 1 + (mp.log(y) if m >= 1 else 0)
    report["factorial_inequality"] = {"points_checked": len(ys) + 10**5 + 1,
                                      "max_ratio_lhs_over_rhs": mp.nstr(worst, 8)}

    # 6: the certificate against an independent psi
    NMAX = 10**6
    spf = mangoldt_sieve(NMAX)
    psi = {N: psi_exact(spf, N) for N in (10**3, 10**4, 10**5, 10**6)}
    report["psi"] = {str(N): mp.nstr(v, 20) for N, v in psi.items()}
    cert_rows = []
    for case in cases:
        L, M = case["period"], case["radix"]
        seed = seed_of(case)
        kappa, C, A = constant(seed, M)
        selected = any(b["period"] == L and b["radix"] == M for b in best)
        for N in (10**3, 10**4, 10**5) + ((10**6,) if selected else ()):
            _, K = lifted(seed, M, N)
            assert M**K <= N < M ** (K + 1)
            B = B_N(seed, M, N)
            with mp.workdps(30):
                logN = mp.log(N)
                simple = C * N + A * (K + 1) * (1 + logN)
                err = A * ((K + 1) * (1 + logN) - mp.log(M) * K * (K + 1) / 2)
                main_term = kappa * N * (1 - mp.mpf(M) ** (-K - 1)) / (1 - mp.mpf(1) / M)
                assert psi[N] <= B, (L, M, N, "psi > B_N")
                assert B <= simple, (L, M, N, "B_N > simple budget")
                assert main_term - err <= B <= main_term + err, (L, M, N, "two-sided budget")
                cert_rows.append({"L": L, "M": M, "N": N, "K": K,
                                  "psi": mp.nstr(psi[N], 15), "B_N": mp.nstr(B, 15),
                                  "B_N_over_N": mp.nstr(B / N, 12), "C": mp.nstr(C, 12),
                                  "B_N_minus_CN": mp.nstr(B - C * N, 8),
                                  "budget_A(K+1)(1+logN)": mp.nstr(A * (K + 1) * (1 + logN), 8)})
    report["certificate_rows"] = cert_rows
    report["certificate_rows_count"] = len(cert_rows)

    # 7: the factorial identity in integers, three selected seeds, N = 10^4
    N = 10**4
    primes = [p for p in range(2, N + 1) if spf[p] == p]
    ident_rows = []
    for case in best:
        L, M = case["period"], case["radix"]
        seed = seed_of(case)
        coeffs, _ = lifted(seed, M, N)
        min_W = None
        for p in primes:
            left = sum((a * legendre(N // j, p) for j, a in coeffs.items()), Fraction(0))
            right = Fraction(0)
            q = p
            while q <= N:
                w = W_N(seed, M, N, Fraction(N, q))
                assert w >= 1, (L, M, p, q, w)
                min_W = w if min_W is None else min(min_W, w)
                right += w
                q *= p
            assert left == right, (L, M, p, left, right)
        ident_rows.append({"L": L, "M": M, "N": N, "primes_checked": len(primes),
                           "min_W_N_at_prime_powers": str(min_W)})
    report["factorial_identity_integer_check"] = ident_rows

    OUT.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    print(f"{len(cases)} seeds exact-feasible; max |C gap| {mp.nstr(max_C_gap, 3)}; "
          f"{len(cert_rows)} certificate rows psi(N) <= B_N <= budget; "
          f"identity checked at {len(primes)} primes x 3 seeds. Wrote {OUT.name}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
