"""One fixed-cutoff algebra check for SIEGEL_UNIFORMITY.md.

Run from the repository root with .venv/bin/python. No CLI size override.
The character and beta fixture does not assert an exceptional zero exists.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import signal
import time
from fractions import Fraction

for variable in (
    "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS",
):
    os.environ[variable] = "1"

N = 128
LIMIT_SECONDS = 60
HERE = Path(__file__).resolve().parent
PROOF = HERE.parent.parent / "SIEGEL_UNIFORMITY.md"


def timeout(_signum, _frame):
    raise TimeoutError("The fixed 60-second diagnostic limit expired")


def factors(n):
    result = {}
    for p in range(2, math.isqrt(n) + 1):
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def mobius(n):
    fs = factors(n)
    return 0 if any(e > 1 for e in fs.values()) else (-1) ** len(fs)


def phi(n):
    answer = n
    for p in factors(n):
        answer = answer // p * (p - 1)
    return answer


def ramanujan(q, h):
    return sum(d * mobius(q // d) for d in range(1, q + 1)
               if q % d == 0 and h % d == 0)


def legendre(p):
    def value(n):
        r = n % p
        return 0 if r == 0 else (1 if pow(r, (p - 1) // 2, p) == 1 else -1)
    return value


def local_characters():
    chi4 = lambda n: (0, 1, 0, -1)[n % 4]
    chi8 = lambda n: (0, 1, 0, -1, 0, -1, 0, 1)[n % 8]
    chi_minus8 = lambda n: chi4(n) * chi8(n)
    chi3, chi5 = legendre(3), legendre(5)
    return [
        (3, "chi3", chi3), (4, "chi4", chi4), (5, "chi5", chi5),
        (8, "chi8", chi8), (8, "chi_minus8", chi_minus8),
        (12, "chi4_chi3", lambda n: chi4(n) * chi3(n)),
        (15, "chi3_chi5", lambda n: chi3(n) * chi5(n)),
        (24, "chi8_chi3", lambda n: chi8(n) * chi3(n)),
        (24, "chi_minus8_chi3", lambda n: chi_minus8(n) * chi3(n)),
    ]


def exact_checks():
    character_rows = []
    for q, name, chi in local_characters():
        assert sum(chi(r) for r in range(q)) == 0
        assert all(any(chi(r) != chi(r + d) for r in range(q))
                   for d in range(1, q) if q % d == 0)
        for h in range(q):
            admissible = [r for r in range(q) if math.gcd(r * (r + h), q) == 1]
            u = sum(chi(r) for r in admissible)
            v = sum(chi(r + h) for r in admissible)
            assert u == (mobius(q) * chi(-h) if q % 2 else 0)
            assert v == (mobius(q) * chi(h) if q % 2 else 0)
            assert sum(chi(r) * chi(r + h) for r in range(q)) == ramanujan(q, h)
        assert sum(ramanujan(q, h) ** 2 for h in range(q)) == q * phi(q)
        for d in range(1, q + 1):
            if math.gcd(d, q) == 1:
                assert all(ramanujan(q, d * h) == ramanujan(q, h) for h in range(q))
        character_rows.append({"conductor": q, "character": name, "shifts": q})
    pair_sums = [0] * (2 * N + 1)
    for a in range(1, N + 1):
        for b in range(1, N + 1):
            pair_sums[a + b] += 1
    count = sum(c * c for c in pair_sums)
    assert count == N * N + 2 * sum(j * j for j in range(1, N))
    assert count == (2 * N ** 3 + N) // 3
    return {"character_rows": character_rows, "additive_quadruples": count}


def main():
    import numpy as np
    from mpmath import mp

    report = {"exact": exact_checks()}
    with mp.workdps(50):
        Z = mp.exp(mp.log(N) ** mp.mpf("0.1"))
        primes = [p for p in range(2, N + 1) if factors(p) == {p: 1}]
        sieve_primes = [p for p in primes if p < Z]
        assert sieve_primes == [2, 3]
        P = math.prod(sieve_primes)
        b = Fraction(P, phi(P))
        b2 = b * b
        lam = [mp.mpf(0)] * (N + 1)
        proper_powers = []
        for p in primes:
            power, exponent = p, 1
            while power <= N:
                lam[power] = mp.log(p)
                if exponent > 1:
                    proper_powers.append(power)
                power *= p
                exponent += 1
        for n in range(1, N + 1):
            fs = factors(n)
            expected = mp.log(next(iter(fs))) if len(fs) == 1 else mp.mpf(0)
            assert lam[n] == expected

        q, chi, beta = 3, legendre(3), mp.mpf("0.99")
        delta = 1 - beta
        nu = [mp.mpf(0)] + [
            mp.mpf(b.numerator) / b.denominator if math.gcd(n, P) == 1 else mp.mpf(0)
            for n in range(1, N + 1)
        ]
        model = [mp.mpf(0)] + [
            nu[n] * (1 - mp.power(n, -delta) * chi(n)) for n in range(1, N + 1)
        ]

        def corr(seq, h):
            return mp.fsum(seq[n] * seq[n + h] for n in range(1, N - h + 1))

        residual = [x - y for x, y in zip(lam, model)]
        fourth_direct = corr(residual, 0) ** 2 + 2 * mp.fsum(
            corr(residual, h) ** 2 for h in range(1, N + 1)
        )
        D_direct = 2 * mp.fsum(
            (corr(lam, h) - corr(model, h)) ** 2 for h in range(1, N + 1)
        )
        grid_size = 4 * N + 1
        F = np.fft.fft(np.array([float(x) for x in lam]), n=grid_size)
        H = np.fft.fft(np.array([float(x) for x in model]), n=grid_size)
        W = F - H
        difference = abs(F) ** 2 - abs(H) ** 2
        D_grid = float(np.mean((difference - np.mean(difference)) ** 2))
        fourth_grid = float(np.mean(abs(W) ** 4))
        relative_D = abs(D_grid / float(D_direct) - 1)
        relative_fourth = abs(fourth_grid / float(fourth_direct) - 1)
        assert relative_D < 1e-11 and relative_fourth < 1e-11
        holder_rhs = fourth_grid ** 0.25 * (
            float(np.mean(abs(F) ** 4)) ** 0.25 +
            float(np.mean(abs(H) ** 4)) ** 0.25
        )
        assert math.sqrt(D_grid) <= holder_rhs * (1 + 1e-12)
        report["fourier_float_checks"] = {
            "grid_size": grid_size, "mpmath_decimal_digits": 50,
            "D_direct": str(D_direct), "D_grid": D_grid,
            "fourth_direct": str(fourth_direct), "fourth_grid": fourth_grid,
            "normalized_U2_fourth": str(fourth_direct / report["exact"]["additive_quadruples"]),
            "relative_D_defect": relative_D, "relative_fourth_defect": relative_fourth,
            "centered_norm": math.sqrt(D_grid), "holder_upper_bound": holder_rhs,
        }

        def alpha(p, h):
            rho = 1 if h % p == 0 else 2
            return Fraction(p * (p - rho), (p - 1) ** 2)

        def as_mp(value):
            return mp.mpf(value.numerator) / value.denominator

        crt_checks = weighted_checks = zero_shifts = 0
        rows = []
        max_ratio = mp.mpf(0)
        divisors = [d for d in range(1, P + 1) if P % d == 0]
        for h in range(1, N + 1):
            T = N - h
            sigma = math.prod((alpha(p, h) for p in sieve_primes), start=Fraction(1))
            if h % 2 or T == 0:
                assert corr(nu, h) == corr(model, h) == 0
                zero_shifts += 1
                continue
            L_h = Fraction(q, phi(q)) ** 2 * math.prod(
                (alpha(p, h) for p in sieve_primes if q % p), start=Fraction(1)
            )
            f = lambda t: mp.power(max(mp.mpf(1), t), -delta)
            g = lambda t: mp.power(t + h, -delta)
            integrals = [
                mp.mpf(T), 1 + (mp.power(T, beta) - 1) / beta,
                (mp.power(N, beta) - mp.power(h, beta)) / beta,
                mp.quad(lambda t: f(t) * g(t), [0, 1, T]) if T > 1
                else mp.quad(lambda t: f(t) * g(t), [0, T]),
            ]
            admissible = [r for r in range(q) if math.gcd(r * (r + h), q) == 1]
            assert len(admissible) * L_h / q == sigma
            error_budget = Fraction(0)
            for r in admissible:
                for d in divisors:
                    roots = math.prod(1 if h % p == 0 else 2 for p in factors(d))
                    slope = Fraction(roots, q * d) if math.gcd(d, q) == 1 else Fraction(0)
                    actual = 0
                    for t in range(T + 1):
                        if t and t % q == r and t * (t + h) % d == 0:
                            actual += 1
                        if math.gcd(d, q) == 1:
                            assert abs(Fraction(actual) - t * slope) <= roots
                        else:
                            assert actual == 0
                        crt_checks += 1
                cumulative, eps = Fraction(0), Fraction(0)
                for t in range(1, T + 1):
                    eps = max(eps, abs(cumulative - t * L_h / q))
                    if t % q == r and math.gcd(t * (t + h), P) == 1:
                        cumulative += b2
                    eps = max(eps, abs(cumulative - t * L_h / q))
                error_budget += 8 * eps
                weights = [
                    lambda n: mp.mpf(1), f, g, lambda n: f(n) * g(n)
                ]
                for weight, integral in zip(weights, integrals):
                    value = mp.fsum(
                        nu[n] * nu[n + h] * weight(n)
                        for n in range(1, T + 1) if n % q == r
                    )
                    error = abs(value - as_mp(L_h / q) * integral)
                    assert error <= 2 * as_mp(eps) + mp.mpf("1e-40")
                    weighted_checks += 1
            u = Fraction(sum(chi(r) for r in admissible), q)
            v = Fraction(sum(chi(r + h) for r in admissible), q)
            correction = as_mp(L_h) * (
                -as_mp(u) * integrals[1] - as_mp(v) * integrals[2]
                + as_mp(Fraction(ramanujan(q, h), q)) * integrals[3]
            )
            actual_error = corr(model, h) - T * as_mp(sigma)
            remainder = actual_error - correction
            assert abs(remainder) <= as_mp(error_budget) + mp.mpf("1e-40")
            max_ratio = max(max_ratio, abs(remainder) / as_mp(error_budget))
            if h in (2, 6, 64, 126):
                rows.append({
                    "h": h, "T": T, "model_minus_T_sigma": str(actual_error),
                    "explicit_correction": str(correction), "retained_remainder": str(remainder),
                    "finite_partial_summation_bound": str(error_budget),
                })
        report["model_fixture"] = {
            "Z": str(Z), "sieve_primes": sieve_primes, "q": q,
            "toy_beta": str(beta), "exceptional_zero_asserted": False,
            "proper_prime_powers": sorted(proper_powers),
            "proper_prime_power_count": len(proper_powers), "all_shifts_checked": N,
            "exact_zero_model_shifts": zero_shifts, "exact_CRT_checks": crt_checks,
            "weighted_partial_summation_checks": weighted_checks,
            "max_remainder_to_retained_bound": str(max_ratio), "selected_rows": rows,
            "scope": "Finite identities only. No asymptotic sieve error or infinite singular series is numerically asserted.",
        }
    return report


if __name__ == "__main__":
    started = time.monotonic()
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(LIMIT_SECONDS)
    output = {
        "N": N, "numerical_threads": 1, "limit_seconds": LIMIT_SECONDS,
        "proof_sha256": hashlib.sha256(PROOF.read_bytes()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    try:
        output.update(main())
        output["status"] = "PASS"
    except Exception as error:
        output.update(status="FAIL", error_type=type(error).__name__, error=str(error))
        raise
    finally:
        signal.alarm(0)
        output["elapsed_seconds"] = round(time.monotonic() - started, 6)
        (HERE / "result.json").write_text(json.dumps(output, indent=2) + "\n")
        print(json.dumps({key: output[key] for key in
                          ("status", "N", "numerical_threads", "elapsed_seconds")}))
