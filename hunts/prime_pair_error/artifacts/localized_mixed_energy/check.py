"""One N=64 check of the localized mixed-energy algebra, capped at 60 seconds.

Uses actual Lambda including proper prime powers. Toy character fixtures
test algebra only; no exceptional zero or asymptotic error is asserted.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import signal
import time

N = 64
LIMIT_SECONDS = 60
HERE = Path(__file__).resolve().parent
HUNT = HERE.parent.parent
HELPERS = HERE.parent / "siegel_uniformity" / "check.py"
spec = importlib.util.spec_from_file_location("parent_helpers", HELPERS)
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)  # Sets one-thread limits; does not call main().


def timeout(_signum, _frame):
    raise TimeoutError("The fixed 60-second diagnostic limit expired")


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def main():
    from mpmath import mp

    with mp.workdps(50):
        tolerance = mp.mpf("1e-34")
        beta = mp.mpf("0.99")
        Z = mp.exp(mp.log(N) ** mp.mpf("0.1"))
        primes = [p for p in range(2, N + 1) if parent.factors(p) == {p: 1}]
        sieve_primes = [p for p in primes if p < Z]
        assert sieve_primes == [2, 3]
        P = math.prod(sieve_primes)
        bZ = Fraction(P, parent.phi(P))

        def numeric(v):
            return mp.mpf(v.numerator) / v.denominator

        def close(a, b):
            defect = abs(a - b)
            assert defect < tolerance, str(defect)
            return defect

        def e(theta):
            return mp.exp(2j * mp.pi * numeric(theta))

        nu_exact = lambda n: bZ if math.gcd(n, P) == 1 else Fraction(0)
        nu = [numeric(nu_exact(n)) for n in range(1, N + 1)]
        lam, powers = [], []
        for n in range(1, N + 1):
            fs = parent.factors(n)
            if len(fs) == 1:
                p, exponent = next(iter(fs.items()))
                lam.append(mp.log(p))
                if exponent > 1:
                    powers.append(n)
            else:
                lam.append(mp.mpf(0))
        assert powers == [4, 8, 9, 16, 25, 27, 32, 49, 64]

        base_denominators = [(d, Fraction(1, parent.phi(d) ** 2))
                             for d in divisors(P)]
        assert sum(weight * parent.phi(d)
                   for d, weight in base_denominators) == bZ
        chi3 = parent.legendre(3)
        chi4 = lambda n: (0, 1, 0, -1)[n % 4]
        chi8 = lambda n: (0, 1, 0, -1, 0, -1, 0, 1)[n % 8]
        fixtures = [(None, None), (3, chi3), (4, chi4), (8, chi8)]
        rows = []
        spectrum_checks = window_checks = sampling_checks = 0
        abel_checks = recombination_checks = 0
        max_window_defect = mp.mpf(0)
        norm_report = None

        for q, chi in fixtures:
            character_denominators = [] if q is None else [
                (q * d, Fraction(q, parent.phi(q * d) ** 2))
                for d in divisors(P) if math.gcd(d, q) == 1
            ]
            if q is not None:
                assert sum(weight * parent.phi(d)
                           for d, weight in character_denominators) == bZ
            for denoms, character in [
                (base_denominators, lambda n: 1),
                *([] if q is None else [(character_denominators, chi)]),
            ]:
                period = P if character is not chi else math.lcm(P, q)
                for h in range(N):
                    covariance = sum(
                        nu_exact(n) * character(n)
                        * nu_exact(n + h) * character(n + h)
                        for n in range(1, period + 1)
                    ) / period
                    spectral = sum(weight * parent.ramanujan(d, h)
                                   for d, weight in denoms)
                    assert covariance == spectral
                    spectrum_checks += 1

            f = [mp.power(n, beta - 1) for n in range(1, N + 1)]
            lambdas = [f[i] - f[i + 1] for i in range(N - 1)] + [f[-1]]
            assert all(value >= 0 for value in lambdas)
            close(mp.fsum(lambdas), 1)
            a = list(nu) if q is None else [
                nu[n - 1] * (1 - chi(n) * f[n - 1])
                for n in range(1, N + 1)
            ]
            w = [x - y for x, y in zip(lam, a)]
            corr = [mp.fsum(w[i] * w[i + h] for i in range(N - h))
                    for h in range(N)]
            D_w = corr[0]

            @lru_cache(maxsize=None)
            def window(s, theta):
                if s == 0:
                    return mp.mpf(0)
                prefix = [mp.mpc(0)]
                for n, value in enumerate(w, 1):
                    prefix.append(prefix[-1] + value * e(n * theta))
                return mp.fsum(
                    abs(prefix[min(N, t + s)] - prefix[max(0, t)]) ** 2
                    for t in range(1 - s, N)
                )

            def fourier_integral(s, theta):
                return s * D_w + 2 * mp.fsum(
                    (s - h) * corr[h] * mp.re(e(h * theta))
                    for h in range(1, s)
                )

            for s in (1, 7, N):
                for theta in (Fraction(0), Fraction(1, 3), Fraction(1, 8)):
                    defect = close(window(s, theta), fourier_integral(s, theta))
                    max_window_defect = max(max_window_defect, defect)
                    window_checks += 1

            A = [mp.mpf(0)]
            for value in w:
                A.append(A[-1] + value)
            prefix_form = 2 * mp.fsum(
                abs(A[k] - A[N] / 2) ** 2 for k in range(1, N)
            ) + mp.mpf(N + 1) / 2 * abs(A[N]) ** 2
            prefix_defect = close(window(N, Fraction(0)), prefix_form)

            m, r = divmod(N, 7)
            for theta in (Fraction(0), Fraction(1, 3), Fraction(1, 8)):
                rhs = (m + 1) * (m * window(7, theta) + window(r, theta))
                assert window(N, theta) <= rhs + tolerance
                recombination_checks += 1

            for denoms in (base_denominators, character_denominators):
                for D in (2, 4, 8):
                    fractions = sorted({
                        Fraction(a0, d) for d, _ in denoms if D <= d < 2 * D
                        for a0 in range(d) if math.gcd(a0, d) == 1
                    })
                    if not fractions:
                        continue
                    if len(fractions) > 1:
                        gaps = [v - u for u, v in zip(fractions, fractions[1:])]
                        gaps.append(1 + fractions[0] - fractions[-1])
                        assert min(gaps) >= Fraction(1, 4 * D * D)
                    for s in (7, N):
                        lhs = mp.fsum(window(s, theta) for theta in fractions)
                        bound = 16 * (s + 4 * D * D) * s * D_w
                        assert lhs <= bound + tolerance
                        sampling_checks += 1

            if q is not None:
                for theta in (Fraction(0), Fraction(1, 7), Fraction(11, 80)):
                    U = mp.fsum(nu[n - 1] * e(n * theta)
                                for n in range(1, N + 1))
                    Ts, total = [], mp.mpc(0)
                    for n in range(1, N + 1):
                        total += nu[n - 1] * chi(n) * e(n * theta)
                        Ts.append(total)
                    direct = mp.fsum(
                        nu[n - 1] * chi(n) * f[n - 1] * e(n * theta)
                        for n in range(1, N + 1)
                    )
                    averaged = mp.fsum(x * y for x, y in zip(lambdas, Ts))
                    close(direct, averaged)
                    assert abs(U - direct) ** 2 <= (
                        2 * abs(U) ** 2
                        + 2 * mp.fsum(x * abs(y) ** 2 for x, y in zip(lambdas, Ts))
                        + tolerance
                    )
                    abel_checks += 1
            else:
                # Exact centered G at finite denominator truncation y, C_N=0.
                # This checks (22)-(23), not the infinite-series E_corr tail.
                y = math.isqrt(N)
                aa = [mp.fsum(a[i] * a[i + h] for i in range(N - h))
                      for h in range(N)]
                ll = [mp.fsum(lam[i] * lam[i + h] for i in range(N - h))
                      for h in range(N)]
                X, Y, R, G = [], [], [], []
                for h in range(1, N):
                    prediction = (N - h) * numeric(sum(
                        (Fraction(parent.mobius(d) ** 2, parent.phi(d) ** 2)
                         * parent.ramanujan(d, h) for d in range(1, y + 1)),
                        Fraction(0),
                    ))
                    X.append(mp.fsum(
                        a[i] * w[i + h] + w[i] * a[i + h]
                        for i in range(N - h)
                    ))
                    Y.append(corr[h])
                    R.append(aa[h] - prediction)
                    G.append(ll[h] - prediction)
                    close(X[-1] + Y[-1] + R[-1], G[-1])

                def dot(x, y):
                    return 2 * mp.fsum(u * v for u, v in zip(x, y))

                full = dot(G, G)
                interactions = 2 * dot(X, Y) + 2 * dot(
                    [x + y for x, y in zip(X, Y)], R
                )
                defect = close(full, dot(X, X) + dot(Y, Y) + dot(R, R)
                               + interactions)
                mixed = aa[0] * D_w + 2 * mp.fsum(
                    aa[h] * corr[h] for h in range(1, N)
                )
                assert mixed >= 0
                assert dot(X, X) <= 4 * mixed + tolerance
                fourth = D_w ** 2 + 2 * mp.fsum(c * c for c in corr[1:])
                close(dot(Y, Y), fourth - D_w ** 2)
                norm_report = {
                    "scope": "exact finite G_y, no-exception C=0; not E_corr scaling",
                    "squared_norm": str(full),
                    "signed_interaction_total": str(interactions),
                    "expansion_defect": str(defect),
                    "actual_mixed_energy": str(mixed),
                }

            rows.append({
                "conductor": q,
                "q_below_Z": q is None or q < Z,
                "D_w": str(D_w),
                "T_N_zero": str(window(N, Fraction(0))),
                "prefix_identity_defect": str(prefix_defect),
            })

        return {
            "status": "PASS", "N": N, "numerical_threads": 1,
            "time_limit_seconds": LIMIT_SECONDS, "precision_decimal_digits": 50,
            "Z": str(Z), "P": P, "b_Z": str(bZ), "toy_beta": str(beta),
            "scope": "finite identities only; no zero existence or asymptotic bound",
            "proper_prime_powers": powers,
            "spectrum_coefficient_checks": spectrum_checks,
            "window_identity_checks": window_checks,
            "sampling_checks": sampling_checks,
            "positive_abel_checks": abel_checks,
            "recombination_checks": recombination_checks,
            "max_window_identity_defect": str(max_window_defect),
            "fixtures": rows, "centered_norm": norm_report,
        }


if __name__ == "__main__":
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(LIMIT_SECONDS)
    started = time.monotonic()
    result = main()
    result["elapsed_seconds"] = round(time.monotonic() - started, 6)
    result["sha256"] = {
        str(path.relative_to(HUNT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (Path(__file__).resolve(), HUNT / "LOCALIZED_MIXED_ENERGY.md",
                     HUNT / "SIEGEL_UNIFORMITY.md", HUNT / "CORRECTED_RH_BRIDGE.md",
                     HELPERS)
    }
    (HERE / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    signal.alarm(0)
    print(json.dumps(result, indent=2))
