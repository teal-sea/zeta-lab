"""One fixed N=128 check of the signed-moment and RH-bridge algebra.

The zero parameter is a toy. Finite prediction remainders are retained;
no infinite singular-series asymptotic or RH assertion is tested numerically.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import signal
import time

N = 128
LIMIT_SECONDS = 60
HERE = Path(__file__).resolve().parent
HUNT = HERE.parent.parent
HELPERS = HERE.parent / "siegel_uniformity" / "check.py"
spec = importlib.util.spec_from_file_location("parent_helpers", HELPERS)
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)  # Loads helpers and one-thread limits, not main().


def timeout(_signum, _frame):
    raise TimeoutError("The fixed 60-second diagnostic limit expired")


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def main():
    from mpmath import mp

    with mp.workdps(50):
        beta = mp.mpf("0.99")
        delta = 1 - beta
        Z = mp.exp(mp.log(N) ** mp.mpf("0.1"))
        ps = [p for p in range(2, N + 1)
              if parent.factors(p) == {p: 1} and p < Z]
        assert ps == [2, 3]
        P = math.prod(ps)
        bZ = Fraction(P, parent.phi(P))

        def as_mp(value):
            return mp.mpf(value.numerator) / value.denominator

        def alpha(p, h):
            rho = 1 if h % p == 0 else 2
            return Fraction(p * (p - rho), (p - 1) ** 2)

        J = [[], [], []]
        for h in range(1, N + 1):
            T = N - h
            if T == 0:
                values = [mp.mpf(0)] * 3
            else:
                f = lambda t: mp.power(max(mp.mpf(1), t), -delta)
                g = lambda t: mp.power(t + h, -delta)
                values = [
                    1 + (mp.power(T, beta) - 1) / beta,
                    (mp.power(N, beta) - mp.power(h, beta)) / beta,
                    mp.quad(lambda t: f(t) * g(t), [0, 1, T] if T > 1 else [0, T]),
                ]
            for row, value in zip(J, values):
                row.append(value)
        upper_weights = [
            mp.mpf(4) / 3 * mp.power(N, beta),
            mp.mpf(4) / 3 * mp.power(N, beta),
            2 * mp.power(N, 2 * beta - 1),
        ]
        for row, bound in zip(J, upper_weights):
            assert all(a >= b >= 0 for a, b in zip(row, row[1:]))
            assert row[-1] == 0 and row[0] <= bound

        def abel(sequence, weights, prefix_bound):
            if not sequence:
                assert not weights
                return mp.mpf(0)
            cumulative = []
            acc = 0
            for value in sequence:
                acc += value
                cumulative.append(acc)
                assert abs(acc) <= prefix_bound
            direct = mp.fsum(a * w for a, w in zip(sequence, weights))
            expanded = cumulative[-1] * weights[-1] + mp.fsum(
                cumulative[i] * (weights[i] - weights[i + 1])
                for i in range(len(weights) - 1)
            )
            assert abs(direct - expanded) < mp.mpf("1e-38")
            assert abs(direct) <= prefix_bound * weights[0] + mp.mpf("1e-38")
            return direct

        chi3 = parent.legendre(3)
        chi4 = lambda n: (0, 1, 0, -1)[n % 4]
        chi8 = lambda n: (0, 1, 0, -1, 0, -1, 0, 1)[n % 8]
        rows = []
        correction3 = None
        exact_prefix_checks = expansion_checks = weighted_checks = 0
        for q, chi in ((3, chi3), (4, chi4), (8, chi8)):
            ph, sig = parent.phi(q), sum(divisors(q))
            assert sum(chi(j) for j in range(1, q + 1)) == 0
            assert sum(parent.ramanujan(q, j) for j in range(1, q + 1)) == 0
            prefix_chi = prefix_ram = 0
            for x in range(1, N + 1):
                prefix_chi += chi(x)
                prefix_ram += parent.ramanujan(q, x)
                formula = sum(a * parent.mobius(q // a) * (x // a) for a in divisors(q))
                incomplete = -sum(
                    a * parent.mobius(q // a) * (Fraction(x, a) - x // a)
                    for a in divisors(q)
                )
                assert prefix_ram == formula == incomplete
                assert abs(prefix_ram) <= sig and abs(prefix_chi) <= q
                exact_prefix_checks += 1
            pstar = [p for p in ps if p > 2 and q % p]
            Pstar = math.prod(pstar)
            ds = divisors(Pstar)
            bstar = math.prod(
                (1 - Fraction(1, (p - 1) ** 2) for p in pstar), start=Fraction(1)
            )
            coeff = {
                d: math.prod((Fraction(1, p - 2) for p in parent.factors(d)), start=Fraction(1))
                for d in ds
            }
            mass = bstar * sum(coeff.values())
            expected_mass = math.prod((Fraction(p, p - 1) for p in pstar), start=Fraction(1))
            assert mass == expected_mass and mass <= bZ / 2
            assert Fraction(sig, q) <= Fraction(q, ph) <= bZ
            corrections = []
            for h in range(1, N + 1):
                Sstar = math.prod((alpha(p, h) for p in ps if q % p), start=Fraction(1))
                factor2 = 2 * int(h % 2 == 0) if q % 2 else 1
                expansion = factor2 * bstar * sum(coeff[d] for d in ds if h % d == 0)
                assert Sstar == expansion
                units = [r for r in range(q) if math.gcd(r * (r + h), q) == 1]
                u = Fraction(sum(chi(r) for r in units), q)
                v = Fraction(sum(chi(r + h) for r in units), q)
                assert u == (Fraction(parent.mobius(q) * chi(-h), q) if q % 2 else 0)
                assert v == (Fraction(parent.mobius(q) * chi(h), q) if q % 2 else 0)
                correction = as_mp(Fraction(q, ph) ** 2 * Sstar) * (
                    -as_mp(u) * J[0][h - 1] - as_mp(v) * J[1][h - 1]
                    + as_mp(Fraction(parent.ramanujan(q, h), q)) * J[2][h - 1]
                )
                corrections.append(correction)
                expansion_checks += 1
            expansion_total = mp.mpf(0)
            for d in ds:
                step = (2 if q % 2 else 1) * d
                assert math.gcd(step, q) == 1
                js = list(range(1, N // step + 1))
                assert all(parent.ramanujan(q, step * j) == parent.ramanujan(q, j) for j in js)
                W = [[weight[step * j - 1] for j in js] for weight in J]
                ram = [parent.ramanujan(q, j) for j in js]
                quadratic = abel(ram, W[2], sig) / q
                weighted_checks += 1
                linear = mp.mpf(0)
                if q % 2:
                    chars = [chi(j) for j in js]
                    linear = -as_mp(Fraction(parent.mobius(q), q)) * (
                        chi(-step) * abel(chars, W[0], q)
                        + chi(step) * abel(chars, W[1], q)
                    )
                    weighted_checks += 2
                expansion_total += as_mp(coeff[d]) * (linear + quadratic)
            expansion_total *= as_mp(Fraction(q, ph) ** 2 * bstar * (2 if q % 2 else 1))
            signed_total = mp.fsum(corrections)
            assert abs(expansion_total - signed_total) < mp.mpf("1e-35")
            bound = as_mp(Fraction(q, ph) ** 2 * bZ) * (
                (mp.mpf(8) / 3 * mp.power(N, beta) if q % 2 else 0)
                + as_mp(Fraction(2 * sig, q)) * mp.power(N, 2 * beta - 1)
            )
            assert abs(signed_total) <= bound
            assert bound <= as_mp(Fraction(14, 3) * N * bZ ** 4)
            rows.append({
                "q": q, "source_q_less_than_Z": bool(q < Z),
                "divisors": ds, "weighted_coefficient_mass": str(mass),
                "sigma1": sig, "signed_correction_sum": str(signed_total),
                "divisor_expansion_sum": str(expansion_total), "moment_bound": str(bound),
                "absolute_signed_sum_to_bound": str(abs(signed_total) / bound),
            })
            if q == 3:
                correction3 = corrections

        # Original correlation identity; no singular-series approximation is needed.
        lam = [mp.mpf(0)]
        powers = []
        for n in range(1, N + 1):
            fs = parent.factors(n)
            lam.append(mp.log(next(iter(fs))) if len(fs) == 1 else mp.mpf(0))
            if len(fs) == 1 and next(iter(fs.values())) > 1:
                powers.append(n)
        psi = mp.fsum(lam)
        diagonal = mp.fsum(x * x for x in lam)
        pairs = [
            mp.fsum(lam[n] * lam[n + h] for n in range(1, N - h + 1))
            for h in range(1, N + 1)
        ]
        corr_defect = psi ** 2 - diagonal - 2 * mp.fsum(pairs)
        assert abs(corr_defect) < mp.mpf("1e-35")
        prediction = []
        for h in range(1, N + 1):
            sigma = math.prod((alpha(p, h) for p in ps), start=Fraction(1))
            prediction.append((N - h) * as_mp(sigma))
        corrected = [p - m - c for p, m, c in zip(pairs, prediction, correction3)]
        finite_Ecorr = 2 * mp.fsum(x * x for x in corrected)
        prediction_remainder = 2 * mp.fsum(prediction) - N * N
        exact_bridge_rhs = (
            2 * mp.fsum(corrected) + 2 * mp.fsum(correction3)
            + diagonal + prediction_remainder
        )
        assert abs(psi ** 2 - N * N - exact_bridge_rhs) < mp.mpf("1e-35")
        bridge_bound = (
            mp.sqrt(2 * N * finite_Ecorr) + 2 * abs(mp.fsum(correction3))
            + abs(diagonal + prediction_remainder)
        ) / N
        assert abs(psi - N) <= bridge_bound
        return {
            "toy_beta": str(beta), "Z": str(Z), "sieve_primes": ps,
            "exceptional_zero_asserted": False,
            "local_fixture_scope": "Even conductors test algebra only; the TT source range is not asserted at N=128.",
            "weight_monotonicity_comparisons": 3 * (N - 1),
            "zero_weight_endpoints": [str(weight[-1]) for weight in J],
            "exact_prefix_checks": exact_prefix_checks,
            "divisor_expansion_checks": expansion_checks,
            "weighted_Abel_checks": weighted_checks, "signed_moment_fixtures": rows,
            "no_exception_signed_sum": "0",
            "finite_bridge_fixture": {
                "proper_prime_powers": powers, "proper_prime_power_count": len(powers),
                "all_shifts_checked": N, "correlation_identity_defect": str(corr_defect),
                "prediction": "Prime-truncated singular product; its entire remainder is retained.",
                "is_original_infinite_series_E_corr": False,
                "prediction_first_moment_remainder": str(prediction_remainder),
                "diagonal": str(diagonal), "psi_minus_N": str(psi - N),
                "finite_corrected_energy": str(finite_Ecorr),
                "bridge_upper_bound": str(bridge_bound), "mpmath_decimal_digits": 50,
            },
        }


if __name__ == "__main__":
    started = time.monotonic()
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(LIMIT_SECONDS)
    output = {"N": N, "numerical_threads": 1, "limit_seconds": LIMIT_SECONDS}
    for key, path in (
        ("proof", HUNT / "CORRECTED_RH_BRIDGE.md"), ("script", Path(__file__)),
        ("parent_proof", HUNT / "EXCEPTIONAL_ENERGY.md"), ("parent_helpers", HELPERS),
    ):
        output[key + "_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
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
