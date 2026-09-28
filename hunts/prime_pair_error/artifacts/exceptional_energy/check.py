"""Fixed N=128 checks for the exceptional-energy continuation.

Only finite identities and explicitly bounded local errors are tested.
There is no numerical assertion of an exceptional zero or original E(N).
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
PARENT_SCRIPT = HERE.parent / "siegel_uniformity" / "check.py"
spec = importlib.util.spec_from_file_location("parent_check", PARENT_SCRIPT)
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)  # Helpers only; does not run the parent diagnostic.


def timeout(_signum, _frame):
    raise TimeoutError("The fixed 60-second diagnostic limit expired")


def period_checks():
    lo, hi = (N + 7) // 8, N // 4
    m = hi - lo + 1
    assert m >= N // 8
    rows = []
    for q in (3, 4, 8):  # One fixture for each local conductor structure.
        ph = parent.phi(q)
        if q % 2:
            d, mass = q, (q - 1) * ph

            def weight(j):
                return int(math.gcd(j, q) > 1) * parent.ramanujan(q, j) ** 2

            removed = sum(parent.ramanujan(q, j) ** 2
                          for j in range(q) if math.gcd(j, q) == 1)
            assert removed == ph
            assert mass == q * ph - removed
        else:
            d, mass = q // 4, q * ph // 2

            def weight(j):
                return parent.ramanujan(q, 2 * j) ** 2

            for j in range(q):
                expected = 4 if q == 4 else 16 * int(j % 2 == 0)
                assert weight(j) == expected
        assert sum(weight(j) for j in range(d)) == mass
        assert all(weight(j + d) == weight(j) for j in range(q))
        whole, leftover = divmod(m, d)
        total = sum(weight(j) for j in range(lo, hi + 1))
        remainder = sum(weight(j) for j in range(lo + whole * d, hi + 1))
        assert total == whole * mass + remainder
        assert 0 <= remainder <= mass
        end_error = Fraction(total) - Fraction(m * mass, d)
        assert abs(end_error) <= mass
        assert N >= 8 * q
        assert total >= Fraction(N * ph, 24)
        if q % 2 == 0:
            assert total >= Fraction(N * ph, 8)
        rows.append({
            "q": q, "j_interval": [lo, hi], "j_count": m, "period": d,
            "period_mass": mass, "complete_periods": whole,
            "leftover_count": leftover, "leftover_mass": remainder,
            "actual_mass": total, "end_error": str(end_error),
            "absolute_end_error_bound": mass,
            "common_lower_bound": str(Fraction(N * ph, 24)),
        })
    product = Fraction(1)
    for m0 in range(2, N + 1):
        product *= 1 - Fraction(1, m0 * m0)
        assert product == Fraction(m0 + 1, 2 * m0)
    return {"period_fixtures": rows, "telescoping_product": str(product)}


def main():
    from mpmath import mp

    report = {"exact": period_checks()}
    with mp.workdps(50):
        q, beta = 3, mp.mpf("0.99")
        ph, delta = parent.phi(q), 1 - beta
        chi = parent.legendre(q)
        Z = mp.exp(mp.log(N) ** mp.mpf("0.1"))
        sieve_primes = [p for p in range(2, N + 1)
                        if parent.factors(p) == {p: 1} and p < Z]
        assert sieve_primes == [2, 3] and q < Z
        P = math.prod(sieve_primes)
        b = Fraction(P, parent.phi(P))

        def as_mp(x):
            return mp.mpf(x.numerator) / x.denominator

        def alpha(p, h):
            rho = 1 if h % p == 0 else 2
            return Fraction(p * (p - rho), (p - 1) ** 2)

        lam, nu, model = [mp.mpf(0)], [mp.mpf(0)], [mp.mpf(0)]
        proper_powers = []
        for n in range(1, N + 1):
            fs = parent.factors(n)
            lam.append(mp.log(next(iter(fs))) if len(fs) == 1 else mp.mpf(0))
            if len(fs) == 1 and next(iter(fs.values())) > 1:
                proper_powers.append(n)
            nu.append(as_mp(b) if math.gcd(n, P) == 1 else mp.mpf(0))
            model.append(nu[n] * (1 - mp.power(n, -delta) * chi(n)))

        def corr(seq, h):
            return mp.fsum(seq[n] * seq[n + h] for n in range(1, N - h + 1))

        corrections, r_sigma, prime_to_model, model_remainders = [], [], [], []
        selected_energy_terms, selected_rows = [], []
        lower_factor_checks = 0
        zero_corrections = 0
        for h in range(1, N + 1):
            T = N - h
            sigma = math.prod((alpha(p, h) for p in sieve_primes), start=Fraction(1))
            S_star = math.prod((alpha(p, h) for p in sieve_primes if q % p),
                               start=Fraction(1))
            if h % 2 or T == 0:
                correction = mp.mpf(0)
                zero_corrections += 1
            else:
                f = lambda t: mp.power(max(mp.mpf(1), t), -delta)
                g = lambda t: mp.power(t + h, -delta)
                J1 = 1 + (mp.power(T, beta) - 1) / beta
                J2 = (mp.power(N, beta) - mp.power(h, beta)) / beta
                J12 = mp.quad(lambda t: f(t) * g(t), [0, 1, T])
                units = [r for r in range(q) if math.gcd(r * (r + h), q) == 1]
                u = Fraction(sum(chi(r) for r in units), q)
                v = Fraction(sum(chi(r + h) for r in units), q)
                scale = as_mp(Fraction(q, ph) ** 2 * S_star)
                correction = scale * (
                    -as_mp(u) * J1 - as_mp(v) * J2
                    + as_mp(Fraction(parent.ramanujan(q, h), q)) * J12
                )
                if 4 * h >= N and 2 * h <= N and math.gcd(h, q) > 1:
                    assert u == v == 0
                    assert S_star >= Fraction(1, 2)
                    J_lower = mp.power(N, 2 * beta - 1) / 2
                    assert J12 >= J_lower
                    pure = scale * as_mp(Fraction(parent.ramanujan(q, h), q)) * J12
                    assert abs(pure - correction) < mp.mpf("1e-40")
                    selected_energy_terms.append(correction ** 2)
                    selected_rows.append({
                        "h": h, "S_star": str(S_star), "J12": str(J12),
                        "J12_lower": str(J_lower), "correction": str(correction),
                    })
                    lower_factor_checks += 1
            prime_pair, model_pair = corr(lam, h), corr(model, h)
            residual = prime_pair - T * as_mp(sigma)
            difference = prime_pair - model_pair
            remainder = model_pair - T * as_mp(sigma) - correction
            assert abs(residual - correction - difference - remainder) < mp.mpf("1e-40")
            corrections.append(correction)
            r_sigma.append(residual)
            prime_to_model.append(difference)
            model_remainders.append(remainder)

        def norm(vector):
            return mp.sqrt(2 * mp.fsum(x * x for x in vector))

        A_exc = norm(corrections) ** 2
        selected_energy = 2 * mp.fsum(selected_energy_terms)
        quadratic_scale = mp.power(N, 4 * beta - 1) * q ** 2 / ph ** 3
        lower_energy = quadratic_scale / 192
        assert A_exc + mp.mpf("1e-35") >= selected_energy >= lower_energy
        vector_error = norm([r - c for r, c in zip(r_sigma, corrections)])
        triangle_budget = norm(prime_to_model) + norm(model_remainders)
        reverse_defect = abs(norm(r_sigma) - norm(corrections))
        assert reverse_defect <= vector_error <= triangle_budget + mp.mpf("1e-35")
        report["lower_energy_fixture"] = {
            "q": q, "Z": str(Z), "toy_beta": str(beta),
            "exceptional_zero_asserted": False, "all_shifts_in_A_exc": N,
            "exact_zero_correction_shifts": zero_corrections,
            "selected_shift_count": lower_factor_checks, "selected_rows": selected_rows,
            "A_exc": str(A_exc), "selected_energy": str(selected_energy),
            "quadratic_scale": str(quadratic_scale), "lower_energy": str(lower_energy),
            "selected_energy_to_lower_bound": str(selected_energy / lower_energy),
        }
        report["finite_vector_fixture"] = {
            "prediction": "(N-h) times the product over primes p<Z",
            "is_original_infinite_series_E": False,
            "proper_prime_powers": proper_powers, "proper_prime_power_count": len(proper_powers),
            "all_shifts_checked": N, "sqrt_E_sigma": str(norm(r_sigma)),
            "sqrt_A_exc": str(norm(corrections)), "reverse_norm_difference": str(reverse_defect),
            "vector_error": str(vector_error), "triangle_budget": str(triangle_budget),
            "mpmath_decimal_digits": 50,
            "scope": "Finite norm algebra with retained model errors; no asymptotic TT estimate tested.",
        }
    return report


if __name__ == "__main__":
    started = time.monotonic()
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(LIMIT_SECONDS)
    output = {"N": N, "numerical_threads": 1, "limit_seconds": LIMIT_SECONDS}
    for name, file in (
        ("proof", HUNT / "EXCEPTIONAL_ENERGY.md"),
        ("script", Path(__file__)),
        ("parent_proof", HUNT / "SIEGEL_UNIFORMITY.md"),
        ("parent_helpers", PARENT_SCRIPT),
    ):
        output[name + "_sha256"] = hashlib.sha256(file.read_bytes()).hexdigest()
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
