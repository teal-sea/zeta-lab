"""Bounded scale-dependent paid-cost experiment; no asymptotic conclusion."""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import importlib.util
import json
from math import isqrt
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("paid_construction", ROOT / "hunts/paid_shortfall/construction.py")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)
CUTOFFS = (144, 576, 2304, 9216, 36864)


def sieve(limit):
    """Smallest factors, Mobius values, and primes by an integer sieve."""
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    mu = [0] * (limit + 1)
    mu[1] = 1
    for n in range(2, limit + 1):
        p, rest = spf[n], n // spf[n]
        mu[n] = 0 if rest % p == 0 else -mu[rest]
    return spf, mu, [p for p in range(2, limit + 1) if spf[p] == p]


def balanced_prefix(y):
    BASE.natural(y, 2)
    _, mu, _ = sieve(y)
    c = {j: F(mu[j]) for j in range(1, y) if mu[j]}
    c[y] = -y * sum((a / j for j, a in c.items()), F(0))
    return {j: a for j, a in c.items() if a}


def averaged_prefix(y):
    """Uniform average of balanced prefixes for h=max(2,ceil(y/2)),...,y."""
    BASE.natural(y, 2)
    a = max(2, (y + 1) // 2)
    m = y - a + 1
    _, mu, _ = sieve(y)
    S, c = F(0), {}
    for j in range(1, y + 1):
        value = F(mu[j] * (y - max(a, j + 1) + 1), m)
        if j >= a:
            value -= F(j, m) * S
        if value:
            c[j] = value
        S += F(mu[j], j)
    return c


def exponent_coefficient(k):
    BASE.natural(k, 2)
    value = -1
    for p, _ in BASE.trial_factors(k):
        value *= 1 - p
    return value


def cap_mass_vector(N):
    """Exact T(N) from integer roots and logarithmic factorials."""
    BASE.natural(N)
    return BASE.combine(*((exponent_coefficient(k),
                           dict(BASE.factorial_vector_items(BASE.integer_root(N, k))))
                          for k in range(2, N.bit_length())))


def cap_remainder_majorant(N):
    BASE.natural(N)
    return BASE.combine(*((k - 1, dict(BASE.factorial_vector_items(BASE.integer_root(N, k))))
                          for k in range(3, N.bit_length())))


def exact_cap_checks(limit=256):
    total = {}
    for N in range(limit + 1):
        if N >= 2:
            total = BASE.combine((1, total), (1, BASE.log_vector(N)),
                                 (-1, BASE.cap_vector(N, "perfect_power")))
        assert total == cap_mass_vector(N)
        square = dict(BASE.factorial_vector_items(isqrt(N)))
        remainder = BASE.combine((1, total), (-1, square))
        assert BASE.nonnegative_coefficients(remainder)
        assert BASE.nonnegative_coefficients(BASE.combine((1, cap_remainder_majorant(N)), (-1, remainder)))
    return limit + 1


def averaging_identity(N, coefficients, cap="perfect_power"):
    """Check the exact hinge cancellation under a common capacity."""
    alpha = F(1, len(coefficients))
    avg = BASE.combine(*((alpha, c) for c in coefficients))
    _, caps = BASE.cells(N, "perfect_power" if cap == "perfect_power" else "log")
    discount = {}
    for q, capacity in caps.items():
        values = [BASE.floor_sum(c, q) - 1 for c in coefficients]
        deficits = alpha * sum((max(F(0), -v) for v in values), F(0))
        surpluses = alpha * sum((max(F(0), v) for v in values), F(0))
        discount = BASE.combine((1, discount), (min(deficits, surpluses), capacity))
    selected_cap = "perfect_power" if cap == "perfect_power" else "log"
    average_cost = BASE.combine(*((alpha, BASE.paid_cost_vectors(N, c, selected_cap)["total"]) for c in coefficients))
    actual_cost = BASE.paid_cost_vectors(N, avg, selected_cap)["total"]
    assert actual_cost == BASE.combine((1, average_cost), (-1, discount))
    assert BASE.nonnegative_coefficients(discount)
    return discount


def prefix_excess(N, h):
    """Exact paid excess using only integers d<=N/h, not psi(N)."""
    c = balanced_prefix(h)
    excess = {}
    for d in range(2, N // h + 1):
        value = BASE.floor_sum(c, N // d) - 1
        m = BASE.mangoldt_vector(d)
        slack = BASE.combine((1, BASE.cap_vector(d, "perfect_power")), (-1, m))
        excess = BASE.combine((1, excess), (max(F(0), value), m), (max(F(0), -value), slack))
    assert BASE.nonnegative_coefficients(excess)
    return excess


def select_prefix(N, y):
    BASE.natural(N, 2)
    BASE.natural(y, 2)
    a = max(2, (y + 1) // 2)
    candidates = {h: prefix_excess(N, h) for h in range(a, y + 1)}
    verified_winner = None
    comparisons = 0
    for backend in ("python-flint", "mpmath.iv"):
        for dps in (35, 70):
            with BASE.log_intervals(backend, dps) as log:
                intervals = {h: BASE.enclose_expression(0, v, log) for h, v in candidates.items()}
                winner = min(intervals, key=lambda h: (sum(intervals[h]), h))
                if verified_winner is not None:
                    assert winner == verified_winner
                verified_winner = winner
                for h, vector in candidates.items():
                    difference = BASE.combine((1, vector), (-1, candidates[winner]))
                    if difference:
                        assert BASE.enclose_expression(0, difference, log)[0] > 0, "cutoff comparison undecided"
                    comparisons += 1
    return verified_winner, candidates[verified_winner], len(candidates), comparisons


def add(out, p, amount):
    out[p] = out.get(p, F(0)) + amount
    if not out[p]:
        del out[p]


def factorial_cost(N, c, primes):
    out = {}
    for j, a in c.items():
        limit = N // j
        for p in primes:
            if p > limit:
                break
            exponent, power = 0, p
            while power <= limit:
                exponent += limit // power
                power *= p
            add(out, p, a * exponent)
    return out


def cost_case(N, c, primes):
    """Full exact logarithmic vectors, checked by the prime-power route."""
    weights = {q: BASE.floor_sum(c, q) for q in {N // d for d in range(2, N + 1)}}
    B = factorial_cost(N, c, primes)
    psi, divisor_B = {}, {}
    for p in primes:
        power = p
        while power <= N:
            add(psi, p, F(1))
            add(divisor_B, p, weights[N // power])
            power *= p
    assert B == divisor_B
    penalties = {"raw": {}, "perfect_power": {}}
    D = max(max(F(0), 1 - w) for w in weights.values())
    deficit_terms = 0
    for d in range(2, N + 1):
        delta = max(F(0), 1 - weights[N // d])
        if not delta:
            continue
        deficit_terms += 1
        for p, e in BASE.trial_factors(d):
            add(penalties["raw"], p, e * delta)
            add(penalties["perfect_power"], p, F(e, BASE.perfect_power_exponent(d)) * delta)
    totals = {name: BASE.combine((1, B), (1, penalty)) for name, penalty in penalties.items()}
    excesses = {name: BASE.combine((1, total), (-1, psi)) for name, total in totals.items()}
    for excess in excesses.values():
        assert BASE.nonnegative_coefficients(excess)
    saving = BASE.combine((1, totals["raw"]), (-1, totals["perfect_power"]))
    assert BASE.nonnegative_coefficients(saving)
    return {"N": N, "support": max(c), "coefficient_mass": sum(map(abs, c.values()), F(0)),
            "harmonic_drift": sum((a / j for j, a in c.items()), F(0)),
            "max_deficit": D, "deficit_integer_terms": deficit_terms,
            "coefficients": c, "factorial": B, "psi": psi, "penalties": penalties,
            "totals": totals, "excess_over_psi": excesses, "cap_saving": saving}


def render_interval(pair):
    import mpmath as mp
    with mp.workdps(45):
        return [mp.nstr(mp.mpf(x.numerator) / x.denominator, 30) for x in pair]


def summarize(case):
    kappa = BASE.combine(*((-a / j, BASE.log_vector(j)) for j, a in case["coefficients"].items()))
    expressions = {"factorial_minus_N": (-case["N"], case["factorial"]),
                   "psi_minus_N": (-case["N"], case["psi"]),
                   "cap_saving": (0, case["cap_saving"]),
                   "kappa": (0, kappa)}
    for cap in case["totals"]:
        expressions[cap + "_minus_N"] = (-case["N"], case["totals"][cap])
        expressions[cap + "_minus_psi"] = (0, case["excess_over_psi"][cap])
        expressions[cap + "_penalty"] = (0, case["penalties"][cap])
    last = {}
    overlaps = 0
    for backend in ("python-flint", "mpmath.iv"):
        previous = None
        for dps in (35, 70):
            with BASE.log_intervals(backend, dps) as log:
                current = {key: BASE.enclose_expression(a, v, log) for key, (a, v) in expressions.items()}
                residual = BASE.combine((1, case["factorial"]), (-case["N"], kappa))
                error = BASE.combine((case["coefficient_mass"], BASE.log_vector(case["N"])))
                for sign in (-1, 1):
                    lo, hi = BASE.enclose_expression(case["coefficient_mass"], BASE.combine((1, error), (sign, residual)), log)
                    assert lo >= 0
            if previous is not None:
                for key, (lo, hi) in current.items():
                    assert max(lo, previous[key][0]) <= min(hi, previous[key][1])
                    overlaps += 1
            previous = current
        last[backend] = current
    for key in expressions:
        a, b = last["python-flint"][key], last["mpmath.iv"][key]
        assert max(a[0], b[0]) <= min(a[1], b[1])
        overlaps += 1
    small = {key: case[key] for key in ("N", "support", "coefficient_mass", "harmonic_drift", "max_deficit", "deficit_integer_terms", "coefficients")}
    small["decimal_values_display_only"] = {key: render_interval(value) for key, value in last["python-flint"].items()}
    small["exact_rational_enclosures"] = last
    small["overlap_checks"] = overlaps
    return small


def run():
    start = time.monotonic()
    rows = []
    cap_cutoffs_checked = exact_cap_checks()
    for cap in ("raw", "perfect_power"):
        for y in (4, 6, 8, 12):
            averaging_identity(y * y, [balanced_prefix(h) for h in range((y + 1) // 2, y + 1)], cap)
    for N in CUTOFFS:
        y = isqrt(N)
        _, _, primes = sieve(N)
        c = balanced_prefix(y)
        assert sum((a / j for j, a in c.items()), F(0)) == 0
        assert all(BASE.floor_sum(c, q) == 1 for q in range(1, y))
        candidate = summarize(cost_case(N, c, primes))
        smooth = averaged_prefix(y)
        assert sum((a / j for j, a in smooth.items()), F(0)) == 0
        assert all(BASE.floor_sum(smooth, q) == 1 for q in range(1, (y + 1) // 2))
        averaged = summarize(cost_case(N, smooth, primes))
        winner, excess, count, comparisons = select_prefix(N, y)
        selected_case = cost_case(N, balanced_prefix(winner), primes)
        assert selected_case["excess_over_psi"]["perfect_power"] == excess
        selected = summarize(selected_case)
        selected["candidate_count"] = count
        selected["comparisons_at_two_precisions_and_backends"] = comparisons
        K = 0
        while 6 ** (K + 2) <= y:
            K += 1
        control = summarize(cost_case(N, BASE.early_lift(BASE.BASE6, 6, 6, K), primes))
        rows.append({"N": N, "y": y, "balanced_prefix": candidate, "averaged_prefix": averaged,
                     "selected_prefix": selected, "base6_control": control})
    return {"status": "PASS", "runtime_seconds": time.monotonic() - start,
            "cap_cutoffs_checked": cap_cutoffs_checked, "averaging_identities_checked": 8,
            "cutoffs": CUTOFFS, "rows": rows,
            "nonclaims": ["These finite values do not establish a growth exponent", "No RH or novelty claim",
                          "Decimal displays are rounded; exact rational enclosures are recorded separately"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run()
    if args.output:
        args.output.write_text(json.dumps(BASE.json_ready(report), indent=2) + "\n")
    for row in report["rows"]:
        values = row["balanced_prefix"]["decimal_values_display_only"]
        print(row["N"], "raw-N", values["raw_minus_N"][0], "refined-N", values["perfect_power_minus_N"][0],
              "saving", values["cap_saving"][0], "averaged-N", row["averaged_prefix"]["decimal_values_display_only"]["perfect_power_minus_N"][0],
              "selected", row["selected_prefix"]["support"], row["selected_prefix"]["decimal_values_display_only"]["perfect_power_minus_N"][0],
              "base6-N", row["base6_control"]["decimal_values_display_only"]["perfect_power_minus_N"][0])
    print("PASS", report["runtime_seconds"])


if __name__ == "__main__":
    main()
