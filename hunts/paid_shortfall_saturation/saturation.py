"""Finite local-cap saturation diagnostic for the selected paid prefixes."""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import importlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import time


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "paid_shortfall_scaling", ROOT / "hunts/paid_shortfall_scaling/scaling.py"
)
S = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(S)
CUTOFFS = (144, 576, 2304, 9216, 36864)


def small_primes(limit):
    """Return every prime at most limit by a separate finite sieve."""
    S.BASE.natural(limit)
    marked = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        marked[0] = 0
    if limit >= 1:
        marked[1] = 0
    for p in range(2, isqrt(limit) + 1):
        if marked[p]:
            marked[p * p : limit + 1 : p] = b"\x00" * (((limit - p * p) // p) + 1)
    return tuple(p for p in range(2, limit + 1) if marked[p])


def saturated_cap(n, tested_primes):
    """Keep prime powers and remove composites exposed by the tested primes."""
    S.BASE.natural(n, 1)
    tested_primes = tuple(tested_primes)
    if any(type(p) is not int or p < 2 or S.BASE.trial_factors(p) != ((p, 1),) for p in tested_primes):
        raise ValueError("tested divisors must be primes")
    for p in tested_primes:
        if n % p:
            continue
        rest = n
        while rest % p == 0:
            rest //= p
        if rest != 1:
            return {}
    return S.BASE.cap_vector(n, "perfect_power")


def local_saturation(X):
    """Check complete small-prime coverage of the finite local interval."""
    S.BASE.natural(X, 2)
    tested_primes = small_primes(isqrt(X))
    counts = {
        "local_integers": 0,
        "tested_primes": len(tested_primes),
        "ordinary_composites": 0,
        "ordinary_composites_excluded": 0,
        "ordinary_composites_retained_failures": 0,
        "prime_power_integers": 0,
        "prime_power_retained": 0,
        "prime_power_retention_failures": 0,
        "cap_equality_failures": 0,
    }
    for d in range(2, X + 1):
        cap = saturated_cap(d, tested_primes)
        truth = S.BASE.mangoldt_vector(d)
        factors = S.BASE.trial_factors(d)
        counts["local_integers"] += 1
        if len(factors) == 1:
            counts["prime_power_integers"] += 1
            if cap == truth:
                counts["prime_power_retained"] += 1
            else:
                counts["prime_power_retention_failures"] += 1
        else:
            counts["ordinary_composites"] += 1
            if cap == {}:
                counts["ordinary_composites_excluded"] += 1
            else:
                counts["ordinary_composites_retained_failures"] += 1
        if cap != truth:
            counts["cap_equality_failures"] += 1
    assert counts["ordinary_composites_retained_failures"] == 0
    assert counts["prime_power_retention_failures"] == 0
    assert counts["cap_equality_failures"] == 0
    return {"X": X, "tested_primes": tested_primes, "counts": counts}


def repair_vector(N, coefficients, selected_y, cap):
    """Exact repair vector, localized by the selected prefix coverage."""
    S.BASE.natural(selected_y, 2)
    repair = {}
    nonzero_deficits = 0
    for d in range(2, N // selected_y + 1):
        deficit = max(F(0), 1 - S.BASE.floor_sum(coefficients, N // d))
        if deficit:
            nonzero_deficits += 1
            repair = S.BASE.combine((1, repair), (deficit, cap(d)))
    return repair, nonzero_deficits


def selected_case(N):
    """Price the unchanged selected prefix with a fully saturated local cap."""
    support_limit = isqrt(N)
    selected_y, _, candidate_count, comparisons = S.select_prefix(N, support_limit)
    coefficients = S.balanced_prefix(selected_y)
    assert all(S.BASE.floor_sum(coefficients, q) == 1 for q in range(1, selected_y))
    X = N // selected_y
    saturation = local_saturation(X)
    tested_primes = saturation["tested_primes"]
    _, _, primes = S.sieve(N)
    source_case = S.cost_case(N, coefficients, primes)
    factorial = source_case["factorial"]
    perfect_power_repair, deficit_count = repair_vector(
        N, coefficients, selected_y, lambda d: S.BASE.cap_vector(d, "perfect_power")
    )
    exact_mangoldt_repair, exact_deficit_count = repair_vector(
        N, coefficients, selected_y, S.BASE.mangoldt_vector
    )
    saturated_repair, saturated_deficit_count = repair_vector(
        N, coefficients, selected_y, lambda d: saturated_cap(d, tested_primes)
    )
    assert deficit_count == exact_deficit_count == saturated_deficit_count
    assert perfect_power_repair == source_case["penalties"]["perfect_power"]
    assert saturated_repair == exact_mangoldt_repair
    removed_composite_overpayment = S.BASE.combine(
        (1, perfect_power_repair), (-1, saturated_repair)
    )
    remaining_prime_power_surplus = S.BASE.combine(
        (1, saturated_repair), (-1, exact_mangoldt_repair)
    )
    assert S.BASE.nonnegative_coefficients(removed_composite_overpayment)
    assert remaining_prime_power_surplus == {}
    total = S.BASE.combine((1, factorial), (1, saturated_repair))
    assert total == S.BASE.combine((1, factorial), (1, exact_mangoldt_repair))
    expressions = {
        "factorial_minus_N": (-N, factorial),
        "perfect_power_repair": (0, perfect_power_repair),
        "exact_mangoldt_repair": (0, exact_mangoldt_repair),
        "residual_composite_overpayment_removed": (0, removed_composite_overpayment),
        "remaining_prime_power_surplus": (0, remaining_prime_power_surplus),
        "full_total_minus_N": (-N, total),
    }
    return {
        "N": N,
        "support_limit": support_limit,
        "selected_support": selected_y,
        "candidate_count": candidate_count,
        "selection_interval_comparisons": comparisons,
        "local_repair_limit_X": X,
        "coefficients": coefficients,
        "nonzero_deficit_terms": deficit_count,
        "local_saturation": saturation,
        "exact_logarithmic_vectors": {key: vector for key, (_, vector) in expressions.items()},
        "expressions": expressions,
    }


def decimal_interval(pair):
    import mpmath as mp

    with mp.workdps(50):
        return [mp.nstr(mp.mpf(value.numerator) / value.denominator, 32) for value in pair]


def interval_evaluations(expressions):
    """Evaluate all exact vectors by both directed logarithm routes."""
    reports, last = {}, {}
    for backend, module in (("python-flint", "flint"), ("mpmath.iv", "mpmath")):
        try:
            imported = importlib.import_module(module)
        except ImportError as exc:
            reports[backend] = {"status": "UNAVAILABLE", "reason": str(exc)}
            continue
        previous = None
        precision_overlap_checks = 0
        for dps in (35, 70):
            with S.BASE.log_intervals(backend, dps) as logarithm:
                current = {
                    key: S.BASE.enclose_expression(constant, vector, logarithm)
                    for key, (constant, vector) in expressions.items()
                }
            if previous is not None:
                for key, pair in current.items():
                    assert max(pair[0], previous[key][0]) <= min(pair[1], previous[key][1])
                    precision_overlap_checks += 1
            previous = current
        last[backend] = previous
        reports[backend] = {
            "status": "PASS",
            "version": imported.__version__,
            "decimal_precision_requests": [35, 70],
            "precision_overlap_checks": precision_overlap_checks,
        }
    cross_backend_overlap_checks = 0
    if len(last) == 2:
        for key in expressions:
            left, right = last["python-flint"][key], last["mpmath.iv"][key]
            assert max(left[0], right[0]) <= min(left[1], right[1])
            cross_backend_overlap_checks += 1
    return {
        "backend_availability": reports,
        "cross_backend_overlap_checks": cross_backend_overlap_checks,
        "exact_rational_enclosures": last,
        "decimal_interval_display_only": {
            backend: {key: decimal_interval(pair) for key, pair in values.items()}
            for backend, values in last.items()
        },
    }


def run():
    start = time.monotonic()
    rows = []
    for N in CUTOFFS:
        case = selected_case(N)
        intervals = interval_evaluations(case.pop("expressions"))
        case["interval_evaluations"] = intervals
        rows.append(case)
    both_available = all(
        row["interval_evaluations"]["backend_availability"].get(backend, {}).get("status") == "PASS"
        for row in rows
        for backend in ("python-flint", "mpmath.iv")
    )
    return {
        "status": "PASS" if both_available else "EXACT_PASS_NUMERICAL_COVERAGE_INCOMPLETE",
        "runtime_seconds": time.monotonic() - start,
        "cutoffs": CUTOFFS,
        "case_count": len(rows),
        "rows": rows,
        "nonclaims": [
            "This finite diagnostic makes no asymptotic inference.",
            "The selected coefficients and cutoff choices are imported unchanged.",
            "Rounded decimal displays are not exact vectors or enclosure endpoints.",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = run()
    except Exception as exc:
        args.output.write_text(json.dumps({"status": "FAIL", "error_type": type(exc).__name__, "error": str(exc)}, indent=2) + "\n")
        raise
    args.output.write_text(json.dumps(S.BASE.json_ready(result), indent=2, sort_keys=True) + "\n")
    for row in result["rows"]:
        display = row["interval_evaluations"]["decimal_interval_display_only"]["python-flint"]
        counts = row["local_saturation"]["counts"]
        print(row["N"], "y", row["selected_support"], "X", row["local_repair_limit_X"],
              "ordinary-failures", counts["ordinary_composites_retained_failures"],
              "prime-power-failures", counts["prime_power_retention_failures"],
              "C-N", display["full_total_minus_N"][0])
    print(result["status"], result["runtime_seconds"])
    return 0 if result["status"] == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
