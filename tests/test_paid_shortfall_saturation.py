"""Regression checks for the finite local saturation diagnostic."""

from fractions import Fraction as F
import importlib.util
from pathlib import Path

import pytest


PATH = Path(__file__).resolve().parents[1] / "hunts/paid_shortfall_saturation/saturation.py"
SPEC = importlib.util.spec_from_file_location("paid_shortfall_saturation", PATH)
Q = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(Q)


def test_small_prime_sieve_and_cap_input_validation():
    assert Q.small_primes(1) == ()
    assert Q.small_primes(30) == (2, 3, 5, 7, 11, 13, 17, 19, 23, 29)
    with pytest.raises(ValueError):
        Q.saturated_cap(12, (4,))


@pytest.mark.parametrize("X", [12, 32, 48, 97, 192])
def test_full_finite_saturation_matches_independent_mangoldt_oracle(X):
    report = Q.local_saturation(X)
    counts = report["counts"]
    assert report["tested_primes"] == Q.small_primes(Q.isqrt(X))
    assert counts["local_integers"] == X - 1
    assert counts["ordinary_composites_excluded"] == counts["ordinary_composites"]
    assert counts["prime_power_retained"] == counts["prime_power_integers"]
    assert counts["ordinary_composites_retained_failures"] == 0
    assert counts["prime_power_retention_failures"] == 0
    assert counts["cap_equality_failures"] == 0


@pytest.mark.parametrize(
    "N,selected_y",
    [(144, 12), (576, 18), (2304, 48), (9216, 95), (36864, 192)],
)
def test_selected_cases_preserve_source_choice_and_exact_cost_identities(N, selected_y):
    case = Q.selected_case(N)
    assert case["selected_support"] == selected_y
    assert case["local_repair_limit_X"] == N // selected_y
    vectors = case["exact_logarithmic_vectors"]
    assert vectors["remaining_prime_power_surplus"] == {}
    assert Q.S.BASE.combine(
        (1, vectors["exact_mangoldt_repair"]),
        (1, vectors["residual_composite_overpayment_removed"]),
    ) == vectors["perfect_power_repair"]
    assert Q.S.BASE.combine(
        (1, vectors["factorial_minus_N"]),
        (1, vectors["exact_mangoldt_repair"]),
    ) == vectors["full_total_minus_N"]


def test_both_interval_routes_enclose_the_same_selected_case_expressions():
    pytest.importorskip("flint")
    case = Q.selected_case(576)
    report = Q.interval_evaluations(case["expressions"])
    assert report["backend_availability"]["python-flint"]["status"] == "PASS"
    assert report["backend_availability"]["mpmath.iv"]["status"] == "PASS"
    assert report["cross_backend_overlap_checks"] == len(case["expressions"])
    assert all(len(pair) == 2 for values in report["exact_rational_enclosures"].values() for pair in values.values())
    assert all(value for values in report["decimal_interval_display_only"].values() for value in values.values())


def test_selected_case_rejects_no_coefficient_substitution():
    case = Q.selected_case(144)
    assert case["coefficients"] == Q.S.balanced_prefix(case["selected_support"])
    assert sum((a / j for j, a in case["coefficients"].items()), F(0)) == 0
