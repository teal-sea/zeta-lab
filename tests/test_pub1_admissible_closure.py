"""Deterministic checks for the Pub 1 source-admissible closure evidence."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import pytest

from hunts.wide_search.admissible_closure import (
    CONCAVITY_TARGET,
    SOURCE_W_LOWER,
    SOURCE_W_UPPER,
    ZPP_TARGET,
    closure_bounds,
    eta,
    eta_derivative,
    eta_prime,
    eta_prime_sq_integral,
    eta_second_l1,
    eta_squared_second_l1_upper,
    l2_error_squared_upper,
    planted_lesions,
    second_kernel_ratio,
    uniform_derivative_bounds,
    validate_distribution_identity,
)


_ROOT = Path(__file__).resolve().parents[1]
_RESULT = _ROOT / "hunts" / "wide_search" / "RESULTS-xiprime-admissible-closure.md"


def test_exact_residual_bounds_close_the_concavity_margin() -> None:
    bounds = closure_bounds()
    assert bounds.r0_l2 < Fraction(7_874_977, 10**16)
    assert bounds.r0_linf < Fraction(21_710_808, 10**12)
    assert bounds.r0pp_linf < Fraction(5_982_627, 10**9)
    assert bounds.z_l2 < Fraction(1_417_496, 10**15)
    assert bounds.z_linf < Fraction(3_907_946, 10**11)
    assert bounds.zpp_linf < ZPP_TARGET
    assert bounds.w_concavity_margin > CONCAVITY_TARGET
    assert bounds.passes


def test_delta_mass_term_is_present_with_exact_coefficient_two() -> None:
    validate_distribution_identity(2)
    with pytest.raises(ValueError, match="exactly 2"):
        validate_distribution_identity(0)


def test_second_derivative_bound_accounts_for_the_delta_mass() -> None:
    bounds = closure_bounds()
    without_delta = (
        bounds.r0pp_linf
        + bounds.second_kernel_tail * bounds.u_l2
        + bounds.q_abs * bounds.z_l2
    )
    assert bounds.zpp_linf - without_delta == 2 * bounds.z_linf


def test_residual_inflation_lesion_destroys_strict_concavity() -> None:
    lesion = closure_bounds(residual_scale=101)
    assert lesion.zpp_linf > lesion.u_concavity
    assert lesion.w_concavity_margin < 0
    assert not lesion.passes


def test_both_planted_lesions_are_detected() -> None:
    assert planted_lesions() == {
        "dropped_delta_detected": True,
        "inflated_residual_detected": True,
    }


def test_second_kernel_tail_ratio_decreases_on_the_used_tail() -> None:
    ratios = [second_kernel_ratio(k) for k in range(21, 80)]
    assert all(a > b for a, b in zip(ratios, ratios[1:]))
    assert ratios[0] < 1


def test_eta_is_an_exact_monotone_c3_endpoint_ramp() -> None:
    assert eta(Fraction(-1)) == 0
    assert eta(Fraction(0)) == 0
    assert eta(Fraction(1)) == 1
    assert eta(Fraction(2)) == 1

    grid = [Fraction(j, 64) for j in range(65)]
    values = [eta(x) for x in grid]
    assert all(a <= b for a, b in zip(values, values[1:]))
    assert all(eta_prime(x) >= 0 for x in grid)

    for order in range(1, 4):
        assert eta_derivative(order, Fraction(0)) == 0
        assert eta_derivative(order, Fraction(1)) == 0


def test_eta_derivative_integrals_are_exact() -> None:
    assert eta_second_l1() == Fraction(35, 8)
    assert eta_prime_sq_integral() == Fraction(700, 429)
    assert eta_squared_second_l1_upper() == Fraction(20615, 1716)


def test_source_derivative_bounds_are_uniform_in_length() -> None:
    kwargs = {
        "sqrt_w_prime": Fraction(3),
        "sqrt_w_second": Fraction(7),
        "w_prime": Fraction(5),
        "w_second": Fraction(11),
    }
    at_eight = uniform_derivative_bounds(Fraction(8), **kwargs)
    at_large = uniform_derivative_bounds(Fraction(8000), **kwargs)
    assert at_large[0] < at_eight[0]
    assert at_large[1] < at_eight[1]
    assert at_eight[0] < Fraction(35, 4) + Fraction(20, 8)
    assert at_eight[1] == 2 * Fraction(20615, 1716) + Fraction(31, 8)


def test_endpoint_strip_bound_converges_to_zero() -> None:
    assert SOURCE_W_LOWER == Fraction(1, 5)
    assert SOURCE_W_UPPER == 1
    assert l2_error_squared_upper(8) == Fraction(1, 4)
    assert l2_error_squared_upper(80) == Fraction(1, 40)
    assert l2_error_squared_upper(800) == Fraction(1, 400)


def test_review_note_pins_source_locations_and_quotient_orientation() -> None:
    text = _RESULT.read_text(encoding="utf-8")
    for location in (
        "Proposition 2.1, p. 7, equation (2.7)",
        "Section 7.1, p. 20, equation (7.3)",
        "Theorem D, p. 21, proof after (7.4)",
        "Remark 7.1(iii), p. 22",
        "Remark 7.3, p. 23",
    ):
        assert location in text
    assert "The quotient orientation is load-bearing" in text
    assert "minimized, not maximized" in text
