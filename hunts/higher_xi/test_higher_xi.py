"""Permanent controls for the higher-xi experiment."""

from fractions import Fraction
from pathlib import Path
import json
import sys

import numpy as np
from scipy.optimize import brentq

sys.path.insert(0, str(Path(__file__).resolve().parent))

from bian_audit import (
    FIGURE_10_1,
    PAGE_93_KAPPA_2,
    alpha_expression,
    audit,
    endpoint_expression,
    required_weighted_tail,
    tail_cancellation_ratio,
)
from cue_oracle import angular_derivative_levels, derived_truncation, f1_closed
from dirichlet_recurrence import (
    dirichlet_convolution,
    dirichlet_inverse,
    run_ell,
    smallest_prime_factors,
)
from window_probe import KNOWN_XIPRIME_H, optimize_measure
from exact_c2 import derive_c2, derive_level_one


def _direct_completed_derivative_roots(
    eigenangles: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Independent product-rule roots for the first two angular derivatives."""

    size = len(eigenangles)

    def derivatives(theta: float) -> tuple[float, float]:
        sine = np.sin(0.5 * (theta - eigenangles))
        cosine = np.cos(0.5 * (theta - eigenangles))
        z_value = float(np.prod(sine))
        first = 0.0
        second_cross = 0.0
        for left in range(size):
            first += 0.5 * cosine[left] * float(np.prod(np.delete(sine, left)))
            for right in range(left + 1, size):
                kept = np.delete(sine, (left, right))
                second_cross += (
                    0.5 * cosine[left] * cosine[right] * float(np.prod(kept))
                )
        second = -0.25 * size * z_value + second_cross
        return first, second

    first_roots = []
    for index, left in enumerate(eigenangles):
        right = eigenangles[(index + 1) % size]
        if index == size - 1:
            right += 2 * np.pi
        gap = right - left
        first_roots.append(
            brentq(
                lambda point: derivatives(point)[0],
                left + gap * 1e-10,
                right - gap * 1e-10,
            )
        )
    first_roots = np.sort(np.mod(first_roots, 2 * np.pi))

    second_roots = []
    for index, left in enumerate(first_roots):
        right = first_roots[(index + 1) % size]
        if index == size - 1:
            right += 2 * np.pi
        second_roots.append(
            brentq(lambda point: derivatives(point)[1], left, right)
        )
    return first_roots, np.sort(np.mod(second_roots, 2 * np.pi))


def test_exact_bian_internal_obstruction() -> None:
    result = audit()
    assert result["kappa1_figure_expression"] == Fraction(348002, 405405)
    assert result["kappa2_figure_expression"] == Fraction(-202, 36855)
    assert result["kappa2_page93_expression"] == Fraction(-107714, 184275)
    assert result["kappa3_figure_expression"] == Fraction(-10284002, 1216215)


def test_page_93_changes_exactly_three_kappa2_signs() -> None:
    changed = [
        index
        for index, (figure, page93) in enumerate(
            zip(FIGURE_10_1[2], PAGE_93_KAPPA_2), start=1
        )
        if figure != page93
    ]
    assert changed == [8, 9, 10]
    assert all(PAGE_93_KAPPA_2[index - 1] > 0 for index in changed)


def test_reported_values_require_non_negligible_unprinted_tails() -> None:
    kappa2_tail = required_weighted_tail(FIGURE_10_1[2], Fraction(1193, 1250))
    kappa3_tail = required_weighted_tail(FIGURE_10_1[3], Fraction(4887, 5000))
    assert kappa2_tail == Fraction(-8844103, 18427500)
    assert kappa3_tail == Fraction(-11472730541, 2432430000)
    assert tail_cancellation_ratio(
        FIGURE_10_1[2], Fraction(1193, 1250)
    ) == Fraction(8844103, 9264250)
    assert tail_cancellation_ratio(
        FIGURE_10_1[3], Fraction(4887, 5000)
    ) == Fraction(11472730541, 11500217000)


def test_endpoint_is_alpha_one_expression() -> None:
    for row in (*FIGURE_10_1.values(), PAGE_93_KAPPA_2):
        assert alpha_expression(row, Fraction(1)) == endpoint_expression(row)


def test_level_one_closed_curve_matches_its_displayed_series() -> None:
    alpha = np.array([0.05, 0.10, 0.20])
    truncation = derived_truncation(1, alpha)
    exact = f1_closed(alpha)
    assert np.max(np.abs(truncation - exact)) < 2e-12


def test_level_one_exact_generator_matches_farmer_gonek_lee() -> None:
    expected = dict(enumerate(FIGURE_10_1[1], start=1))
    assert derive_level_one(11) == expected


def test_level_two_exact_routes_agree_and_reject_bian_row() -> None:
    expected = {
        1: Fraction(1),
        2: Fraction(-8),
        3: Fraction(24),
        4: Fraction(-32),
        5: Fraction(64, 3),
        6: Fraction(-64, 3),
        7: Fraction(1216, 45),
        8: Fraction(-256, 15),
        9: Fraction(1088, 63),
        10: Fraction(-11776, 945),
        11: Fraction(42496, 4725),
    }
    assert derive_c2(11)["coefficients"] == expected
    assert expected[1] == FIGURE_10_1[2][0]
    assert all(expected[index] != FIGURE_10_1[2][index - 1] for index in range(2, 12))


def test_first_level_two_divergence_is_the_missing_binomial_weight() -> None:
    q = derive_c2(2)["dirichlet_coefficients"]
    assert q[0] == {(0,): Fraction(-1)}
    assert q[1] == {(1,): Fraction(2)}
    assert derive_c2(2)["coefficients"][2] == Fraction(-8)
    assert FIGURE_10_1[2][1] == Fraction(-4)


def test_exact_fixture_matches_both_generators() -> None:
    fixture_path = Path(__file__).with_name("C2_EXACT.json")
    fixture = json.loads(fixture_path.read_text())
    derived = derive_c2(11)["coefficients"]
    for row in fixture["coefficients"]:
        index = row["i"]
        route_a = Fraction(row["route_a"])
        route_b = Fraction(row["route_b"])
        printed = Fraction(row["bian_figure_10_1"])
        assert route_a == route_b == derived[index]
        assert (route_a == printed) == (row["status"] == "MATCH")


def test_completed_picket_fence_stays_a_picket_fence() -> None:
    size = 12
    eigenangles = (np.arange(size) + 0.23) * (2 * np.pi / size)
    levels = angular_derivative_levels(eigenangles, max_level=2)
    assert [len(level) for level in levels] == [size, size, size]
    for level in levels:
        cyclic_gaps = np.diff(np.r_[level, level[0] + 2 * np.pi])
        assert np.max(np.abs(cyclic_gaps - 2 * np.pi / size)) < 1e-11


def test_completed_derivative_roots_match_direct_product_rule() -> None:
    eigenangles = np.array(
        [0.10, 0.43, 0.91, 1.48, 2.02, 2.77, 3.18, 3.71, 4.26, 4.83, 5.41, 6.02]
    )
    fourier = angular_derivative_levels(eigenangles, max_level=2)
    direct_first, direct_second = _direct_completed_derivative_roots(eigenangles)
    assert np.max(np.abs(fourier[1] - direct_first)) < 1e-10
    assert np.max(np.abs(fourier[2] - direct_second)) < 1e-10


def test_dirichlet_inverse_is_an_inverse() -> None:
    factors = smallest_prime_factors(40)
    coefficients = np.zeros(41, dtype=complex)
    coefficients[1] = 3 + 2j
    coefficients[2] = -1
    coefficients[3] = 4j
    coefficients[5] = 2
    inverse = dirichlet_inverse(coefficients, factors)
    product = dirichlet_convolution(coefficients, inverse)
    assert abs(product[1] - 1) < 1e-14
    assert np.max(np.abs(product[2:])) < 1e-13


def test_direct_recurrence_known_level_is_the_control() -> None:
    row = run_ell(ell=8, alphas=(0.25, 0.5))
    level_one = np.array(row["cumulative"]["1"])
    known = np.array(row["controls"]["fgl_level1_integral"])
    level_two = np.array(row["cumulative"]["2"])
    assert np.all(level_one > 0)
    assert np.all(level_two > 0)
    assert np.max(np.abs(level_one - known)) < 0.003


def test_window_objective_reconstructs_known_level_one_limit() -> None:
    bins = 600
    locations = (np.arange(bins) + 0.5) / bins
    weights = f1_closed(locations) / bins
    result = optimize_measure(
        locations,
        weights,
        basis_count=10,
        bins=bins,
        quadrature=80,
    )
    assert abs(result["H"] - KNOWN_XIPRIME_H) < 1e-6
