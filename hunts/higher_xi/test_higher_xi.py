"""Permanent controls for the higher-xi experiment."""

from fractions import Fraction
from pathlib import Path
import json
import math
import sys

import numpy as np
import sympy as sp
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
from bandwidth_forensics import (
    constant_window_bound,
    continuation_scan,
    f2_half_band_bernstein_floor,
    gaussian_powerful_rate,
    half_band_coercivity_margin,
    improved_architecture_feasible,
    improved_parameter_witness,
    optimized_cluster_feasible,
    optimized_gaussian_rho,
    optimized_parameter_witness,
    numerical_window_optimum,
    original_architecture_feasible,
    original_parameter_witness,
    prime_split_architecture_feasible,
    prime_split_parameter_witness,
    shell_stieltjes_bound,
    split_powerful_witness,
    universal_window_denominator_floor,
    useful_bandwidth_bounds,
)
from bridge_obstruction import (
    claimed_decay_upper,
    computed_overlap_boundary_coefficient,
    counterexample_height,
    kernel_interval_lower_bound,
    level_one_fixed_b_value,
    target_overlap_boundary_coefficient,
    target_window_endpoint,
)
from cue_oracle import angular_derivative_levels, derived_truncation, f1_closed
from dirichlet_recurrence import (
    dirichlet_convolution,
    dirichlet_inverse,
    run_ell,
    smallest_prime_factors,
)
from corrected_form_factor import (
    TWO_STEP_RATIO,
    coarse_two_step_ratio,
    corrected_coefficients,
    fock_upper_coefficient,
    gram_weight_inequalities,
    ratio_residue_formula,
    sign_coherence_holds,
    tail_bound,
    value_interval,
)
from window_probe import KNOWN_XIPRIME_H, optimize_measure
from exact_c2 import derive_c2, derive_level_one
from resummed_bridge import (
    absolute_word_mass,
    closed_absolute_word_mass,
    coefficientwise_ratio,
    exact_denominator_split_defect,
    exact_numerator_split_defect,
    frozen_q_defect,
    level_two_resolvent_defect,
)
from urms2_attack import (
    convolution_inverse_defect,
    inverse_difference_bound,
    inverse_height_derivative_bound,
    inverse_wiener_bound,
    level_one_envelope,
    level_two_envelope,
    level_two_multiplicativity_defect,
    normalized_trivial_square_bound,
    projection_order_for_square_tail,
    resummed_projection_errors,
    young_multiplier_bound,
)
from rams1 import (
    alpha_symmetry_defects,
    borel_multiplicativity_defects,
    cauchy_partial_fraction_defect,
    cauchy_two_range_exponent_defects,
    commutator_local_mass,
    formal_level_one_layers,
    independent_resolvent_defect,
    phi1,
    powerful_factorization_defects,
    powerful_split_coefficient_defects,
    powerful_squarefree_defects,
    prime_power_layer,
    prime_power_resummed,
    square_density_decomposition,
    squarefree_identity_defects,
    support_loss_control,
)
from rams2_cluster import (
    connected_component_defects,
    exact_route_defects,
    full_squarefree_majorant_coefficient,
    inverse_series_terms,
    majorant_ratios,
    pq_borel_defect,
    pq_connected_defect,
    pq_direct_resolvent,
    prime_power_q_cluster,
    prime_power_q_direct,
    rc2_parameter_margins,
    squarefree_q_cluster,
)
from window_certificate import exact_window_check, positivity_floor


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


def test_extended_fixture_matches_all_exact_routes() -> None:
    fixture = json.loads(Path(__file__).with_name("C2_EXTENDED.json").read_text())
    derived = derive_c2(40)["coefficients"]
    assert derived == corrected_coefficients(40)
    assert len(fixture["coefficients"]) == 40
    for row in fixture["coefficients"]:
        index = row["i"]
        value = Fraction(row["value"])
        assert value == derived[index]
        assert Fraction(row["scaled_integer"]) == (
            value * math.factorial(index) / 2 ** (index - 1)
        )


def test_corrected_coefficients_have_exact_alternating_sign() -> None:
    assert sign_coherence_holds(40)
    assert all(
        (value > 0) == (index % 2 == 1)
        for index, value in corrected_coefficients(40).items()
    )


def test_fock_majorant_dominates_the_exact_fixture() -> None:
    assert all(left <= right for left, right in gram_weight_inequalities().values())
    assert all(
        abs(value) <= fock_upper_coefficient(index)
        for index, value in corrected_coefficients(40).items()
    )


def test_coarse_tail_ratio_has_the_claimed_uniform_bound() -> None:
    for total_power in range(101, 181):
        index = total_power + 1
        assert coarse_two_step_ratio(index) == ratio_residue_formula(
            total_power % 4, total_power // 4
        )
        assert coarse_two_step_ratio(index) <= TWO_STEP_RATIO


def test_uniform_index_40_tail_and_endpoint_interval() -> None:
    bound = tail_bound()
    assert bound < Fraction(328, 10**11)
    lower, upper = value_interval(Fraction(1))
    target = Fraction(4763446325, 10**9)
    assert lower < target < upper


def test_small_exact_window_gives_a_strict_point_9234015_bound() -> None:
    result = exact_window_check()
    assert positivity_floor() == Fraction(68213, 100000)
    assert result["tail_loss"] == tail_bound()
    assert result["simplicity_lower_bound"] > Fraction(9234015, 10**7)


def test_contour_tail_has_no_claimed_height_decay() -> None:
    for constant in (Fraction(1), Fraction(10), Fraction(10**6), Fraction(7, 3)):
        height = counterexample_height(constant, cutoff=17)
        assert height >= 17
        assert kernel_interval_lower_bound() > claimed_decay_upper(constant, height)


def test_distinct_fixed_orders_cannot_have_one_pointwise_limit() -> None:
    alpha = Fraction(1, 2)
    first = level_one_fixed_b_value(1, alpha)
    second = level_one_fixed_b_value(2, alpha)
    assert second - first == Fraction(1, 24)


def test_untruncated_level_two_resolvent_identities_are_exact() -> None:
    assert level_two_resolvent_defect() == 0
    assert exact_denominator_split_defect() == 0
    assert exact_numerator_split_defect() == 0


def test_frozen_resolvent_is_the_corrected_q_object() -> None:
    assert frozen_q_defect() == 0


def test_absolute_word_mass_has_closed_geometric_growth() -> None:
    assert [absolute_word_mass(power) for power in range(20)] == [
        closed_absolute_word_mass(power) for power in range(20)
    ]


def test_elementary_absolute_resummation_boundary_is_one_quarter() -> None:
    assert coefficientwise_ratio(Fraction(1, 5)) == Fraction(4, 5)
    assert coefficientwise_ratio(Fraction(1, 4)) == 1
    assert coefficientwise_ratio(Fraction(1, 3)) == Fraction(4, 3)


def test_exact_convolution_inverse_toy_control() -> None:
    assert all(value == 0 for value in convolution_inverse_defect())


def test_level_two_inverse_is_not_multiplicative() -> None:
    defect = level_two_multiplicativity_defect()
    assert defect != 0
    assert defect.subs({"z": Fraction(1, 10), "l2": 2, "l3": 3}) != 0


def test_wiener_and_hilbert_resolvent_bounds() -> None:
    inverse = inverse_wiener_bound(Fraction(5), Fraction(2))
    assert inverse == Fraction(1, 3)
    assert inverse_height_derivative_bound(inverse, Fraction(9)) == 1
    assert inverse_difference_bound(inverse, Fraction(1, 2), Fraction(6)) == 1
    assert young_multiplier_bound(Fraction(3, 2), Fraction(4, 3)) == 2


def test_resummed_envelopes_and_one_log_loss() -> None:
    assert level_one_envelope(Fraction(2, 5)) == Fraction(5, 3)
    assert level_two_envelope(Fraction(2, 5)) == Fraction(21, 5)
    first = normalized_trivial_square_bound(Fraction(100), Fraction(1))
    second = normalized_trivial_square_bound(Fraction(200), Fraction(1))
    assert second == 2 * first


def test_square_tail_requires_only_logarithmic_projection_order() -> None:
    contraction = Fraction(4, 5)
    small = projection_order_for_square_tail(10**3, contraction)
    large = projection_order_for_square_tail(10**6, contraction)
    assert 0 < small < large
    assert Fraction(10**6) * contraction ** (2 * (large + 1)) <= Fraction(
        1, 10**6
    )
    assert Fraction(10**6) * contraction ** (2 * large) > Fraction(1, 10**6)


def test_exact_resummed_recurrence_matches_corrected_taylor_projections() -> None:
    errors = resummed_projection_errors()
    assert all(right < left for left, right in zip(errors, errors[1:]))
    assert errors[-1] < 1e-12


def test_level_one_squarefree_support_has_exactly_one_depth() -> None:
    assert all(defect == 0 for defect in squarefree_identity_defects())


def test_level_one_alpha_is_log_n_over_k_times_lambda_k() -> None:
    assert all(defect == 0 for defect in alpha_symmetry_defects())


def test_borel_convolution_generator_is_multiplicative() -> None:
    assert all(defect == 0 for defect in borel_multiplicativity_defects())


def test_powerful_squarefree_support_split_is_exact() -> None:
    assert all(defect == 0 for defect in powerful_squarefree_defects())
    assert all(defect == 0 for defect in powerful_factorization_defects())


def test_resummed_coefficient_factors_over_the_powerful_split() -> None:
    assert all(defect == 0 for defect in powerful_split_coefficient_defects())


def test_early_smoothed_cauchy_kernel_selects_the_two_ranges() -> None:
    assert cauchy_partial_fraction_defect() == 0
    assert cauchy_two_range_exponent_defects() == (0, 0)
    radius = sp.Symbol("R", positive=True)
    variable = sp.Symbol("u", positive=True)
    direct = 2 * sp.integrate(
        variable / (1 + variable**2),
        (variable, 0, radius),
    )
    assert sp.simplify(direct - commutator_local_mass(radius)) == 0


def test_level_one_depth_sum_matches_independent_exact_inverse() -> None:
    assert independent_resolvent_defect() < 1e-13


def test_level_one_prime_formula_is_exact() -> None:
    layers, logs = formal_level_one_layers(10, 3)
    for prime in (2, 3, 5, 7):
        assert layers[0][prime] == -logs[prime]
        assert layers[1][prime] == logs[prime] ** 2
        assert layers[2][prime] == 0
        assert layers[3][prime] == 0


def test_level_one_prime_power_layers_and_resummation_are_exact() -> None:
    layers, logs = formal_level_one_layers(32, 5)
    z = Fraction(2, 7)
    for prime, exponent in ((2, 5), (3, 3), (5, 2)):
        integer = prime**exponent
        for depth in range(1, 6):
            assert layers[depth][integer] == prime_power_layer(
                exponent, depth, logs[prime]
            )
        reconstructed = layers[0][integer] + sum(
            z**depth * layers[depth][integer] for depth in range(1, 6)
        )
        assert sp.expand(
            reconstructed - prime_power_resummed(exponent, z, logs[prime])
        ) == 0


def test_exact_finite_square_density_partitions_by_support_and_depth() -> None:
    result = square_density_decomposition(300, 0.5)
    assert result.total > 0
    assert math.isclose(result.total, sum(result.categories.values()), rel_tol=1e-12)
    assert math.isclose(
        result.total,
        result.depth_diagonal
        + result.depth_cross_positive
        + result.depth_cross_negative,
        rel_tol=1e-12,
    )
    assert result.depth_cross_negative < 0


def test_level_one_fixed_depth_mains_define_the_expected_square_factor() -> None:
    assert abs(phi1(0.0) - 1.0) < 1e-15
    assert abs(phi1(0.5) - 0.2552963145041274) < 1e-15


def test_support_control_distinguishes_a_genuine_second_logarithm() -> None:
    small = support_loss_control(1000)
    large = support_loss_control(10000)
    assert large["prime_supported_over_x_log_x"] < 1.2
    assert large["prime_supported_over_x_log_x"] > 0.8
    assert large["dense_toy_over_x_log_x"] > small["dense_toy_over_x_log_x"]
    assert large["dense_toy_over_x_log_x"] > 5


def test_level_two_inverse_has_an_exact_untruncated_ab_expansion() -> None:
    terms = inverse_series_terms(6)
    assert terms[0] == {(0, 0): 1}
    assert terms[1] == {(1, 0): 2}
    assert terms[2] == {(2, 0): 3, (0, 1): -1}
    assert terms[4] == {(4, 0): 5, (2, 1): -10, (0, 2): 1}


def test_level_two_squarefree_inverse_agrees_by_three_exact_routes() -> None:
    assert exact_route_defects(5) == (sp.Integer(0),) * 10


def test_pq_is_the_first_exact_connected_defect() -> None:
    z, t, lp, lq = sp.symbols("z t lp lq")
    assert pq_direct_resolvent(lp, lq, z) == sp.expand(
        6 * lp * lq * z**2
        - 4 * lp * lq * (lp + lq) * z**3
        + 2 * lp**2 * lq**2 * z**4
    )
    assert sp.expand(
        pq_connected_defect(lp, lq, z)
        - lp * lq * z**2 * (2 - 2 * z * (lp + lq) + z**2 * lp * lq)
    ) == 0
    assert pq_borel_defect(lp, lq, z, t) == -2 * t * z**2 * lp * lq


def test_hadamard_clusters_are_alternating_paths_and_even_cycles() -> None:
    assert connected_component_defects(6) == (sp.Integer(0),) * 6


def test_gaussian_cluster_route_includes_repeated_prime_support() -> None:
    z, log_prime = sp.symbols("z log_prime")
    for exponent in range(1, 5):
        assert sp.expand(
            prime_power_q_cluster(exponent, log_prime, z)
            - prime_power_q_direct(exponent, log_prime, z)
        ) == 0


def test_squarefree_q_matching_formula_starts_with_corrected_words() -> None:
    z, lp, lq = sp.symbols("z lp lq")
    assert squarefree_q_cluster((lp,), z) == (
        -lp + 2 * z * lp**2 - z**2 * lp**3
    )
    assert squarefree_q_cluster((lp, lq), z) == sp.expand(
        (lp + lq)
        * z**2
        * lp
        * lq
        * ((2 - z * lp) * (2 - z * lq) - 2)
    )


def test_all_support_size_majorant_is_uniformly_summable() -> None:
    coefficients = [full_squarefree_majorant_coefficient(size) for size in range(1, 21)]
    ratios = majorant_ratios(20)
    assert coefficients[:5] == [
        4,
        3,
        Fraction(49, 45),
        Fraction(289, 840),
        Fraction(1681, 18900),
    ]
    assert all(ratio < 1 for ratio in ratios)
    assert ratios[-1] < Fraction(1, 12)


def test_first_rc2_band_has_strict_exact_parameter_margins() -> None:
    margins = rc2_parameter_margins()
    assert margins == {
        "target_rams": Fraction(3, 50),
        "upper_cutoff_rams": Fraction(3, 250),
        "tail_at_epsilon_zero": Fraction(1, 500),
        "maximum_epsilon": Fraction(1, 22),
    }


def test_one_hundredth_was_a_parameter_choice_not_an_endpoint() -> None:
    witness = original_parameter_witness(Fraction(11, 1000))
    assert all(
        witness[key] > 0
        for key in (
            "target_rho_margin",
            "cutoff_rho_margin",
            "far_tail_margin",
        )
    )
    assert original_architecture_feasible(Fraction(249, 10000))
    assert not original_architecture_feasible(Fraction(1, 40))


def test_intermediate_shell_doubles_the_natural_bridge_band() -> None:
    witness = improved_parameter_witness(Fraction(49, 1000))
    assert all(
        witness[key] > 0
        for key in (
            "target_rho_margin",
            "rams_cutoff_margin",
            "shell_decay_margin",
            "envelope_rho_margin",
            "far_tail_margin",
        )
    )
    assert improved_architecture_feasible(Fraction(499, 10000))
    assert not improved_architecture_feasible(Fraction(1, 20))
    log_y = sp.Symbol("log_y")
    assert shell_stieltjes_bound(log_y) == (
        sp.Rational(3, 2) * log_y**2
        + sp.Rational(3, 2) * log_y
        + sp.Rational(3, 4)
    )


def test_continuation_scan_finds_the_first_binding_checkpoint() -> None:
    rows = {row["alpha"]: row for row in continuation_scan()}
    assert rows["1/50"]["old_architecture"] == "PROVABLE WITH CURRENT LEMMA"
    assert rows["1/40"]["old_architecture"] == "FAILS"
    assert rows["1/40"]["after_shell_split"] == "PROVED"
    assert rows["1/20"]["after_shell_split"] == "FAILS"
    assert rows["1/20"]["after_cauchy_optimization"] == "PROVED"
    assert rows["3/40"]["after_cauchy_optimization"] == "FAILS"
    assert rows["3/40"]["after_prime_split"] == "PROVED"
    assert rows["3/10"]["after_prime_split"] == "PROVED"
    assert rows["1/2"]["after_prime_split"] == "FAILS"
    assert rows["1/2"]["first_failed_obligation"].startswith("far-tail")


def test_powerful_core_cauchy_radius_gives_the_point_07_milestone() -> None:
    rho_star = optimized_gaussian_rho()
    assert abs(float(rho_star) - 0.14545246030840452) < 1e-15
    assert optimized_cluster_feasible(Fraction(7, 100))
    assert not optimized_cluster_feasible(Fraction(3, 40))
    witness = optimized_parameter_witness(Fraction(7, 100))
    assert witness["laplace_margin"] == Fraction(3854691, 841000000)
    assert gaussian_powerful_rate(Fraction(143, 1000), Fraction(71, 100)) < 1
    assert all(
        witness[key] > 0
        for key in (
            "target_rho_margin",
            "rams_cutoff_margin",
            "shell_decay_margin",
            "envelope_rho_margin",
            "far_tail_margin",
        )
    )


def test_finite_prime_peeling_removes_the_fixed_rho_barrier() -> None:
    for rho in (Fraction(1, 10), Fraction(1), Fraction(21, 10), Fraction(10)):
        witness = split_powerful_witness(rho)
        radius = witness["tail_radius"]
        cutoff = witness["small_prime_cutoff"]
        assert witness["laplace_rate"] < Fraction(1, 2)
        assert cutoff * radius**2 == 1
    assert prime_split_architecture_feasible(Fraction(499, 1000))
    assert not prime_split_architecture_feasible(Fraction(1, 2))
    witness = prime_split_parameter_witness(Fraction(499, 1000))
    assert all(
        witness[key] > 0
        for key in (
            "shell_decay_margin",
            "far_tail_margin",
            "mean_value_margin",
            "dyadic_margin",
        )
    )


def test_window_obstruction_and_point_51_candidate_bracket_useful_bandwidth() -> None:
    assert f2_half_band_bernstein_floor() > 0
    assert constant_window_bound(Fraction(1, 2))["simplicity_lower_bound"] < 0
    obstruction = universal_window_denominator_floor(Fraction(1227, 2500))
    assert obstruction["denominator_floor"] > 2
    bounds = useful_bandwidth_bounds()
    coercivity = half_band_coercivity_margin()
    assert coercivity["denominator_margin_over_two"] > Fraction(23, 1000)
    assert bounds["lower_bound"] == Fraction(1, 2)
    assert bounds["initial_cauchy_lower_bound"] == Fraction(1227, 2500)
    assert bounds["upper_bound"] == Fraction(51, 100)
    assert bounds["upper_bound_simplicity"] > 0


def test_exploratory_window_scan_finds_no_candidate_below_half() -> None:
    below = numerical_window_optimum(0.499, nodes=300)
    above = numerical_window_optimum(0.51, nodes=300)
    assert -0.029 < below["simplicity_value"] < -0.028
    assert 0.014 < above["simplicity_value"] < 0.016
    assert below["window_minimum"] > 0
    assert above["window_minimum"] > 0


def test_target_window_has_only_a_simple_overlap_zero_at_band_edge() -> None:
    endpoint = target_window_endpoint()
    assert endpoint == Fraction(68213, 100000)
    assert target_overlap_boundary_coefficient() == endpoint**2
    assert computed_overlap_boundary_coefficient() == endpoint**2


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
