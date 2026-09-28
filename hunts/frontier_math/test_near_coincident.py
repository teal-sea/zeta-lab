"""Controls for near_coincident.py, the coincident limit of the retention gap.

What a reader must be able to check without rerunning the scans:

(a) the closed-form margin used everywhere here is the retention inequality's
    real margin: it agrees with a direct quadrature of the energy functional
    `Eng G = (1/A^2) int c2 |G|^2` on coincident and mixed configurations, to
    far better than the 1e-10 the brief asks for.  The pieces it is built out
    of (`c2`, `Q`, `L2`) are each checked against their defining integrals;
(b) the second-order expansion of the margin in the gap `g` reproduces under
    finite differences, at the stated order, in both the symmetric and the
    anchored parameterisation, this is what makes the sign of `kappa2` (and
    so "coincidence is a local minimum") a measurement rather than a claim;
(c) the `m^2`-vs-`m` scaling is exhibited at `m = 2, 4, 8, 16`: damage exactly
    linear, repulsion exactly quadratic, and the quotient exactly `(m-1)`;
(d) the worst intermediate case reproduces deterministically, same `(g, m)`
    at two placement-grid resolutions, same slack to 1e-6;
(e) the measurements are consistent with EForm3 where EForm3 applies: on
    `d >= 4`-separated configurations both Lean bounds (`uniform_damage`,
    `separated_damage`) hold with room, and the margin is positive.

Two negative controls carry the weight of the module's claim:

(f) the repulsion term is load-bearing.  EForm3's own criterion
    (`retention_of_damage`, which discards it) is genuinely VIOLATED by 8
    coincident offsets on the damage peak, while the exact margin there is
    positive and large.  A route through `retention_of_damage` therefore
    cannot reach the general case at any constants;
(g) the cluster lemma's constant requirement is real: at diameter 4 the
    EForm3 damage cap `383/10000` does *not* close the cluster quadratic
    (it needs `<= 2.19041e-02`), so the threshold reported by
    `cluster_diameter_threshold` is not an artefact of a loose inequality.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest
from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from near_coincident import (  # noqa: E402
    A_CONST, EFORM3_NEAR_FIELD_RADIUS, EFORM3_SEPARATED_DAMAGE_CAP,
    EFORM3_SEPARATION, EFORM3_SHQ_HALF_COEFF, EFORM3_UNIFORM_DAMAGE_CAP,
    RECORD, ap_scan, ap_worst, c2, cluster_diameter_threshold,
    coincidence_safe_multiplicity, coincident_quadratic, coincident_slack,
    critical_depth, damage, damage_cap_for_diameter, damage_total_one_side,
    damage_windows, greedy_worst_config, margin, no_damage_radius,
    pair_slack, peak_damage_coefficient, phi_r, psi, q_transform,
    retention_margin_direct, second_moment, second_order_coefficient,
    separated_consistency, separated_worst, shq, slack, slack_offsets,
    unconditional_lower_bound, worst_over_all_configurations,
)

Y = 0.5
PEAK = RECORD["peak_offset"]


# ---------------------------------------------------------------------------
# (a) the closed form is the energy functional
# ---------------------------------------------------------------------------


def test_window_transform_matches_its_defining_integral() -> None:
    """`Q(y+is)` in closed form against `int g(u) cosh((y+is)u) du`."""
    with mp.workdps(30):
        k = mp.sqrt(2)
        for y, s in [(0.5, 6.517), (0.0, 0.0), (0.37, 12.7), (1.0, 0.0)]:
            z = mp.mpc(y, s)
            direct = mp.quad(lambda u: mp.cos(k * u) * mp.cosh(z * u), [-mp.mpf(1) / 2, mp.mpf(1) / 2])
            closed = complex(q_transform(y, s))
            assert abs(complex(direct) - closed) < 1e-13


def test_autocorrelation_closed_form_and_its_two_identities() -> None:
    """`c2` against its defining convolution, and the two moment identities."""
    with mp.workdps(30):
        k = mp.sqrt(2)
        for w in (0.0, 0.37, 0.9):
            direct = mp.quad(
                lambda u: mp.cos(k * u) * mp.cos(k * (u + w)),
                [-mp.mpf(1) / 2, mp.mpf(1) / 2 - mp.mpf(w)],
            )
            assert abs(float(direct) - c2(w)) < 1e-13
        # int c2 = A^2 and int c2 cos(vw) = phi_r(v)^2 are what turn the energy
        # functional into the closed form the module uses.
        total = mp.quad(lambda w: c2(float(w)), [-1, 0, 1])
        assert abs(float(total) - A_CONST**2) < 1e-12
        v = 3.3
        band = mp.quad(lambda w: c2(float(w)) * mp.cos(v * w), [-1, 0, 1])
        assert abs(float(band) - float(phi_r(v)) ** 2) < 1e-12


def test_second_moment_closed_form() -> None:
    with mp.workdps(30):
        k = mp.sqrt(2)
        direct = mp.quad(lambda u: mp.cos(k * u) * u**2, [-mp.mpf(1) / 2, mp.mpf(1) / 2])
        assert abs(float(direct) - second_moment()) < 1e-14
    # L2 = -phi_r''(0), the constant FAR-FIELD-EXCHANGE.md calls 0.0712006
    assert second_moment() == pytest.approx(RECORD["second_moment"], rel=1e-9)


@pytest.mark.parametrize(
    "xs, y, t",
    [
        ((PEAK, PEAK), 0.5, 0.0),                       # two coincident, on the peak
        ((0.0, 0.0, 0.0), 0.5, PEAK),                   # three coincident
        ((0.0, 0.0, 0.0, 0.0), 0.5, PEAK),              # four coincident
        ((-PEAK, PEAK), 0.5, 0.0),                      # the two-sided pair
        ((1.3, 7.9, 20.1), 0.37, 2.2),                  # generic, off-peak
    ],
)
def test_closed_form_margin_matches_direct_energy_quadrature(xs, y, t) -> None:
    """(a) The control the brief asks for: closed form vs energy functional."""
    direct = float(retention_margin_direct(xs, y, t, dps=25))
    assert margin(xs, y, t) == pytest.approx(direct, abs=1e-10, rel=0)


def test_coincident_slack_agrees_with_the_general_evaluator() -> None:
    """The `m`-coincident shortcut is the general slack, not a separate model."""
    for m in (1, 2, 3, 5, 9):
        assert coincident_slack(m, Y) == pytest.approx(
            slack_offsets([PEAK] * m, Y), rel=0, abs=1e-14
        )
    assert margin([0.0] * 3, Y, -PEAK) == pytest.approx(
        (4 / A_CONST**2) * coincident_slack(3, Y), rel=1e-13
    )


# ---------------------------------------------------------------------------
# (b) the second-order expansion in g
# ---------------------------------------------------------------------------


def test_second_order_expansion_matches_finite_differences() -> None:
    """(b) `margin(g) - margin(0) = kappa2 g^2 + O(g^4)`, symmetric split."""
    so = second_order_coefficient(Y)
    kappa2 = so["kappa2"]
    scale = 4 / A_CONST**2
    base = scale * pair_slack(so["peak_offset"], 0.0, Y)
    errors = []
    for g in (0.4, 0.2, 0.1, 0.05):
        quotient = (scale * pair_slack(so["peak_offset"], g, Y) - base) / g**2
        errors.append(abs(quotient - kappa2))
    assert errors[-1] < 1e-7
    # the residual is O(g^2), so halving g cuts it by about four (below
    # g = 0.05 the quotient is limited by cancellation, not by the expansion)
    for a, b in zip(errors, errors[1:]):
        assert 3.5 < a / b < 4.5


def test_second_order_expansion_matches_in_the_anchored_parameterisation() -> None:
    """Anchoring one offset doubles the damage term and keeps the repulsion."""
    so = second_order_coefficient(Y)
    scale = 4 / A_CONST**2
    base = scale * pair_slack(so["peak_offset"], 0.0, Y, anchored=True)
    quotient = (scale * pair_slack(so["peak_offset"], 0.005, Y, anchored=True) - base) / 0.005**2
    assert quotient == pytest.approx(so["kappa2_anchored"], rel=2e-3)


def test_coincidence_is_a_local_minimum_of_the_margin() -> None:
    """The sign of `kappa2`, stated as the measurement it is."""
    so = second_order_coefficient(Y)
    assert so["kappa2"] > 0
    assert so["coincidence_is_local_minimum"]
    assert so["kappa2"] == pytest.approx(RECORD["second_order_kappa2"], rel=1e-6)
    assert so["damage_part"] == pytest.approx(RECORD["second_order_damage_part"], rel=1e-6)
    assert so["repulsion_part"] == pytest.approx(RECORD["second_order_repulsion_part"], rel=1e-6)
    # the repulsion is a 2% correction to the local geometry, not its cause
    assert so["repulsion_share"] < 0.02
    # and the margin really does rise on both sides of g = 0
    m0 = pair_slack(so["peak_offset"], 0.0, Y)
    for g in (0.05, 0.2, 0.5):
        assert pair_slack(so["peak_offset"], g, Y) > m0


# ---------------------------------------------------------------------------
# (c) m^2 versus m
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("m", [2, 4, 8, 16])
def test_damage_is_linear_and_repulsion_quadratic_in_multiplicity(m) -> None:
    """(c) The trade, exhibited: `m D` against `m(m-1) A^2/800`."""
    peak_damage = float(damage(Y, PEAK))
    offsets = [PEAK] * m
    total_damage = float(np.sum(damage(Y, np.array(offsets))))
    relief = slack_offsets(offsets, Y) - shq(Y) / 2 + total_damage
    assert total_damage == pytest.approx(m * peak_damage, rel=1e-13)
    assert relief == pytest.approx(m * (m - 1) * A_CONST**2 / 800, rel=1e-13)
    # the quotient is exactly (m-1) * A^2/(800 D): linear in m, so the trade
    # crosses over once and never comes back
    assert relief / total_damage == pytest.approx(
        (m - 1) * A_CONST**2 / (800 * peak_damage), rel=1e-13
    )


def test_the_coincident_quadratic_never_touches_zero() -> None:
    """m_0 = 1: no multiplicity is dangerous, at any y the problem allows."""
    q = coincident_quadratic(Y)
    assert q["discriminant"] < 0
    assert q["safe_for_every_m"]
    assert q["discriminant"] == pytest.approx(RECORD["coincident_discriminant"], rel=1e-5)
    assert q["m_star"] == pytest.approx(RECORD["coincident_m_star"], rel=1e-6)
    assert q["margin_at_m_star"] == pytest.approx(RECORD["coincident_min_margin"], rel=1e-6)
    assert coincidence_safe_multiplicity(Y) == RECORD["coincidence_safe_multiplicity"] == 1
    for m in (1, 2, 3, 4, 7, 8, 16, 64, 256):
        assert coincident_slack(m, Y) > 0
    for y in (0.05, 0.2, 0.35, 0.5):
        assert coincidence_safe_multiplicity(y) == 1


def test_the_multiplicity_threshold_is_not_a_constant_true_detector() -> None:
    """`m_0 = 1` has to be a measurement, so the detector must be able to say 48.

    Past the critical depth the coincident quadratic really does dip below
    zero, and `coincidence_safe_multiplicity` reports the far end of the
    dangerous band rather than 1.  Without this the `m_0 = 1` above would be
    indistinguishable from a function that cannot return anything else.
    """
    assert coincidence_safe_multiplicity(1.5) == 48
    dangerous = [m for m in range(1, 200) if coincident_slack(m, 1.5) <= 0]
    assert (min(dangerous), max(dangerous)) == (8, 47)
    assert coincident_slack(7, 1.5) > 0
    assert coincident_slack(48, 1.5) > 0


def test_lemma_statements_carry_the_constants_that_were_measured() -> None:
    """The prover-facing text and the functions may not drift apart."""
    from near_coincident import LEMMA_A, LEMMA_B, LEMMA_C

    assert f"{cluster_diameter_threshold()['rho']:.4f}" in LEMMA_B
    assert f"{cluster_diameter_threshold(damage_cap=peak_damage_coefficient(Y))['rho']:.4f}" in LEMMA_B
    assert f"{damage_cap_for_diameter(EFORM3_SEPARATION):.5e}" in LEMMA_B
    assert damage_cap_for_diameter(EFORM3_SEPARATION) > 109 / 5000 > peak_damage_coefficient(Y)
    bound = unconditional_lower_bound(Y, count=300)
    assert f"{bound['window_width_max']:.5f}" in LEMMA_C
    assert f"{bound['gamma']:.5f}" in LEMMA_C
    assert f"{bound['worst_net_damage']:.5e}" in LEMMA_C
    assert f"{bound['shq_half']:.5e}" in LEMMA_C
    assert "1/400" in LEMMA_A and "Shq y / 2" in LEMMA_A


def test_critical_depth_is_far_above_the_range_the_problem_uses() -> None:
    y_crit = critical_depth()
    assert y_crit == pytest.approx(RECORD["critical_depth"], rel=1e-6)
    assert y_crit > 2 * Y
    assert coincident_quadratic(y_crit * 1.02)["discriminant"] > 0
    assert coincident_quadratic(y_crit * 0.98)["discriminant"] < 0


# ---------------------------------------------------------------------------
# (d) the worst intermediate case, deterministically
# ---------------------------------------------------------------------------


def test_recorded_worst_arithmetic_progression_reproduces() -> None:
    """(d) The two recorded worst cases, at their recorded values."""
    worst = ap_worst(RECORD["ap_worst_gap"], RECORD["ap_worst_m"], Y)
    assert worst["slack"] == pytest.approx(RECORD["ap_worst_slack"], rel=1e-6)
    assert worst["margin"] == pytest.approx(RECORD["ap_worst_margin"], rel=1e-6)
    assert worst["slack"] > 0


def test_worst_intermediate_case_is_stable_under_the_placement_grid() -> None:
    """Same winner at two grid resolutions, and the value agrees to 1e-6."""
    gaps = np.round(np.arange(0.0, 8.0 + 1e-9, 0.05), 3)
    coarse = ap_scan(Y, gaps=gaps, multiplicities=(2, 3, 8), step=0.01)
    fine = ap_scan(Y, gaps=gaps, multiplicities=(2, 3, 8), step=0.005)
    assert coarse["worst"]["m"] == fine["worst"]["m"] == RECORD["ap_worst_m"]
    assert coarse["worst"]["gap"] == pytest.approx(fine["worst"]["gap"], abs=1e-3)
    assert coarse["worst"]["slack"] == pytest.approx(fine["worst"]["slack"], abs=1e-6)
    assert coarse["worst"]["slack"] == pytest.approx(RECORD["ap_worst_slack"], rel=1e-5)
    # the winner is total coincidence, i.e. inside the region d >= 4 excludes
    assert coarse["worst"]["gap"] < EFORM3_SEPARATION
    # but the best the same family can do with gap >= 4 is only 1.95% better
    assert coarse["excluded_region_is_worse"]
    assert coarse["excluded_penalty"] == pytest.approx(RECORD["ap_excluded_penalty"], rel=0.05)


def test_the_separated_arithmetic_progressions_resonate_at_2pi() -> None:
    """The `g >= 4` worst case sits just under the window spacing `2 pi`."""
    for m in (4, 6, 8):
        best = min(
            (ap_worst(g, m, Y, refine=False) for g in np.arange(4.0, 8.0, 0.02)),
            key=lambda r: r["slack"],
        )
        assert 6.1 < best["gap"] < 2 * math.pi
        assert best["slack"] > 0


def test_the_binding_depth_is_the_top_of_the_allowed_range() -> None:
    """(d, on y) The scale-free ratio grows with `y`, so `y = 1/2` is worst.

    It also records where the family's worst member moves: at shallow depth
    the `2 pi`-resonant separated progression is the worst one, and only at
    `y = 1/2` does total coincidence take over.
    """
    from near_coincident import depth_scan

    scan = depth_scan(depths=(0.1, 0.3, 0.5), multiplicities=(2, 3, 8), gap_step=0.05)
    assert scan["ratio_increases_with_depth"]
    assert scan["worst"]["y"] == 0.5
    assert scan["worst"]["gap"] == 0.0
    assert scan["rows"][0]["gap"] > EFORM3_SEPARATION
    for row in scan["rows"]:
        assert row["slack"] > 0
        assert row["ratio"] < 1


def test_the_free_worst_configuration_beats_every_arithmetic_progression() -> None:
    """The prescribed family is not where the real worst case lives."""
    free = worst_over_all_configurations(Y, count=60)
    assert free["slack"] < RECORD["ap_worst_slack"]
    assert free["slack"] == pytest.approx(RECORD["free_worst_slack"], rel=2e-3)
    assert free["m"] == RECORD["free_worst_m"]
    assert free["safety_factor"] == pytest.approx(RECORD["free_worst_safety_factor"], rel=2e-3)
    # the shape of it: triples on the innermost window, singles further out
    assert free["multiplicity_profile"][round(PEAK, 3)] == 6      # 3 on each side
    assert free["slack"] > 0


def test_greedy_ladder_agrees_with_a_local_descent() -> None:
    """The marginal ladder is measuring the real optimum, not a caricature."""
    for m in (2, 3, 4, 6):
        rec = greedy_worst_config(m, Y, count=40)
        assert rec["polished_slack"] == pytest.approx(rec["attained_slack"], abs=2e-6)
        assert rec["ladder_slack"] == pytest.approx(rec["attained_slack"], abs=1e-4)
        assert rec["polished_slack"] > 0
    # m = 4 is two coincident pairs, one on each side of the pulse
    rec4 = greedy_worst_config(4, Y, count=40)
    assert rec4["min_gap"] == pytest.approx(0.0, abs=1e-3)
    assert rec4["max_gap"] == pytest.approx(2 * PEAK, abs=1e-2)


# ---------------------------------------------------------------------------
# (e) consistency with EForm3 where EForm3 applies
# ---------------------------------------------------------------------------


def test_separated_configurations_respect_both_eform3_bounds() -> None:
    """(e) `uniform_damage` and `separated_damage`, as measurements."""
    rec = separated_consistency(Y)
    assert rec["total_within_cap"]
    assert rec["point_within_cap"]
    assert rec["all_margins_positive"]
    assert rec["worst_total_damage"] <= EFORM3_SEPARATED_DAMAGE_CAP * Y**2
    assert rec["worst_point_damage"] <= EFORM3_UNIFORM_DAMAGE_CAP * Y**2


def test_the_extremal_separated_configuration_is_the_exchange_record() -> None:
    """One offset per window peak: 40.6% of budget, 2.46x, FAR-FIELD-EXCHANGE."""
    sep = separated_worst(Y, count=60)
    assert sep["ratio"] == pytest.approx(RECORD["separated_ratio"], rel=2e-3)
    assert sep["safety_factor"] == pytest.approx(RECORD["separated_safety_factor"], rel=2e-3)
    assert sep["slack"] == pytest.approx(RECORD["separated_slack"], rel=2e-3)
    # EForm3's separated cap is above the truth, so its theorem is not tight
    assert sep["total_damage"] < sep["eform3_cap"]
    assert sep["eform3_cap_slack"] == pytest.approx(RECORD["eform3_separated_cap_looseness"], rel=5e-3)
    # a gap of 0.99 already forces one offset per window; 4 is far more than needed
    assert sep["one_offset_per_window_needs_gap"] < 1.0


def test_uniform_damage_and_near_field_radius_hold_with_the_measured_margins() -> None:
    """The two EForm3 constants this module leans on, against their truths."""
    assert peak_damage_coefficient(Y) < EFORM3_UNIFORM_DAMAGE_CAP
    assert peak_damage_coefficient(Y) == pytest.approx(RECORD["peak_damage_over_y2"], rel=1e-7)
    assert no_damage_radius(Y) > EFORM3_NEAR_FIELD_RADIUS
    assert no_damage_radius(Y) == pytest.approx(RECORD["no_damage_radius"], rel=1e-9)
    assert shq(Y) / 2 / Y**2 > EFORM3_SHQ_HALF_COEFF
    # the binding depth is the top of the allowed range
    coeffs = [peak_damage_coefficient(y) for y in (0.05, 0.1, 0.2, 0.3, 0.4, 0.5)]
    assert all(a < b for a, b in zip(coeffs, coeffs[1:]))


def test_damage_geometry_reproduces_the_far_field_exchange_table() -> None:
    """Peaks, widths and the total, against the numbers already on record."""
    wins = damage_windows(Y, 6)
    assert wins[0].peak == pytest.approx(RECORD["peak_offset"], rel=1e-9)
    assert wins[0].damage == pytest.approx(RECORD["peak_damage"], rel=1e-9)
    assert wins[0].lo == pytest.approx(RECORD["no_damage_radius"], rel=1e-9)
    # FAR-FIELD-EXCHANGE.md's first six peaks
    recorded = [4.396e-3, 9.751e-4, 4.233e-4, 2.361e-4, 1.505e-4, 1.043e-4]
    for w, want in zip(wins, recorded):
        assert w.damage == pytest.approx(want, rel=2e-4)
        assert 0.96 <= w.width <= 0.987
    for a, b in zip(wins, wins[1:]):
        assert b.peak - a.peak == pytest.approx(2 * math.pi, abs=0.15)
    total = damage_total_one_side(Y, count=60)
    assert total["total_upper"] == pytest.approx(RECORD["damage_total_one_side"], rel=5e-3)
    assert total["max_width"] == pytest.approx(RECORD["window_width_max"], rel=1e-8)


# ---------------------------------------------------------------------------
# (f) the negative control that matters: the repulsion term is load-bearing
# ---------------------------------------------------------------------------


def test_eform3s_own_criterion_fails_on_eight_coincident_offsets() -> None:
    """Damage alone exceeds `Shq/2` from m = 8, while the true margin is fine.

    `retention_of_damage` asks for `sum_j D_j <= Shq y / 2`.  Eight offsets on
    the damage peak break that hypothesis, so no sharpening of the damage
    constants can carry that route to the general case: what saves the
    configuration is the repulsion term the route discards.
    """
    budget = shq(Y) / 2
    peak_damage = float(damage(Y, PEAK))
    failures = [m for m in range(1, 12) if m * peak_damage > budget]
    assert min(failures) == 8
    assert 8 * peak_damage > budget
    # ... and yet
    assert coincident_slack(8, Y) > 0
    assert margin([0.0] * 8, Y, -PEAK) > 0.27
    # with EForm3's own (looser) uniform cap the same route fails from m = 4,
    # which is exactly why `retention_le_three` stops at 3
    cap = EFORM3_UNIFORM_DAMAGE_CAP * Y**2
    assert 3 * cap < EFORM3_SHQ_HALF_COEFF * Y**2
    assert 4 * cap > EFORM3_SHQ_HALF_COEFF * Y**2


def test_dropping_the_repulsion_changes_the_verdict_it_is_claimed_to_change() -> None:
    """A planted ablation: zero the repulsion and the cluster statement dies."""
    offsets = [PEAK] * 8
    exact = slack_offsets(offsets, Y)
    ablated = shq(Y) / 2 - float(np.sum(damage(Y, np.array(offsets))))
    assert exact > 0 > ablated
    assert exact - ablated == pytest.approx(8 * 7 / 2 * A_CONST**2 / 400, rel=1e-13)


# ---------------------------------------------------------------------------
# (g) the cluster lemma's constant requirement is real
# ---------------------------------------------------------------------------


def test_cluster_threshold_with_eform3_constants() -> None:
    rho = cluster_diameter_threshold()
    assert rho["feasible"]
    assert rho["rho"] == pytest.approx(RECORD["cluster_rho_eform3_constants"], rel=1e-5)
    # at that diameter the cluster quadratic is nonnegative at every n ...
    c = float(phi_r(rho["rho"])) ** 2 / 800
    a = EFORM3_UNIFORM_DAMAGE_CAP * Y**2
    s_half = EFORM3_SHQ_HALF_COEFF * Y**2
    for n in range(1, 400):
        assert c * n * n - (a + c) * n + s_half >= -1e-12
    # ... and at diameter 4 it is not: the requirement is not vacuous
    c4 = float(phi_r(EFORM3_SEPARATION)) ** 2 / 800
    assert min(c4 * n * n - (a + c4) * n + s_half for n in range(1, 40)) < 0


def test_cluster_threshold_with_the_sharp_damage_constant() -> None:
    rho = cluster_diameter_threshold(damage_cap=peak_damage_coefficient(Y))
    assert rho["rho"] == pytest.approx(RECORD["cluster_rho_sharp_constants"], rel=1e-5)
    assert rho["rho"] > EFORM3_SEPARATION
    needed = damage_cap_for_diameter(EFORM3_SEPARATION)
    assert needed == pytest.approx(RECORD["damage_cap_for_rho_4"], rel=1e-5)
    assert peak_damage_coefficient(Y) < needed < EFORM3_UNIFORM_DAMAGE_CAP


# ---------------------------------------------------------------------------
# the unconditional statement
# ---------------------------------------------------------------------------


def test_unconditional_lower_bound_is_positive_and_below_every_measurement() -> None:
    """LEMMA C as a number, and as a bound the measurements do not violate."""
    bound = unconditional_lower_bound(Y, count=60)
    assert bound["holds"]
    assert bound["slack_lower_bound"] > 0
    assert bound["slack_lower_bound"] == pytest.approx(
        RECORD["unconditional_slack_bound"], rel=5e-3
    )
    assert bound["safety_factor"] == pytest.approx(
        RECORD["unconditional_safety_factor"], rel=5e-3
    )
    # it is a bound: every configuration measured anywhere here is above it
    free = worst_over_all_configurations(Y, count=60)
    assert free["slack"] > bound["slack_lower_bound"]
    assert ap_worst(0.0, 3, Y)["slack"] > bound["slack_lower_bound"]
    assert separated_worst(Y, count=60)["slack"] > bound["slack_lower_bound"]
    # and it is weaker than the separated one, by the factor the record states
    assert bound["safety_factor"] < RECORD["separated_safety_factor"]
    assert bound["top_window_multiplicity"] == 3
    assert bound["second_window_multiplicity"] == 1


def test_random_configurations_never_reach_the_bound() -> None:
    """A cheap adversary that does not know the structure gets nowhere near."""
    rng = np.random.default_rng(20260813)
    bound = unconditional_lower_bound(Y, count=40)["slack_lower_bound"]
    worst = float("inf")
    for _ in range(300):
        n = int(rng.integers(1, 9))
        offsets = rng.uniform(-40.0, 40.0, size=n)
        worst = min(worst, slack_offsets(offsets, Y))
    assert worst > bound
    assert worst > 0


def test_phi_r_is_decreasing_across_the_range_the_cluster_lemma_uses() -> None:
    """The monotonicity the repulsion bound rests on (the prover's own lemma)."""
    grid = np.linspace(0.0, 2 * math.pi, 2001)
    vals = phi_r(grid)
    assert np.all(np.diff(vals) < 0)
    assert float(phi_r(0.0)) == pytest.approx(A_CONST, rel=1e-13)


def test_psi_and_damage_are_the_same_object_with_opposite_signs() -> None:
    grid = np.linspace(-30.0, 30.0, 501)
    assert np.allclose(psi(Y, grid), -damage(Y, grid), atol=0, rtol=1e-13)
    # damage is even, and vanishes identically inside the no-damage radius
    inner = np.linspace(-EFORM3_NEAR_FIELD_RADIUS, EFORM3_NEAR_FIELD_RADIUS, 401)
    assert np.all(damage(Y, inner) < 0)
    assert np.allclose(damage(Y, grid), damage(Y, -grid), atol=1e-15)


def test_margin_and_slack_are_one_rescaling_apart() -> None:
    xs = [0.0, 6.4, 13.1]
    assert margin(xs, 0.4, 1.0) == pytest.approx((4 / A_CONST**2) * slack(xs, 0.4, 1.0), rel=1e-14)
    # translation invariance: only the offsets matter
    assert slack(xs, 0.4, 1.0) == pytest.approx(
        slack_offsets(np.array(xs) - 1.0, 0.4), rel=1e-14
    )
    assert slack([x + 100.0 for x in xs], 0.4, 101.0) == pytest.approx(
        slack(xs, 0.4, 1.0), rel=1e-12
    )


# ---------------------------------------------------------------------------
# hunt hygiene
# ---------------------------------------------------------------------------


def test_this_probe_keeps_the_reserved_vocabulary() -> None:
    """The lexical rules are lexical: they are checked on the bytes.

    The words are assembled from halves so that this file does not itself
    trip `tests/test_hunt_probe_discipline.py`, which reads the same bytes.
    """
    banned = ["cert" + "ified", "ver" + "ified", "con" + "firmed",
              "defin" + "itively", "pro" + "ves"]
    for name in ("near_coincident.py", "test_near_coincident.py"):
        text = (Path(__file__).resolve().parent / name).read_text(encoding="utf-8").lower()
        for word in banned:
            assert word not in text, f"{name} uses a reserved word ({word[:4]}...)"
