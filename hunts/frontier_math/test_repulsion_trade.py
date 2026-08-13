"""Controls for the repulsion trade.

The five the brief names, in order:

  (a) the gap identity reproduces the independent (quadrature) evaluators to
      1e-10 on mixed configurations -- ``test_gap_identity_*``;
  (b) the coincident-point limit: two on-line points at gap `g -> 0` give
      `R -> 2` with finite damage, so the trade must hold with room --
      ``test_coincident_pair_*``;
  (c) consistency with EForm3's `d >= 4` result -- ``test_delta_four_*``;
  (d) a planted violation (inflated damage) is detected -- ``test_planted_*``;
  (e) `theta = 1` diverges where it must -- ``test_theta_one_*``.

Plus the measurements the trade rests on: the damage-window geometry (S1)-(S5),
the marginal ratio, the extremal search and its refinement ladder, and the
four configuration families the sharpest statement is tested on.

Nothing here is a theorem and nothing here is evidence for or against RH.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from repulsion_trade import (  # noqa: E402
    A_CONST, A_SQ, C_EFORM3, NAMED_GAPS, PINNED, SHARPEST_STATEMENT, THETA_EFORM3,
    adversarial_search, budget, c2, cluster_embedded_scan, critical_c, damage,
    damage_total, damage_windows, energy_F, energy_FP, energy_quad,
    eform3_crosscheck, extremal_multiplicities, gap_identity_residual,
    gap_profile, ghat,
    lattice_scan, local_position_refinement, marginal_trade, phi_R, qim, qre,
    random_scan, relief_coefficient, repulsion_R, repulsion_raw,
    resolution_ladder, retention_margin, separable_worst_excess, shq,
    theta_one_counterexample, trade_slack, window_geometry,
    worst_marginal_ratio,
)

#: the six mixed configurations control (a) is run on.
MIXED_CONFIGS = (
    ([], 0.5, 0.0),                                    # empty
    ([0.0], 0.5, 0.0),                                 # one point
    ([0.0, 6.517], 0.5, 0.0),                          # a separated pair
    ([1.25, 1.25 + 1e-6, 1.25 + 2e-6], 0.37, 0.4),     # a near-coincident triple
    ([-8.0, -2.5, 0.0, 3.1, 9.4, 15.0], 0.5, 1.7),     # a spread six
    ([6.517] * 8, 0.5, 0.0),                           # eight coincident
    ([0.0, 0.31, 0.62, 6.9, 7.1, 13.4], 0.11, -2.2),   # mixed cluster + spread
    (list(np.arange(12) * 2.002), 0.4999, 5.0),        # a commensurate lattice
)

_GEO_KW = dict(s_max=200.0, step=5e-4)


# ---------------------------------------------------------------------------
# the functions themselves
# ---------------------------------------------------------------------------

def test_constants_match_the_eform3_arm() -> None:
    assert A_CONST == pytest.approx(PINNED["A"], abs=1e-13)
    assert A_CONST == pytest.approx(math.sqrt(2.0) * math.sin(1 / math.sqrt(2)), abs=1e-14)
    assert A_SQ == pytest.approx(PINNED["A_sq"], abs=1e-13)
    assert float(np.real(ghat(-1j))) == pytest.approx(PINNED["ghat_1"], abs=1e-12)
    assert shq(0.5) / 2 == pytest.approx(PINNED["shq_half_at_half"], abs=1e-12)


def test_qre_qim_agree_with_direct_quadrature() -> None:
    """`Qre`/`Qim` are `Re`/`Im` of `ghat(s - i y)`; check against the integral."""
    nodes, weights = np.polynomial.legendre.leggauss(200)
    u = 0.5 * nodes
    w = 0.5 * weights
    g = np.cos(math.sqrt(2.0) * u)
    for y, s in ((0.5, 6.517), (0.31, -2.4), (0.0, 3.3), (0.5, 0.0), (0.17, 41.9)):
        assert float(qre(y, s)) == pytest.approx(
            float(np.sum(w * g * np.cosh(y * u) * np.cos(s * u))), abs=1e-13)
        assert float(qim(y, s)) == pytest.approx(
            float(np.sum(w * g * np.sinh(y * u) * np.sin(s * u))), abs=1e-13)


def test_c2_is_the_autocorrelation_and_integrates_to_A_squared() -> None:
    nodes, weights = np.polynomial.legendre.leggauss(400)
    total = 0.0
    for lo, hi in ((-1.0, 0.0), (0.0, 1.0)):
        mid, half = 0.5 * (lo + hi), 0.5 * (hi - lo)
        total += half * float(np.sum(weights * c2(mid + half * nodes)))
    assert total == pytest.approx(A_SQ, abs=1e-13)
    assert float(c2(1.0)) == 0.0
    assert float(c2(1.5)) == 0.0
    assert float(c2(0.0)) == pytest.approx(0.5 + math.sin(math.sqrt(2.0)) / (2 * math.sqrt(2.0)),
                                           abs=1e-14)


def test_phi_R_is_ghat_and_peaks_at_A() -> None:
    assert float(phi_R(0.0)) == pytest.approx(A_CONST, abs=1e-14)
    s = np.linspace(0.0, 2 * math.pi, 400)
    v = phi_R(s)
    assert np.all(np.diff(v) < 1e-9), "phiR must be decreasing on [0, 2pi] -- (S4)"
    assert float(np.max(np.abs(v))) == pytest.approx(A_CONST, abs=1e-12)


# ---------------------------------------------------------------------------
# (a) the gap identity against the independent evaluators
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("x,y,t", MIXED_CONFIGS)
def test_gap_identity_reproduces_the_evaluators(x, y, t) -> None:
    """Control (a): closed forms vs the definition-route quadrature, 1e-10."""
    res = gap_identity_residual(x, y, t, order=500)
    assert res["energy_F_residual"] < 1e-10, res
    assert res["energy_FP_residual"] < 1e-10, res
    assert res["gap_identity_residual"] < 1e-12, res
    assert res["gap_identity_vs_quadrature"] < 1e-10, res


@pytest.mark.parametrize("x,y,t", MIXED_CONFIGS)
def test_retention_margin_is_four_over_A_squared_times_the_slack(x, y, t) -> None:
    """(RT) and the retention inequality are the same statement, rescaled."""
    lhs = retention_margin(x, y, t, THETA_EFORM3)
    rhs = (4.0 / A_SQ) * trade_slack(x, y, t, THETA_EFORM3)
    assert lhs == pytest.approx(rhs, rel=1e-11, abs=1e-13)


def test_repulsion_is_A_squared_times_energy_F_minus_n() -> None:
    for x, _y, _t in MIXED_CONFIGS:
        n = len(x)
        assert repulsion_raw(x) == pytest.approx(A_SQ * (energy_F(x) - n), abs=1e-11)
        assert repulsion_raw(x) >= -1e-12


def test_energy_FP_quadrature_route_is_not_the_closed_form_route() -> None:
    """The two evaluators must actually be independent: break one constant and
    only the closed-form side moves."""
    x, y, t = [0.0, 2.5, 7.7], 0.45, 0.9
    quad = energy_quad(lambda w: np.exp(1j * np.outer(np.asarray(x), w)).sum(axis=0), 400)
    assert quad == pytest.approx(energy_F(x), abs=1e-11)
    fp_quad = energy_quad(
        lambda w: (np.exp(1j * np.outer(np.asarray(x), w)).sum(axis=0)
                   + 2.0 * np.cosh(y * w) * np.exp(1j * t * w)), 400)
    assert fp_quad == pytest.approx(energy_FP(x, y, t), abs=1e-10)
    # a lesion in the closed form (wrong A) must show up as disagreement
    fake = (A_SQ * energy_F(x)) / (A_SQ * 1.01)
    assert abs(fake - quad) > 1e-4


# ---------------------------------------------------------------------------
# (b) the coincident-point limit
# ---------------------------------------------------------------------------

def test_coincident_pair_repulsion_tends_to_two() -> None:
    """Control (b): `R = Rraw/A^2 -> 2` as the gap closes, and finite damage."""
    y, s = 0.5, PINNED["peak_argmax"]
    prev = None
    for g in (1.0, 1e-1, 1e-2, 1e-3, 1e-4, 1e-6):
        x = [s, s + g]
        R = repulsion_R(x)
        assert R < 2.0 + 1e-12
        if prev is not None:
            assert R > prev - 1e-12, "R must increase as the pair closes"
        prev = R
    assert repulsion_R([s, s]) == pytest.approx(PINNED["coincident_pair_R"], abs=1e-12)
    assert repulsion_R([s, s + 1e-6]) == pytest.approx(2.0, abs=1e-10)


def test_coincident_pair_trade_holds_with_room() -> None:
    """The pair's damage is finite and the budget covers it many times over."""
    y, s = 0.5, PINNED["peak_argmax"]
    x = [s, s]
    d = damage_total(x, y)
    assert d == pytest.approx(2 * PINNED["peak_damage"], rel=1e-6)
    b = budget(x, y)
    assert b > d
    # base budget alone already covers a coincident pair, 3.8x over
    assert shq(y) / 2 / d > 3.5
    # and the repulsion adds 2 A^2 / 800 on top
    assert b - shq(y) / 2 == pytest.approx(2 * A_SQ * C_EFORM3, abs=1e-14)
    assert trade_slack(x, y) > 0.0
    assert retention_margin(x, y) > 0.0


def test_coincident_cluster_repulsion_is_quadratic() -> None:
    """`m` coincident points give `Rraw = m(m-1) A^2`: the quadratic growth the
    whole trade rests on."""
    s = PINNED["peak_argmax"]
    for m in (2, 3, 5, 8, 13):
        assert repulsion_raw([s] * m) == pytest.approx(m * (m - 1) * A_SQ, rel=1e-12)


# ---------------------------------------------------------------------------
# the geometry (S1)-(S5): why the trade can work at all
# ---------------------------------------------------------------------------

def test_damage_windows_sit_on_the_zeros_of_ghat() -> None:
    """(S2): the damage set is `Re(ghat(s-iy)^2) < 0`, i.e. windows around the
    real zeros of `ghat`, spacing `2 pi`."""
    wins = damage_windows(0.5, s_max=60.0, step=2e-4)
    assert len(wins) >= 8
    for w in wins:
        # a zero of phi_R inside every window
        assert float(phi_R(w.lo)) * float(phi_R(w.hi)) < 0.0
        assert float(damage(0.5, w.peak_s)) > 0.0
        assert float(damage(0.5, w.lo - 1e-3)) <= 0.0
        assert float(damage(0.5, w.hi + 1e-3)) <= 0.0
    spacing = np.diff([w.peak_s for w in wins])
    assert np.all(np.abs(spacing - 2 * math.pi) < 0.2)


def test_window_geometry_matches_the_far_field_exchange_record() -> None:
    """The numbers `FAR-FIELD-EXCHANGE.md` §3 records, re-measured here."""
    g = window_geometry(0.5, **_GEO_KW)
    assert g.peak_max == pytest.approx(PINNED["peak_damage"], rel=1e-6)
    assert g.peak_argmax == pytest.approx(PINNED["peak_argmax"], abs=1e-3)
    assert g.no_damage_radius == pytest.approx(PINNED["no_damage_radius"], abs=1e-6)
    assert g.shq_half == pytest.approx(PINNED["shq_half_at_half"], abs=1e-12)
    # the six leading peaks
    for got, want in zip(g.peaks, (4.396e-3, 9.751e-4, 4.233e-4, 2.361e-4,
                                   1.505e-4, 1.043e-4)):
        assert got == pytest.approx(want, rel=2e-3)
    assert g.one_side_total == pytest.approx(PINNED["one_side_peak_sum"], rel=5e-3)
    assert g.separated_ratio == pytest.approx(PINNED["separated_ratio"], rel=5e-3)


def test_the_structural_dichotomy_two_damaging_points_are_close_or_far() -> None:
    """(S3)+(S4): the fact that makes the trade work.  Two points that both
    damage are either inside one window -- gap <= W, so `phiR(gap)^2` is near
    its maximum -- or more than 5.18 apart.  There is no clustered
    configuration with damage and without repulsion."""
    for y in (0.5, 0.4, 0.25, 0.1):
        g = window_geometry(y, **_GEO_KW)
        assert g.max_window_width < 2 * y + 1e-3, "window half-width ~ y"
        # windows sit on the zeros of ghat, whose spacing rises to 2 pi from
        # below (6.1122 between the first two), so the separation is
        # `min zero spacing - W(y)`, not `2 pi - W(y)`.
        spacing = np.diff(np.asarray(g.peak_positions))
        assert float(spacing.min()) > 6.11
        assert float(spacing.max()) < 2 * math.pi + 1e-6
        # peaks are not exactly window centres, so this is the shape of the
        # relation rather than an identity; 0.05 absorbs the offset.
        assert g.min_window_gap >= float(spacing.min()) - g.max_window_width - 0.05
        assert g.min_window_gap > 5.1
        assert g.phi_floor > 0.78
        assert g.phi_floor <= A_SQ
    g = window_geometry(0.5, **_GEO_KW)
    assert g.max_window_width == pytest.approx(PINNED["max_window_width"], rel=1e-3)
    assert g.min_window_gap == pytest.approx(PINNED["min_window_gap"], rel=1e-3)
    assert g.phi_floor == pytest.approx(PINNED["phi_floor"], rel=1e-4)


def test_peak_sequence_decays_like_k_squared() -> None:
    """(S5): `p_k k^2` is measured decreasing, which is what bounds the tail."""
    g = window_geometry(0.5, **_GEO_KW)
    scaled = np.asarray(g.peaks) * (np.arange(1, len(g.peaks) + 1) ** 2)
    assert np.all(np.diff(scaled) < 1e-9)
    assert float(scaled[0]) == pytest.approx(PINNED["peak_damage"], rel=1e-6)
    assert g.tail_bound < 1e-3


# ---------------------------------------------------------------------------
# the marginal trade: measured, and it fails -- which is not the question
# ---------------------------------------------------------------------------

def test_marginal_ratio_for_a_pair_exceeds_one_at_every_gap() -> None:
    """A pair never pays for itself out of its own repulsion: the extra damage
    can be the full peak while the relief is at most `2 A^2/800`."""
    ratio_bound = PINNED["peak_damage"] / (2 * A_SQ * C_EFORM3)
    assert ratio_bound > 2.0
    w = worst_marginal_ratio(0.5, 2, gaps=np.arange(0.05, 4.0001, 0.05))
    assert w.ratio == pytest.approx(PINNED["worst_marginal_ratio_pair"], rel=1e-3)
    assert w.gap == pytest.approx(4.0, abs=1e-9), "worst at the widest gap scanned"
    assert w.ratio > 1.0
    # and the coincident pair, the best case for the trade, still exceeds 1
    tight = marginal_trade(0.5, 2, 1e-6, PINNED["peak_argmax"])
    assert 2.0 < tight.ratio < 2.2


def test_marginal_ratio_crosses_one_between_four_and_five() -> None:
    """Coincident clusters: the ratio is `~4.167/m`, so the cluster starts
    paying for itself at m = 5.  Below that the base budget carries it."""
    s = PINNED["peak_argmax"]
    ratios = {}
    for m in (2, 3, 4, 5, 6, 8):
        mt = marginal_trade(0.5, m, 1e-7, s)
        ratios[m] = mt.ratio
        assert mt.extra_relief == pytest.approx(C_EFORM3 * m * (m - 1) * A_SQ, rel=1e-6)
    assert ratios[4] > 1.0 > ratios[5]
    assert ratios[2] == pytest.approx(4.1668 / 2, rel=2e-3)
    assert ratios[8] == pytest.approx(4.1668 / 8, rel=2e-3)


def test_marginal_ratio_is_worst_at_y_one_half() -> None:
    """Damage and `Shq` both scale like `y^2`; `Rraw` does not, so small `y`
    only makes the trade easier."""
    prev = math.inf
    for y in (0.5, 0.4, 0.3, 0.2, 0.1):
        w = worst_marginal_ratio(y, 3, gaps=np.arange(0.05, 4.0001, 0.1))
        assert w.ratio < prev
        prev = w.ratio


# ---------------------------------------------------------------------------
# the global trade -- the decisive measurement
# ---------------------------------------------------------------------------

def test_extremal_configuration_needs_less_relief_than_is_available() -> None:
    """The headline: the worst configuration found needs `c = 4.75e-4` and
    `theta = 199/200` supplies `1/800 = 1.25e-3`."""
    cfg = extremal_multiplicities(0.5, n_windows=12, m_max=16, **_GEO_KW)
    assert cfg.critical_c > 0.0
    assert cfg.critical_c < C_EFORM3
    assert cfg.critical_c == pytest.approx(4.7496e-4, rel=5e-3)
    assert cfg.margin_factor > 2.5
    assert cfg.theta_supported > THETA_EFORM3
    assert cfg.theta_supported == pytest.approx(PINNED["theta_supported"], abs=2e-5)
    assert cfg.multiplicities[:6] == (6, 2, 1, 1, 1, 1)
    assert cfg.slack > 0.0
    assert cfg.damage_over_budget < 1.0


def test_extremal_c_is_stable_up_the_refinement_ladder() -> None:
    """MISSION.md's precision-response rule: four knobs, and the value moves by
    under 3% while the multiplicity profile does not move at all."""
    ladder = resolution_ladder(0.5, rungs=((6, 12, 100.0, 5e-4),
                                           (12, 16, 200.0, 5e-4),
                                           (24, 24, 400.0, 2e-4)))
    cs = [r["critical_c"] for r in ladder]
    assert all(c < C_EFORM3 for c in cs)
    assert max(cs) - min(cs) < 0.03 * max(cs)
    assert all(r["profile"] == (6, 2, 1, 1, 1, 1) for r in ladder)
    # refinement lowers it: more resolved windows means more repulsion credit
    assert cs == sorted(cs, reverse=True)


def test_peak_coincident_ansatz_is_not_beaten_by_local_moves() -> None:
    """The extremal search assumes clusters sit coincident on the peaks.
    Random position moves off that ansatz do not improve `critical_c`."""
    cfg = extremal_multiplicities(0.5, n_windows=12, m_max=16, **_GEO_KW)
    for scale in (0.4, 0.1, 0.02):
        r = local_position_refinement(cfg, trials=150, scale=scale)
        assert not r["improved"], r


def test_separable_bound_is_the_shape_a_prover_would_carry() -> None:
    """Discard every cross-window pair, charge within-cluster pairs only the
    window-width floor, maximise each window independently: still under the
    budget, with a 1.72x margin."""
    sep = separable_worst_excess(0.5, **_GEO_KW)
    assert sep["slack"] > 0.0
    assert sep["margin_factor"] > 1.7
    assert sep["worst_both_sides"] == pytest.approx(1.9592e-2, rel=5e-3)
    assert sep["multiplicity_profile"][0] == 3
    assert all(m == 1 for m in sep["multiplicity_profile"][1:])
    # the bound is on `damage - c*Rraw`, since it discards every cross-window
    # pair; the structured search maximising exactly that must respect it.
    cfg = extremal_multiplicities(0.5, n_windows=12, m_max=16,
                                  objective="excess", **_GEO_KW)
    reduced = cfg.damage_total - C_EFORM3 * cfg.repulsion_raw
    assert reduced <= sep["worst_both_sides"] + 1e-9
    assert reduced < sep["shq_half"], "which is exactly (RT)"
    assert sep["shq_half"] / reduced > 1.8


def test_critical_c_falls_with_y() -> None:
    prev = math.inf
    for y in (0.5, 0.4, 0.3, 0.2):
        cfg = extremal_multiplicities(y, n_windows=8, m_max=12, **_GEO_KW)
        assert cfg.critical_c < prev
        assert cfg.critical_c < C_EFORM3
        prev = cfg.critical_c


# ---------------------------------------------------------------------------
# (c) consistency with EForm3's d >= 4 theorem
# ---------------------------------------------------------------------------

def _separated(x, d=4.0) -> bool:
    xs = np.sort(np.asarray(x, dtype=float))
    return xs.size < 2 or bool(np.all(np.diff(xs) >= d - 1e-12))


def test_delta_four_configurations_need_no_repulsion_at_all() -> None:
    """Control (c): on 4-separated configurations the bare budget already
    suffices, which is `Retention.retention_of_damage`'s hypothesis -- so (RT)
    holds there a fortiori and agrees with `retention_separated_of_le`."""
    rng = np.random.default_rng(11)
    worst = -math.inf
    for _ in range(400):
        n = int(rng.integers(1, 25))
        gaps = 4.0 + rng.exponential(3.0, size=n - 1) if n > 1 else np.zeros(0)
        x = np.concatenate([[0.0], np.cumsum(gaps)]) - 20.0
        for y in (0.5, 0.31, 0.12):
            t = float(rng.uniform(-30.0, 30.0))
            assert _separated(x)
            d = damage_total(x, y, t)
            assert d <= shq(y) / 2, (x, y, t)          # EForm3's hypothesis
            assert trade_slack(x, y, t) > 0.0          # (RT), a fortiori
            assert retention_margin(x, y, t) > 0.0     # the retention inequality
            worst = max(worst, d / (shq(y) / 2))
    assert worst < 1.0
    assert worst > 0.05, "the separated family must actually reach some damage"


def test_delta_four_worst_case_is_the_sum_of_peaks() -> None:
    """The `d >= 4` extremal configuration -- one point in every damage window,
    which is 4-separated because windows are 5.18 apart -- lands at 40.7% of
    the bare budget, the 2.46x margin `FAR-FIELD-EXCHANGE.md` §3 records."""
    g = window_geometry(0.5, **_GEO_KW)
    peaks = np.asarray(g.peak_positions)
    x = np.concatenate([peaks, -peaks])
    assert _separated(x)
    d = damage_total(x, 0.5, 0.0)
    assert d == pytest.approx(2 * sum(g.peaks), rel=1e-9)
    assert d / (shq(0.5) / 2) == pytest.approx(0.3995, rel=5e-3)
    assert g.separated_ratio == pytest.approx(0.4064, rel=5e-3)   # + the tail
    assert trade_slack(x, 0.5) > 0.0


def test_crosscheck_against_the_lean_arm_and_the_far_field_record() -> None:
    """Control (c), second half: the measurement must sit inside the two
    conservative bounds `EForm3/Estimates.lean` and `EForm3/Counting.lean`
    carry, and must reproduce `FAR-FIELD-EXCHANGE.md` §3."""
    cc = eform3_crosscheck(0.5, **_GEO_KW)
    assert cc["shq_half_respects_lean_floor"]
    assert cc["separated_respects_lean_cap"]
    # the Lean route's margin is 1.058x; the measured truth is 2.46x
    assert cc["lean_margin"] == pytest.approx(1.0575, rel=1e-3)
    assert cc["measured_margin"] == pytest.approx(2.4606, rel=5e-3)
    assert cc["far_field_budget_fraction"] == pytest.approx(0.4064, rel=5e-3)
    assert cc["far_field_peak"] == pytest.approx(4.39642e-3, rel=1e-5)
    assert cc["far_field_peak_s"] == pytest.approx(6.51700, abs=1e-3)
    assert cc["far_field_R0"] == pytest.approx(6.0653187731, abs=1e-6)
    assert cc["far_field_one_side_total"] == pytest.approx(6.8591e-3, rel=5e-3)


def test_the_statement_strictly_contains_the_eform3_hypothesis() -> None:
    """(RT) with the repulsion term deleted *is* `retention_of_damage`; keeping
    it is a strictly weaker hypothesis, so nothing is lost."""
    for x, y, t in MIXED_CONFIGS:
        bare = shq(y) / 2
        assert budget(x, y) >= bare - 1e-15
        if len(x) > 1:
            assert budget(x, y) > bare or repulsion_raw(x) < 1e-12


# ---------------------------------------------------------------------------
# the four families the sharpest statement is tested on
# ---------------------------------------------------------------------------

def test_uniform_lattices_at_every_spacing() -> None:
    res = lattice_scan(spacings=np.round(np.arange(0.1, 8.0001, 0.1), 4),
                       sizes=(2, 3, 5, 8, 13, 21))
    assert res.n_configs > 3000
    assert res.violations == 0, (res.worst_config, res.worst_y, res.worst_t)
    assert res.worst_ratio < 1.0
    assert res.worst_c < C_EFORM3


def test_clusters_at_every_gap_in_zero_to_four() -> None:
    """The brief's family: clusters of 2..6 at gaps 0 < g < 4, embedded in a
    4-separated background that already carries the worst separated damage."""
    res = cluster_embedded_scan(0.5, gaps=np.round(np.arange(0.02, 4.0001, 0.02), 4))
    assert res.n_configs >= 1000
    assert res.violations == 0
    assert res.worst_ratio < 1.0


def test_gap_profile_has_no_bad_g() -> None:
    """The decisive per-gap read: at no gap in (0,4) does the cluster's damage
    outrun what the configuration's budget can pay."""
    rows = gap_profile(0.5, gaps=np.arange(0.05, 4.0001, 0.05))
    assert rows
    for r in rows:
        assert r["slack"] > 0.0, r
        assert r["ratio"] < 1.0, r
    worst = max(rows, key=lambda r: r["ratio"])
    assert worst["ratio"] < 0.75
    # the marginal ratio is a different question and does exceed 1
    assert max(r["marginal_ratio"] for r in rows) > 1.0


def test_randomised_configurations() -> None:
    res = random_scan(n=2000)
    assert res.n_configs == 2000
    assert res.violations == 0, (res.worst_config, res.worst_y, res.worst_t)
    assert res.worst_ratio < 1.0


def test_mixed_configurations_hold() -> None:
    for x, y, t in MIXED_CONFIGS:
        assert trade_slack(x, y, t) > 0.0, (x, y, t)


@pytest.mark.slow
def test_free_position_annealing_finds_no_violation() -> None:
    """No peak ansatz and no multiplicity ansatz: continuous positions, long
    jumps.  This is the control that could refute (RT)."""
    adv = adversarial_search(0.5, sizes=(2, 4, 8, 16, 32), restarts=4, steps=1500)
    assert not adv["violated"], adv["best_config"]
    assert adv["best_excess"] < -1.0e-2
    sep = separable_worst_excess(0.5, **_GEO_KW)
    assert adv["best_excess"] <= sep["worst_both_sides"] - sep["shq_half"] + 1e-9


@pytest.mark.slow
def test_full_lattice_and_random_scans() -> None:
    for res in (lattice_scan(), random_scan(n=4000, seed=4242)):
        assert res.violations == 0, res
        assert res.worst_ratio < 1.0


# ---------------------------------------------------------------------------
# (d) planted violations
# ---------------------------------------------------------------------------

def test_planted_damage_inflation_is_detected() -> None:
    """Control (d): the instrument is not vacuous.  Inflating the damage by a
    factor the trade cannot pay for must turn the slack negative."""
    cfg = extremal_multiplicities(0.5, n_windows=12, m_max=16, **_GEO_KW)
    x = list(cfg.positions)
    assert trade_slack(x, 0.5) > 0.0
    # the extremal configuration's headroom, as a damage multiplier
    honest = damage_total(x, 0.5)
    factor = budget(x, 0.5) / honest
    assert 1.0 < factor < 6.0
    assert trade_slack(x, 0.5, inflate=factor * 1.01) < 0.0
    assert trade_slack(x, 0.5, inflate=factor * 0.99) > 0.0
    # and on a simple coincident cluster
    s = PINNED["peak_argmax"]
    y = 0.5
    for m in (2, 5, 12):
        z = [s] * m
        f = budget(z, y) / damage_total(z, y)
        assert trade_slack(z, y, inflate=f * 1.05) < 0.0


def test_planted_wrong_relief_coefficient_is_detected() -> None:
    """A lesion in the constant that carries the trade: with the relief
    coefficient set to zero the clustered case must fail, and with it set ten
    times too large the instrument must stop distinguishing anything."""
    s = PINNED["peak_argmax"]
    x = [s] * 8
    assert trade_slack(x, 0.5, theta=THETA_EFORM3) > 0.0
    assert trade_slack(x, 0.5, theta=1.0) < 0.0                 # c = 0
    assert relief_coefficient(1.0) == 0.0
    assert relief_coefficient(THETA_EFORM3) == pytest.approx(C_EFORM3, rel=1e-15)
    # a ten-times-too-large coefficient would pass the planted lesion above
    huge = 1.0 - 40.0 * C_EFORM3
    assert trade_slack(x, 0.5, theta=huge, inflate=3.0) > 0.0


def test_planted_wrong_window_floor_breaks_the_separable_bound() -> None:
    """The separable bound's only free input is `gamma`.  Set it to a tenth of
    the measured floor and the bound must stop closing."""
    good = separable_worst_excess(0.5, **_GEO_KW)
    bad = separable_worst_excess(0.5, gamma=good["gamma"] / 10.0, **_GEO_KW)
    assert good["slack"] > 0.0
    assert bad["slack"] < 0.0
    assert bad["multiplicity_profile"][0] > good["multiplicity_profile"][0]


# ---------------------------------------------------------------------------
# (e) theta = 1
# ---------------------------------------------------------------------------

def test_theta_one_fails_on_eight_coincident_points() -> None:
    """Control (e): at `theta = 1` there is no relief coefficient, so (RT)
    reduces to `sum damage <= Shq/2` -- and eight coincident points at the
    damage peak break it.  This is what the repulsion term is for."""
    tc = theta_one_counterexample(0.5, s_max=60.0)
    assert tc["m"] == PINNED["theta_one_cluster"] == 8
    assert tc["damage_total"] > tc["shq_half"]
    assert tc["theta_one_slack"] < 0.0
    assert tc["retention_margin_theta_one"] < 0.0
    # seven does not break it
    seven = [tc["s"]] * 7
    assert trade_slack(seven, 0.5, theta=1.0) > 0.0
    # and theta = 199/200 pays for it 2.6x over
    assert tc["theta_eform3_slack"] > 0.0
    assert tc["retention_margin_theta_eform3"] > 0.0
    assert tc["repulsion_raw"] == pytest.approx(8 * 7 * A_SQ, rel=1e-12)
    ratio = tc["damage_total"] / (tc["shq_half"] + C_EFORM3 * tc["repulsion_raw"])
    assert ratio < 0.4


def test_theta_one_holds_on_separated_configurations() -> None:
    """The divergence is exactly the clustered case: `theta = 1` is fine for
    every 4-separated configuration, and fails only when points crowd."""
    g = window_geometry(0.5, **_GEO_KW)
    peaks = np.asarray(g.peak_positions)
    x = np.concatenate([peaks, -peaks])
    assert _separated(x)
    assert trade_slack(x, 0.5, theta=1.0) > 0.0
    # give every point a multiplicity and theta = 1 breaks; the multiplicity
    # is exactly what the repulsion term is paid for
    doubled = np.concatenate([x, x + 1e-6])
    assert trade_slack(doubled, 0.5, theta=1.0) > 0.0        # 2x is still under
    tripled = np.concatenate([x, x + 1e-6, x + 2e-6])
    assert damage_total(tripled, 0.5) > shq(0.5) / 2
    assert trade_slack(tripled, 0.5, theta=1.0) < 0.0
    assert trade_slack(tripled, 0.5, theta=THETA_EFORM3) > 0.0


# ---------------------------------------------------------------------------
# discipline
# ---------------------------------------------------------------------------

#: the reserved vocabulary, spelled in halves so this file does not itself
#: contain the bytes the repo-level lexical scan looks for.
_RESERVED = ("certi" + "fied", "veri" + "fied", "con" + "firmed",
             "defini" + "tively", "pro" + "ves")


def test_statement_and_gaps_are_present_and_hedged() -> None:
    assert "Shq(y) / 2" in SHARPEST_STATEMENT
    assert "1/800" in SHARPEST_STATEMENT
    assert len(NAMED_GAPS) >= 4
    joined = (SHARPEST_STATEMENT + " ".join(NAMED_GAPS)).lower()
    for word in _RESERVED:
        assert word not in joined, word


def test_no_reserved_vocabulary_in_the_module_sources() -> None:
    here = Path(__file__).resolve().parent
    for name in ("repulsion_trade.py", "test_repulsion_trade.py"):
        text = (here / name).read_text(encoding="utf-8").lower()
        for word in _RESERVED:
            assert word not in text, f"{name}: {word}"
