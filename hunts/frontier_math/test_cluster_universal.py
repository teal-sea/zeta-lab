"""Controls for cluster_universal.py, the cluster-decomposition attack.

What a reader must be able to check without rerunning the long map:

(a) the T-decay constant is DERIVED and the measured cross-terms sit
    under it with margin, at several separations and depths;
(b) the separation lemma holds one-sidedly on random multi-cluster
    configurations at two separations, with the exact budget cross-term
    inside its derived bound on every draw;
(c) the Poisson closed form for the lattice budget reproduces direct
    summation to within the derived truncation tail, and the depth-free
    dense-regime floor is what the closed form says it is;
(d) the periodic limit against finite-m ladders at three (s, y) points
    including the binding family (2.05 mean gaps, y = 0.49), every rung
    closes, and the finite-size direction flags are pinned (they differ
    by spacing: that non-uniformity is a finding, not a tolerance);
(e) the recorded sup of the rho map reproduces at its recorded step, and
    the resonance peaks stay below 1;
(f) jitter direction: position noise on the resonant lattice raises the
    margin (coherent = worst);
(g) theta = 1 diverges on clusters, finite and periodic;
(h) the coordinator's pre-refutation of the global-density rescue
    reproduces in one measurement.

Everything runs on the coarse conservative instrument (step 0.005,
G = 60) except where the record being checked was taken at a finer step.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cluster_universal import (  # noqa: E402
    A, C2_EDGE_SLOPE, EXTREMALITY_CONJECTURE, LEGAL_PAIR_DENSITY, MEAN_GAP,
    RHO_SUP_RECORD, THETA_FULL, autocorr_d1, autocorr_d2,
    autocorr_deriv_defect, b_infty, b_perpair_direct, cross_budget_bound,
    field_decay_check, finite_m_ladder, jitter_campaign,
    legal_density_prerefutation, periodic_cap, poisson_defect,
    random_separated_config, rho_point, separation_campaign,
    separation_record, t_decay_check, t_decay_constant,
)
from paper_joint import PaperJoint  # noqa: E402

#: one shared coarse instrument so band caches are reused across tests
PJ = PaperJoint(step=0.005, G=60.0)


# ---------------------------------------------------------------------------
# (a) the derived T-decay constant
# ---------------------------------------------------------------------------


def test_c2_derivative_closed_forms():
    """The IBP inputs: closed-form c2', c2'' against central differences,
    and the two boundary slopes (corner at 0, edge at 1) agree in
    magnitude with the closed form (1 + cos sqrt2)/2."""
    d = autocorr_deriv_defect()
    assert d["d1"] < 1e-8
    assert d["d2"] < 1e-5
    assert abs(float(autocorr_d1(np.array([1e-9]))[0])
               + C2_EDGE_SLOPE) < 1e-6
    assert abs(float(autocorr_d1(np.array([1 - 1e-9]))[0])
               + C2_EDGE_SLOPE) < 1e-6
    # oddness / evenness
    assert float(autocorr_d1(np.array([-0.3]))[0]) \
        == -float(autocorr_d1(np.array([0.3]))[0])
    assert float(autocorr_d2(np.array([-0.3]))[0]) \
        == float(autocorr_d2(np.array([0.3]))[0])


def test_t_decay_bound_holds_with_margin():
    """|T(dt, y1, y2)| <= C_T / dt^2 with the DERIVED constant, measured
    at several separations and depth combinations.  The worst quotient
    must stay clearly below 1, the constant is a majorant, not a fit."""
    rec = t_decay_check()
    assert rec["holds"]
    assert rec["worst_quotient"] < 0.75, rec
    assert abs(rec["C_T"] - 27.497) < 0.01
    # and the constant is depth-uniform: a deep-deep pair at a moderate
    # separation still sits under it
    from paper_chain import PaperChain
    assert abs(PaperChain().T(6.0, 0.4999, 0.4999)) * 36 < rec["C_T"]


def test_field_decay_bound_holds():
    """The cross-field law the separation lemma leans on: one pair's
    positive damage part beyond g decays like the derived 1/g^2 tail."""
    rec = field_decay_check()
    assert rec["holds"]
    assert rec["worst_quotient"] < 1.0


# ---------------------------------------------------------------------------
# (b) the separation lemma
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("delta_gaps,seed", [(3.0, 5), (6.0, 6)])
def test_separation_lemma_on_random_multicluster_configs(delta_gaps, seed):
    """>= 10 random multi-cluster configurations per separation (>= 20
    across the two parametrizations): the one-sided inequality

        margin(whole) >= sum_cl margin(cl) - eps_T(Delta) - eps_cap

    holds on every draw, the exact budget cross-term sits inside its
    derived bound on every draw, and on these campaigns the derived
    budget epsilon alone sufficed (the measured cap term never bit)."""
    rec = separation_campaign(n_configs=10, delta_gaps=delta_gaps,
                              seed=seed, pj=PJ)
    assert rec["all_budget_cross_contained"]
    assert rec["all_one_sided"]
    assert rec["all_with_derived_eps_only"]


def test_cross_budget_bound_tightens_with_separation():
    """The derived cross bound scales like 1/Delta^2: the same two
    clusters pushed twice as far apart get a four-fold smaller bound,
    and the exact cross term stays inside at both distances."""
    rng = np.random.default_rng(11)
    near = random_separated_config(rng, 3.0, max_clusters=2)
    far = [near[0], [(t + 3.0 * MEAN_GAP, y) for t, y in near[1]]]
    b_near = cross_budget_bound(near)
    b_far = cross_budget_bound(far)
    assert b_near["contained"] and b_far["contained"]
    assert b_far["bound"] < b_near["bound"]


def test_separation_record_shape_on_a_named_config():
    """One deterministic three-cluster configuration, so the lemma's
    bookkeeping (cross-pair count, margins) is pinned to exact values."""
    clusters = [[(0.0, 0.49), (2.0, 0.3)],
                [(30.0, 0.49)],
                [(70.0, 0.2), (72.0, 0.4), (73.0, 0.1)]]
    rec = separation_record(clusters, THETA_FULL, PJ)
    assert rec["k"] == 6 and rec["n_clusters"] == 3
    assert rec["n_cross"] == 2 * 1 + 2 * 3 + 1 * 3
    assert rec["one_sided_holds"]
    assert rec["budget_cross_contained"]


# ---------------------------------------------------------------------------
# (c) the Poisson closed form
# ---------------------------------------------------------------------------


def test_poisson_budget_matches_direct_summation():
    """The closed form against 4000-term direct T-summation, inside the
    derived truncation tail, at dense, resonant and sparse spacings."""
    for x, y in ((0.5, 0.49), (1.0, 0.1), (2.005, 0.49), (3.0, 0.3)):
        rec = poisson_defect(x * MEAN_GAP, y)
        assert rec["within"], (x, y, rec)


def test_dense_regime_budget_is_depth_free_with_floor_at_one_gap():
    """For s <= one mean gap only the k = 0 Bragg term survives:
    b_inf = 4 c2(0)/(A^2 x) - 4, independent of depth, floor at x = 1."""
    c20 = 0.5 + math.sin(math.sqrt(2.0)) / (2 * math.sqrt(2.0))
    for x in (0.3, 0.7, 1.0):
        want = 4 * c20 / (A * A * x) - 4
        assert abs(b_infty(x * MEAN_GAP, 0.1) - want) < 1e-12
        assert b_infty(x * MEAN_GAP, 0.1) == b_infty(x * MEAN_GAP, 0.49)
    assert abs(b_infty(MEAN_GAP, 0.3) - 0.024509) < 1e-5
    # the coincident blowup: budget wins hugely as s -> 0
    assert b_infty(0.1 * MEAN_GAP, 0.49) > 30.0


def test_lattice_budget_is_positive_over_the_probe_range():
    """No spacing/depth on the probe grid drives the per-pair budget
    through zero, the E-form's -4k never wins on the lattice family."""
    for x in np.arange(0.3, 6.05, 0.05):
        for y in (0.1, 0.3, 0.49):
            assert b_infty(float(x) * MEAN_GAP, y) > 0.0, (x, y)


# ---------------------------------------------------------------------------
# (d) periodic limit vs finite-m ladders
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("s_gaps,y,expect_up", [
    (2.05, 0.49, True),    # the binding family: edges worse, margin rises
    (2.0, 0.49, False),    # the resonance: interior worse, margin falls
    (1.5, 0.3, True),      # shielded lattice: margin rises toward limit
])
def test_finite_m_ladder_closes_and_direction_is_as_recorded(
        s_gaps, y, expect_up):
    """m = 4, 8, 16, 32 all close, and the finite-size direction is the
    recorded one: UP at the binding family and the shielded lattice,
    DOWN at the resonance.  The non-uniform sign is the honest negative:
    the periodic limit does not one-sidedly dominate finite clusters."""
    rec = finite_m_ladder(s_gaps, y, ms=(4, 8, 16, 32), pj=PJ)
    assert rec["all_close"], rec
    assert rec["monotone_up"] == expect_up, rec
    assert rec["monotone_down"] == (not expect_up), rec
    # the limit itself closes
    assert rec["limit_margin"] > 0.0


def test_periodic_cap_is_shielded_dense_and_resonant_sparse():
    """The two regimes the map found: total shielding (cap exactly 0)
    off resonance, a positive cap on resonance, both below budget."""
    shielded = rho_point(1.5, 0.49, step=0.004)
    assert shielded["cap"] == 0.0 and shielded["rho"] == 0.0
    resonant = rho_point(2.0, 0.49, step=0.004)
    assert resonant["cap"] > 0.0
    assert 0.0 < resonant["rho"] < 1.0
    assert resonant["complete"]


# ---------------------------------------------------------------------------
# (e) the recorded supremum
# ---------------------------------------------------------------------------


def test_rho_sup_record_reproduces_and_stays_below_one():
    """The map's argmax at its recorded step, and the refinement
    direction (rho falls as the step shrinks, so the recorded number is
    the conservative end of its own ladder)."""
    r = rho_point(RHO_SUP_RECORD["s_gaps"], RHO_SUP_RECORD["y"],
                  step=RHO_SUP_RECORD["step"])
    assert abs(r["rho"] - RHO_SUP_RECORD["rho"]) < 5e-3, r
    assert r["rho"] < 1.0
    coarse = rho_point(RHO_SUP_RECORD["s_gaps"], RHO_SUP_RECORD["y"],
                       step=0.004)
    assert coarse["rho"] > r["rho"], "refinement must move rho down"
    assert coarse["rho"] < 1.0


def test_resonance_peaks_decay_with_spacing():
    """rho at the integer resonances falls with s (toward the isolated
    ratio), so the s = 2 resonance is the family's worst."""
    r2 = rho_point(2.0, 0.49, step=0.004)["rho"]
    r3 = rho_point(3.0, 0.49, step=0.004)["rho"]
    r4 = rho_point(4.0, 0.49, step=0.004)["rho"]
    assert r2 > r3 > r4
    assert r2 < 1.0


# ---------------------------------------------------------------------------
# (f) jitter direction
# ---------------------------------------------------------------------------


def test_jitter_raises_the_margin_at_the_resonance():
    """Coherent = worst: position noise on the resonant lattice raises
    the relative margin monotonically in the amplitude, at every seed
    drawn (min, not only mean)."""
    rec = jitter_campaign(amps=(0.0, 0.3, 1.2), n_seeds=3, pj=PJ)
    assert rec["jitter_helps_on_average"]
    mins = [r["min_rel_margin"] for r in rec["rows"]]
    assert mins[1] > mins[0] and mins[2] > mins[1]


# ---------------------------------------------------------------------------
# (g) theta = 1
# ---------------------------------------------------------------------------


def test_theta_one_diverges_on_clusters_finite_and_periodic():
    """No charge, unbounded stack: the cap must report infinity on a
    finite cluster and on the periodic instrument alike."""
    assert PJ.cap([(0.0, 0.49)] * 3, 1.0)["cap"] == math.inf
    assert periodic_cap(2.0 * MEAN_GAP, 0.49, 1.0,
                        step=0.004)["cap"] == math.inf


# ---------------------------------------------------------------------------
# (h) the pre-refutation, reproduced once
# ---------------------------------------------------------------------------


def test_legal_density_window_cannot_rescue_per_pair_accounting():
    """The coordinator's pre-refutation in one measurement: a legal-
    density window holding one k = 8 nu = 1 cluster leaves per-pair
    accounting broken by two orders of magnitude, the pair-free credit
    rate is ~3e-5 per mean gap against an O(0.3) cluster deficit."""
    rec = legal_density_prerefutation()
    assert rec["still_broken"]
    assert rec["deficit"] > 0.2
    assert rec["credit_rate_per_gap"] < 1e-4
    assert rec["shortfall_factor"] > 100


def test_the_extremality_statement_is_labelled_a_conjecture():
    """The module's strongest structural claim must carry its grade in
    the artifact itself."""
    assert "conjecture" in EXTREMALITY_CONJECTURE
    assert 0.0 < LEGAL_PAIR_DENSITY < 0.5
    assert t_decay_constant() > 0
    assert b_perpair_direct(2 * MEAN_GAP, 0.49) > 0
