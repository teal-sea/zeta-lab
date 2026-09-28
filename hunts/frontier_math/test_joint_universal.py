"""Controls for joint_universal.py, the multi-pair quantifier.

The module's job is to say honestly how far the joint verdict extends
beyond `paper_joint.py`'s configuration sweep.  These controls pin the
five things a reader has to be able to check without rerunning a search:

(a) what the rung-1 domination inequality does on the swept families, and
    that it FAILS off them (coincident stacks);
(b) the slack-additivity relation, exactly, in both the LAW K + LAW L
    form and the autocorrelation form;
(c) the worst configuration the randomised search found is still inside
    budget, re-checked at the module's own resolution;
(d) theta = 1 diverges (no charge, unbounded stack);
(e) a planted inflation of one pair's damage opens a verdict that closes
    honestly, the detector has power.

Each cap evaluation costs a field pass over a 400-grid-unit halo, so the
configurations are built once at import and reused.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from joint_universal import (  # noqa: E402
    A, MEAN_GAP, THETA_FULL, InflatedJoint, JointUniversal, PaperChain,
    PaperJoint, WORST_RANDOM, WORST_RANDOM_RATIO_PAIRS, WORST_RANDOM_RECORD,
    autocorr, autocorr_defect,
    autocorr_mass, budget_terms, budget_via_autocorr, coincident_ratios,
    completion, completion_excess, completion_matches_module,
    completion_relaxed, damage_and_charge, even_split_defect,
    even_split_theta, pair_energy_matrix, per_pair_route_witness,
    planted_violation, verdict_fourier_gap, W_autocorr_defect,
)

JU = JointUniversal()
PC = PaperChain()

ISOLATED = [(0.0, 0.49)]
COINCIDENT2 = [(0.0, 0.49)] * 2
COINCIDENT3 = [(0.0, 0.49)] * 3
NU1_K3 = [(i * MEAN_GAP, 0.49) for i in range(3)]
DIPOLE = [(0.0, 0.49), (6.406, 0.49)]


# ---------------------------------------------------------------------------
# the kernel the whole restatement rests on
# ---------------------------------------------------------------------------


def test_autocorrelation_closed_form_and_mass():
    """c2 = phi^2 * phi^2 in closed form, its mass A^2, and its sign.

    Positivity is not a measurement here, both terms of the closed form
    have arguments inside the first quadrant, but a numerical floor is
    pinned anyway so that a future edit to the formula cannot quietly
    lose it.
    """
    assert autocorr_defect() < 1e-9
    assert abs(autocorr_mass() - A * A) < 1e-12
    ws = np.linspace(-0.9999, 0.9999, 20001)
    assert float(autocorr(ws).min()) > 0.0
    assert float(autocorr(np.array([1.0]))[0]) == 0.0
    assert float(autocorr(np.array([1.5]))[0]) == 0.0
    # c2(0) = int phi^4 = 1/2 + sin(sqrt2)/(2 sqrt2)
    want = 0.5 + math.sin(math.sqrt(2.0)) / (2 * math.sqrt(2.0))
    assert abs(float(autocorr(np.array([0.0]))[0]) - want) < 1e-14


def test_W_is_a_cosine_transform_of_a_nonnegative_measure():
    """LAW L's ingredient: W(g,y) = (2/A^2) int c2 cosh(yw) cos(gw) dw."""
    assert W_autocorr_defect() < 1e-9


# ---------------------------------------------------------------------------
# (b) the slack-additivity relation
# ---------------------------------------------------------------------------


def test_budget_is_summed_slack_plus_a_signed_pair_term():
    """**The relation, exactly.**  budget(P) = sum_i slack(y_i) +
    sum_{i != j} T_ij, reproducing ``PaperJoint.budget`` to float noise,
    and the pair term is signed, so "k pairs give k * slack" is false in
    both directions.
    """
    for pairs in (ISOLATED, COINCIDENT2, DIPOLE, NU1_K3):
        bt = budget_terms(pairs)
        assert abs(bt["budget"] - JU.pj.budget(pairs)) < 1e-9
        assert abs(bt["sum_slack"]
                   - sum(PC.slack(y) for _, y in pairs)) < 1e-12
    # coincidence pays, separation costs: both directions occur
    assert budget_terms(COINCIDENT2)["pair_term"] > 8.0
    assert budget_terms(DIPOLE)["pair_term"] < -0.08
    assert budget_terms(ISOLATED)["pair_term"] == 0.0


def test_budget_per_pair_split_is_exact_but_not_a_per_pair_bound():
    """b_i = slack_i + sum_{j != i} T_ij sums to the budget exactly; the
    individual shares are not bounded below by anything useful, which is
    why the pair term cannot be charged one pair at a time."""
    bt = budget_terms(NU1_K3)
    assert abs(sum(bt["per_pair"]) - bt["budget"]) < 1e-9
    lattice = [(i * MEAN_GAP, 0.49) for i in range(9)]
    inner = budget_terms(lattice)["per_pair"][4]
    assert inner < PC.slack(0.49), (
        "the interior pair of a nu=1 lattice must lose budget to its "
        f"neighbours; got {inner} against slack {PC.slack(0.49)}"
    )


def test_pair_energy_is_a_nonnegative_kernel_form():
    """sum_{i,j} T_ij >= 0 for every configuration, with diagonal
    T_ii = 4 + slack(y_i); hence budget = sum_{i,j} T_ij - 4k."""
    for pairs in (ISOLATED, COINCIDENT2, DIPOLE, NU1_K3):
        T = pair_energy_matrix(pairs)
        assert float(T.sum()) >= 0.0
        for i, (_, y) in enumerate(pairs):
            assert abs(T[i, i] - (4.0 + PC.slack(y))) < 1e-10
        bt = budget_terms(pairs)
        assert abs(bt["budget"] - (bt["pair_energy"] - 4 * len(pairs))) < 1e-9


def test_budget_autocorrelation_form():
    """budget(P) = (4/A^2) int c2(w) [ |S_P(w)|^2 - k ] dw, quadrature
    grade.  Only the -k is negative, which is the form in which "the
    budget never goes through zero" would have to be shown."""
    for pairs in (ISOLATED, DIPOLE, NU1_K3):
        bt = budget_terms(pairs)
        assert abs(budget_via_autocorr(pairs) - bt["budget"]) < 1e-8


def test_the_whole_verdict_restates_in_one_variable():
    """budget - [D - (1-theta) R] = E[F_on+F_p] - theta E[F_on]
    - (1-theta) n - 4k, exactly, for on-line multisets and pair sets."""
    cases = [([0.3, 1.7, 5.0], [(0.9, 0.25)]),
             ([0.0, 0.77, 2.1, 2.1], [(0.4, 0.45), (1.6, 0.1)]),
             ([], [(0.0, 0.49), (MEAN_GAP, 0.3)])]
    for online, pairs in cases:
        for theta in (THETA_FULL, 0.5):
            rec = verdict_fourier_gap(online, pairs, theta)
            assert rec["defect"] < 1e-7, (online, pairs, theta, rec)


def test_damage_and_charge_signs():
    """D is the damage the on-line multiset collects and R >= 0 is the
    internal charge; a repeated ordinate stacks charge."""
    rec1 = damage_and_charge([0.0], [(0.0, 0.49)])
    assert rec1["R"] == 0.0
    rec2 = damage_and_charge([0.0, 0.0], [(0.0, 0.49)])
    assert rec2["R"] > 1.9  # two coincident on-line zeros: 2 * omega^2(0)
    assert rec2["D"] < 0    # sitting on the pair is protective, not damaging


# ---------------------------------------------------------------------------
# (a) rung 1: the domination inequality
# ---------------------------------------------------------------------------


def test_rung1_holds_on_the_swept_families():
    """On the families paper_joint.py sweeps, the joint cap IS dominated
    by the sum of single-pair caps (ratio <= 1 + a window allowance).

    The allowance is not slack in the mathematics: the joint window runs
    2G beyond the OUTERMOST pair, so a far-apart configuration resolves
    more of each pair's own far bands than a one-pair window does.  It is
    measured at 3.3e-3 for the 40-mean-gap separation.
    """
    families = [ISOLATED, [(0.0, 0.1)], DIPOLE,
                [(0.0, 0.49), (40 * MEAN_GAP, 0.49)],
                [(i * 2 * MEAN_GAP, 0.49) for i in range(3)]]
    for pairs in families:
        rec = JU.domination(pairs, THETA_FULL)
        assert rec["ratio"] <= 1.005, (pairs, rec["ratio"])


def test_rung1_fails_off_them_on_coincident_stacks():
    """**The rung-1 verdict.**  Coincident pairs, which the sweep never
    contains, break subadditivity outright, and the ratio grows with k.
    """
    ratios = coincident_ratios(THETA_FULL, 0.49, ks=(2, 3, 4))
    assert ratios[2] > 1.4
    assert ratios[3] > ratios[2] and ratios[4] > ratios[3]
    assert not JU.domination(COINCIDENT2, THETA_FULL)["subadditive"]


def test_the_failure_is_the_square_completion_alone():
    """Below the k-fold single-occupancy threshold the completion is
    additive in F and the ratio is exactly 1: the band structure is not
    what breaks, the multiplicity branch is."""
    for k in (2, 3, 4):
        thr = JU.multiplicity_threshold_k(0.49, k)
        theta = thr - 0.02
        assert theta > 0
        rec = JU.domination([(0.0, 0.49)] * k, theta)
        assert abs(rec["ratio"] - 1.0) < 1e-12, (k, theta, rec["ratio"])


def test_completion_excess_closed_form():
    """The exact superadditivity identity, and its sign flip: the excess
    is positive once the pairwise products beat the per-cell credit."""
    K = JU.pj.K_of(1.0)
    hot = completion_excess((0.02, 0.02), K, 0.005)
    assert hot["defect"] < 1e-12 and hot["positive"]
    cold = completion_excess((0.02, 0.02), K, 0.05)
    assert cold["defect"] < 1e-12 and not cold["positive"]
    three = completion_excess((0.02, 0.02, 0.02), K, 0.005)
    assert three["defect"] < 1e-12
    assert three["lhs"] > 2 * hot["lhs"]  # grows faster than pairwise


def test_completion_reproduces_the_module_under_test():
    """This module never re-implements the cap; the local completion is
    pinned against ``PaperJoint.cap`` so a difference in a domination
    ratio is structural, not a second implementation."""
    assert completion_matches_module(THETA_FULL, ((0.0, 0.49),)) < 1e-12
    assert completion_relaxed(0.02, 0.9, 0.005) >= completion(0.02, 0.9, 0.005)


# ---------------------------------------------------------------------------
# the witness that closes the per-pair route
# ---------------------------------------------------------------------------


def test_the_per_pair_route_is_refuted_by_a_three_pair_witness():
    """**The decisive control.**  At the nu = 1 lattice, y = 0.49,
    theta = 0.995, the sum of single-pair caps exceeds the budget from
    k = 3 on, while the JOINT verdict closes comfortably.

    So no argument bounding the joint cap by a sum of single-pair caps
    can fund universality at theta*, the conclusion of such an argument
    is false, independently of the direction of the subadditivity
    inequality.  The joint field's shielding is load-bearing.
    """
    w = per_pair_route_witness(THETA_FULL, 0.49, kmax=4)
    assert w["first_failing_k"] == 3
    row = [r for r in w["rows"] if r["k"] == 3][0]
    assert row["per_pair_margin"] < 0
    assert row["joint_margin"] > 0.1 and row["joint_closes"]
    assert row["cap_joint"] < row["cap_single_sum"]


def test_even_split_lemma_is_exact_at_coincidence():
    """The per-cell even-split lemma B(sum F_p, K) <= sum_p B(F_p, K/k)
    holds, with equality for equal F, which is why it cannot be tightened
    into a useful bound at theta*."""
    K = JU.pj.K_of(1.0)
    assert even_split_defect(0.02, 0.02, K, 0.005) >= -1e-15
    assert abs(even_split_defect(0.02, 0.02, K, 0.005)) < 1e-15
    assert even_split_defect(0.03, 0.01, K, 0.005) > 0
    assert abs(even_split_theta(0.995, 2) - 0.9975) < 1e-15


def test_even_split_bound_is_valid_and_insufficient():
    """It dominates the joint cap, and at the nu = 1 lattice it exceeds
    the budget, a valid bound that cannot fund the verdict."""
    rec = JU.even_split_bound(NU1_K3, THETA_FULL)
    assert rec["dominates"]
    assert not rec["funds_universality"]
    assert rec["theta_k"] > THETA_FULL


def test_refinement_inflates_the_cap():
    """Rung 2's suggested repair, answered: band maxima do not grow under
    refinement, but every sub-cell inherits the parent band's maximum, so
    the per-cell sum grows monotonically as delta shrinks.  A common
    refinement is one-sided in the direction that inflates the cap."""
    rows = JU.refinement_ladder(ISOLATED, THETA_FULL,
                                deltas=(0.25, 0.5, 1.0, 2.0))
    sums = [r["sum"] for r in rows]
    assert sums[0] > sums[1] > sums[2]
    assert abs(sums[2] - sums[3]) < 1e-12      # delta >= band width: 1 cell
    assert rows[0]["cells"] == 4 * rows[2]["cells"]


# ---------------------------------------------------------------------------
# (c) the randomised search
# ---------------------------------------------------------------------------


def test_the_worst_random_configuration_is_inside_budget():
    """The search's worst find, re-checked at the module's own resolution
    (the search itself runs a coarser, conservative instance).

    A search is a lower bound on the adversary and no bound at all on the
    quantifier; this control only pins the datum reported.
    """
    rec = JU.verdict(WORST_RANDOM, THETA_FULL)
    assert rec["closes"], rec
    assert rec["rel_margin"] > 0
    assert abs(rec["rel_margin"] - WORST_RANDOM_RECORD["rel_margin_full"]) \
        < 5e-3, (rec["rel_margin"], WORST_RANDOM_RECORD)


def test_the_blind_search_also_breaks_rung_one():
    """37 of 320 random configurations broke per-pair domination, the
    subadditivity failure is not an artifact of hand-built stacks.  The
    worst find is a near-coincident nine-pair cluster, re-checked here at
    the module's own resolution."""
    rec = JU.domination(WORST_RANDOM_RATIO_PAIRS, THETA_FULL)
    assert not rec["subadditive"]
    assert abs(rec["ratio"] - WORST_RANDOM_RECORD["worst_ratio_full"]) < 5e-3
    span = (max(t for t, _ in WORST_RANDOM_RATIO_PAIRS)
            - min(t for t, _ in WORST_RANDOM_RATIO_PAIRS))
    assert span < 1.0, "the worst ratio comes from a near-coincident cluster"
    # and it still closes: a domination failure is not a verdict failure
    assert JU.verdict(WORST_RANDOM_RATIO_PAIRS, THETA_FULL)["closes"]


def test_the_search_instance_is_conservative():
    """A coarser step at the same resolved half-range raises the cap
    (wider band edges, larger local slope margins), so a configuration
    that closes on the search instance closes at the default."""
    coarse = JointUniversal(PaperJoint(step=0.005))
    for pairs in (ISOLATED, NU1_K3):
        assert coarse.pj.cap(pairs, THETA_FULL)["cap"] \
            >= JU.pj.cap(pairs, THETA_FULL)["cap"]
        assert coarse.pj.no_missed_band(pairs)["worst_ratio"] > 100


# ---------------------------------------------------------------------------
# (d) theta = 1
# ---------------------------------------------------------------------------


def test_cap_diverges_at_theta_one():
    """No charge, so an unbounded stack on one band costs nothing: the
    cap must report infinity, at every k."""
    for pairs in (ISOLATED, COINCIDENT3, NU1_K3):
        assert JU.pj.cap(pairs, 1.0)["cap"] == math.inf
    assert completion(0.02, 0.9, 0.0) == math.inf
    assert completion_relaxed(0.02, 0.9, 0.0) == math.inf


def test_the_domination_ratio_is_not_defined_by_infinities_at_theta_one():
    """Both sides diverge at theta = 1, so the rung-1 statement is empty
    there, pinned so nobody reads a ratio off it."""
    rec = JU.domination(ISOLATED, 1.0)
    assert math.isinf(rec["cap_joint"]) and math.isinf(rec["cap_single_sum"])


# ---------------------------------------------------------------------------
# (e) the planted violation
# ---------------------------------------------------------------------------


def test_planted_inflation_opens_a_closing_verdict():
    """Detector power.  Scale ONE pair's damage contribution and leave the
    budget alone: the verdict must flip to OPEN.  A margin that survived
    an arbitrary inflation would be measuring nothing."""
    rows = planted_violation(NU1_K3, THETA_FULL, inflations=(1.0, 2.0, 4.0))
    assert rows[0]["closes"]
    assert not rows[1]["closes"]
    assert not rows[2]["closes"]
    assert rows[2]["cap"] > rows[0]["cap"] * 3


def test_the_lesion_leaves_the_budget_untouched():
    """The planted fault is on the damage side only, otherwise the
    control would be measuring its own arithmetic."""
    honest = PaperJoint().budget(NU1_K3)
    for s in (1.0, 4.0):
        assert abs(InflatedJoint(inflate=s).budget(NU1_K3) - honest) < 1e-12
