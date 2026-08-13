"""Controls for ``cluster_sdp.py``.

Six families, in the order the module's claims are made:

(a) EVERY DERIVED CONSTRAINT IS SATISFIED BY GENUINE CONFIGURATIONS.  This
    is the load-bearing one.  A constraint a real configuration violates is
    not a tightening, it is a bug: the relaxation would then be excluding
    the very objects it is supposed to bound, and a positive value would
    mean nothing.  34 configurations (10 fixed, 24 random), every derived
    slack, tolerance 1e-9.
(b) THE COURT OF THE EARLIER ATTEMPT.  ``sos_certificate.cone_violator``
    -- the exact rational family that closed the plain Gram route -- must
    now be excluded, and the test names WHICH constraint does it: the depth
    cap at the published ``t``, and (T3) at the largest ``t`` the depth cap
    admits, where the family still violates the target.
(c) ``n = 0`` still recovers ``4k`` (``PairEnergy.lean``), which the
    earlier degree-2 lift did NOT for ``k >= 2``.
(d) CLARABEL against SCS.
(e) planted infeasibility: a constant raised above the true optimum is
    rejected, and a constraint deleted from the window bound makes it fail.
(f) the relaxations are LOWER bounds: below the sampled configuration
    minimum at every size, and the window bound below the measured
    single-pair minimum at every ``n``.

The slow marks are on the SDP families and on the configuration searches.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from cluster_sdp import (  # noqa: E402
    C_DAMAGE, C_TRADE, NAMED_GAPS, N_PAID_FOR, SAMPLE_CONFIGS, TRADE_RECORD,
    WINDOW_RECORD, budget, cluster_relaxation, configuration_minimum,
    constraint_defects, cross_entry, damage, damage_windows,
    depth_curve_convexity_defect, depth_curve_cuts, entry_dual_certificate,
    line_kernel, window_peak_fit,
    localizing_defect, multi_pair_requirement, nu_moment_defect,
    occupancy_max, psi, random_configs, relax_trade, slack, trade_index,
    trade_prediction, trade_weight_matrix, violator_family_in_sdp,
    violator_screen, window_occupancy_bound, window_repulsion,
)
from sos_certificate import (  # noqa: E402
    PSI_HALF, PSI_ONE, SDP_RECORD, THETA_FULL, cone_violator,
    target_from_config,
)


# ---------------------------------------------------------------------------
# 0. the structural fact the whole module rests on
# ---------------------------------------------------------------------------


def test_squares_are_moments_of_the_self_convolution() -> None:
    """``psi(z)^2 = int e^{zw} dnu(w)``, ``dnu = c2 dw/A^2``.

    Every derived constraint reads the objective as a 2-body energy in the
    single positive measure ``nu``.  If this identity failed, none of them
    would be about the obligation at all.
    """
    assert nu_moment_defect() < 1e-9


def test_the_line_kernel_is_a_positive_definite_function() -> None:
    """Bochner, measured: ``[G(v_i - v_j)]`` is positive semidefinite for
    arbitrary reals, which is what makes the on-line block's entries values
    of one fixed function rather than free reals."""
    rng = np.random.default_rng(3)
    for _ in range(20):
        v = rng.uniform(-40.0, 40.0, 9)
        M = line_kernel(v[:, None] - v[None, :])
        assert float(np.linalg.eigvalsh(M).min()) > -1e-12


def test_the_depth_curve_is_convex_so_its_tangent_cuts_are_valid() -> None:
    assert depth_curve_convexity_defect(300) <= 1e-12
    cuts = depth_curve_cuts()
    for y in np.linspace(0.0, 0.5, 41):
        r = float(np.real(psi(y)))
        d = float(np.real(psi(2 * y)))
        for (r0, d0, m0) in cuts["tangents"]:
            assert d >= d0 + m0 * (r - r0) - 1e-9
        assert d <= 1.0 + cuts["chord"] * (r - 1.0) + 1e-12


def test_the_derived_constants_are_what_the_module_says() -> None:
    """The two constants, re-measured on an independent grid.  They are
    MEASURED, so the test asks that the module's stored value is an
    admissible one (never smaller than what a fresh scan needs)."""
    ss = np.linspace(0.0, 220.0, 220001)
    g2 = line_kernel(ss) ** 2
    need_d, need_t = -math.inf, -math.inf
    for y in np.linspace(1e-3, 0.5, 121):
        v = np.real(cross_entry(ss, y) ** 2)
        sl = slack(y)
        need_d = max(need_d, float((-v).max() / sl))
        need_t = max(need_t, float(((g2 - v) / sl).max()))
    assert need_d <= C_DAMAGE + 1e-9, (need_d, C_DAMAGE)
    assert need_t <= C_TRADE + 1e-9, (need_t, C_TRADE)
    assert abs(N_PAID_FOR - 1.0 / (2.0 * C_DAMAGE)) < 1e-12


# ---------------------------------------------------------------------------
# (a) every derived constraint holds on genuine configurations
# ---------------------------------------------------------------------------


ALL_CONFIGS = SAMPLE_CONFIGS + random_configs(24, seed=11)


@pytest.mark.parametrize("name,online,pairs", ALL_CONFIGS,
                         ids=[c[0] for c in ALL_CONFIGS])
def test_every_derived_constraint_holds_on_genuine_configurations(
        name, online, pairs) -> None:
    """**The load-bearing control.**  Each constraint is a signed slack on
    a real configuration; a negative one would mean the relaxation excludes
    genuine objects, so its value would bound nothing."""
    d = constraint_defects(online, pairs)
    bad = {k: v for k, v in d.items() if v < -1e-9}
    assert not bad, f"{name}: derived constraints violated by a genuine "\
                    f"configuration: {bad}"


def test_the_sample_is_large_enough_to_be_a_control() -> None:
    assert len(ALL_CONFIGS) >= 20
    with_pairs = [c for c in ALL_CONFIGS if c[2]]
    assert len(with_pairs) >= 20


def test_the_localizing_matrices_are_positive_semidefinite() -> None:
    """(T5): band limitation.  ``supp mu`` in ``[-1/2,1/2]`` makes both the
    moment matrix of ``{f_a} u {u f_a}`` and ``Q/4 - Q_2`` positive
    semidefinite; measured on random configurations."""
    from cluster_sdp import augmented_atoms
    rng = np.random.default_rng(5)
    for _ in range(12):
        n, k = int(rng.integers(0, 5)), int(rng.integers(1, 3))
        xs = rng.uniform(-25, 25, n)
        pr = [(float(rng.uniform(-25, 25)), float(rng.uniform(0, 0.5)))
              for _ in range(k)]
        z, _s, _kk = augmented_atoms(xs, pr)
        rec = localizing_defect(z)
        assert rec["moment_min_eig"] > -1e-9
        assert rec["localizing_min_eig"] > -1e-9


# ---------------------------------------------------------------------------
# (b) the cone violator is now excluded, and by a named constraint
# ---------------------------------------------------------------------------


def test_the_cone_violator_still_violates_the_target() -> None:
    """The premise of the exclusion test: the witness is a genuine problem
    for the earlier cone, so excluding it is doing work."""
    for n in (3, 4, 6):
        s = violator_screen(n)
        assert s["Xi"] < 0
        assert s["Xi_at_admissible_t"] < 0, (
            "at the largest depth-admissible t the family must still "
            "violate, otherwise the depth cap alone would be the whole story"
        )


def test_the_depth_cap_excludes_the_published_violator() -> None:
    """At ``t = 1/2`` the witness has pair diagonal ``3/2`` while
    ``psi(2y) <= psi(1) = 1.0392`` for every admissible depth."""
    s = violator_screen(3, Fraction(1, 2))
    assert s["depth_cap_excludes"]
    assert s["d"] > PSI_ONE


def test_T3_excludes_the_depth_admissible_violator() -> None:
    """The constraint that does the work once the range alone cannot: the
    witness's cross entries are purely imaginary, so ``Re(C^2) = -t^2``,
    and (T3) allows only ``-C_DAMAGE (d^2-1)`` -- short by 3.76x."""
    s = violator_screen(3)
    assert s["T3_slack_at_admissible_t"] < 0
    assert s["T3_ratio_at_admissible_t"] > 3.0
    # and it is (T3), not the range: the witness passes |C| <= psi(1/2)
    assert s["t_admissible"] <= PSI_HALF


@pytest.mark.slow
def test_the_violator_is_infeasible_in_the_program_as_built() -> None:
    """The machine-checked half: pin the witness's first and second moments
    into the relaxation and the program is infeasible, at every ``t`` on
    the family including the depth-admissible one."""
    for n in (3, 4):
        rows = violator_family_in_sdp(n)
        assert rows, "no violator rows"
        for row in rows:
            assert row["infeasible"], (n, row)
        last = rows[-1]
        assert not last["depth_cap_excludes"] and last["T3_excludes"], (
            "the depth-admissible member must be excluded by (T3)")


@pytest.mark.slow
def test_deleting_T3_lets_the_violator_back_in() -> None:
    """The lesion: with (T3) and the depth curve switched off, the same
    program admits a matrix at least as bad as the witness -- i.e. the
    exclusion is (T3)'s doing and not an accident of the lift."""
    with_cut = relax_trade(3, 1)["value"]
    without = relax_trade(3, 1, damage_cut=False, trade_cut=False,
                          depth_curve=False)["value"]
    assert with_cut > -1e-6
    assert without < violator_screen(3)["Xi_at_admissible_t"] + 1e-9


# ---------------------------------------------------------------------------
# (c) n = 0 recovers the kernel-checked 4k
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("k", [1, 2, 3, 4])
def test_pairs_only_recovers_four_k(k) -> None:
    """``PairEnergy.lean`` (zero sorry) gives ``sum over the pair block of
    Q^2 >= 4k``.  The earlier degree-2 lift returned ``-4k`` here for
    ``k >= 2`` (its finding F4) because the bound is an inertia fact; this
    lift is handed it as (T6a) and returns 0."""
    v = relax_trade(0, k)["value"]
    assert v > -1e-6, (k, v)
    if k >= 2:
        assert SDP_RECORD["values"][(0, k)] <= -8.0 + 1e-9, (
            "the earlier lift's failure at n=0, k>=2 is the thing being "
            "repaired; if it were not there this test would be vacuous")


@pytest.mark.parametrize("k,without", [(2, -0.069453), (3, -0.204398),
                                       (4, -0.405163)])
def test_which_constraint_recovers_four_k(k, without) -> None:
    """WHICH constraint does the recovery, measured rather than assumed.

    Removing (T6) does NOT send the value back to the earlier lift's
    ``-4k``: the derived entry ranges and the depth curve already get the
    pairs-only block to within 0.07 (k=2) to 0.41 (k=4) of ``4k``, and
    (T6a) closes the rest.  Recorded here because it is the one place the
    module's improvement is NOT the supplied theorem's doing.
    """
    v = relax_trade(0, k, proved_bounds=False)["value"]
    assert abs(v - without) < 2e-3, (k, v)
    assert v < -1e-3, "if this were 0 the supplied theorem would be idle"
    assert relax_trade(0, k)["value"] > -1e-6
    bare = relax_trade(0, k, proved_bounds=False, ranges=False,
                       depth_curve=False, damage_cut=False,
                       trade_cut=False)["value"]
    assert bare < -3.0 * k, (k, bare)


# ---------------------------------------------------------------------------
# (d) solver agreement
# ---------------------------------------------------------------------------


@pytest.mark.slow
@pytest.mark.parametrize("n,k", [(0, 1), (2, 1), (8, 1), (2, 2)])
def test_clarabel_and_scs_agree(n, k) -> None:
    a = relax_trade(n, k, solver="CLARABEL")["value"]
    b = relax_trade(n, k, solver="SCS", eps=1e-9)["value"]
    assert abs(a - b) < 1e-5, (n, k, a, b)


# ---------------------------------------------------------------------------
# (e) planted infeasibility
# ---------------------------------------------------------------------------


def test_planted_infeasibility_is_detected() -> None:
    """Raise the constant above the true optimum and the relaxation must go
    negative; at the true constant it must not."""
    assert relax_trade(2, 1, constant=4.0)["value"] > -1e-6
    for c in (4.25, 5.0):
        assert relax_trade(2, 1, constant=c)["value"] < -1e-6


def test_planted_infeasibility_in_the_window_bound() -> None:
    """The same control for the configuration-level bound: inflate the
    budget's competitor (halve the repulsion charge, which is what the
    trade buys) and the bound must fall; delete the occupancy charge
    entirely and the first window's cost must rise."""
    y = 0.5
    ref = window_occupancy_bound(y, n_s=200001)
    w0 = ref["terms"][0]
    honest = occupancy_max(w0["peak"], w0["gamma"])
    lesioned = occupancy_max(w0["peak"], w0["gamma"] / 4.0)
    assert lesioned["value"] > honest["value"]
    assert lesioned["N"] >= honest["N"]
    # and with no charge at all the occupancy is unbounded, which is
    # precisely the pointwise-bound failure the module is repairing
    assert occupancy_max(w0["peak"], 0.0)["value"] == math.inf


# ---------------------------------------------------------------------------
# (f) everything is a LOWER bound
# ---------------------------------------------------------------------------


@pytest.mark.slow
@pytest.mark.parametrize("n,k", [(1, 1), (2, 1), (4, 1), (0, 2), (2, 2)])
def test_the_relaxation_sits_below_every_sampled_configuration(n, k) -> None:
    """A relaxation value above some real configuration's ``Xi`` would mean
    a constraint excludes genuine objects."""
    rng = np.random.default_rng(17 + 3 * n + k)
    v = relax_trade(n, k)["value"]
    worst = math.inf
    for _ in range(40):
        xs = np.sort(rng.uniform(-30, 30, n))
        pr = [(float(rng.uniform(-30, 30)), float(rng.uniform(0.0, 0.5)))
              for _ in range(k)]
        worst = min(worst, target_from_config(xs, pr, THETA_FULL))
    assert v <= worst + 1e-6, (n, k, v, worst)


def test_the_window_bound_is_below_the_recorded_configuration_minima() -> None:
    """The window bound claims to hold for every ``n``; the recorded
    single-pair minima at ``y = 1/2`` are what it must sit under."""
    b = window_occupancy_bound(0.5, n_s=200001)["bound"]
    for _n, v in WINDOW_RECORD["configuration_minimum_y_half"].items():
        assert b <= v + 1e-9, (b, v)


@pytest.mark.slow
def test_the_window_bound_is_below_a_freshly_searched_minimum() -> None:
    """The same, with the configuration search re-run rather than recalled."""
    b = window_occupancy_bound(0.5, n_s=200001)["bound"]
    for n in (2, 5, 9):
        m = configuration_minimum(0.5, n, restarts=12, seed=n)["min"]
        assert b <= m + 1e-9, (n, b, m)


def test_the_window_bound_is_positive_at_every_depth() -> None:
    """(F4): the single-pair case closes, size-free."""
    for y in (0.05, 0.1, 0.2, 0.3, 0.4, 0.49, 0.5):
        r = window_occupancy_bound(y, n_s=200001)
        assert r["bound"] > 0, (y, r["bound"])
        assert r["ratio"] > 0.4, (y, r["ratio"])
        assert r["tail_single_occupancy"], (
            "the tail estimate assumes one atom per far window; if the last "
            "scanned window wants more, the estimate is not one-sided")


def test_the_window_bound_carries_no_n() -> None:
    """Size independence, as a property of the code rather than a claim: the
    bound's signature takes no atom count, and its parts are indexed by
    windows only."""
    import inspect
    sig = inspect.signature(window_occupancy_bound)
    assert "n" not in sig.parameters
    r = window_occupancy_bound(0.5, n_s=100001)
    assert set(r["terms"][0]) >= {"peak", "gamma", "N", "M"}
    assert all(t["N"] is not None for t in r["terms"])


def test_the_damage_windows_are_where_the_asymptotics_say() -> None:
    """The window structure is the mechanism behind the bound: positive
    damage only near ``s = 2 pi j``, peaks falling like ``1/j^2``."""
    wins = damage_windows(0.5, s_max=100.0, n_s=200001)
    assert len(wins) >= 15
    for j, w in enumerate(wins[:8], start=1):
        assert abs(w["peak_at"] - 2 * math.pi * j) < 0.6, (j, w)
        assert 0.9 < w["width"] < 1.1
    peaks = [w["peak"] for w in wins[:6]]
    assert all(peaks[i] > peaks[i + 1] for i in range(len(peaks) - 1))
    ratio = peaks[0] / peaks[1]
    assert 3.0 < ratio < 6.0, ratio
    # and outside the windows the damage is nonpositive, which is what lets
    # the accounting drop every atom that is not in one
    ss = np.linspace(0.0, 100.0, 200001)
    D = damage(ss, 0.5)
    inside = np.zeros_like(ss, bool)
    for w in wins:
        inside |= (ss >= w["lo"]) & (ss <= w["hi"])
    assert float(D[~inside].max()) <= 0.0


def test_the_repulsion_charge_is_one_sided_downward() -> None:
    """``gamma_j`` must be a lower bound for ``G(x_a-x_b)^2`` at every pair
    of atoms inside the window, or the charge is overstated."""
    for w in damage_windows(0.5, s_max=60.0, n_s=200001)[:5]:
        gam = window_repulsion(w["width"])
        v = np.linspace(-w["width"], w["width"], 501)
        assert gam <= float((line_kernel(v) ** 2).min()) + 1e-12


# ---------------------------------------------------------------------------
# the before/after table, and the diagnosis
# ---------------------------------------------------------------------------


@pytest.mark.slow
@pytest.mark.parametrize("n,k", [(0, 2), (2, 1), (4, 1), (7, 1), (8, 1),
                                 (2, 2), (8, 4)])
def test_the_recorded_table_reproduces(n, k) -> None:
    v = relax_trade(n, k)["value"]
    assert abs(v - TRADE_RECORD["trade"][(n, k)]) < 2e-4, (n, k, v)


@pytest.mark.slow
def test_the_single_pair_relaxation_is_tight_up_to_the_derived_count() -> None:
    """(F1): the entry-level program is exactly 0 for ``k = 1`` while
    ``n <= 1/(2 C_DAMAGE) = 7.68``, and negative after."""
    for n in range(0, 8):
        assert relax_trade(n, 1)["value"] > -1e-6, n
    v8 = relax_trade(8, 1)["value"]
    assert v8 < -1e-4
    assert abs(v8 - trade_prediction(8, 1)) < 1e-4
    assert 7 < N_PAID_FOR < 8


def test_the_trade_prediction_floors_the_relaxation() -> None:
    """The closed form derived from (T3) must never be above the solved
    value: it is an accounting the program is free to beat."""
    for (n, k), v in TRADE_RECORD["trade"].items():
        assert trade_prediction(n, k) <= v + 1e-4, (n, k, v)


def test_the_multi_pair_gap_is_on_the_budget_side() -> None:
    """(F5): the same accounting needs a budget floor about 2x the measured
    one.  Recorded as a failure, not reframed."""
    r = multi_pair_requirement(ys=(0.1, 0.3, 0.5))
    assert not r["closes_for_k_ge_2"]
    assert 1.5 < r["short_by_factor"] < 2.5
    assert 0.5 < r["required_ratio"] < 0.7


@pytest.mark.slow
def test_the_cluster_program_agrees_with_the_window_bound() -> None:
    """The two configuration-level instruments are independent formulations
    of the same trade: a moment program over occupancies, and a closed-form
    per-window charge.  Both must be positive and both must sit below the
    configuration minimum."""
    cl = cluster_relaxation(0.5, s_max=20.0, h=1.0)
    assert cl["status"] == "optimal"
    assert cl["bound"] > 0
    assert cl["bound"] <= min(
        WINDOW_RECORD["configuration_minimum_y_half"].values()) + 1e-9
    assert cl["mass"] > 1.0, "a size-free program that chooses mass 0 is idle"


def test_the_weight_matrix_gives_the_shadow_atoms_no_say() -> None:
    """(T1)'s admission price: the shadow atoms are extra columns of the
    same Gram matrix and must not enter the objective, or the program would
    be bounding a different quantity."""
    L = trade_index(3, 2)
    c = trade_weight_matrix(L.kinds, THETA_FULL)
    for a in range(L.N):
        for b in range(L.N):
            if L.kinds[a] == 2 or L.kinds[b] == 2:
                assert c[a, b] == 0.0
    on = np.flatnonzero(L.kinds == 0)
    pr = np.flatnonzero(L.kinds == 1)
    assert c[on[0], on[1]] == pytest.approx(1.0 - THETA_FULL)
    assert c[on[0], on[0]] == 0.0
    assert c[pr[0], pr[0]] == 1.0
    assert c[on[0], pr[0]] == 1.0


def test_the_named_gaps_are_on_disk() -> None:
    """A measured accounting that does not say what it has not established
    reads as more than it is."""
    assert len(NAMED_GAPS) >= 5
    blob = " ".join(NAMED_GAPS).lower()
    for token in ("measured", "single-pair", "tail", "proof"):
        assert token in blob


# ---------------------------------------------------------------------------
# size independence: the two certificates, and what each one reaches
# ---------------------------------------------------------------------------


def test_the_entry_level_dual_is_size_independent_and_insufficient() -> None:
    """The multiplier has no size in it -- weight 1 on the pair block's
    identity, weight 2 on every cross-entry cut -- and it carries exactly
    while ``n <= 1/(2 C_DAMAGE)``.  Both halves are the claim."""
    shapes = {(entry_dual_certificate(n)["pair_block_multiplier"],
               entry_dual_certificate(n)["cross_cut_multiplier"])
              for n in range(1, 12)}
    assert shapes == {(1.0, 2.0)}, "the multiplier must not depend on n"
    for n in range(0, 8):
        c = entry_dual_certificate(n)
        assert c["sufficient"] and c["value"] > -1e-12, n
    for n in (8, 12, 30):
        c = entry_dual_certificate(n)
        assert not c["sufficient"] and c["value"] < 0, n
    assert entry_dual_certificate(8)["value"] == pytest.approx(
        trade_prediction(8, 1), abs=1e-12)


def test_the_window_peak_law_matches_its_closed_form() -> None:
    """The size-free certificate's summability, as a fit: the ``j``-th
    window's peak times ``(2 pi j)^2`` tends to the integration-by-parts
    constant ``8 c^2 (cosh y - 1)``, ``c = cos(sqrt2/2)/A``."""
    for y in (0.3, 0.5):
        fit = window_peak_fit(y, n_s=200001)
        assert fit["worst_rel_error_tail"] < 5e-3, (y, fit["predicted"])
        assert abs(fit["asymptote"] / fit["predicted"] - 1.0) < 5e-3
        # and the law is decreasing in j, which is what makes the tail sum
        peaks = [r["peak"] for r in fit["rows"][:10]]
        assert all(peaks[i] > peaks[i + 1] for i in range(len(peaks) - 1))


def test_the_occupancy_schedule_is_the_certificate() -> None:
    """The size-free certificate is a list of integers, one per window,
    with no atom count anywhere: ``N_j = 3, 1, 1, ...`` at ``y = 1/2``."""
    r = window_occupancy_bound(0.5, n_s=200001)
    Ns = [t["N"] for t in r["terms"]]
    assert Ns[0] == 3
    assert set(Ns[1:]) == {1}
    assert r["bound"] == pytest.approx(
        budget(0.5) - 2 * (r["body"] + r["tail"]), abs=1e-12)


@pytest.mark.slow
def test_the_measured_constants_are_stable_up_a_ladder() -> None:
    """Precision response, as the hunt's checklist requires: both derived
    constants are re-measured at three grid resolutions and must not move.
    A constant that drifts with the grid is a constant that has not been
    measured."""
    from cluster_sdp import CONSTANT_LADDER, constant_ladder
    ladder = ((100.0, 100001, 51), (200.0, 200001, 101), (300.0, 300001, 201))
    for kind, recorded in (("damage", CONSTANT_LADDER["damage"]),
                           ("trade", CONSTANT_LADDER["trade"])):
        got = [r["constant"] for r in constant_ladder(kind, ladder=ladder)]
        assert max(got) - min(got) < 1e-9, (kind, got)
        for a, b in zip(got, recorded):
            assert abs(a - b) < 1e-9, (kind, a, b)
        top = C_DAMAGE if kind == "damage" else C_TRADE
        assert max(got) <= top + 1e-9
