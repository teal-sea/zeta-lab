"""Controls for `counting_lemma` (Road B, step 3)."""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from counting_lemma import (  # noqa: E402
    ATOM_RELIEF, A_CONST, C2_ZERO, CRITICAL_LATTICE_LIMIT,
    D_ONE, KAPPA_W, NAMED_GAPS, W_MAX,
    am_gm_margin, budget, budget_floor_ladder, budget_per_pair, damage,
    critical_lattice_limit, critical_lattice_partial_sum, kappa,
    kappa_is_nonincreasing, kernel, lattice_budget_per_pair, phi_r,
    site_lower_bound, site_value, window_occupancy, worst_spacing,
)


# -- the constants ----------------------------------------------------------

def test_constants_match_the_window_table():
    assert A_CONST == pytest.approx(0.9187253698655684, abs=1e-15)
    assert W_MAX == pytest.approx(0.9860008, abs=1e-6)
    assert D_ONE == pytest.approx(damage(0.5, 6.516999776), rel=1e-8)


def test_atom_relief_is_gamma_squared_over_800():
    assert ATOM_RELIEF == pytest.approx(phi_r(W_MAX) ** 2 / 800, rel=1e-12)
    assert phi_r(W_MAX) == pytest.approx(0.88452, abs=1e-4)


def test_kappa_is_the_pair_pair_term():
    assert KAPPA_W == pytest.approx(kappa(W_MAX), rel=1e-12)
    # at coincidence it is the measured shield
    assert kappa(0.0) == pytest.approx(1.7556, abs=1e-3)


def test_kappa_is_not_a_pure_repulsion():
    """C4: it goes slightly negative near the window period."""
    assert kappa(2 * math.pi) < 0
    assert kappa(2 * math.pi) == pytest.approx(-1.82e-2, abs=1e-3)
    assert kappa(0.5) > 1.0


# -- 1. the counting lemma --------------------------------------------------

def test_am_gm_condition_holds_with_margin():
    """Defect #21: the pair relief is `j(j-1) kappa/2`, not `j(j-1) kappa`.

    The sum in the k-pair identity is over UNORDERED pairs. The first
    version doubled it, which doubled this margin too.
    """
    a = am_gm_margin()
    assert a["holds"]
    assert a["margin"] == pytest.approx(164.0, rel=1e-2)
    assert a["lhs"] == pytest.approx(1.932855e-05, rel=1e-4)
    assert a["rhs"] == pytest.approx(3.169087e-03, rel=1e-4)


def test_site_value_uses_the_unordered_pair_count():
    """Pin the factor that was wrong, against the exact pair relief."""
    # two coincident pairs relieve exactly kappa(0), not 2 kappa(0)
    exact_two_coincident = kappa(0.0)
    modelled = 2 * 1 * KAPPA_W / 2
    assert modelled < exact_two_coincident          # conservative direction
    assert modelled == pytest.approx(KAPPA_W, rel=1e-12)
    assert exact_two_coincident == pytest.approx(1.7556, abs=1e-3)


def test_site_value_pairs_with_k_shq_not_with_B():
    """Defect #22: `slack >= B - f` double-counts the pair relief.

    `B` already contains `sum_{p<q} kappa`, which `f` subtracts again.
    The wrong form must FAIL for j >= 2 and the right one must hold.
    """
    from gram_form import slack_direct, budget, shq
    bad_B = ok_S = 0
    for j in (1, 2, 3):
        for m in (1, 3, 5):
            xs, ts = [0.0] * m, [6.516999776] * j
            sl, B, f = slack_direct(xs, ts, 0.5), budget(ts, 0.5), site_value(m, j)
            bad_B += sl < B - f - 1e-12
            ok_S += sl >= j * shq(0.5) / 2 - f - 1e-12
    assert bad_B == 6, bad_B      # the wrong pairing really is wrong
    assert ok_S == 9, ok_S        # the right one holds everywhere


def test_kappa_nonincreasing_on_the_window():
    """The step `sum kappa >= j(j-1) kappa(w_max)/2` needs this."""
    r = kappa_is_nonincreasing()
    assert r["nonincreasing"]
    assert r["start"] == pytest.approx(1.75562102, rel=1e-8)
    assert r["end"] == pytest.approx(1.62023918, rel=1e-8)
    assert r["min"] == pytest.approx(r["end"], rel=1e-12)


def test_site_lower_bound_is_cleared_by_the_exact_slack():
    from gram_form import slack_direct
    for j in (1, 2, 3):
        for m in (1, 3, 5):
            xs, ts = [0.0] * m, [6.516999776] * j
            assert slack_direct(xs, ts, 0.5) >= site_lower_bound(m, j) - 1e-12


def test_site_value_is_not_a_bound_on_the_adversary():
    """Defect #21, second half: `slack >= B - f`, so `f` understates slack.

    The exact slack exceeds `f` at every occupancy, because `f` discards
    the budget entirely. `f < 0` therefore means "safe outright", not
    "the adversary loses".
    """
    from gram_form import slack_direct
    for m in (1, 3, 5):
        for j in (1, 2, 3):
            xs, ts = [0.0] * m, [6.516999776] * j
            assert slack_direct(xs, ts, 0.5) > site_value(m, j)


def test_pair_species_cannot_crowd():
    """`kappa(w_max)/2` dwarfs the per-pair atom relief."""
    r = am_gm_margin()["kappa_over_atom_relief"]
    assert r == pytest.approx(828, rel=2e-2)


def test_at_most_one_pair_per_window_is_profitable():
    """THE counting lemma."""
    rows = {r["j"]: r for r in window_occupancy()}
    assert rows[1]["profitable"]
    assert not rows[2]["profitable"]
    assert not rows[3]["profitable"]
    assert rows[2]["best"] < -1.5
    assert rows[3]["best"] < rows[2]["best"]


def test_single_pair_optimum_reproduces_the_k_one_answer():
    """j = 1 must give the multiplicity-3 optimum the k=1 closure found."""
    r = window_occupancy(js=(1,))[0]
    assert r["m"] == 3
    assert r["best"] == pytest.approx(7.321459e-03, rel=1e-4)


def test_site_value_is_decreasing_in_j_beyond_one():
    for m in (1, 3, 5, 8):
        assert site_value(m, 2) < site_value(m, 1)
        assert site_value(m, 3) < site_value(m, 2)


# -- 2. the budget floor ----------------------------------------------------

def test_worst_spacing_sits_just_past_the_window_period():
    ws = worst_spacing()
    assert 2 * math.pi < ws["spacing"] < 6.31
    assert ws["min_budget_per_pair"] > 0


def test_lattice_difference_sum_matches_direct_budget():
    """The O(k) reduction must be identical to the original O(k^2) sum."""
    for k in (2, 8, 64):
        assert lattice_budget_per_pair(6.3, k) == pytest.approx(
            budget_per_pair(6.3, k), abs=2e-14)


def test_critical_lattice_limit_has_the_poisson_closed_form():
    expected = (0.5 + math.sin(math.sqrt(2)) / (2 * math.sqrt(2))
                - 2 * math.sin(1 / math.sqrt(2)) ** 2)
    assert C2_ZERO == pytest.approx(0.8492279993183042, abs=1e-15)
    assert CRITICAL_LATTICE_LIMIT == pytest.approx(expected, abs=1e-15)
    assert critical_lattice_limit() == pytest.approx(
        0.00517169408367867955, abs=1e-15)


def test_poisson_sum_converges_to_the_closed_form_target():
    """Independent kernel-side check of the analytic Poisson identity."""
    assert critical_lattice_partial_sum(50000) == pytest.approx(
        critical_lattice_limit(), abs=4e-7)


@pytest.mark.slow
def test_budget_per_pair_does_not_decay_to_zero():
    ladder = budget_floor_ladder()
    vals = [r["budget_per_pair"] for r in ladder]
    assert all(v > CRITICAL_LATTICE_LIMIT for v in vals), vals
    assert vals[-1] > critical_lattice_limit()
    assert vals[-1] < 5.31e-3


@pytest.mark.slow
def test_reoptimised_ladder_keeps_falling_toward_two_pi():
    vals = [r["budget_per_pair"] for r in budget_floor_ladder()]
    spacings = [r["spacing"] for r in budget_floor_ladder()]
    assert all(a > b for a, b in zip(vals, vals[1:]))
    assert all(a > b for a, b in zip(spacings, spacings[1:]))
    assert spacings[-1] - 2 * math.pi < 5e-4


@pytest.mark.slow
def test_fixed_spacing_turnaround_was_an_artifact():
    """Defect #24: the old ladder reused the k=64 minimiser at every k."""
    ks = (64, 128, 256, 512, 1024)
    fixed = [r["budget_per_pair"] for r in budget_floor_ladder(L=6.3, ks=ks)]
    optimised = [r["budget_per_pair"] for r in budget_floor_ladder(ks=ks)]
    assert fixed[-1] > min(fixed)
    assert all(a > b for a, b in zip(optimised, optimised[1:]))
    assert optimised[-1] < fixed[-1]


def test_budget_is_nonnegative_on_random_pair_sets():
    rng = random.Random(4)
    for _ in range(200):
        k = rng.randint(1, 10)
        ts = [rng.uniform(-80, 80) for _ in range(k)]
        assert budget(ts) > 0


def test_coincident_pairs_have_an_enormous_budget():
    assert budget_per_pair(1e-9, 6) > 100 * budget_per_pair(6.3, 6)


# -- what it does NOT settle ------------------------------------------------

def test_one_pair_at_every_window_peak_still_beats_the_floor():
    """C1, pinned: this is why k >= 2 is not closed.

    The nine windows to `s = 60` give `1.2888e-02`; that is a LOWER bound
    for the full sum `1.372e-02` (`window_table` caps nine windows at
    `6.5954e-03` one-sided, and the tail past `s = 60` carries the rest).
    Either number beats the floor, which is the point, but they are two
    different truncations and must not be quoted for each other.
    """
    peaks = [6.517, 12.755, 18.977, 25.20, 31.47, 37.72, 43.96, 50.21, 56.46]
    nine = 2 * sum(damage(0.5, p) for p in peaks)
    assert nine == pytest.approx(1.2888e-2, rel=1e-3)
    assert nine < 1.372e-2                      # a lower bound for the total
    assert nine > CRITICAL_LATTICE_LIMIT
    assert nine / CRITICAL_LATTICE_LIMIT > 2.4


def test_named_gaps_are_stated():
    joined = " ".join(NAMED_GAPS).lower()
    assert "not closed" in joined
    assert "not proved" in joined
    assert "re-optimising" in joined
    assert "rh" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "counting_lemma.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
