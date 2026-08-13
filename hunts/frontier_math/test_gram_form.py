"""Controls for `gram_form` (Road B, step 2)."""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from gram_form import (  # noqa: E402
    ALL_PEAKS, A_CONST, BUDGET_RECORD, NAMED_GAPS, budget, budget_gram,
    budget_is_shq_at_k_one, budget_search, cauchy_schwarz_gap, cross, damage,
    kernel, pd_min_eigenvalue, phi_r, repulsion, shq, slack_direct,
    slack_three_term,
)


# -- the identity -----------------------------------------------------------

def test_three_term_form_matches_the_direct_slack():
    """If this fails, every reading in the module is wrong."""
    rng = random.Random(11)
    worst = 0.0
    for _ in range(40):
        n, k = rng.randint(1, 7), rng.randint(1, 5)
        xs = [rng.uniform(-30, 30) for _ in range(n)]
        ts = [rng.uniform(-30, 30) for _ in range(k)]
        y = rng.uniform(0.05, 0.5)
        worst = max(worst, abs(slack_three_term(xs, ts, y)
                               - slack_direct(xs, ts, y)))
    assert worst < 1e-12, worst


@pytest.mark.parametrize("ts,y", [([6.517], 0.5), ([0.0] * 3, 0.4),
                                  (list(ALL_PEAKS), 0.5),
                                  ([1.3, -4.2, 19.0], 0.25)])
def test_budget_gram_equals_budget(ts, y):
    assert budget(ts, y) == pytest.approx(budget_gram(ts, y), abs=1e-14)


# -- B is the true budget ---------------------------------------------------

def test_budget_is_shq_over_two_at_k_one():
    assert budget_is_shq_at_k_one() < 1e-13


def test_budget_is_not_k_times_shq_half():
    """The whole point: the budget has no additivity to fail."""
    for lab, r in BUDGET_RECORD.items():
        b, add = r["B"], r["k_times_shq_half"]
        if lab == "k=1":
            assert b == pytest.approx(add, rel=1e-9)
        else:
            assert abs(b - add) / add > 0.25, (lab, b, add)


def test_recorded_budgets_reproduce():
    cases = {"k=1": ([6.517], 0.5),
             "10 pairs on windows": (list(ALL_PEAKS), 0.5),
             "6 coincident": ([0.0] * 6, 0.5),
             "8 on a 2pi lattice": ([6.283185307 * i for i in range(8)], 0.5)}
    for lab, (ts, y) in cases.items():
        assert budget(ts, y) == pytest.approx(BUDGET_RECORD[lab]["B"], rel=1e-8)


def test_clustered_pairs_have_a_much_larger_budget():
    """Coincident centres are self-defeating for the adversary."""
    y = 0.5
    assert budget([0.0] * 6, y) > 100 * budget(list(ALL_PEAKS), y)


# -- the two free terms -----------------------------------------------------

def test_budget_is_nonnegative():
    r = budget_search()
    assert not r["negative_found"], r
    assert r["min_budget"] > 0


def test_budget_nonnegativity_has_the_stated_proof():
    """`int c2 |That|^2 >= k A^2` (energy_F_ge) with `cosh^2 >= 1`.

    Checked in the form it is used: the `kappa = 0` Gram sum alone already
    dominates `k A^2`, and the `2y` Gram sum dominates the `0` one.
    """
    for ts in ([6.517], list(ALL_PEAKS), [0.0] * 5,
               [6.283185307 * i for i in range(8)]):
        k, y = len(ts), 0.5
        g0 = sum(kernel(0.0, a - b) for a in ts for b in ts)
        g2 = sum(kernel(2 * y, a - b) for a in ts for b in ts)
        assert g0 >= k * A_CONST ** 2 - 1e-12, (ts, g0)   # energy_F_ge
        assert g2 >= g0 - 1e-12, (ts, g2, g0)             # cosh^2 >= 1


def test_repulsion_is_a_sum_of_squares():
    rng = random.Random(3)
    for _ in range(30):
        xs = [rng.uniform(-30, 30) for _ in range(rng.randint(0, 8))]
        assert repulsion(xs) >= 0.0


def test_slack_is_at_least_the_cross_term():
    """`slack_k >= Cross`, since B >= 0 and R >= 0."""
    rng = random.Random(21)
    for _ in range(40):
        xs = [rng.uniform(-30, 30) for _ in range(rng.randint(1, 6))]
        ts = [rng.uniform(-30, 30) for _ in range(rng.randint(1, 4))]
        y = rng.uniform(0.05, 0.5)
        assert slack_three_term(xs, ts, y) >= cross(xs, ts, y) - 1e-12


# -- Bochner ----------------------------------------------------------------

def test_kernel_is_positive_definite():
    assert pd_min_eigenvalue() > -1e-9


def test_kernel_is_minus_damage():
    for y, s in ((0.5, 6.517), (0.3, 0.0), (0.5, 20.0)):
        assert kernel(y, s) == pytest.approx(-damage(y, s), abs=1e-15)


def test_kernel_at_zero_depth_is_phi_r_squared():
    """`K_0(v) = phi_r(v)^2`, which is why R is a sum of squares."""
    for v in (0.0, 1.0, 6.517, 20.0):
        assert kernel(0.0, v) == pytest.approx(phi_r(v) ** 2, abs=1e-14)


# -- the recorded negative result -------------------------------------------

def test_cauchy_schwarz_route_is_recorded_as_insufficient():
    rows = cauchy_schwarz_gap()
    assert all(r["ratio"] > 10 for r in rows), rows
    assert max(r["ratio"] for r in rows) > 100


# -- discipline -------------------------------------------------------------

def test_constants_match_the_tree():
    assert A_CONST == pytest.approx(0.9187253698655684, abs=1e-15)
    assert shq(0.5) / 2 == pytest.approx(0.0337542039303, abs=1e-11)
    assert damage(0.5, 6.516999776) == pytest.approx(0.004396424, abs=1e-8)


def test_named_gaps_are_stated():
    joined = " ".join(NAMED_GAPS).lower()
    assert "not proved" in joined
    assert "insufficient" in joined
    assert "rh" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "gram_form.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
