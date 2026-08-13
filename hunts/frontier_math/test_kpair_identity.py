"""Controls for `kpair_identity`.

The load-bearing test is `test_identity_matches_definition_route`: if the
k-pair slack formula is wrong, every reading in the module is wrong, and
the definition route (quadrature against `c2`) shares no code with it.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from kpair_identity import (  # noqa: E402
    A_CONST, COINCIDENT_SHIELD, IDENTITY_CASES, NAMED_GAPS, PEAKS,
    SEARCH_RECORD, damage, identity_residual, joint_search,
    margin_definition, phi_r, planted_fault_ladder, shq, slack_k,
    spread_lattice_scan, stack_seen_by_every_pair, stacked_centres,
)


# -- the identity -----------------------------------------------------------

@pytest.mark.parametrize("xs,pairs", IDENTITY_CASES)
def test_identity_matches_definition_route(xs, pairs):
    """`margin = (4/A^2) slack_k` against independent quadrature."""
    m = float(margin_definition(xs, pairs, dps=25))
    pred = 4 / A_CONST ** 2 * slack_k(xs, pairs)
    assert abs(m - pred) < 1e-12, f"{m} vs {pred}"


def test_identity_residual_is_machine_precision():
    assert identity_residual(dps=25) < 1e-12


def test_k_one_reduces_to_the_single_pair_slack():
    """At k=1 the inter-pair term is empty and this is EForm3's slack."""
    xs, y, t = [6.517, 6.6, -6.5], 0.5, 0.0
    dam = sum(damage(y, x - t) for x in xs)
    rel = sum(phi_r(xs[a] - xs[b]) ** 2
              for a in range(3) for b in range(a + 1, 3)) / 400
    assert slack_k(xs, [(y, t)]) == pytest.approx(shq(y) / 2 - dam + rel, abs=1e-15)


def test_constants_match_the_tree():
    assert A_CONST == pytest.approx(0.9187253698655684, abs=1e-15)
    assert shq(0.5) / 2 == pytest.approx(0.03375420393, abs=1e-10)
    assert damage(0.5, PEAKS[0]) == pytest.approx(0.004396424, abs=1e-8)


# -- the two adversary routes ----------------------------------------------

def test_damage_per_gain_falls_when_centres_spread():
    """Only two top-peak positions exist, so damage/k cannot stay maximal."""
    rows = {r["k"]: r for r in stack_seen_by_every_pair(ks=(1, 2, 4, 8, 12),
                                                       ms=(8,))}
    assert rows[1]["dam_over_gain"] == pytest.approx(1.0420, abs=2e-3)
    assert rows[2]["dam_over_gain"] == pytest.approx(rows[1]["dam_over_gain"],
                                                     abs=2e-3)
    for a, b in ((2, 4), (4, 8), (8, 12)):
        assert rows[b]["dam_over_gain"] < rows[a]["dam_over_gain"]
    assert rows[12]["dam_over_gain"] < 0.30


def test_every_spread_configuration_has_positive_slack():
    for r in stack_seen_by_every_pair():
        assert r["slack"] > 0, r


def test_coincident_centres_shield_rather_than_help_the_adversary():
    """`D(2y,0)+D(0,0) < 0`, so it enters `slack_k` as a positive gain."""
    assert COINCIDENT_SHIELD > 1.7
    assert COINCIDENT_SHIELD == pytest.approx(1.7556, abs=1e-3)
    rows = {(r["k"], r["m"]): r for r in stacked_centres()}
    # the per-pair shield grows with k, so stacking is self-defeating
    assert rows[(8, 8)]["inter_per_pair"] > rows[(2, 8)]["inter_per_pair"] > 0
    assert rows[(8, 8)]["slack"] > 10 * rows[(2, 8)]["slack"]


def test_spread_lattice_scan_stays_positive():
    rows = spread_lattice_scan()
    assert all(r["slack"] > 0 for r in rows)
    assert min(r["slack_per_pair"] for r in rows) > 0.02


# -- the search and its power ----------------------------------------------

@pytest.mark.slow
def test_joint_search_finds_no_violation():
    out = joint_search(ks=(1, 2, 4), restarts=12, iters=2500)
    assert out["worst"] > 0.25, out


@pytest.mark.slow
def test_planted_fault_has_power_and_the_right_threshold():
    """A search that cannot find negatives when they exist proves nothing.

    The honest worst relative margin `r` predicts the first negative at
    `1/(1-r)`; the ladder must be clean at 1.0 and negative by 2.0.
    """
    rows = planted_fault_ladder(scales=(1.0, 2.0), restarts=8)
    honest = rows[0]
    inflated = rows[1]
    assert honest["damage_scale"] == 1.0 and not honest["fires"]
    assert inflated["fires"], "detector has no power"
    assert 1.0 / (1.0 - honest["worst"]) < 2.5


def test_relative_objective_does_not_collapse_at_small_depth():
    """Why the search minimises the ratio: the absolute slack -> 0 as y -> 0
    for the trivial reason that gain, damage and repulsion all do."""
    xs = [0.0]
    small = slack_k(xs, [(0.01, PEAKS[0])])
    big = slack_k(xs, [(0.5, PEAKS[0])])
    assert small < big / 100          # absolute slack collapses
    rs = slack_k(xs, [(0.01, PEAKS[0])], relative=True)
    rb = slack_k(xs, [(0.5, PEAKS[0])], relative=True)
    assert rs > rb                    # relative margin does not


def test_search_record_is_internally_consistent():
    r = SEARCH_RECORD
    assert r["worst"] == min(r["relative_margin"].values())
    assert r["predicted_break_scale"] == pytest.approx(
        1 / (1 - r["worst"]), rel=1e-3)
    # the planted ladder must first fire at or just below the prediction
    assert r["planted_first_negative_at"] <= r["predicted_break_scale"]
    assert r["planted_first_negative_at"] > 1.0


def test_no_downward_trend_in_k():
    """The concern was `relief/k -> 0`; the record must not show decay."""
    rec = SEARCH_RECORD["relative_margin"]
    assert rec[6] > 0.3 and rec[4] > 0.3
    assert rec[6] > rec[4]


# -- discipline -------------------------------------------------------------

def test_named_gaps_are_stated():
    assert len(NAMED_GAPS) >= 5
    joined = " ".join(NAMED_GAPS).lower()
    assert "not proved" in joined
    assert "rh" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "kpair_identity.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
