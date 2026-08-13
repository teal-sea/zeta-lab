"""Controls for `shared_repulsion` (Road B, step 4)."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from shared_repulsion import (  # noqa: E402
    A_CONST, EFFORT_FLOOR, LADDER_RECORD, MODES, NAMED_GAPS, SCAN_RECORD,
    SIZES, anneal, planted_ladder, scan_record, shq, slack, structured,
)


def test_slack_matches_the_kpair_identity():
    """The vectorised evaluator against the reference implementation."""
    from kpair_identity import slack_k
    for xs, ts in (([0.0], [6.517]),
                   ([0.0, 1.3, -6.5], [6.517, -6.517]),
                   ([i * 6.283185307 for i in range(6)], [3.1, 9.4, 15.7])):
        got = slack(xs, ts, 0.5)[0]
        ref = slack_k(xs, [(0.5, t) for t in ts])
        assert got == pytest.approx(ref, abs=1e-10), (got, ref)


def test_constants_match_the_tree():
    assert A_CONST == pytest.approx(0.9187253698655684, abs=1e-15)
    assert shq(0.5) / 2 == pytest.approx(0.0337542039303, abs=1e-11)


# -- the scan ---------------------------------------------------------------

@pytest.mark.slow
def test_structured_families_are_all_positive_at_scale():
    rec = scan_record()
    for m in MODES:
        assert rec[m] > 1.0, (m, rec[m])


@pytest.mark.slow
def test_no_degradation_as_n_over_k_grows():
    """The shared-R worry predicts the margin FALLS as n/k rises."""
    import random
    rng = random.Random(20260813)
    rels = []
    for n, k in ((50, 2), (100, 4), (200, 8), (400, 16)):
        xs, ts = structured(n, k, "atoms_spread_pairs_lattice", rng)
        s, g = slack(xs, ts, 0.5)
        rels.append(s / g)
    assert all(r > 20 for r in rels), rels
    assert rels[-1] >= rels[0] - 0.5      # flat or rising, not falling


def test_extreme_n_over_k_is_still_positive():
    """n/k = 100, the shape the worry is about."""
    import random
    xs, ts = structured(400, 4, "atoms_spread_pairs_lattice",
                        random.Random(1))
    s, g = slack(xs, ts, 0.5)
    assert s > 0 and s / g > 20


# -- the adversary's preference ---------------------------------------------

def test_recorded_worst_has_few_atoms_and_many_pairs():
    """The reverse of what the shared-R argument fears."""
    assert SCAN_RECORD["anneal_worst_n"] < 15
    assert SCAN_RECORD["anneal_worst_k"] > 15
    assert SCAN_RECORD["anneal_worst"] > 0
    assert SCAN_RECORD["anneal_worst"] == pytest.approx(0.2716, abs=1e-4)


def test_many_atom_family_only_wins_once_already_broken():
    """n swings large only at damage scales where the ladder has fired."""
    assert LADDER_RECORD[2.5] < 0 and LADDER_RECORD[3.0] < 0
    assert LADDER_RECORD[1.0] > 0 and LADDER_RECORD[1.5] > 0


# -- the control, which is what makes the above mean anything ---------------

def test_ladder_record_is_clean_at_one_and_fires_at_two():
    assert LADDER_RECORD[1.0] > 0
    assert LADDER_RECORD[2.0] < 0
    assert LADDER_RECORD[3.0] < LADDER_RECORD[2.0]


def test_effort_floor_is_recorded_and_is_a_real_floor():
    """Power is effort-dependent; below the floor the scan means nothing.

    This pins the negative result: at reduced effort the x2.0 rung does
    NOT fire, so any verdict taken at that effort is uninformative.
    """
    assert EFFORT_FLOOR[(6, 5000, 1)] > 0        # no power
    assert EFFORT_FLOOR[(20, 5000, 1)] > 0       # still no power
    assert EFFORT_FLOOR[(20, 12000, 1)] > 0      # still no power, but close
    assert EFFORT_FLOOR[(20, 12000, 3)] < 0      # power only here
    assert EFFORT_FLOOR[(20, 12000, 3)] == pytest.approx(
        LADDER_RECORD[2.0], abs=1e-6)


@pytest.mark.slow
def test_reduced_effort_really_lacks_power():
    """Reproduce the floor's top row: 20 x 5000 must NOT fire at x2.0."""
    b = anneal(n_max=120, k_max=30, iters=5000, restarts=20, seed=99,
               damage_scale=2.0)
    assert b[0] > 0, b
    assert b[0] == pytest.approx(EFFORT_FLOOR[(20, 5000, 1)], abs=1e-3)


@pytest.mark.slow
def test_planted_control_has_power_at_the_documented_effort():
    """Best of 3 seeds at 20 x 12000 must fire at x2.0."""
    best = None
    for seed in (99, 7, 20260813):
        b = anneal(n_max=120, k_max=30, iters=12000, restarts=20, seed=seed,
                   damage_scale=2.0)
        if best is None or b[0] < best[0]:
            best = b
    assert best[0] < 0, best


@pytest.mark.slow
def test_anneal_finds_nothing_negative_honestly():
    b = anneal(n_max=80, k_max=25, iters=5000, restarts=6)
    assert b[0] > 0, b


# -- discipline -------------------------------------------------------------

def test_named_gaps_state_the_upper_bound_caveat():
    joined = " ".join(NAMED_GAPS).lower()
    assert "upper bound" in joined
    assert "drifts down" in joined
    assert "not a proof" in joined
    assert "rh" in joined


def test_named_gaps_record_the_effort_floor_and_the_scratchpad_slip():
    """S4/S4b must survive: both negative results are part of the record."""
    joined = " ".join(NAMED_GAPS)
    assert "EFFORT-DEPENDENT" in joined
    assert "does not fire" in joined
    assert "0.2651" in joined and "0.0023" in joined
    assert "SCRATCHPAD" in joined and "-0.5954" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "shared_repulsion.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
