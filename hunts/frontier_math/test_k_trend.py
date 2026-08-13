"""Pins for the k-trend probe.

The cheap pins are the load-bearing ones: a saved witness re-evaluates in
milliseconds, whereas re-running the search costs minutes and would not be a
pin at all (a search is not reproducible across a changed `ks` tuple).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))

import k_trend as T  # noqa: E402
import kpair_identity as K  # noqa: E402


def test_the_saved_witness_reevaluates_to_its_recorded_margin():
    assert T.witness_margin() == pytest.approx(0.265409, abs=1e-6)


def test_the_witness_beats_the_documented_floor():
    """The point of the whole probe: k=12 sits below the k<=6 headline.

    `PROOF-LEDGER.md` quotes `+0.343` with "no downward trend in k". A saved
    k=12 configuration at `+0.2654` is a counterexample to the trend claim,
    though NOT to `k >= 2` itself -- it is still comfortably positive.
    """
    assert T.witness_margin() < min(T.DOCUMENTED.values())
    assert T.witness_margin() > 0


def test_the_witness_is_a_genuine_k_of_twelve_configuration():
    w = T.WITNESS_K12
    assert len(w["ts"]) == 12 and len(w["ys"]) == 12
    assert len(w["xs"]) == 24
    assert all(0.0 < y <= 0.5 for y in w["ys"])


def test_the_witness_depths_sit_on_the_corners():
    """Consistency with the bang-bang probe: 10 of 12 depths are at an end."""
    ys = T.WITNESS_K12["ys"]
    corner = sum(1 for y in ys if y <= 0.02 or y >= 0.48)
    assert corner >= 10


def test_documented_table_is_recorded_verbatim():
    """Guards against the table being edited to match a later run."""
    assert T.DOCUMENTED == {1: 0.4915, 2: 0.3719, 3: 0.3908, 4: 0.3430,
                            6: 0.3618}


@pytest.mark.slow
def test_joint_search_reproduces_the_documented_table():
    """It does, exactly -- so the record is sound and only its RANGE is at issue."""
    out = K.joint_search(ks=(1, 2, 3, 4, 6), restarts=60, n_max=24,
                         seed=20260813)
    for k, v in T.DOCUMENTED.items():
        assert out[k]["relative_margin"] == pytest.approx(v, abs=5e-5)


@pytest.mark.slow
def test_the_stock_search_collapses_to_one_atom_at_large_k():
    """The failure mode that made the first large-k reading worthless."""
    import random

    rng = random.Random(31415)
    best = None
    for _ in range(6):
        s, st = K._anneal(16, 24, rng, 6000, 1.0)
        if best is None or s < best[0]:
            best = (s, st)
    assert len(best[1][0]) <= 3, "expected the atom set to collapse"
