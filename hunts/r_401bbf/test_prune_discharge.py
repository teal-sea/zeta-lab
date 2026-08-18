"""Pins for the discharge of `zone_trade`'s inner prune.

Fast tier: the full 13200-cell table is `probe.py` run end to end (about six
minutes).  What is pinned here is the part a suite can afford: that the
exhaustive solver agrees with the published search on the binding cells and on
random components of the table's shape, that it is a genuine detector (it sees
a planted bite), and that the hypothesis making the prune sound holds by
construction rather than by luck.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
sys.path.insert(0, str(_HERE.parent / "frontier_math"))

import k2_closure as K   # noqa: E402
import probe as P        # noqa: E402

TOL = 1e-14


def test_exhaustive_agrees_with_zone_trade_on_random_components():
    """No cut in the published search may cost the adversary anything."""
    rec = P.control_agreement()
    assert rec["instances_where_exact_lower"] == 0
    assert rec["max_exact_minus_pruned"] < TOL


def test_dfs_transcription_matches_the_published_search():
    """The switchable transcription must BE `zone_trade`, or the planted
    control below tests a strawman."""
    assert P.control_transcription()["max_abs_difference"] == 0.0


def test_planted_bite_is_detected():
    """DETECTOR POWER.  One negative pair charge, the exact hypothesis the
    soundness argument needs, and the prune must be seen to bite."""
    pb = P.control_planted_bite()
    assert pb["prune_bites"]
    assert pb["exhaustive"] > pb["both_cuts"] + 1e-6
    assert pb["both_off_equals_exhaustive"]


def test_pair_charges_are_nonnegative_by_construction():
    """`Kpair(u) = Re(ghat(0,u))**2 >= 0`, so the charge matrix is nonnegative
    for every input, not merely for the ones this table happens to build."""
    us = np.linspace(0.0, 6.0, 601)
    assert float(K._kpair(us).min()) >= 0.0


@pytest.mark.parametrize("ta", [6.30, 6.32, 12.84, 63.40, 126.04])
@pytest.mark.parametrize("signed", [True, False])
def test_binding_cells_unchanged_by_exhaustive_trade(ta, signed):
    """The published margins survive removing every cut from the trade."""
    m_p, m_e, near_p, near_e, zmax = P.cell_pair(ta, ta + 0.02, signed=signed)
    assert abs(near_e - near_p) < TOL
    assert m_e > 0.0
    assert zmax <= 8, "component wider than the enumeration was sized for"


def test_published_binding_margins_reproduced():
    """Guards against the probe drifting off the table it is auditing."""
    m_signed, _, _, _, _ = P.cell_pair(12.84, 12.86, signed=True)
    m_unsigned, _, _, _, _ = P.cell_pair(6.32, 6.34, signed=False)
    assert m_signed == pytest.approx(K.TABLE_RECORD["signed"]["worst_margin"],
                                     abs=1e-6)
    assert m_unsigned == pytest.approx(
        K.TABLE_RECORD["unsigned"]["worst_margin"], abs=1e-6)
