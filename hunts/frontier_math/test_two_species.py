"""Controls for `two_species` (the restatement and the landscape)."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from two_species import (  # noqa: E402
    LANDSCAPE_RECORD, centre_gas_row, d_zero_is_minus_kpair, dam,
    depth1_windows, far_constant, four_slack_two_species, identity_residual,
    identity_residual_general, kpair, no_damage_radius, signed_field,
)


# -- the identity: if these fail, every reading downstream is wrong ---------

def test_two_species_form_matches_the_direct_slack():
    assert identity_residual(trials=60) < 1e-12


def test_general_depth_form_matches_kpair_identity():
    assert identity_residual_general(trials=30) < 1e-12


def test_depth_zero_damage_is_minus_kpair_exactly():
    assert d_zero_is_minus_kpair() == 0.0


# -- the landscape: pinned numbers ------------------------------------------

def test_no_damage_radius_shrinks_with_depth():
    """28/5 holds at depth 1/2 (left edge 6.0653) and FAILS at depth 1."""
    r_half = no_damage_radius(0.5)
    r_one = no_damage_radius(1.0)
    assert abs(r_half - 6.065319) < 1e-4
    assert abs(r_one - 5.398373) < 1e-4
    assert r_one < 28 / 5 < r_half


def test_depth1_far_constant_exceeds_the_proved_half_depth_one():
    c1 = far_constant(1.0, lo=12.0, hi=14.0, step=1e-3)  # peak is at 12.625
    assert c1 > 637 / 1000, c1


def test_depth1_windows_nest_the_official_table():
    """Depth-1 window 0 must contain the official I_0 = [6.0653, 7.0514]."""
    w0 = depth1_windows(1.0, s_lo=4.0, s_hi=8.0)[0]
    assert w0[0] < 60653 / 10000 and w0[1] > 35257 / 5000


def test_signed_field_is_poisonous_on_the_tight_lattice():
    """An atom at one centre's window peak sits in the next centre's near
    zone: the SIGNED field is deeply negative.  This is why tight centre
    lattices are barren for atoms."""
    f = signed_field([6.517], [0.0, 6.285], 0.5)[0]
    assert f < -0.5, f


def test_centre_gas_row_matches_record():
    rec = LANDSCAPE_RECORD["centre_gas"]
    assert abs(centre_gas_row(rec["worst_uniform_lam"]) - rec["row"]) < 5e-4
