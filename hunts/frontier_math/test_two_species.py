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


def test_the_centre_gas_row_convention_matches_the_form_itself():
    """G4's withdrawal, pinned. `centre_gas_row` sums d >= 1 ONCE; the x4
    factor carries the ordered-pair sum. The net centre-centre cost computed
    directly from the two-species form must converge to that row, not to
    twice it — comparing a two-sided chain sum against this one is what made
    G4 wrong."""
    import math
    from two_species import dam, kpair
    twopi = 2 * math.pi
    ts_c = [d * twopi for d in range(101)]
    rep = 2 * sum(kpair(a - b) for i, a in enumerate(ts_c)
                  for j, b in enumerate(ts_c) if i != j)
    dmg = 2 * sum(dam(1.0, a - b) for i, a in enumerate(ts_c)
                  for j, b in enumerate(ts_c) if i != j)
    net = (dmg - rep) / len(ts_c)
    row = centre_gas_row(twopi)
    assert abs(net - row) < 0.01, (net, row)      # converges to the row
    assert abs(net - 2 * row) > 0.05, "two-sided would be the G4 error"


def test_g4_is_withdrawn_with_its_cause_recorded():
    from two_species import NAMED_GAPS
    g4 = [g for g in NAMED_GAPS if g.startswith("G4")][0]
    assert "WITHDRAWN" in g4 and "2.0027" in g4


def test_centre_gas_summand_is_exactly_minus_four_kappa_on_the_lattice():
    """The transfer this closed form rests on: `two_species`'s centre-gas
    summand and `counting_lemma`'s `kappa` are the same kernel at y = 1/2.

    Verified pointwise rather than argued from the source, because the two
    modules build it through separate `_ghat`/`_gh` implementations.

    The claim is made ON THE LATTICE, and that restriction is not cosmetic:
    `dam` rectifies, so off the lattice the identity fails outright (see the
    companion test). It holds at every `2*pi*d` because the rectification
    never binds there."""
    import math
    import counting_lemma as cl
    from two_species import dam, kpair
    twopi = 2 * math.pi
    for d in range(1, 41):
        s = d * twopi
        summand = 4 * dam(1.0, s) - 4 * kpair(s)
        assert abs(summand + 4 * cl.kappa(s)) < 1e-12, d


def test_the_summand_identity_fails_off_the_lattice_where_dam_clips():
    """The honest boundary of the identity above. At s = 0.3 the raw damage
    is negative, `dam` clips it to zero, and the summand is no longer
    `-4*kappa`. Recorded so nobody reads the lattice identity as global."""
    import counting_lemma as cl
    from gram_form import damage
    from two_species import dam, kpair
    assert damage(1.0, 0.3) < 0                 # the clip fires
    summand = 4 * dam(1.0, 0.3) - 4 * kpair(0.3)
    assert abs(summand + 4 * cl.kappa(0.3)) > 1.0


def test_the_rectification_never_binds_on_the_critical_lattice():
    """`dam` clips at zero, and clipping would break the band-limitedness
    Poisson summation needs. On the `2*pi` lattice it never fires, which is
    what makes the closed form applicable rather than merely suggestive."""
    import math
    from gram_form import damage
    twopi = 2 * math.pi
    assert all(damage(1.0, d * twopi) > 0 for d in range(1, 201))


def test_centre_gas_row_converges_to_the_closed_form():
    """`centre_gas_row` is a truncated sum over a `1/d`-decaying kernel. It
    approaches the closed form from below at `O(1/dmax)` and never reaches
    it, which is why the recorded 0.114045 understates."""
    import math
    from two_species import centre_gas_row, centre_gas_row_closed
    twopi = 2 * math.pi
    exact = centre_gas_row_closed()
    assert abs(exact - 0.11433003938654052) < 1e-15
    prev = None
    for dmax in (200, 2000, 20000):
        got = centre_gas_row(twopi, dmax=dmax)
        assert got < exact, (dmax, got, exact)          # always from below
        if prev is not None:
            assert (exact - got) < (exact - prev) / 5   # O(1/dmax)
        prev = got


def test_the_closed_form_is_claimed_only_at_the_derived_depth():
    import pytest
    from two_species import centre_gas_row_closed
    with pytest.raises(ValueError):
        centre_gas_row_closed(y=0.75)
