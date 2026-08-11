"""Controls for the signed on/off incidence law and the family exclusion.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_incidence_law.py
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

from mpmath import mp, mpc, mpf

sys.path.insert(0, str(Path(__file__).resolve().parent))
from incidence_law import (  # noqa: E402
    Grid,
    Window,
    audit_identities,
    dh_rival_check,
    envelope_scan,
    family_margins,
    law_d_defect,
    online_subgrid_strictness,
    theta_recovery_floor,
)
from interaction_obstruction import MomentMatchedFamily, ScalarFamily  # noqa: E402


def test_law_d_and_e_descend_and_lesion_does_not() -> None:
    """Real identities respond to refinement; the aliasing lesion must not."""
    rec = audit_identities(K_ladder=(100, 200), dps=18)
    for key in ("law_d_ladder", "law_d_deep_diag_ladder", "law_e_ladder"):
        first, last = rec[key][0], rec[key][-1]
        # the omitted tail is O(K^-3): one doubling buys roughly 8x
        assert last < first / 3, (key, first, last)
        assert last < mpf("1e-9"), (key, last)
    lesion = rec["lesion_ladder"]
    assert min(lesion) > mpf("0.01"), lesion
    assert max(lesion) / min(lesion) < 2, lesion
    # translation invariance of the identity
    assert rec["law_d_shifted"] < mpf("1e-9")
    # the planted-wrong diagonal is refuted at exactly its planted offset
    assert abs(rec["decoy_gap"] - rec["decoy_wrong_by"]) < mpf("1e-6")


def test_diagonal_law_is_depth_and_position_blind() -> None:
    """The full-grid bilinear diagonal equals a L^2 at any depth, anywhere."""
    with mp.workdps(18):
        window = Window(8, 1)
        for z in (mpc("0.0", "-0.49"), mpc("6.4", "-0.05"), mpc("-3.3", "0.3")):
            defect = law_d_defect(window, z, z, 250, offset=1.7)
            assert defect < mpf("1e-9"), (z, defect)


def test_envelope_floors_hold_on_random_subgrids() -> None:
    scan = envelope_scan(trials=25, K=120, dps=15, seed=20260811)
    assert scan["worst_floor_margin"] >= 0
    assert scan["worst_ceiling_margin"] >= 0
    assert scan["worst_cross_margin"] >= 0


def test_negative_bilinear_diagonal_needs_depth() -> None:
    """sigma(0) = 0: at depth zero the diagonal envelope is [0, aL^2]."""
    with mp.workdps(18):
        window = Window(8, 1)
        assert abs(window.sigma_sq(0)) < mpf("1e-15")
        # and sigma^2 grows monotonically toward the strip edge
        values = [window.sigma_sq(y) for y in (mpf("0.1"), mpf("0.3"), mpf("0.49"))]
        assert values[0] < values[1] < values[2]
        # convexity majorant from LAW F
        for y in (mpf("0.1"), mpf("0.3"), mpf("0.49")):
            assert window.sigma_sq(y) <= window.sigma_sq_sinh_bound(y)


def test_online_declarations_fail_strictly_on_proper_subgrids() -> None:
    for _, deficit in online_subgrid_strictness(K=150, dps=18):
        assert deficit > 0


def test_family_full_grid_margin_is_exact() -> None:
    for m in (1, 2, 10, 100):
        fam = ScalarFamily(m)
        # declared bilinear pair trace is -2m^2; LAW D pins +2 on the full grid
        assert fam.q == -2 * m * m
        assert Fraction(2) - Fraction(fam.q) == Fraction(2 + 2 * m * m)


def test_family_depth_walls_at_bandwidth_eight() -> None:
    rec1 = family_margins(1, L=8, dps=18)
    rec2 = family_margins(2, L=8, dps=18)
    rec10 = family_margins(10, L=8, k=100_000, dps=18)
    # m = 1 squeaks under the cap but owes depth >= 0.41 of a possible 0.5
    assert not rec1["excluded_at_every_placement"]
    assert rec1["depth_floor"] > mpf("0.4")
    # m >= 2 is unrealisable at any placement at this bandwidth
    assert rec2["excluded_at_every_placement"]
    assert rec10["excluded_at_every_placement"]
    # the dilution reuses the identical bad block, so the walls transfer
    assert rec10["moment_matched_shares_bad_block"]
    assert MomentMatchedFamily(10, 100_000, 0).bad == ScalarFamily(10)


def test_theta_recovery_floor_is_positive_and_decreasing() -> None:
    with mp.workdps(18):
        floors = [theta_recovery_floor(L, dps=18) for L in (8, 16, 24)]
        assert all(f > 0 for f in floors)
        assert floors[0] > floors[1] > floors[2]


def test_laws_hold_at_the_davenport_heilbronn_offline_zero() -> None:
    """The rival passes, as a structural kernel lemma must (MISSION item 1)."""
    rec = dh_rival_check(K=200, dps=15)
    assert abs(rec["depth"] - mpf("0.30851718245663738555")) < mpf("1e-10")
    assert rec["diag_defect"] < mpf("1e-7")
    assert 0 < rec["sigma_sq_at_dh_depth"] < 1


def test_grid_stretch_is_a_real_lesion_knob() -> None:
    """Sanity: stretch = 1 recovers the identity the lesion breaks."""
    with mp.workdps(15):
        window = Window(8, 1)
        z = mpc("0.4", "-0.3")
        healthy = law_d_defect(window, z, z, 150, offset=2.2, stretch=1.0)
        broken = law_d_defect(window, z, z, 150, offset=2.2, stretch=65 / 64)
        assert healthy < mpf("1e-7") < broken
