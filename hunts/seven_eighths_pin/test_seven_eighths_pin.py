"""Hunt #139 (opened as #134): every number RESULTS.md states is pinned here.

All tests are live and exact (Python fractions): the reproductions of the paper's
printed constants, the derived identities, the two walls and the exact bound.  The
float scans are not re-run; ``results.json`` holds them and one test checks the
prose quotes it.  Planted faults show that the reproductions can fail.

The last three tests are the landing checks of 2026-10-21 (RESULTS.md section 10).
They run the same exact code at 45-digit rational approximations of the public
closed forms of Guo, Liu and Gao, which are irrational, so they hold to a stated
tolerance rather than exactly.  The block just before them, added the same day with
the prior-art extension, pins in exact arithmetic each translation section 10 states
between this hunt's variables and those of tomoto0, Gao, Guo, Argonaut Math and LW56e2.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as Fr

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import probe  # noqa: E402

RATIONALS = [Fr(0), Fr(1, 12), Fr(1, 7), Fr(1, 6), Fr(3, 17), Fr(1, 5)]


def test_every_printed_constant_is_reproduced():
    reps = probe.reproductions()
    assert len(reps) == 38
    assert [r["name"] for r in reps if not r["ok"]] == []


def test_every_citation_names_a_line():
    assert len(probe.CITATIONS) == 39
    for n, snip in probe.CITATIONS.values():
        assert 1 <= n <= 16677 and snip


@pytest.mark.parametrize("ell", RATIONALS)
@pytest.mark.parametrize("b", [Fr(0), Fr(1, 8), Fr(1, 5)])
@pytest.mark.parametrize("dM", [Fr(0), Fr(-1, 10), Fr(-1, 4)])
def test_target_closed_form(ell, b, dM):
    M = 1 - ell + dM
    assert probe.target(ell, b, M) == probe.target_closed(ell, b, M)
    assert probe.target(ell, b, M) == Fr(5, 6) + (M - 2 * ell) / 12
    g = probe.geometry(ell, b, M)
    assert probe.target(ell, b, M) == 1 - g["h"] / 6 + b / 12
    # b cancels; on the paper's line M + ell = 1 the target is 11/12 - ell/4
    assert probe.target(ell, b, 1 - ell) == Fr(11, 12) - ell / 4


def test_both_stages_lie_on_the_same_line():
    assert probe.target(Fr(0), Fr(0), Fr(1)) == Fr(11, 12)        # Part I
    assert probe.target(Fr(1, 6), Fr(1, 8), Fr(5, 6)) == Fr(7, 8)  # Part II


@pytest.mark.parametrize("ell", RATIONALS)
@pytest.mark.parametrize("b", [Fr(0), Fr(1, 8)])
@pytest.mark.parametrize("dM", [Fr(0), Fr(-1, 10)])
def test_c0_closed_form(ell, b, dM):
    M = 1 - ell + dM
    assert probe.c0(ell, b, M) == probe.c0_closed(ell, b, M)


@pytest.mark.parametrize("ell", [Fr(1, 7), Fr(1, 6), Fr(1, 5)])
@pytest.mark.parametrize("b", [Fr(0), Fr(1, 8)])
@pytest.mark.parametrize("dM", [Fr(0), Fr(-1, 20)])
def test_endpoint_closed_form(ell, b, dM):
    M = 1 - ell + dM
    for delta in (Fr(1, 10), Fr(7, 18), Fr(2, 3)):
        for x in (Fr(0), Fr(1, 4), Fr(1, 2)):
            assert (probe.endpoint_neg_e(ell, b, delta, x, M)
                    == probe.endpoint_neg_e_closed(ell, b, delta, x, M))


def test_paper_geometry_is_the_corner_of_two_low_side_lines():
    """M + ell = 1 (dual length) and M - 2 ell = 1/2 (per-summand losslessness) meet at (1/6, 5/6)."""
    ell, M = Fr(1, 6), Fr(5, 6)
    assert M + ell == 1 and M - 2 * ell == Fr(1, 2)
    assert all(probe.row_loss(ell, M, Fr(k, 60)) == 0 for k in range(0, 11))
    # one step past the corner along M + ell = 1, the last summands lose
    assert probe.row_loss(Fr(1, 6) + Fr(1, 100), 1 - Fr(1, 6) - Fr(1, 100), Fr(1, 6)) > 0


@pytest.mark.parametrize("ell", RATIONALS)
def test_per_summand_reading_forces_seven_eighths(ell):
    """No row loss at d = ell means M - 2 ell >= 1/2, hence target >= 7/8, whatever ell, b."""
    for M in (2 * ell + Fr(1, 2), 2 * ell + Fr(1, 2) + Fr(1, 50)):
        if M + ell > 1:
            continue
        assert probe.low_side_ok_per_summand(ell, M)
        for b in (Fr(0), Fr(1, 8)):
            assert probe.target(ell, b, M) >= Fr(7, 8)
    M = 2 * ell + Fr(1, 2) - Fr(1, 100)
    assert not probe.low_side_ok_per_summand(ell, M)


def test_total_accounting_needs_only_the_d0_summand():
    for ell in RATIONALS:
        M = (1 + 3 * ell) / 2
        for k in range(0, 21):
            d = ell * Fr(k, 20)
            assert -d + probe.row_loss(ell, M, d) / 2 <= 0
        assert probe.row_loss(ell, M - Fr(1, 100), Fr(0)) > 0


def test_floor_corner_is_thirteen_fifteenths():
    fc = probe.floor_corner()
    assert fc["sigma0"] == Fr(13, 15)
    assert fc["C_0"] == 0 and fc["dual_slack"] == 0 and fc["d0_lossless_slack"] == 0
    # the floor rows: E(h) = C_0 + (1 + ell - M/2) delta0 with R = 1, q = delta0/2
    for ell, b, M in [(Fr(1, 6), Fr(1, 8), Fr(5, 6)), (Fr(1, 5), Fr(0), Fr(4, 5))]:
        g = probe.geometry(ell, b, M)
        d0 = Fr(1, 50)
        lhs = probe.high_exponent(ell, b, probe.target(ell, b, M), g["h"], d0, d0 / 2, Fr(1), M=M)
        assert lhs == probe.c0_closed(ell, b, M) + (1 + ell - M / 2) * d0


def test_no_geometry_beats_the_floor_corner():
    """sigma_0 < 13/15 with M + ell <= 1, b >= 0 forces C_0 > 0, on a rational grid."""
    for i in range(0, 41):
        ell = Fr(i, 160)
        for j in range(0, 41):
            M = Fr(j, 40)
            if M + ell > 1:
                continue
            for b in (Fr(0), Fr(1, 20), Fr(1, 8)):
                if probe.target(ell, b, M) < Fr(13, 15):
                    assert probe.c0_closed(ell, b, M) > 0


def test_constant_target_slope():
    """Along M = 12 s - 10 + 2 ell (target fixed), d(-E_*)/d ell = 1 + delta (1/2 - x)."""
    s, b = Fr(7, 8), Fr(1, 10)
    for delta, x in [(Fr(7, 18), Fr(1, 2)), (Fr(1, 5), Fr(1, 4)), (Fr(2, 3), Fr(0))]:
        def g(ell):
            return probe.endpoint_neg_e(ell, b, delta, x, 12 * s - 10 + 2 * ell)
        l1, l2 = Fr(1, 10), Fr(3, 20)
        assert (g(l2) - g(l1)) / (l2 - l1) == 1 + delta * (Fr(1, 2) - x)


def test_robust_bound_and_its_witness():
    delta, x = probe.ROBUST_WITNESS
    rb = probe.robust_single_point_bound(delta, x)
    assert rb == Fr(5655673, 6464057)
    assert Fr(874941, 10**6) < rb < Fr(7, 8)
    # the witness kills every geometry on M + ell = 1 at or below the bound, for any b >= 0
    ell_star = (Fr(11, 12) - rb) * 4
    for ell in (ell_star + Fr(1, 10**7), ell_star + Fr(1, 1000), Fr(1, 5)):
        for b in (Fr(0), Fr(1, 8), Fr(1, 2), Fr(3)):
            assert probe.endpoint_neg_e(ell, b, delta, x, 1 - ell) < 0
    # and every geometry with M + ell < 1 and a target at or below the bound
    for ell in (Fr(1, 10), Fr(3, 20), ell_star):
        M = 12 * rb - 10 + 2 * ell
        if M + ell <= 1:
            for b in (Fr(0), Fr(1, 4)):
                assert probe.endpoint_neg_e(ell, b, delta, x, M) <= 0


def test_gram_limited_bound():
    sb, sd, sx = probe.best_single_point_bound()
    assert sb == Fr(44117, 50422) and sd == Fr(7, 18) and sx == Fr(1, 2)
    assert probe.robust_single_point_bound(*probe.ROBUST_WITNESS) < sb < Fr(7, 8)


def test_paper_value_is_feasible_with_its_own_margin():
    worst = probe.endpoint_neg_e(Fr(1, 6), Fr(1, 8), Fr(79, 204), Fr(1, 2), Fr(5, 6))
    assert worst == Fr(7, 30672) and worst > Fr(49, 440640)


@pytest.mark.parametrize("name,value", [("ZC_PAPER", Fr(1, 3)), ("ALPHA", Fr(4, 5)),
                                        ("C_PAPER", Fr(1, 2))])
def test_planted_fault_is_caught(monkeypatch, name, value):
    """A wrong transcription of one constant must break at least one reproduction."""
    monkeypatch.setattr(probe, name, value)
    if name == "C_PAPER":
        monkeypatch.setattr(probe.d_x, "__defaults__", (value,))
        monkeypatch.setattr(probe.p_x, "__defaults__", (value,))
        monkeypatch.setattr(probe.r_star, "__defaults__", (value,))
        monkeypatch.setattr(probe.endpoint_neg_e, "__defaults__", (None, value))
        monkeypatch.setattr(probe.endpoint_neg_e_closed, "__defaults__", (None, value))
    if name == "ZC_PAPER":
        monkeypatch.setattr(probe.high_exponent, "__defaults__", (value, None))
    assert any(not r["ok"] for r in probe.reproductions())


def test_results_json_matches_the_prose():
    path = os.path.join(HERE, "results.json")
    res = json.load(open(path))
    assert res["robust_bound"]["sigma0"] == "5655673/6464057"
    assert res["gram_limited_bound"]["sigma0"] == "44117/50422"
    assert res["floor_corner"]["sigma0"] == "13/15"
    bf, bt = res["endpoint_best_c_fixed"], res["endpoint_best_c_tied"]
    assert abs(bf["sigma0_c_fixed"] - 0.874958) < 2e-6 and abs(bf["b"] - 0.12) < 1e-9
    # tying c = 1/(3(2 sigma_0 - 1)) to the target moves nothing visible near 7/8
    assert abs(bt["sigma0_c_tied"] - bf["sigma0_c_fixed"]) < 1e-6
    text = open(os.path.join(HERE, "RESULTS.md")).read()
    for s in ("5655673/6464057", "44117/50422", "13/15", "0.874958", "7/30672"):
        assert s in text


# ------------------------ prior-art translations, 2026-10-21 (RESULTS.md section 10)
#
# The prior-art extension compares this hunt with sources that write the same
# quantities in other variables.  These exact checks pin each translation that
# section 10 states, so the comparison does not rest on algebra done in prose.

@pytest.mark.parametrize("l_x", [Fr(1, 3), Fr(17, 48), Fr(3, 8), Fr(2, 5)])
@pytest.mark.parametrize("b", [Fr(0), Fr(1, 12), Fr(1, 8)])
def test_tomoto0_target_floor_exponent_and_corner_in_this_hunts_terms(l_x, b):
    """tomoto0 (2026-10-07) works on M + ell = 1 in (l_x, b): M = 2 l_x + b, ell = 1 - M.

    Its target 2/3 + l_x/2 + b/4 is this hunt's 11/12 - ell/4; its floor-row exponent
    E = 1 - (5/2) l_x - (13/12) b is this hunt's C_0 on that line; and its corner
    condition l_x - ell >= 3/16 (h <= 13/16) is M - 2 ell >= 3/8 + b, the per-summand
    line M - 2 ell = 1/2 only at b = 1/8.
    """
    M = 2 * l_x + b
    ell = 1 - M
    g = probe.geometry(ell, b, M)
    assert g["l_x"] == l_x and g["h"] == 2 - 3 * l_x - b
    assert probe.target(ell, b, M) == Fr(2, 3) + l_x / 2 + b / 4 == Fr(11, 12) - ell / 4
    e_tomoto0 = 1 - Fr(5, 2) * l_x - Fr(13, 12) * b
    assert probe.c0(ell, b, M) == probe.c0_closed(ell, b, M) == e_tomoto0
    assert (l_x - ell) - Fr(3, 16) == ((M - 2 * ell) - (Fr(3, 8) + b)) / 2
    if b == Fr(1, 8):
        assert (l_x - ell >= Fr(3, 16)) == (M - 2 * ell >= Fr(1, 2))
    if (l_x, b) == (Fr(2, 5), Fr(0)):  # tomoto0's limit point is this hunt's floor corner
        assert (ell, M) == (Fr(1, 5), Fr(4, 5)) and e_tomoto0 == 0
        assert probe.target(ell, b, M) == Fr(13, 15)


@pytest.mark.parametrize("ell", [Fr(0), Fr(1, 6), Fr(1001, 6000), Fr(3, 17), Fr(1, 5)])
def test_follow_ups_low_side_loss_is_this_hunts_total_accounting(ell):
    """Gao, Guo and Argonaut Math: row energy M' + (5 ell - 1 + d)_+/4 on M + ell = 1, and
    -d + (5 ell - 1 + d)_+/8 <= -7d/8 once ell <= 1/5.

    That loss is this hunt's row_loss on the line, the absorption is its total accounting
    (only d = 0 must be lossless), and per-summand losslessness on the line is ell <= 1/6,
    the paper's corner.
    """
    M = 1 - ell
    for k in range(13):
        d = ell * Fr(k, 12)
        loss = max(Fr(0), (5 * ell - 1 + d) / 4)
        assert probe.row_loss(ell, M, d) == loss
        assert -d + loss / 2 <= -Fr(7, 8) * d
    assert probe.low_side_ok_total(ell, M)
    assert probe.low_side_ok_per_summand(ell, M) == (ell <= Fr(1, 6))


def test_follow_ups_absorption_fails_just_past_one_fifth():
    ell = Fr(1, 5) + Fr(1, 1000)
    assert not probe.low_side_ok_total(ell, 1 - ell)
    assert probe.row_loss(ell, 1 - ell, Fr(0)) > 0  # the unrescaled summand now loses


def test_lw56e2_and_argonaut_boundaries_against_sigma_star():
    """LW56e2 (2026-10-08): 4374785349/5000000000, which Guo's README calls just above
    sigma*; Argonaut Math (2026-10-08): 7/8 - 1/4000000.  Guo writes ell_* as
    (33 + 8 sqrt 921)/1653, this hunt as 11/551 + 8 sqrt 921/1653.
    """
    with mp.workdps(60):
        sigma_star = _rational((1507 - 2 * mp.sqrt(921)) / 1653)
    lw56e2 = Fr(4374785349, 5000000000)
    assert Fr(8, 10**13) < lw56e2 - sigma_star < Fr(9, 10**13)
    assert Fr(3499999, 4000000) == Fr(7, 8) - Fr(1, 4000000) > lw56e2
    assert Fr(33, 1653) == Fr(11, 551)


# ------------------------------------------------ landing checks, 2026-10-21

HALF = Fr(1, 2)


def _rational(value, digits=45):
    """A rational within 10**-digits of an mpmath value, so probe's exact code can take it."""
    return Fr(int(mp.nint(value * 10**digits)), 10**digits)


def test_gao_boundary_lies_on_this_hunts_target_line():
    """Z. Gao (draft of 2026-10-07): 20999/24000 at ell = 1001/6000, b = 1/8."""
    ell = Fr(1001, 6000)
    assert probe.target(ell, Fr(1, 8), 1 - ell) == Fr(20999, 24000) == Fr(11, 12) - ell / 4


def test_one_witness_bound_at_the_binding_delta_is_the_public_optimum():
    """Guo and Liu (2026-10-08): sigma* = (1507 - 2 sqrt 921)/1653, the re-optimized geometry.

    At x = 1/2 and c = 4/9 the b-coefficient of -E_* vanishes at delta* = (49 - sqrt 921)/48.
    The one-witness bound holds at every witness where that coefficient is <= 0, the
    recorded 223/576 among them, and at delta* it is sigma* itself.  The endpoint
    inequality is tight there, at ell* = 11/551 + 8 sqrt 921/1653 and
    b* = -4/29 + 230 sqrt 921/26709: zero at delta*, a minimum in delta, the cap x = 1/2
    binding.
    """
    with mp.workdps(60):
        r = mp.sqrt(921)
        d_star = _rational((49 - r) / 48)
        sigma_star = _rational((1507 - 2 * r) / 1653)
        ell = _rational(mp.mpf(11) / 551 + 8 * r / 1653)
        b = _rational(-mp.mpf(4) / 29 + 230 * r / 26709)

    def b_coefficient(delta):
        def f(ell_, b_):
            return probe.endpoint_neg_e_closed(ell_, b_, delta, HALF, 1 - ell_)
        return f(Fr(0), Fr(1)) - f(Fr(0), Fr(0))

    eps = Fr(1, 10**12)
    assert b_coefficient(d_star - eps) < 0 < b_coefficient(d_star + eps)
    bound = probe.robust_single_point_bound(d_star - Fr(1, 10**40), HALF)
    assert bound is not None and abs(bound - sigma_star) < Fr(1, 10**35)
    assert probe.robust_single_point_bound(d_star + eps, HALF) is None
    # the recorded bound is valid and looser; the gain over 7/8 is 4.29e-5, not 5.8e-5
    assert probe.robust_single_point_bound(*probe.ROBUST_WITNESS) < bound < Fr(7, 8)
    assert Fr(429, 10**7) < Fr(7, 8) - sigma_star < Fr(430, 10**7)

    assert abs(probe.target(ell, b, 1 - ell) - sigma_star) < Fr(1, 10**40)

    def neg_e(delta, x=HALF):
        return probe.endpoint_neg_e_closed(ell, b, delta, x, 1 - ell)

    assert abs(neg_e(d_star)) < Fr(1, 10**35)
    for step in (Fr(1, 10**3), Fr(1, 10**6)):
        assert neg_e(d_star - step) > 0 and neg_e(d_star + step) > 0
    assert neg_e(d_star, HALF - Fr(1, 10**6)) > neg_e(d_star)
    # the recorded float scan (offset grid 0.01) sits 5.9e-7 above sigma*
    res = json.load(open(os.path.join(HERE, "results.json")))
    gap = res["endpoint_best_c_fixed"]["sigma0_c_fixed"] - float(sigma_star)
    assert 5.8e-7 < gap < 6.0e-7


def test_liu_closed_form_is_the_tight_point_with_the_capacity_tied():
    """B. Liu, arXiv:2610.12234v2 (2026-10-12): B_new = (18 xi + 7)/(18 xi + 9), Guo's sigma_dagger.

    xi is the root of 1188 xi^3 - 2160 xi^2 + 171 xi + 190 in (0.38858, 0.38859), with
    ell_new = (5 - 6 xi)/(9 + 18 xi), b_new below and kappa_new = (18 xi + 5)/(18 xi + 9)
    = 2 B_new - 1, which is section 7's tied capacity c = 1/(3 kappa_0), kappa_0 =
    2 sigma_0 - 1.  With that c this hunt's endpoint formula is zero at delta = xi,
    x = 1/2, a minimum in delta and flat in b, and B_new is on the target line: Liu's xi is
    this hunt's binding delta.
    """
    with mp.workdps(60):
        xi = mp.findroot(lambda t: 1188 * t**3 - 2160 * t**2 + 171 * t + 190, mp.mpf("0.388585"))
        ell = (5 - 6 * xi) / (9 + 18 * xi)
        b = (8 * (3 * xi - 1) * (12 * xi**2 - 40 * xi + 15)
             / (9 * (2 * xi + 1) * (24 * xi**2 - 20 * xi + 5)))
        bound_new = (18 * xi + 7) / (18 * xi + 9)
        kappa_new = (18 * xi + 5) / (18 * xi + 9)
        guo = mp.findroot(lambda s: 7884 * s**3 - 18819 * s**2 + 14643 * s - 3686,
                          mp.mpf("0.874957"))
        sigma_star = (1507 - 2 * mp.sqrt(921)) / 1653
        xi, ell, b, bound_new, kappa_new, guo, sigma_star = (
            _rational(v) for v in (xi, ell, b, bound_new, kappa_new, guo, sigma_star))
    assert Fr(38858, 10**5) < xi < Fr(38859, 10**5)
    assert Fr(8749570194, 10**10) < guo < Fr(8749570195, 10**10)
    assert abs(bound_new - guo) < Fr(1, 10**40)
    assert Fr(50, 10**9) < sigma_star - guo < Fr(51, 10**9)  # the step from sigma* to sigma_dagger
    sigma = probe.target(ell, b, 1 - ell)
    assert abs(sigma - bound_new) < Fr(1, 10**40)
    assert abs(kappa_new - (2 * sigma - 1)) < Fr(1, 10**40)
    c = 1 / (3 * kappa_new)

    def neg_e(delta, b_=b):
        return probe.endpoint_neg_e_closed(ell, b_, delta, HALF, 1 - ell, c)

    assert abs(neg_e(xi)) < Fr(1, 10**35)
    for step in (Fr(1, 10**3), Fr(1, 10**6)):
        assert neg_e(xi - step) > 0 and neg_e(xi + step) > 0
    assert abs(neg_e(xi, b + 1) - neg_e(xi)) < Fr(1, 10**35)  # affine in b, with slope zero
