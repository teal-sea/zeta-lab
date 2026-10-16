"""Hunt #134: every number RESULTS.md states is pinned here.

All tests are live and exact (Python fractions): the reproductions of the paper's
printed constants, the derived identities, the two walls and the exact bound.  The
float scans are not re-run; ``results.json`` holds them and the last test checks the
prose quotes it.  Planted faults show that the reproductions can fail.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as Fr

import pytest

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
