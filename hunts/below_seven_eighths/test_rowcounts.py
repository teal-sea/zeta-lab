"""Hunt #136, lane rowcounts: every number ROWCOUNTS.md states is pinned here.

The exact tests use Python fractions and sympy; the measured ones (the evaluator with
capacity caps) use float grids and carry explicit tolerances.  Planted faults show that the
reproductions, the enumerations, the evaluator and the page test can fail.  The page test
checks whole table rows and maps every decimal on the page to a pinned value, so a wrong
cell cannot hide behind a correct copy of the same number elsewhere on the page.
"""

from __future__ import annotations

import os
import re
import sys
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import rowcounts as rc  # noqa: E402

PAPER = rc.PAPER
HALF = Fr(1, 2)
MD = Path(HERE) / "ROWCOUNTS.md"

# ----------------------------------------------------------- pinned values shared with the page

SIGMA_STAR = 0.87495706979916874
SIGMA_DAGGER = 0.8749570194200989
WALL = 0.8725498721285638
WALL_PAPER_DHALF = 0.8740524833750909
ALPHA0_PAPER_DHALF = Fr(84031, 96156)
SHADOW = {"alpha": 0.0047006134689794, "c_M": -0.0095710836631790, "c_P": -0.0019776984099936}
BREAK_EVEN = {("alpha", 1): (0.8186903585209, -0.017572), ("c_M", 1): (0.5073016701988, 0.014603),
              ("c_P", 1): (0.2565018831557, 0.154258), ("alpha", 2): (0.8031897029848, -0.036172),
              ("c_M", 2): (0.5152786070976, 0.030557), ("c_P", 2): (0.2916822892735, 0.312570)}
BE_ALPHA_LINE = (0.8028731275017, -0.036552)
EXCESS = {Fr(3, 4): 0.8728554191659, Fr(1, 2): 0.8707660092714, Fr(1, 4): 0.8687000048273}
FIXED_B = {Fr(-1, 50): 0.8723954793115, Fr(-1, 20): 0.8722121220468}
SIGMA_CP_5_22 = 0.874947027273891
#: the measured values quoted on the page (full-resolution evaluator)
M_CM1 = 0.8734852
M_CM1_SECOND_OFF = 0.8731593
#: what the first version printed for it, from a coarser b-search
M_CM1_FIRST_VERSION = 0.8731594
M_CP1 = 0.8734556
M_PAPER_DHALF = 0.8740525


# ------------------------------------------------------------------ citations and reproductions

def test_citations_name_lines_and_sit_on_them_when_the_paper_is_present():
    assert len(rc.CITATIONS) == 98
    for n, snip in rc.CITATIONS.values():
        assert 1 <= n <= 16677 and snip
    if not rc.PAPER_DEFAULT.is_file():
        pytest.skip("pinned paper.tex not present on this machine")
    assert rc.verify_citations(rc.PAPER_DEFAULT) == []


def test_every_row_count_constant_is_reproduced():
    reps = rc.reproductions()
    assert len(reps) == 39
    assert [r["name"] for r in reps if not r["ok"]] == []


def test_endpoint_constants_are_reproduced_and_can_fail():
    eps = rc.endpoint_reproductions()
    assert len(eps) == 10 and [r["name"] for r in eps if not r["ok"]] == []
    bad = [r["cite"] for r in rc.endpoint_reproductions(fault="R_no_floor") if not r["ok"]]
    assert sorted(bad) == sorted(["R_76_75_floor", "slope_101_150", "E_half", "E_half_bound"])
    # the Bernstein check of that bound fails just above the attained minimum 7/30672
    ell, M, b = Fr(1, 6), Fr(5, 6), Fr(1, 8)
    over = Fr(7, 30672) + Fr(1, 10**6)
    poly = rc._add2(rc.endpoint_polynomial(PAPER, ell, M, b), rc._scale2(rc.j_polynomial(PAPER), -over))
    assert not rc.bernstein_positive(poly, (Fr(0), Fr(5, 6), Fr(0), HALF))["positive"]
    assert rc.floor_value(ell, M, b) == Fr(-7, 1200)  # the printed floor bound, line 15847


def test_planted_input_faults_break_the_reproductions():
    """The reproductions can fail: a wrong marked capacity or slope is caught."""
    bad_cm = [r for r in rc.reproductions(replace(PAPER, c_M=Fr(1, 3))) if not r["ok"]]
    bad_al = [r for r in rc.reproductions(replace(PAPER, alpha=Fr(4, 5))) if not r["ok"]]
    bad_cp = [r for r in rc.reproductions(replace(PAPER, c_P=Fr(1, 4))) if not r["ok"]]
    assert len(bad_cm) == 15 and len(bad_al) == 2 and len(bad_cp) > 0


GENERAL = [PAPER, rc.Inputs(Fr(4, 5), Fr(3, 5), Fr(1, 4)), rc.Inputs(Fr(2, 3), Fr(1, 3), Fr(1, 3)),
           rc.Inputs(Fr(5, 6), Fr(9, 10), Fr(9, 10))]


@pytest.mark.parametrize("inp", GENERAL)
def test_general_inputs_crossing_is_independent_of_r_and_balances(inp):
    """R_short is the common value at the crossing for any (alpha, c_M, c_P), and R_* = L(t)."""
    for dl in (Fr(1, 10), Fr(7, 18), Fr(3, 5)):
        if dl >= inp.alpha:
            continue
        for x in (Fr(0), Fr(1, 4), HALF):
            for t in (Fr(1), Fr(9, 8), Fr(5, 4), Fr(3, 2)):
                rcx = rc.r_cross(x, t, inp)
                assert rc.count_marked(dl, x, rcx, inp) == rc.count_plain(dl, x, t - rcx, inp) \
                    == rc.r_short(dl, x, t, inp)
            assert rc.r_cross(x, Fr(3, 2), inp) == 1
            tb = rc.t_balance(dl, x, inp)
            assert rc.r_star(dl, x, inp) == rc.l_count(dl, tb, inp) == rc.r_short(dl, x, tb, inp)


@pytest.mark.parametrize("inp", GENERAL[:3])
def test_endpoint_transcription_equals_closed_form(inp):
    for ell, b, dM in ((Fr(1, 6), Fr(1, 8), Fr(0)), (Fr(1, 5), Fr(0), Fr(-1, 20)), (Fr(1, 7), Fr(1, 5), Fr(0))):
        M = 1 - ell + dM
        for dl in (Fr(1, 10), Fr(7, 18), Fr(2, 3)):
            for x in (Fr(0), Fr(1, 4), HALF):
                assert rc.neg_e_star(dl, x, ell, M, b, inp) == rc.neg_e_star_transcribed(dl, x, ell, M, b, inp)


def test_hunt_134_numbers_are_recomputed():
    n = rc.numbers_from_134()
    assert n["paper_target"] == Fr(7, 8) and n["paper_C0"] == Fr(-1, 48)
    assert n["paper_worst"] == Fr(7, 30672)
    assert n["floor_corner"] == Fr(13, 15) and n["floor_corner_C0"] == 0
    assert n["robust_bound"] == Fr(5655673, 6464057)


def test_cross_check_with_hunt_134_probe_when_available(tmp_path):
    import subprocess
    try:
        src = subprocess.run(["git", "show", "origin/claude/hunt-134-seven-eighths-pin:"
                              "hunts/seven_eighths_pin/probe.py"], cwd=HERE, capture_output=True,
                             text=True, check=True).stdout
    except Exception:  # pragma: no cover - the branch may be absent
        pytest.skip("hunt #134 branch not available")
    path = tmp_path / "probe134.py"
    path.write_text(src)
    cc = rc.cross_check_134(path)
    assert cc == {"points": 162, "mismatches": 0}


# --------------------------------------------------------------------------- the exact evaluator

@pytest.fixture(scope="module")
def opt():
    return rc.slice_optimum(PAPER)


def test_slice_optimum_is_a_quadratic_irrationality(opt):
    sp = rc._sympy()
    assert sp.simplify(opt["sigma"] - (sp.Rational(1507, 1653) - 2 * sp.sqrt(921) / 1653)) == 0
    assert sp.simplify(opt["ell"] - (sp.Rational(11, 551) + 8 * sp.sqrt(921) / 1653)) == 0
    assert sp.simplify(opt["b"] - (sp.Rational(-4, 29) + 230 * sp.sqrt(921) / 26709)) == 0
    assert opt["minpoly_sigma"] == [4959, -9042, 4115]
    assert str(opt["sigma_float"]).startswith("0.87495706979916874")
    assert abs(float(opt["delta_v"]) - 0.38858371227110341) < 1e-15
    assert abs(float(opt["ell"]) - 0.16683839) < 5e-9 and abs(float(opt["b"]) - 0.12340544) < 5e-9
    assert opt["disc_bb"] > 0 and opt["u_at_opt"] > 0  # convex in b; N(0) > 0


@pytest.fixture(scope="module")
def br():
    return rc.bracket(PAPER)


def test_exact_bracket_around_the_slice_optimum(br, opt):
    lo, up = br["sigma_lp"], br["sigma_up"]
    assert isinstance(lo, Fr) and isinstance(up, Fr)
    star = float(opt["sigma_float"])
    assert float(lo) <= star <= float(up)
    assert up - lo < Fr(3, 10**9)
    assert br["feasibility"]["feasible"] and br["feasibility"]["boxes"] == 51
    side = br["side"]
    assert {k for k, v in side.items() if not v} == {"low_paper"}  # needs total accounting
    assert side["marked_second"] and side["d_le_half"] and side["b_nonneg"] and side["floor"]
    # the quoted widths: sigma* - sigma_LP is about 5e-23, sigma_up - sigma* about 2.5e-9
    import mpmath as mp
    with mp.workdps(50):
        star_mp = (mp.mpf(1507) - 2 * mp.sqrt(921)) / 1653
        below = star_mp - mp.mpf(lo.numerator) / lo.denominator
        above = mp.mpf(up.numerator) / up.denominator - star_mp
    assert mp.mpf("4e-23") < below < mp.mpf("5e-23")
    assert abs(above - mp.mpf("2.5e-9")) < mp.mpf("1e-17")


def test_side_condition_values_quoted_on_the_page(br):
    ell, b = br["ell_up"], br["b_up"]
    M = 1 - ell
    assert abs(float(rc.c0(ell, M, b)) + 0.0209) < 5e-5
    assert abs(float(rc.floor_value(ell, M, b)) + 0.0059) < 5e-5
    new, old = rc.e_half_max(ell, M, b), rc.e_half_max(ell, M, b, R_const=Fr(1))
    assert abs(float(new) + 0.0027) < 5e-5 and abs(float(old) + 0.0093) < 5e-5
    assert abs(float(old / new) - 3.5) < 0.05
    assert abs(float(ell / rc.h_of(ell, M, b)) - 0.2055) < 5e-5 and ell / rc.h_of(ell, M, b) > Fr(7, 37)
    assert rc.e_half_max_balanced(ell, M, b)["negative"]


def test_tied_capacity_reproduces_guo(opt):
    """With c_P = 1/(6(2 sigma - 1)) the optimum is the cubic root that matches Guo's sigma_dagger."""
    ot = rc.slice_optimum(PAPER, tied=True)
    assert ot["minpoly_sigma"] == [7884, -18819, 14643, -3686]
    s = ot["sigma_float"]
    assert str(s).startswith("0.87495701942009894")
    assert str(s).startswith(rc.GUO_SIGMA_DAGGER)
    gain = float(s - opt["sigma_float"])
    assert -5.04e-8 < gain < -5.03e-8
    assert 2 * float(s) - 1 < 0.75  # Lemma plain is stated only for kappa >= 3/4 (line 12532)
    assert abs((2 * float(s) - 1) - 0.74991) < 5e-6
    bt = rc.bracket(PAPER, tied=True)
    assert bt["feasibility"]["feasible"] and float(bt["sigma_lp"]) <= float(s) <= float(bt["sigma_up"])


def test_x0_wall_is_independent_of_the_capacities():
    sp = rc._sympy()
    w = rc.slice_optimum(PAPER, x=Fr(0))
    assert sp.simplify(w["sigma"] - (sp.Rational(101, 108) - sp.sqrt(286) / 270)) == 0
    assert w["minpoly_sigma"] == [10800, -20200, 9403] and w["b"] == 0
    assert str(w["sigma_float"]).startswith("0.8725498721285638")
    for inp in (replace(PAPER, c_M=Fr(1)), replace(PAPER, c_M=Fr(1), c_P=Fr(1))):
        assert rc.slice_optimum(inp, x=Fr(0))["sigma_float"] == w["sigma_float"]
    # with perfect capacities the x = 0 slice is the binding one
    ideal = replace(PAPER, c_M=Fr(1), c_P=Fr(1))
    for x in (Fr(1, 10), Fr(1, 4), Fr(2, 5)):
        assert rc.slice_optimum(ideal, x=x)["sigma_float"] < w["sigma_float"]
    # at the paper's inputs it is slack
    assert w["sigma_float"] < rc.slice_optimum(PAPER)["sigma_float"]


def test_gram_hypothesis_b_nonnegative_is_active_at_the_wall():
    """b >= 0 (P_a >= 1, line 8345) binds on the x = 0 slice; a negative b would lower the wall."""
    assert abs(float(rc.slice_fixed_b(PAPER, Fr(0), Fr(0))["sigma_float"]) - WALL) < 1e-15
    prev = WALL
    for bb, want in FIXED_B.items():
        s = rc.slice_fixed_b(PAPER, bb, Fr(0))
        v = float(s["sigma_float"])
        assert abs(v - want) < 1e-12 and v < prev
        prev = v
        ell = Fr(str(s["ell"].evalf(40))).limit_denominator(10**15)
        assert rc.e_half_max_balanced(ell, 1 - ell, bb)["negative"]  # rows d <= 1/2 recounted


def test_shadow_prices_two_routes():
    sp_ = rc.shadow_prices(PAPER)
    for k, v in SHADOW.items():
        assert abs(sp_[k + "_float"] - v) < 1e-13
    assert abs(sp_["db_at_opt"]) < 1e-25
    # per one percent of each input (a linearization): about 3.9, 4.8 and 0.44 x 1e-5
    per_pct = [abs(sp_[k + "_float"]) * float(getattr(PAPER, k)) / 100 for k in ("alpha", "c_M", "c_P")]
    assert [round(v * 1e5, 2) for v in per_pct] == [3.92, 4.79, 0.44]
    h = Fr(1, 10**6)
    for name, val in SHADOW.items():
        base = getattr(PAPER, name)
        hi = rc.sigma_slice_float(replace(PAPER, **{name: base + h}))
        lo = rc.sigma_slice_float(replace(PAPER, **{name: base - h}))
        assert abs((hi - lo) / (2 * float(h)) - val) < 1e-8


@pytest.mark.parametrize("key", sorted(BREAK_EVEN))
def test_break_even_values_and_their_side_conditions(key):
    param, which = key
    goal = rc.XU_SANG if which == 1 else rc.TRACKER_RECORD
    value, rel = BREAK_EVEN[key]
    be = rc.break_even_exact(param, goal=goal)
    assert abs(be["theta"] - value) < 1e-12 and abs(be["relative_change"] - rel) < 1e-6
    assert be["degree"] == (7 if param == "alpha" else 8)
    assert abs(be["check_sigma"] - float(goal)) < 1e-12
    assert be["marked_second_slack"]  # c_M stays below 37/65, so the closed form is exact
    o = rc.slice_optimum(replace(PAPER, **{param: Fr(be["theta"]).limit_denominator(10**12)}))
    ell = Fr(str(o["ell"].evalf(40))).limit_denominator(10**18)
    b = Fr(str(o["b"].evalf(40))).limit_denominator(10**18)
    # the paper's count of the rows d <= 1/2 fails only for alpha to the tracker record
    assert (rc.e_half_max(ell, 1 - ell, b) < 0) == (key != ("alpha", 2))
    inp = replace(PAPER, **{param: Fr(be["theta"]).limit_denominator(10**12)})
    assert rc.e_half_max_balanced(ell, 1 - ell, b, inp)["negative"]


def test_alpha_break_even_with_the_paper_count_of_the_rows_d_half():
    be = rc.break_even_on_dhalf_line("alpha", rc.TRACKER_RECORD)
    assert abs(be["theta"] - BE_ALPHA_LINE[0]) < 1e-12 and abs(be["relative_change"] - BE_ALPHA_LINE[1]) < 1e-6
    assert len(be["poly"]) == 3  # an exact quadratic
    lg = Fr(11, 3) - 4 * rc.TRACKER_RECORD
    bl = Fr(be["b_line"].p, be["b_line"].q)
    assert rc.e_half(Fr(5, 6), lg, 1 - lg, bl) == 0 and rc.e_half(rc.DELTA0, lg, 1 - lg, bl) < 0
    assert be["theta"] < BREAK_EVEN[("alpha", 2)][0]  # the paper's count needs the smaller alpha


def test_the_line_break_even_sits_on_the_line():
    """At the line break-even the stationary b lies below the line, so the line is where the optimum is."""
    sp = rc._sympy()
    be = rc.break_even_on_dhalf_line("alpha", rc.TRACKER_RECORD)
    th = Fr(be["theta"]).limit_denominator(10**14)
    (ell, b, d), (A2, A1, A0), _ = rc._slice_coeffs(rc._sym_rat(th), sp.Rational(1, 2), sp.Rational(2, 9))
    disc = sp.expand(A1 ** 2 - 4 * A0 * A2)
    lg = sp.Rational(11, 3) - 4 * rc._sym_rat(rc.TRACKER_RECORD)
    b_stat = sp.solve(sp.diff(disc, b).subs(ell, lg), b)[0]
    assert float(b_stat) < float(be["b_line"])
    at = {ell: lg, b: be["b_line"]}
    scale = float((A1 ** 2).subs(at) + abs((4 * A0 * A2).subs(at)))
    assert abs(float(disc.subs(at))) < 1e-10 * scale  # zero up to the rational rounding of theta
    a2 = float(A2.subs({ell: lg, b: be["b_line"]}))
    dv = -float(A1.subs({ell: lg, b: be["b_line"]})) / (2 * a2)
    assert a2 > 0 and 0 < dv < float(th)


def test_paper_count_of_the_rows_d_half_fails_at_every_recounted_optimum():
    """The third column of the page's table needs the recount; the paper's count fails at each of
    its optima, and no input reaches below 84031/96156 under the paper's count (two input-free lines)."""
    geoms = []
    for inp in (replace(PAPER, c_M=Fr(1)), replace(PAPER, c_P=Fr(1)), replace(PAPER, c_M=Fr(1), c_P=Fr(1))):
        g = rc.sigma_general(inp, d_half="balanced", **COARSE)
        ell = Fr(4) * (Fr(11, 12) - Fr(g["sigma"]).limit_denominator(10**12))
        geoms.append((inp, ell, Fr(g["b"]).limit_denominator(10**12)))
    a0 = replace(PAPER, alpha=Fr(0))
    geoms += [(a0, Fr(3, 16), Fr(0)), (a0, Fr(1, 5), Fr(0))]
    for inp, ell, b in geoms:
        assert rc.e_half_max(ell, 1 - ell, b) > 0, (inp, ell, b)
        assert rc.e_half_max_balanced(ell, 1 - ell, b, inp)["negative"], (inp, ell, b)
    # the floor is slack at every capacity optimum, recounted or on the paper's line
    w = rc.slice_on_dhalf_line(PAPER, Fr(0))
    line_pt = (Fr(str(w["ell"].evalf(40))).limit_denominator(10**15), Fr(str(w["b"].evalf(40))).limit_denominator(10**15))
    for ell, b in [(g[1], g[2]) for g in geoms[:3]] + [line_pt]:
        assert rc.floor_value(ell, 1 - ell, b) < 0
    # the floor caps ell decreasingly in b, the line increasingly, and both ignore the inputs
    L0, k = rc.d_half_line()
    floor_ell = lambda bb: (Fr(1, 4) - rc.DELTA0 / 2 - bb / 6) / (Fr(5, 4) + Fr(3, 2) * rc.DELTA0)  # noqa: E731
    assert all(rc.floor_value(floor_ell(bb), 1 - floor_ell(bb), bb) == 0 for bb in (Fr(0), Fr(1, 10)))
    assert floor_ell(Fr(1, 10)) < floor_ell(Fr(0)) and k > 0
    cross = rc.alpha_zero_paper_dhalf()
    assert max(min(floor_ell(bb), L0 + k * bb) for bb in [Fr(j, 1000) for j in range(0, 201)]) <= cross["ell"]
    # along the constant-target direction (d ell, d M) = (1, 2) both constraints improve
    ell, M, b = Fr(1, 6), Fr(5, 6), Fr(1, 8)
    step = Fr(1, 100)
    assert rc.target(ell + step, M + 2 * step, b) == rc.target(ell, M, b)
    assert rc.floor_value(ell + step, M + 2 * step, b) - rc.floor_value(ell, M, b) == -step
    assert rc.e_half(Fr(5, 6), ell + step, M + 2 * step, b) - rc.e_half(Fr(5, 6), ell, M, b) == -step


def test_c_p_five_twenty_seconds_for_scale(opt):
    s = rc.sigma_slice_float(replace(PAPER, c_P=Fr(5, 22)))
    assert abs(s - SIGMA_CP_5_22) < 1e-12
    assert abs((float(opt["sigma_float"]) - s) * 1e5 - 1.0) < 0.05


def test_excess_scaling_matches_hunt_134_table():
    """The exact slice optima sit just below #134's float scan (b-grid step 0.01)."""
    table_134 = {Fr(3, 4): 0.872856, Fr(1, 2): 0.870767, Fr(1, 4): 0.868701}
    for lam, v134 in table_134.items():
        s = rc.sigma_slice_float(PAPER, lam=lam)
        assert abs(s - EXCESS[lam]) < 1e-12
        assert 0 <= v134 - s < 2e-6


def test_floor_and_alpha_zero():
    """alpha = 0: 13/15 only with the floor at 1/2, 167/192 at the paper's floor, 84031/96156 as the
    paper counts the rows d <= 1/2."""
    inp = replace(PAPER, alpha=Fr(0))
    assert all(rc.r_star(Fr(k, 24), Fr(j, 10), inp) == 1 - Fr(k, 24) for k in range(1, 21) for j in range(6))
    # floor pushed to 1/2: C_0 <= 0 and ell <= 1/5 give the corner
    assert rc.geometry_feasible_exact(inp, Fr(1, 5) - Fr(1, 10**6), Fr(0))["feasible"]
    assert rc.target(Fr(1, 5), Fr(4, 5), Fr(0)) == Fr(13, 15) and rc.c0(Fr(1, 5), Fr(4, 5), Fr(0)) == 0
    # there a negative b hurts: ell <= 1/5 + b/5 from the rows x = 1/2, delta = 5/6
    bb = Fr(-1, 100)
    lim = Fr(1, 5) + bb / 5
    assert rc.geometry_feasible_exact(inp, lim - Fr(1, 10**6), bb)["feasible"]
    assert not rc.geometry_feasible_exact(inp, lim + Fr(1, 10**6), bb)["feasible"]
    assert rc.target(lim, 1 - lim, bb) > Fr(13, 15)
    # the paper's floor delta_0 = 1/50 binds first, at ell = 3/16
    assert rc.floor_value(Fr(3, 16), Fr(13, 16), Fr(0)) == 0
    assert rc.target(Fr(3, 16), Fr(13, 16), Fr(0)) == Fr(167, 192)
    assert abs(float(Fr(167, 192)) - 0.8697917) < 5e-8 and abs(float(Fr(167, 192)) - 0.86979) < 5e-6
    assert not rc.side_conditions(Fr(1, 5) - Fr(1, 10**6), Fr(4, 5), Fr(0), inp)["floor"]
    assert rc.geometry_feasible_exact(inp, Fr(3, 16), Fr(0))["feasible"]
    # the rows d <= 1/2: the paper's count fails at both corners, the recount holds
    for ell in (Fr(3, 16), Fr(1, 5)):
        assert rc.e_half_max(ell, 1 - ell, Fr(0)) > 0
        assert rc.e_half_max_balanced(ell, 1 - ell, Fr(0), inp)["negative"]
    # with the paper's count, the floor meets the line ell <= 188/1593 + 223 b/531
    a0 = rc.alpha_zero_paper_dhalf()
    assert a0["sigma"] == ALPHA0_PAPER_DHALF and a0["floor"] == 0 and a0["e_half"] == 0
    assert (a0["ell"], a0["b"]) == (Fr(4112, 24039), Fr(1012, 8013))
    assert rc.geometry_feasible_exact(inp, a0["ell"], a0["b"])["feasible"]
    side = rc.side_conditions(a0["ell"], 1 - a0["ell"], a0["b"], inp)
    assert side["gram"] and side["small"] and side["b_nonneg"]
    assert abs(float(ALPHA0_PAPER_DHALF) - 0.8739028) < 5e-8
    # at the paper's floor (rows d <= 1/2 recounted) b >= 0 binds: b = -12/317 would reach 826/951,
    # where the floor and the rows x = 1/2, delta = 5/6 bind together
    ell, bb = Fr(61, 317), Fr(-12, 317)
    assert rc.target(ell, 1 - ell, bb) == Fr(826, 951) < Fr(167, 192)
    assert rc.floor_value(ell, 1 - ell, bb) == 0 and rc.neg_e_star(Fr(5, 6), HALF, ell, 1 - ell, bb, inp) == 0
    assert rc.geometry_feasible_exact(inp, ell - Fr(1, 10**9), bb)["feasible"]
    assert not rc.geometry_feasible_exact(inp, ell + Fr(1, 10**9), bb)["feasible"]
    assert rc.e_half_max_balanced(ell, 1 - ell, bb, inp)["negative"]
    side = rc.side_conditions(ell - Fr(1, 10**9), 1 - ell + Fr(1, 10**9), bb, inp)
    assert side["gram"] and side["small"] and side["floor"] and not side["b_nonneg"]


def test_marked_second_condition_threshold_and_slack():
    assert rc.marked_second_margin(Fr(0)) == Fr(1, 8) and rc.marked_second_margin(HALF) == Fr(1, 16)
    assert rc.marked_second_threshold() == Fr(37, 65) and abs(float(Fr(37, 65)) - 0.5692) < 5e-5
    assert rc.marked_second_slack(PAPER)
    at = replace(PAPER, c_M=Fr(37, 65))
    assert rc.marked_second_margin(HALF, at) == 0 and rc.marked_second_slack(at)
    assert not rc.marked_second_slack(replace(PAPER, c_M=Fr(37, 65) + Fr(1, 1000)))
    # the margin is D_x times the slack of the second condition at r_*(1), for any inputs
    for inp in (PAPER, replace(PAPER, c_M=Fr(3, 5)), rc.Inputs(Fr(4, 5), Fr(3, 5), Fr(1, 4))):
        for x in (Fr(0), Fr(1, 7), Fr(1, 4), HALF):
            r = rc.r_cross(x, Fr(1), inp)
            assert rc.d_x(x, inp) * (inp.c_M2 * (Fr(3, 2) - r) - inp.c_M * (1 - r)) == rc.marked_second_margin(x, inp)
    # the 1/16 is the paper's margin 9/37 of 2r - 1 at r = 23/37 (line 15378), times D_{1/2}/8
    assert rc.d_x(HALF) * (2 * Fr(23, 37) - 1) / 8 == Fr(1, 16)


def test_closed_form_is_exact_only_below_the_threshold():
    import numpy as np
    ds = np.linspace(0, 5 / 6, 31)[1:]
    xs = np.linspace(0, 0.5, 6)
    D, X = np.meshgrid(ds, xs, indexing="ij")

    def gap(inp):
        R = rc.r_star_capped(D, X, inp, 1e9)
        ex = np.array([[float(rc.r_star(Fr(d).limit_denominator(10**9), Fr(x).limit_denominator(10**9), inp))
                        for x in xs] for d in ds])
        return R - ex
    assert np.abs(gap(replace(PAPER, c_M=Fr(11, 20)))).max() < 1e-12
    g = gap(replace(PAPER, c_M=Fr(3, 5)))
    assert g.max() > 1e-6 and g.min() > -1e-12  # the cap only raises the count


def test_paper_count_of_the_rows_d_half_and_its_wall():
    sp = rc._sympy()
    assert rc.d_half_line() == (Fr(188, 1593), Fr(223, 531))
    w = rc.slice_on_dhalf_line(PAPER, Fr(0))
    want = sp.Rational(772834171, 849405636) - 1115 * sp.sqrt(185950102) / 424702818
    assert sp.simplify(w["sigma"] - want) == 0 and abs(float(w["sigma_float"]) - WALL_PAPER_DHALF) < 1e-15
    assert 0 < float(w["delta_v"]) < 5 / 6
    # the x = 0 slice does not involve the capacities
    ideal = rc.slice_on_dhalf_line(replace(PAPER, c_M=Fr(1), c_P=Fr(1)), Fr(0))
    assert ideal["sigma_float"] == w["sigma_float"]
    # along the line the x = 0 slice's ell decreases in b, so the intersection is the optimum
    ells = [float(rc.slice_fixed_b(PAPER, bb, Fr(0))["ell"]) for bb in (Fr(0), Fr(1, 10), Fr(1249, 10000), Fr(3, 20))]
    assert all(a > c for a, c in zip(ells, ells[1:]))
    ell = Fr(str(w["ell"].evalf(40))).limit_denominator(10**15)
    bb = Fr(str(w["b"].evalf(40))).limit_denominator(10**15)
    assert rc.e_half(rc.DELTA0, ell, 1 - ell, bb) < 0  # the other end is slack
    # both input-free bounds sit above the recounted values
    assert float(ALPHA0_PAPER_DHALF) < WALL_PAPER_DHALF and WALL < WALL_PAPER_DHALF < SIGMA_STAR


# --------------------------------------------------------------------------- measured evaluator

def test_measured_evaluator_calibrates_against_the_exact_optimum(opt):
    g = rc.sigma_general(PAPER, cap_supply=False)
    assert abs(g["sigma"] - float(opt["sigma_float"])) < 1e-8


def test_capped_r_star_reduces_to_the_closed_form():
    import numpy as np
    ds = np.linspace(0, 5 / 6, 31)[1:]
    xs = np.linspace(0, 0.5, 6)
    D, X = np.meshgrid(ds, xs, indexing="ij")
    for inp, second in ((PAPER, True), (replace(PAPER, c_M=Fr(11, 20)), True),
                        (replace(PAPER, c_M=Fr(3, 5)), False), (replace(PAPER, c_M=Fr(1)), False)):
        R = rc.r_star_capped(D, X, inp, 1e9, second=second)
        ex = np.array([[float(rc.r_star(Fr(d).limit_denominator(10**9), Fr(x).limit_denominator(10**9), inp))
                        for x in xs] for d in ds])
        assert np.abs(R - ex).max() < 1e-12


def _brute_rshort(delta, x, t, inp, s, second, n=20001):
    """max over a dense r grid of min(A(r), S(t - r)), with the caps written out afresh."""
    import numpy as np
    r = np.linspace(t - 0.5, 1.0, n)
    zM = np.minimum(float(inp.c_M) * (1 - r), s)
    if second:
        zM = np.minimum(zM, float(inp.c_M2) * (1.5 - r))
    A = 1 - delta * r - 2 * x * delta * np.maximum(zM, 0)
    m = t - r
    S = 1 - 2 * delta * m - 2 * x * delta * np.minimum(float(inp.c_P) * np.maximum(1 - 2 * m, 0), s)
    return float(np.max(np.minimum(A, S)))


def test_capped_short_rows_match_a_dense_brute_force():
    """The breakpoint max-min against a grid, including the non-monotone marked count at c_M = 10."""
    import numpy as np
    worst = 0.0
    for inp in (PAPER, replace(PAPER, c_M=Fr(1)), replace(PAPER, c_M=Fr(10)), replace(PAPER, c_P=Fr(1))):
        for s in (0.18, 0.22, 1e9):
            for second in (True, False):
                for delta, x, t in ((0.2, 0.5, 1.0), (0.39, 0.5, 1.13), (0.6, 0.3, 1.3), (0.39, 0.1, 1.45)):
                    got = float(rc.rshort_capped(np.array(delta), np.array(x), t, inp, s, second))
                    worst = max(worst, abs(got - _brute_rshort(delta, x, t, inp, s, second)))
    assert worst < 1e-4


IDEAL = [("c_M=1", replace(PAPER, c_M=Fr(1)), {}, M_PAPER_DHALF),
         ("c_P=1", replace(PAPER, c_P=Fr(1)), {}, M_PAPER_DHALF),
         ("c_M=c_P=1", replace(PAPER, c_M=Fr(1), c_P=Fr(1)), {}, M_PAPER_DHALF),
         ("alpha=0", replace(PAPER, alpha=Fr(0)), {}, float(ALPHA0_PAPER_DHALF)),
         ("c_M=1 recounted", replace(PAPER, c_M=Fr(1)), {"d_half": "balanced"}, M_CM1),
         ("c_M=1 recounted, second off", replace(PAPER, c_M=Fr(1)), {"d_half": "balanced", "second": False},
          M_CM1_SECOND_OFF),
         ("c_P=1 recounted", replace(PAPER, c_P=Fr(1)), {"d_half": "balanced"}, M_CP1),
         ("c_M=c_P=1 recounted", replace(PAPER, c_M=Fr(1), c_P=Fr(1)), {"d_half": "balanced"}, WALL),
         ("alpha=0 recounted", replace(PAPER, alpha=Fr(0)), {"d_half": "balanced"}, 167 / 192),
         ("alpha=0 recounted, floor at 1/2", replace(PAPER, alpha=Fr(0)), {"d_half": "balanced", "delta0": 0.0},
          13 / 15)]
COARSE = {"n_delta": 60, "n_x": 11, "s_step": 0.005}


@pytest.mark.slow
@pytest.mark.parametrize("name,inp,kw,value", IDEAL)
def test_measured_ideal_inputs_full_resolution(name, inp, kw, value):
    """The resolution behind the numbers quoted in ROWCOUNTS.md (default grids)."""
    g = rc.sigma_general(inp, **kw)
    tol = 1e-12 if name.startswith("alpha=0 recounted") else 5e-6
    assert abs(g["sigma"] - value) < tol, (name, g)
    if name in ("c_M=c_P=1 recounted", "alpha=0 recounted"):
        assert g["b"] == 0
    if name == "c_M=1 recounted":
        # the second marked condition binds, not the supply, and c_M = 10 changes nothing
        assert abs(rc.sigma_general(inp, cap_supply=False, **kw)["sigma"] - g["sigma"]) < 1e-12
        assert abs(rc.sigma_general(replace(inp, c_M=Fr(10)), **kw)["sigma"] - g["sigma"]) < 1e-12
    if name == "c_M=1 recounted, second off":  # then the supply binds; without it, the wall
        assert abs(rc.sigma_general(inp, cap_supply=False, **kw)["sigma"] - WALL) < 1e-8


@pytest.mark.parametrize("name,inp,kw,value", IDEAL)
def test_measured_ideal_inputs_coarse(name, inp, kw, value):
    g = rc.sigma_general(inp, **COARSE, **kw)
    tol = 1e-12 if name.startswith("alpha=0 recounted") else 5e-5
    assert abs(g["sigma"] - value) < tol, (name, g)


def test_measured_values_quoted_on_the_page_are_consistent():
    """c_P is ahead of c_M by about 3e-5 once the second condition is kept; the paper-count
    value of every capacity sits on the exact x = 0 wall of the paper's count; the first
    version's printed value differs from today's by the finer b-search only."""
    assert abs((M_CM1 - M_CP1) - 3e-5) < 5e-6
    assert abs(M_PAPER_DHALF - WALL_PAPER_DHALF) < 5e-8
    assert abs(M_CM1_FIRST_VERSION - M_CM1_SECOND_OFF) < 1.5e-7  # one unit in the 7th digit


def test_planted_faults_in_the_evaluator_are_caught():
    """Dropping the second marked condition, then the supply cap, then the rows d <= 1/2 each
    changes the c_M = 1 answer: each is load-bearing somewhere."""
    cm1 = replace(PAPER, c_M=Fr(1))
    bal = rc.sigma_general(cm1, d_half="balanced", **COARSE)["sigma"]
    no_second = rc.sigma_general(cm1, d_half="balanced", second=False, **COARSE)["sigma"]
    assert bal - no_second > 2.5e-4
    no_cap = rc.sigma_general(cm1, d_half="balanced", second=False, cap_supply=False, **COARSE)["sigma"]
    assert no_second - no_cap > 5e-4
    paper = rc.sigma_general(cm1, **COARSE)["sigma"]
    left_out = rc.sigma_general(cm1, d_half=None, **COARSE)["sigma"]
    assert paper - left_out > 5e-4
    # with the second condition kept the supply cap is slack at c_M = 1
    assert abs(rc.sigma_general(cm1, d_half="balanced", cap_supply=False, **COARSE)["sigma"] - bal) < 1e-12
    # everything dropped gives back the first version's number
    first = rc.sigma_general(cm1, d_half=None, second=False, **COARSE)["sigma"]
    assert abs(first - M_CM1_SECOND_OFF) < 5e-5


# ------------------------------------------------------------------------------ enumerations

def test_selection_enumeration_and_its_planted_fault():
    ok = rc.enumerate_selection()
    assert ok == {"cases": 137925, "paper_fail": 0, "sharp_fail": 0, "uniform_cases": 5364,
                  "uniform_above_2qz": 0}
    bad = rc.enumerate_selection(fault="ascending")
    assert bad["paper_fail"] == 54 and bad["sharp_fail"] == 6117


def test_multi_t_adversary_on_a_grid_and_its_planted_fault():
    """A consistency check only: the grid result is bounded by the paper's grid bound by weak duality."""
    a = rc.adversary_multi_t(Fr(7, 18), HALF)
    assert a["types_checked"] == 57337
    assert a["adversary"] == Fr(643, 972) and a["paper_grid_bound"] == Fr(2687, 3996)
    assert a["R_star"] == Fr(2363, 3546)
    assert a["adversary"] <= a["paper_grid_bound"] and a["adversary"] < a["R_star"]
    f = rc.adversary_multi_t(Fr(7, 18), HALF, fault="no_cover")
    assert f["adversary"] == Fr(5, 6) > f["paper_grid_bound"]


def test_multi_t_adversary_attains_r_star_exactly():
    for kd in range(1, 20):
        for kx in range(11):
            dl, x = Fr(5, 6) * Fr(kd, 20), Fr(kx, 20)
            a = rc.adversary_exact(dl, x)
            assert a["covers"] and a["value"] == rc.r_star(dl, x)


def test_capacity_and_copy_alternatives_are_dead():
    b = rc.beyond_capacity_signs()
    assert b["cases"] == 1100 and b["min_plain_net"] == 0 and b["min_marked_net"] == 0
    o = rc.one_copy_vs_two()
    assert o["cases"] == 2200 and o["min_one_minus_two"] == Fr(7, 4320)
    c = rc.conductor_strata()
    assert c["cases"] == 1260 and c["min_gap"] == 0


def test_sextic_reciprocity_factor_depends_on_m_mod_4_only():
    t = rc.reciprocity_factor_table()
    assert t["primes"] == 74 and t["all_ok"] and len(t["rows"]) == 6
    assert all(r["classes"] == 12 and set(r["values"]) <= {0, 3} for r in t["rows"])
    assert {r["norm"] for r in t["rows"]} == {7, 13, 19}


def test_exceptional_gram_frequencies_keep_a_nonzero_mean_for_every_xi():
    g = rc.exceptional_gram_means()
    assert g["all_ok"] and g["count"] == 30
    assert not rc.exceptional_gram_means(fault="wrong_e")["all_ok"]


def test_local_correlation_formula_totient_bound_and_the_withdrawn_bound():
    c = rc.local_correlation_check()
    assert c["all_ok"]
    assert c["totals"] == {"tested": 392, "formula_mismatch": 0, "totient_violations": 0,
                           "totient_attained": 123, "withdrawn_violations": 15, "withdrawn_outside": 0}
    logs7, logs13 = rc._logs(7), rc._logs(13)
    assert rc._local_L_np(7, 6, 7, 1, 1, logs7) == (100842, 0) == (7 ** 5 * 6, 0)
    assert rc._local_L_np(13, 6, 13, 1, 1, logs13) == (4455516, 0) == (13 ** 5 * 12, 0)
    assert (7 ** 5 * 5, 13 ** 5 * 11) == (84035, 4084223)
    f = rc.local_correlation_check(fault="sign")
    assert not f["all_ok"] and f["totals"]["formula_mismatch"] == 60


def test_local_sums_two_implementations_agree():
    n = bad = 0
    for p, c in ((7, 1), (13, 1), (19, 1), (7, 2), (13, 2)):
        logs = rc._logs(p)
        for n1 in (1, 2, 3, p, 2 * p):
            for n2 in (1, 5, p):
                if n1 % p == 0 and n2 % p == 0:
                    continue
                for k in (0, 1, 2, p, 2 * p):
                    n += 1
                    bad += rc._local_L_np(p, c, n1, n2, k, logs) != rc._local_L(p, c, n1, n2, k, logs)
    assert (n, bad) == (325, 0)


def test_amplification_lift_counts():
    a = rc.amplification_lift_counts()
    assert (a["rows"], a["lifts_per_row"], a["images"], a["collisions"]) == (21, 5, 105, 0)
    assert a["H"] == 724021350 and a["ball"] == 218871651 and a["P_to_5"] == 371293
    assert a["ball_over_images"] == Fr(218871651, 105) and a["ball_over_images"] > a["P_to_5"]
    assert 5.6 <= float(a["ball_over_images"]) / a["P_to_5"] < 5.65
    for B in (50, 1000, 5000):
        assert rc.count_primary_ball(B) == len(rc._primary_elements(B))


# --------------------------------------------------------------------------------- the prose

def test_loss_table_is_complete():
    res = {"shadow": rc.shadow_prices(PAPER), "tied_gain": -5.04e-8,
           "ideal_alpha_gain": float(ALPHA0_PAPER_DHALF) - SIGMA_STAR,
           "ideal_cM_gain": M_PAPER_DHALF - SIGMA_STAR, "ideal_cP_gain": M_PAPER_DHALF - SIGMA_STAR,
           "be_alpha": 0.8187, "be_cM": 0.5073, "be_cP": 0.2565}
    rows = rc.loss_table(res)
    assert len(rows) == 14 and len({r["key"] for r in rows}) == 14
    priced = {r["key"]: r["buys"] for r in rows if r["key"] in ("amplification", "marked_capacity", "plain_capacity")}
    assert priced["amplification"] < priced["marked_capacity"] == priced["plain_capacity"] < 0
    assert all(r["buys"] == 0.0 for r in rows if r["key"] not in
               ("amplification", "marked_capacity", "plain_capacity", "kappa_floor", "numerator"))
    assert next(r for r in rows if r["key"] == "numerator")["buys"] is None


#: whole table rows of ROWCOUNTS.md: a changed cell fails even if its number appears elsewhere
MD_ROWS = [
    "   | amplification slope α | 84031/96156 ≈ 0.8739028 (exact) | 167/192 (exact; 13/15 with the floor "
    "pushed to 1/2) | 0.8186904, 1.76 % smaller | 0.8028731, 3.66 % smaller (0.8031897, 3.62 %, recounted) "
    "| dσ*/dα = 0.0047006 |",
    "   | marked capacity c_M | about 0.8740525 (measured) | about 0.8734852 (measured; the second marked "
    "condition binds) | 0.5073017, 1.46 % larger | 0.5152786, 3.06 % larger | dσ*/dc_M = -0.0095711 |",
    "   | plain capacity c_P | about 0.8740525 (measured) | about 0.8734556 (measured, supply-capped) | "
    "0.2565019, 15.4 % larger | 0.2916823, 31.3 % larger | dσ*/dc_P = -0.0019777 |",
    "| 1 | slot selection, 15116 to 15134 | `\\|∏Q_i\\|² ≥ U^{2qz - δ max w_i}` | `U^{2q(z - max w_i)}`, and the "
    "mean q is the exact worst case | exhaustive, 137925 configurations | holds | 0 |",
    "| 2 | one detector length t per bin, 15196 to 15210, 15962 to 15986 | min over t of max(R_short(t), L(t)) "
    "| use the witnesses at every t at once | exact attaining type on a 19 × 11 grid | dead | 0 |",
    "| 3 | capacity cuts, 14259, 12873, 15021 | slots only up to z_M, z_P | more slots, paid by the pointwise "
    "prime bound | exact grid, 1100 cases | dead | 0 |",
    "| 4 | two copies of S_m, 15242 | `\\|S_m\\|^4` in Lemma plain | one copy with capacity (1 - m)/(6κ) | "
    "exact grid, 2200 cases | dead | 0 |",
    "| 5 | floor rows, 15843 to 15848 | counted in full, R = 1 | none tried | none | slack at the paper's "
    "inputs | 0 |",
    "| 6 | conductor in the per-row bound, 4354 to 4367 | conductor ≤ q_u for every row | strata by the "
    "powerful part | exact grid, 1260 cases | dead | 0 |",
    "| 7 | Gram exceptional frequencies, 8527 to 8557 | trivial two-column count for k = a^6 e | the ray twist "
    "χ_s(b_*)/ξ(s) has mean zero on T-classes | exhaustive in Z[ω] and F_p | dead | 0 |",
    "| 8 | Gram correlation, 7114 to 7130, 8546 | `\\|L_C\\| ≤ q_C` | `\\|L_C\\| ≤ φ(C)` | brute force, 392 "
    "local sums | holds | 0 |",
    "| 9 | κ in the plain capacity, 12532, 15327 | κ_0 = 3/4 | κ_0 = 2σ - 1 | exact (cubic) | matched by Guo "
    "| 5.04 × 10^-8 |",
    "| 10 | sixth-power lift, 12410 to 12455 | sparse lifts bounded by the whole ball | a smaller α | lift "
    "count, exhaustive | real, priced | section 5 |",
    "| 11 | marked capacity, 9254, 9808 to 9809, 12208 to 12209, 9904 | r + 2z < 1 and 2r + 8z < 3 | larger "
    "c_M | priced; the second condition binds above c_M = 37/65 | real, priced | section 5 |",
    "| 12 | plain capacity, 12561, 14259 | 2m + 6κz ≤ 1 | larger c_P | priced only | real, priced | "
    "section 5 |",
    "| 13 | count times pointwise numerator, 15799 to 15810 | U^R times U^{δ/2} for every row | an average "
    "of the numerator over the bin | not tested here | real, outside the lemmas | not priced |",
    "| 14 | rows d ≤ 1/2, 16146 to 16160 | t = 1, no primes: R = 76/75 - 2δ/3 | the balancing t, no primes: "
    "R_*(δ, 0) | exact sign checks | holds (inferred available) | 0 at σ*; needed by every perfect value |",
    "| t for the rows d ≤ 1/2 | 1 (line 16146) | nothing new: the balancing t uses the same no-slot counts "
    "(inferred) | genuine, needs no new lemma (inferred); slack at σ*, binds at every perfect-input optimum |",
    "| amplification slope α | 5/6 (line 15300) | sixth-power lift density against the ball | genuine; the "
    "only route to the floor |",
    "| marked capacity c_M | 1/2 (line 15182) | the mark's length in the reflected energy | genuine; largest "
    "leverage, alone down to about 0.8734852 |",
    "| second marked condition c_M2 | 1/4 (line 9254) | the 6z_0 charge of the second invariant | slack at "
    "the paper's inputs; binds once c_M exceeds 37/65 |",
    "| plain capacity c_P | 2/9 (line 15327) | the induction's exchange rate 6κ | genuine; small leverage |",
    "| κ_0 in c_P | 3/4 | Lemma plain's stated range | worth 5.04 × 10^-8, taken by Guo |",
    "| Gram offset b ≥ 0 | P_a ≥ 1 (line 8345) | a Gram estimate for P_a < 1 | slack at σ*; active at the "
    "x = 0 wall (0.8723955 at b = -1/50) and at 167/192, not at 13/15 |",
    "| detector window t | [1, 3/2] (line 4513) | nothing: one t per bin is exact | none |",
    "| slot mesh | fine (line 16246) | nothing: its loss tends to zero | none |",
    "| floor | 51/100 (line 15843) | slack except at α = 0 | 167/192 to 13/15, only at α = 0 |",
]


def _md_decimals() -> dict:
    """Every decimal the page may print, mapped to its pinned value and a rounding tolerance."""
    be = {k: v for k, v in BREAK_EVEN.items()}
    star = SIGMA_STAR
    d = {
        "0.87495706979917": (star, 5e-15), "0.8749570194200989": (SIGMA_DAGGER, 1e-16),
        "0.8749570194": (SIGMA_DAGGER, 1e-10), "0.87254987212856": (WALL, 5e-15),
        "0.0047006": (SHADOW["alpha"], 5e-8), "-0.0095711": (SHADOW["c_M"], 5e-8),
        "-0.0019777": (SHADOW["c_P"], 5e-8),
        "0.8186904": (be[("alpha", 1)][0], 5e-8), "0.5073017": (be[("c_M", 1)][0], 5e-8),
        "0.2565019": (be[("c_P", 1)][0], 5e-8), "0.8031897": (be[("alpha", 2)][0], 5e-8),
        "0.5152786": (be[("c_M", 2)][0], 5e-8), "0.2916823": (be[("c_P", 2)][0], 5e-8),
        "1.76": (-100 * be[("alpha", 1)][1], 5e-3), "1.46": (100 * be[("c_M", 1)][1], 5e-3),
        "15.4": (100 * be[("c_P", 1)][1], 0.05), "3.62": (-100 * be[("alpha", 2)][1], 5e-3),
        "3.06": (100 * be[("c_M", 2)][1], 5e-3), "31.3": (100 * be[("c_P", 2)][1], 0.05),
        "0.8028731": (BE_ALPHA_LINE[0], 5e-8), "3.66": (-100 * BE_ALPHA_LINE[1], 5e-3),
        "0.8739028": (float(ALPHA0_PAPER_DHALF), 5e-8), "0.8740525": (WALL_PAPER_DHALF, 5e-8),
        "0.8697917": (167 / 192, 5e-8), "0.86979": (167 / 192, 5e-6), "0.8685594": (826 / 951, 5e-8),
        "0.8734852": (M_CM1, 0), "0.8734556": (M_CP1, 0), "0.8731593": (M_CM1_SECOND_OFF, 0), "0.8731594": (M_CM1_FIRST_VERSION, 0),
        "0.8723955": (FIXED_B[Fr(-1, 50)], 5e-8), "0.8722121": (FIXED_B[Fr(-1, 20)], 5e-8),
        "0.8749470": (SIGMA_CP_5_22, 5e-8), "1.0": ((star - SIGMA_CP_5_22) * 1e5, 0.05),
        "0.8748867": (float(rc.XU_SANG), 0), "0.8748087": (float(rc.TRACKER_RECORD), 0),
        "0.8728554": (EXCESS[Fr(3, 4)], 5e-8), "0.8707660": (EXCESS[Fr(1, 2)], 5e-8),
        "0.8687000": (EXCESS[Fr(1, 4)], 5e-8),
        "0.872856": (0.872856, 0), "0.870767": (0.870767, 0), "0.868701": (0.868701, 0),
        "0.16683839": (11 / 551 + 8 * 921 ** 0.5 / 1653, 5e-9),
        "0.12340544": (-4 / 29 + 230 * 921 ** 0.5 / 26709, 5e-9),
        "0.38858371": (0.38858371227110341, 5e-9), "0.38858": (0.38858371227110341, 5e-6),
        "0.74991": (2 * SIGMA_DAGGER - 1, 5e-6), "0.5692": (37 / 65, 5e-5),
        "-0.0209": (-0.0209, 5e-5), "-0.0059": (-0.0059, 5e-5), "-0.0027": (-0.0027, 5e-5),
        "-0.0093": (-0.0093, 5e-5), "3.5": (3.5, 0.05), "0.2055": (0.2055, 5e-5),
        "2.5": (2.5, 0.05), "3.9": (3.92, 0.05), "4.8": (4.79, 0.05), "0.44": (0.44, 5e-3),
        "5.04": (5.04, 5e-3), "5.6": (5.6, 0.05),
    }
    return d


def md_problems(text: str) -> list[str]:
    """What the page test finds wrong with a version of ROWCOUNTS.md (empty when it is right)."""
    problems = []
    lines = set(text.splitlines())
    problems += [f"row missing or changed: {row[:60]}" for row in MD_ROWS if row not in lines]
    table = _md_decimals()
    scan = re.sub(r"arXiv:\S+", "", text)
    for tok in re.findall(r"-?\d+\.\d+", scan):
        if tok not in table:
            problems.append(f"unpinned decimal {tok}")
            continue
        value, tol = table[tok]
        if abs(float(tok) - value) > tol + 1e-15:
            problems.append(f"decimal {tok} does not match its pinned value {value}")
    for s in ["(1507 - 2√921)/1653", "4959σ² - 9042σ + 4115", "7884σ³ - 18819σ² + 14643σ - 3686",
              "101/108 - √286/270", "10800σ² - 20200σ + 9403", "84031/96156", "188/1593 + 223b/531",
              "37/65", "167/192", "13/15", "137925", "57337", "643/972", "2687/3996", "2363/3546", "7/4320",
              "218871651", "371293", "39 selected", "Ten more", "98 of 98", "162", "137/96", "139/96",
              "392", "123 of the 392", "15 such sums", "100842", "84035", "4455516", "4084223", "60",
              "325 sums", "1/16", "1/8", "5/22", "3 × 10^-5", "1.0 × 10^-5", "2.5 × 10^-4", "5 × 10^-4",
              "826/951", "-12/317"]:
        if s not in text:
            problems.append(f"missing: {s}")
    return problems


def test_rowcounts_md_quotes_the_pinned_numbers():
    if not MD.is_file():
        pytest.skip("ROWCOUNTS.md not written yet")
    assert md_problems(MD.read_text(encoding="utf-8")) == []


def test_planted_wrong_cells_in_the_page_are_caught():
    """The verifier's plant: three wrong cells whose correct values still appear in the prose."""
    if not MD.is_file():
        pytest.skip("ROWCOUNTS.md not written yet")
    text = MD.read_text(encoding="utf-8")
    row = next(r for r in MD_ROWS if r.startswith("   | marked capacity c_M"))
    planted = text.replace(row, row.replace("1.46 %", "1.64 %").replace("-0.0095711", "-0.0059711")
                           .replace("about 0.8734852", "about 0.8713594"))
    assert planted != text
    found = md_problems(planted)
    assert any(p.startswith("row missing or changed") for p in found)
    assert {"unpinned decimal 1.64", "unpinned decimal -0.0059711", "unpinned decimal 0.8713594"} <= set(found)
    # a swap of two pinned numbers inside one row is caught by the row check alone
    swapped = text.replace(row, row.replace("0.5073017", "@").replace("0.5152786", "0.5073017").replace("@", "0.5152786"))
    assert any(p.startswith("row missing or changed") for p in md_problems(swapped))


def test_lane_files_respect_the_lexical_rules():
    banned = "cert" + "ified"  # the reserved word, assembled so this file does not contain it
    for name in ("rowcounts.py", "test_rowcounts.py", "ROWCOUNTS.md"):
        path = Path(HERE) / name
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        assert banned not in text.lower(), name
        assert chr(0x2014) not in text and chr(0x2013) not in text, name  # no em or en dashes
    if MD.is_file():
        low = MD.read_text(encoding="utf-8").lower()
        for claim in ("is novel", "novel result", "we prove that", "is a theorem", "is established",
                      "nobody has proved", "no count in the assembly loses anything"):
            assert claim not in low, claim
