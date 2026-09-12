"""The assembled ball enclosure really contains DH, checked by the Hurwitz route.

`scripts/62_rung3_rho_w.py --arith ball` reports margins of 2.1-3.8 where the
shipped rectangle arithmetic reports 0.57-0.96.  A 14x improvement is exactly the
shape of result the house rule says to distrust ("if a computation appears to
settle something, the correct inference is a bug"), so the assembled enclosure is
checked here against `zeta.epstein.dh_f`, which reaches DH through Hurwitz zeta
and never forms the Dirichlet partial sum the mirror is summing.

If the ball assembly had dropped enclosure, this is where it shows up.
"""
from __future__ import annotations

import importlib
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest
from mpmath import mp

from zeta.epstein import dh_f

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

meas = importlib.import_module("62_rung3_rho_w")

# Three sites spanning the frontier: the low-sigma left edge (where the cost
# concentrates), a sigma = 1 right-edge box, and a corner-adjacent bottom box.
SITE_IDS = ["B_left_17", "B_right_06", "B_bottom_11"]
SITES = [b for b in meas.PLAN["big"]["boxes"] if b["id"] in SITE_IDS]


def _assembled(site, arith):
    meas.use_arith(arith)
    return meas.box_norms(site)


def _true_dh(sre: F, sim: F):
    with mp.workdps(40):
        s = mp.mpf(sre.numerator) / sre.denominator + 1j * (
            mp.mpf(sim.numerator) / sim.denominator)
        return dh_f(s, dps=30)


@pytest.mark.parametrize("site", SITES, ids=SITE_IDS)
@pytest.mark.parametrize("arith", ["rect", "ball"])
def test_assembled_enclosure_brackets_the_true_modulus(site, arith):
    """`normLower <= |DH(s)| <= normBound` at sampled points of the segment.

    Run for both arithmetics: the rectangle case is the control that the harness
    itself is faithful, so a ball-only failure cannot be blamed on the harness.
    """
    n = _assembled(site, arith)
    relo, rehi = F(site["re_lo"]), F(site["re_hi"])
    imlo, imhi = F(site["im_lo"]), F(site["im_hi"])
    nb, nl = float(n["nb_box"]), float(n["nl_box"])
    for j in range(5):
        sre = relo + (rehi - relo) * F(j, 4)
        sim = imlo + (imhi - imlo) * F(j, 4)
        a = abs(_true_dh(sre, sim))
        assert nl <= a <= nb, (
            site["id"], arith, float(sre), float(sim), nl, float(a), nb)


@pytest.mark.parametrize("site", SITES, ids=SITE_IDS)
def test_ball_encloses_and_is_strictly_tighter_than_the_rectangle(site):
    """The ball must be *inside* the rectangle's bound, not merely smaller,
    a smaller number that failed to enclose would be a defect, not a win."""
    rect = _assembled(site, "rect")
    ball = _assembled(site, "ball")
    assert ball["nb_box"] < rect["nb_box"], site["id"]
    # and both still enclose the truth, so the shrink is real
    relo, imlo = F(site["re_lo"]), F(site["im_lo"])
    imhi = F(site["im_hi"])
    a = abs(_true_dh(relo, (imlo + imhi) / 2))
    assert float(ball["nl_box"]) <= a <= float(ball["nb_box"]), site["id"]


gc = importlib.import_module("64_rung3_grid_centre")


def test_the_rect_harness_reproduces_the_recorded_centre_failure():
    """The control that licenses everything else: run the shipped arithmetic and
    the harness must land on `docs/25` §4.3's recorded numbers, not near them."""
    small, c = gc.PLAN["small"], gc.PLAN["centre"]
    n = gc.evaluate(F(small["cre"]), F(small["cim"]), c["K"], F(c["r"]), "rect")
    eps = F(small["eps"])
    margin = float(eps / n["normBound"])
    assert abs(margin - 0.6321) < 5e-4, margin              # recorded: FAIL at x0.6321
    assert abs(float(n["normBound"]) - 7.9e-4) < 2e-5       # recorded: normBound 7.9e-4


def test_the_centre_ball_enclosure_contains_the_true_value():
    """The centre asserts |DH| < eps'.  A ball that passed by *losing* DH would
    be the worst possible defect here, so it is checked against the Hurwitz route."""
    small, c = gc.PLAN["small"], gc.PLAN["centre"]
    cre, cim = F(small["cre"]), F(small["cim"])
    n = gc.evaluate(cre, cim, c["K"], F(c["r"]), "ball")
    a = abs(_true_dh(cre, cim))
    assert float(n["normLower"]) <= a <= float(n["normBound"]), (
        float(n["normLower"]), float(a), float(n["normBound"]))
    assert n["normBound"] < F(small["eps"])


@pytest.mark.parametrize("gid", ["g_bottom_00", "g_left_13", "g_right_00"])
def test_grid_ball_normLower_really_bounds_the_modulus_below(gid):
    """`normLower` is a claim that |DH| is at least that big.  Ball arithmetic
    raises it by up to 1.3x, which is only legitimate if it stays below |DH|."""
    site = next(s for s in gc.PLAN["grid"] if s["id"] == gid)
    re, im = gc.site_point(site)
    n = gc.evaluate(re, im, site["K"], F(site["r"]), "ball")
    a = abs(_true_dh(re, im))
    assert float(n["normLower"]) <= a, (gid, float(n["normLower"]), float(a))


def test_ball_width_sits_just_above_the_first_order_floor():
    """The ball width is bracketed by calculus, from both sides.

    Over an `s`-ball of radius delta/2, each term `m^{-s}` genuinely varies by
    about `log(m) * m^{-sigma} * delta/2`, so the coefficient-weighted sum of
    those is an information-theoretic floor no sound enclosure can beat.
    Measured over 15 big boxes, the ball evaluator's width term sits at
    1.09-1.20x that floor: the rect -> ball gain (13.7x) is exactly the
    rotation waste, and what remains is the irreducible variation plus
    Taylor/coarsening slop.

    Pinned from both sides at one site because each side kills a different
    defect: width BELOW the floor means enclosure is being dropped (the
    too-good-to-be-true failure mode), width far ABOVE it means the wrapping
    waste has crept back in.
    """
    import math

    site = next(b for b in meas.PLAN["big"]["boxes"] if b["id"] == "B_right_06")
    n = _assembled(site, "ball")
    delta = float(n["delta"])
    width = float(n["nb_box"] - n["nb_point"])
    sigma = float(F(site["sigma_lo"]))
    kappa = 0.2840791
    s_w = s_u = 0.0
    for m in range(2, 5 * site["K"]):
        j = m % 5
        if j == 0:
            continue
        c = kappa if j in (2, 3) else 1.0
        v = m ** (-sigma) * math.log(m)
        s_w += c * v
        s_u += v
    floor = 0.5 * delta * s_w
    assert 0.95 * floor <= width <= 1.35 * floor, (width, floor, width / floor)


def test_the_ball_gain_is_in_the_width_term_not_the_centre():
    """Attribute the 14x: it must come from the boxed-vs-point difference
    (rotation wrapping), not from the point evaluation moving."""
    site = next(b for b in meas.PLAN["big"]["boxes"] if b["id"] == "B_left_17")
    rect, ball = _assembled(site, "rect"), _assembled(site, "ball")
    w_rect = float(rect["nb_box"] - rect["nb_point"])
    w_ball = float(ball["nb_box"] - ball["nb_point"])
    assert w_ball < w_rect / 5, (w_rect, w_ball)
