"""The assembled ball enclosure really contains DH — checked by the Hurwitz route.

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
    """The ball must be *inside* the rectangle's bound, not merely smaller —
    a smaller number that failed to enclose would be a defect, not a win."""
    rect = _assembled(site, "rect")
    ball = _assembled(site, "ball")
    assert ball["nb_box"] < rect["nb_box"], site["id"]
    # and both still enclose the truth, so the shrink is real
    relo, imlo = F(site["re_lo"]), F(site["im_lo"])
    imhi = F(site["im_hi"])
    a = abs(_true_dh(relo, (imlo + imhi) / 2))
    assert float(ball["nl_box"]) <= a <= float(ball["nb_box"]), site["id"]


def test_the_ball_gain_is_in_the_width_term_not_the_centre():
    """Attribute the 14x: it must come from the boxed-vs-point difference
    (rotation wrapping), not from the point evaluation moving."""
    site = next(b for b in meas.PLAN["big"]["boxes"] if b["id"] == "B_left_17")
    rect, ball = _assembled(site, "rect"), _assembled(site, "ball")
    w_rect = float(rect["nb_box"] - rect["nb_point"])
    w_ball = float(ball["nb_box"] - ball["nb_point"])
    assert w_ball < w_rect / 5, (w_rect, w_ball)
