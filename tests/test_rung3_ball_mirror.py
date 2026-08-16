"""Soundness of the ball-arithmetic mirror, against mpmath and against the box mirror.

A ball mirror that reports thin radii because it *drops* enclosure would make the
rho_W measurement in `scripts/62_rung3_rho_w.py` look good and mean nothing.  So
the instrument is pinned before it is believed: every ball must contain the true
value, at a point and over a segment, and its radius must bound the box mirror's
own half-width on the quantities both compute.
"""
from __future__ import annotations

import importlib
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest
from mpmath import mp

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

ball = importlib.import_module("63_rung3_ball_mirror")
box = importlib.import_module("61_rung3_mirror")

# Points chosen to straddle the certificate's real geometry: the oracle zero, the
# low-sigma left edge of the big square, and the tame DHDemo point.
POINTS = [
    (F(808517, 10**6), F(85699348, 10**6)),
    (F(589767, 10**6), F(857, 10)),
    (F(3, 2), F(3, 1)),
]
MS = [2, 3, 4, 7, 12, 49, 101, 256]


def _true_cpow(m: int, sre: F, sim: F):
    with mp.workdps(50):
        s = mp.mpf(sre.numerator) / sre.denominator + 1j * (
            mp.mpf(sim.numerator) / sim.denominator)
        return mp.mpc(m) ** (-s)


def _contains(b, z, slack=F(0)) -> bool:
    """Is `z` (an mpmath complex) inside the ball, allowing an oracle slack?"""
    with mp.workdps(50):
        dre = mp.mpf(str(b.cre.numerator)) / b.cre.denominator - z.real
        dim = mp.mpf(str(b.cim.numerator)) / b.cim.denominator - z.imag
        d = mp.sqrt(dre * dre + dim * dim)
        r = mp.mpf((b.rad + slack).numerator) / (b.rad + slack).denominator
        return d <= r


@pytest.mark.parametrize("sre,sim", POINTS)
@pytest.mark.parametrize("m", MS)
def test_ball_cpow_encloses_the_true_value_at_a_point(m, sre, sim):
    S = ball.C(sre, sim, 0)
    b = ball.cpowBox(m, S)
    assert _contains(b, _true_cpow(m, sre, sim)), (
        m, float(sre), float(sim), b, float(b.rad))


@pytest.mark.parametrize("sre,sim", POINTS[:2])
def test_ball_cpow_encloses_every_sampled_point_of_a_segment(sre, sim):
    """The certificate's sites are segments, so the boxed case is the real one."""
    half = F(1, 200)
    S = ball.from_box(sre, sre, sim - half, sim + half)
    for m in (2, 3, 7, 12, 101):
        b = ball.cpowBox(m, S)
        for j in range(-4, 5):
            t = sim + half * F(j, 4)
            assert _contains(b, _true_cpow(m, sre, t)), (m, float(t), b)


def test_the_enclosing_ball_of_a_segment_is_exact_in_radius():
    """A degenerate rectangle's minimal ball has radius half the segment length —
    so switching `s` to a ball costs no enclosure at the input."""
    half = F(3, 1000)
    b = ball.from_box(F(1, 2), F(1, 2), F(10) - half, F(10) + half)
    assert b.rad == half
    assert b.cre == F(1, 2) and b.cim == F(10)


def test_ball_and_box_agree_on_a_term_to_within_their_radii():
    """Both enclose the same truth, so their centres cannot be far apart."""
    sre, sim = POINTS[0]
    S_ball = ball.C(sre, sim, 0)
    S_box = box.C(box.I(sre, sre), box.I(sim, sim))
    for m in (2, 7, 49):
        b = ball.cpowBox(m, S_ball)
        x = box.cpowBox(m, S_box)
        bre = (x.re.lo + x.re.hi) / 2
        bim = (x.im.lo + x.im.hi) / 2
        halfw = max(x.re.hi - x.re.lo, x.im.hi - x.im.lo) / 2
        sep = ball.sqrt_upper((b.cre - bre) ** 2 + (b.cim - bim) ** 2)
        assert sep <= b.rad + halfw + F(1, 10**20), (m, float(sep))


def test_ball_inverse_encloses_the_true_inverse():
    sre, sim = POINTS[0]
    S = ball.from_box(sre, sre, sim - F(1, 500), sim + F(1, 500))
    inv = ball.invC(ball.inv5sBox(S))
    with mp.workdps(50):
        for j in (-1, 0, 1):
            t = sim + F(j, 500)
            s = mp.mpf(sre.numerator) / sre.denominator + 1j * (
                mp.mpf(t.numerator) / t.denominator)
            assert _contains(inv, 1 / (5 * (1 - s)))


def test_normBound_and_normLower_bracket_the_true_modulus():
    sre, sim = POINTS[0]
    S = ball.from_box(sre, sre, sim - F(1, 500), sim + F(1, 500))
    b = ball.cpowBox(7, S)
    nb, nl = ball.normBound(b), ball.normLower(b)
    with mp.workdps(50):
        for j in (-1, 0, 1):
            z = _true_cpow(7, sre, sim + F(j, 500))
            a = abs(z)
            assert float(nl) <= a <= float(nb)


def test_a_deliberately_broken_ball_is_caught():
    """The planted-fault control: halve every radius and the enclosure must fail.

    Without this, the suite above only shows the radii are *large enough for the
    points sampled*, which a too-thin mirror could also pass by luck.
    """
    orig = ball.cmul

    def thin(x, y):
        r = orig(x, y)
        return ball.C(r.cre, r.cim, r.rad / 1000)

    ball.cmul = thin
    try:
        sre, sim = POINTS[0]
        half = F(1, 200)
        S = ball.from_box(sre, sre, sim - half, sim + half)
        b = ball.cpowBox(101, S)
        bad = any(not _contains(b, _true_cpow(101, sre, sim + half * F(j, 4)))
                  for j in range(-4, 5))
        assert bad, "thinned radii still enclosed everything — the check has no power"
    finally:
        ball.cmul = orig
