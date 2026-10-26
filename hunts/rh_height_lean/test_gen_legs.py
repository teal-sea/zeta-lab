"""Pins for the generated Lean files of the piece `horizontal_legs`, and the planted faults.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/rh_height_lean/test_gen_legs.py

`gen_legs.py` evaluates, in exact rational arithmetic, the same quantities the Lean kernel
decides in `lean/RHHeight/Legs*.lean`. This file checks that the files on disk are what the
generator writes, that every segment and both point boxes close, and that the checks can
fail: a segment stretched past its end, a height moved to where `Re zeta(1/2 + iy) < 0`, and
an argument bound tighter than the box gives are each refused. Two cross-checks use other
routes (measured, not proofs): Arb (python-flint) values of `m^(-s)` lie in the mirror's term
boxes, and mpmath values of zeta lie in the point boxes and above the segment lower bound.
Nothing is written into the tree.
"""
from __future__ import annotations

from fractions import Fraction as F

import flint
import mpmath
import pytest
from mpmath import mp

from hunts.rh_height_lean import gen_legs as G


@pytest.fixture(scope="module")
def M():
    return G.load_mirror()


@pytest.fixture(scope="module")
def out(M):
    return G.build(M)


def _segments(out):
    return [d for name in ("LegsBottom", "LegsTop1", "LegsTop2") for d in out[name][1]]


def test_files_on_disk_match_the_generator(out):
    for name, (text, _) in out.items():
        path = G.LEAN_DIR / f"{name}.lean"
        assert path.read_text(encoding="utf-8") == text, f"{path.name} is stale"


def test_segments_tile_both_legs(out):
    for height, segs in ((F(3), out["LegsBottom"][1]),
                         (F(52), out["LegsTop1"][1] + out["LegsTop2"][1])):
        assert all(d["y"] == height for d in segs)
        assert segs[0]["a"] == F(1, 2) and segs[-1]["b"] == 2
        assert all(d0["b"] == d1["a"] for d0, d1 in zip(segs, segs[1:]))


def test_every_segment_closes_with_the_margin(out):
    slacks = [d["slack"] for d in _segments(out)]
    assert all(s > G.MARGIN for s in slacks)
    # the pinned worst slack (exact rationals, rounded here)
    assert abs(float(min(slacks)) - 0.050059) < 1e-5


def test_point_boxes_close(out):
    pts = dict(out["LegsArg"][1])
    for tag, lower, ratio in (("Arg3", F(-1, 5), -0.152136), ("Arg52", F(-1, 3), -0.310108)):
        d = pts[tag]
        assert d["ok"] and d["lower"] == lower
        assert d["re"][0] > 0 and d["im"][1] <= 0
        assert abs(float(d["ratio"]) - ratio) < 1e-5


def test_prime_tower_count(out):
    total = sum(G.towers(d["N"]) for d in _segments(out))
    total += sum(G.towers(d["N"]) for _, d in out["LegsArg"][1])
    assert total == 41


# ---------------------------------------------------------------------------
# Planted faults: each must be refused
# ---------------------------------------------------------------------------


def test_planted_stretched_segment_is_refused(M):
    # the second bottom segment closes up to 19/16 and not to 5/4
    assert G.segment(M, F(43, 64), F(19, 16), F(3), 2)["slack"] > 0
    assert G.segment(M, F(43, 64), F(5, 4), F(3), 2)["slack"] < 0
    # one table cannot carry the whole bottom leg
    assert G.segment(M, F(1, 2), F(2), F(3), 2)["slack"] < 0


def test_planted_height_where_re_zeta_is_negative_is_refused(M):
    # Re zeta(1/2 + 50i) = -0.0817 (measured), so the first top segment moved to 50 fails
    assert G.segment(M, F(1, 2), F(39, 64), F(50), 12)["slack"] < 0


def test_planted_tighter_argument_is_refused(M):
    assert not G.point(M, F(1, 2), F(3), 4, F(-1, 10))["ok"]
    assert not G.point(M, F(1, 2), F(52), 28, F(-3, 10))["ok"]


def test_planted_short_truncation_is_refused(M):
    # at 52 the remainder radius at N = 8 is too large for the first segment
    assert G.segment(M, F(1, 2), F(39, 64), F(52), 8)["slack"] < 0


# ---------------------------------------------------------------------------
# Cross-checks by other routes (measured)
# ---------------------------------------------------------------------------


def test_arb_values_lie_in_the_term_boxes(out):
    flint.ctx.prec = 200
    for d in _segments(out)[:2] + _segments(out)[-1:]:
        s = flint.acb(flint.arb(d["a"].numerator) / d["a"].denominator, int(d["y"]))
        for m in range(2, d["N"] + 1):
            v = flint.acb(m) ** (-s)
            bx = d["boxes"][m]
            for part, iv in ((v.real, bx.re), (v.imag, bx.im)):
                lo = flint.arb(iv.lo.numerator) / iv.lo.denominator
                hi = flint.arb(iv.hi.numerator) / iv.hi.denominator
                assert lo <= part and part <= hi, (d["a"], d["y"], m)


def test_mpmath_zeta_lies_in_the_point_boxes(out):
    with mp.workdps(30):
        for _, d in out["LegsArg"][1]:
            z = mpmath.zeta(mpmath.mpc(mpmath.mpf(d["x"].numerator) / d["x"].denominator,
                                       int(d["y"])))
            assert float(d["re"][0]) < z.real < float(d["re"][1])
            assert float(d["im"][0]) < z.imag < float(d["im"][1])


def test_segment_bound_lies_below_mpmath(out):
    with mp.workdps(25):
        for d in _segments(out):
            a, b, y = d["a"], d["b"], d["y"]
            for k in range(9):
                sigma = a + (b - a) * F(k, 8)
                bound = d["main_lo"] - (sigma - a) * d["L"] - d["R"]
                z = mpmath.zeta(mpmath.mpc(mpmath.mpf(sigma.numerator) / sigma.denominator, int(y)))
                assert float(bound) < z.real
