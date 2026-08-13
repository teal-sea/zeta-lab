"""Pins for the two-dimensional O9 leaf table.

The load-bearing tests here are the *enclosure* ones: `r_iv` and `qre_iv` are
new compositions, and a wrong one would still produce a table that passes its
own check while proving something other than O9.  They are therefore checked
against `o9_scoping.py`'s independent Arb evaluation of the same two
quantities, which shares no code with the integer layer.

`r_iv`'s sign is pinned separately, because the table only ever uses `R^2`
and a sign error would otherwise be invisible.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))

import o9_leaf2d as M  # noqa: E402
import o9_scoping as S  # noqa: E402

flint = pytest.importorskip("flint")

SO = M.SO

#: Boxes spanning the interesting geometry: inside a window, in a gap, hard
#: against `y = 0` (the branch the removable form exists for), and at `y = 1/2`.
BOXES = [
    (F(61, 10), F(6105, 1000), F(1, 10), F(11, 100)),
    (F(20), F(2001, 100), F(0), F(1, 1000)),
    (F(30), F(3005, 1000), F(4, 10), F(1, 2)),
    (F(45), F(451, 10), F(2, 10), F(25, 100)),
    (F(7), F(71, 10), F(0), F(1, 100)),
    (F(56), F(561, 10), F(0), F(1, 2)),
]


def _arb_at(s: F, y: F):
    from flint import arb, ctx

    ctx.prec = 300
    sv = arb(s.numerator) / arb(s.denominator)
    yv = arb(y.numerator) / arb(y.denominator)
    return sv, yv


@pytest.mark.parametrize("box", BOXES)
def test_qre_iv_encloses_the_independent_evaluation(box):
    a, b, c, d = box
    Q = M.qre_iv(M.leaves2d(a, b, c, d))
    assert Q is not None
    for t in range(5):
        s, y = a + (b - a) * F(t, 4), c + (d - c) * F(t, 4)
        sv, yv = _arb_at(s, y)
        v = float(S.Qre(yv, sv).mid())
        assert Q.lo / SO <= v <= Q.hi / SO


@pytest.mark.parametrize("box", BOXES)
def test_r_iv_encloses_qim_over_y_with_the_right_sign(box):
    a, b, c, d = box
    R = M.r_iv(M.leaves2d(a, b, c, d))
    assert R is not None
    for t in range(5):
        s, y = a + (b - a) * F(t, 4), c + (d - c) * F(t, 4)
        sv, yv = _arb_at(s, y)
        v = float(S.Qim_over_y(yv, sv).mid())
        assert R.lo / SO <= v <= R.hi / SO


def test_r_iv_is_not_merely_correct_up_to_sign():
    """The negation in `r_iv` is load-bearing; drop it and this fails."""
    a, b, c, d = F(20), F(2001, 100), F(1, 10), F(11, 100)
    R = M.r_iv(M.leaves2d(a, b, c, d))
    sv, yv = _arb_at(F(20), F(1, 10))
    v = float(S.Qim_over_y(yv, sv).mid())
    assert R.lo / SO <= v <= R.hi / SO
    assert not (R.lo / SO <= -v <= R.hi / SO), "box straddles 0; pick another"


def test_the_widening_respects_the_O3_ceiling():
    """O9-SCOPING §2 knob B: exceeding this silently breaks O3."""
    assert M.O3_CEILING == F(139, 20000)
    assert M.WIDEN <= M.O3_CEILING
    with pytest.raises(ValueError):
        M.widened_windows(widen=F(1, 50))


def test_widened_windows_stay_disjoint_and_inside_the_range():
    ws = M.widened_windows()
    assert ws[0][0] > M.S_LO
    assert ws[-1][1] < M.S_HI
    for (_, hi, _), (lo, _, _) in zip(ws, ws[1:]):
        assert hi < lo


def test_gaps_tile_the_complement_exactly():
    ws = M.widened_windows()
    gs = M.gaps()
    assert len(gs) == 10
    covered = sorted([(lo, hi) for lo, hi, _ in ws] + gs)
    assert covered[0][0] == M.S_LO
    assert covered[-1][1] == M.S_HI
    for (_, hi), (lo, _) in zip(covered, covered[1:]):
        assert hi == lo


def test_caps_are_the_recorded_suprema_times_the_inflation():
    for (_, _, sup), (_, _, cap) in zip(M.WINDOWS_SUP, M.widened_windows()):
        assert cap == M.INFLATION * sup


@pytest.mark.slow
def test_the_table_closes_at_the_recommended_operating_point():
    """339 cells at `1.20x`, every one decided.

    Read against the 1-D route's 344 (`o9_leaf.N_CELLS_KERNEL`) this looks
    like a saving, and the comparison is **not** like-for-like: the 1-D table
    is built at `1.05x`.  `test_the_2d_route_is_dearer_at_equal_inflation`
    below is the honest side-by-side.  What is true is that the 2-D route is
    affordable -- at the recommended operating point it is no larger than the
    table already generated -- and that it needs no depth-reduction lemma.
    """
    v = M.validate()
    assert v["undecided"] == 0
    assert v["all_decided"]
    assert v["cells"] == 339
    assert v["max_depth"] == 17
    assert v["mode1"] + v["mode2"] == v["cells"]
    assert v["min_margin_ulp"] > 0


@pytest.mark.slow
def test_the_2d_route_is_dearer_at_equal_inflation():
    """At `1.05x`, where the 1-D table lives, the 2-D one costs 601 cells.

    So dropping `D(y,s)/y^2 <= 4 D(1/2,s)` costs +257 cells (+75%) at fixed
    inflation, or nothing at all if the extra `1.05x -> 1.20x` inflation is
    spent instead -- which the §7 budget absorbs (surplus `2.60e-02` against
    a `1.3945x` wall).  It is a trade between table size and budget margin,
    not a free lunch, and `O9-SCOPING.md`'s "45 extra leaves" understates it
    by comparing an Arb-grade 2-D count against a kernel-grade 1-D one.
    """
    import o9_leaf as A

    assert A.N_CELLS_KERNEL == 344
    v = M.validate(M.build(inflation=F(21, 20)))
    assert v["undecided"] == 0
    assert v["cells"] == 601


@pytest.mark.slow
def test_every_box_touching_y_equals_zero_decides():
    """95 of the 339 boxes reach `y = 0`, and all of them close.

    Both modes carry them (21 by mode 1, 74 by mode 2, the latter because
    `y_hi^2` is small down there).  The claim being pinned is that none is
    left undecided -- `O9-SCOPING.md` §1 measured the literal form hitting a
    depth wall exactly here.
    """
    t = M.build()
    touching = [z for z in t["cells"] if z["y_lo"] == 0]
    assert len(touching) == 95
    assert all(z["mode"] in (1, 2) for z in touching)


def test_the_literal_form_really_does_fail_where_the_removable_one_works():
    """The control for the test above, and it fires.

    At `y = 0` the literal inequality `Qim^2 - Qre^2 <= cap y^2` degenerates
    to `Qim^2 <= Qre^2`, which is false at a zero of `Qre(0, .)`.  Pick a box
    straddling one: the literal test cannot close it at any width, while the
    `R = Qim/y` form closes it immediately.  Without this, "the removable
    branch is needed" would be an assertion rather than a measurement.
    """
    from flint import arb, ctx

    ctx.prec = 300

    # `Qre(0, .)` has exactly one zero in window 0, and the window is there
    # *because* of it: damage needs `|Qim| > |Qre|`.
    a, b = F(66430, 10000), F(66455, 10000)
    zero = arb(0)
    va = float(S.Qre(zero, _arb_at(a, F(0))[0]).mid())
    vb = float(S.Qre(zero, _arb_at(b, F(0))[0]).mid())
    assert va * vb < 0, "box must straddle a zero of Qre(0, .)"

    cap = M.widened_windows()[0][2]
    for y_hi in (F(1, 8), F(1, 4), F(1, 2)):
        L = M.leaves2d(a, b, F(0), y_hi)
        Q = M.qre_iv(L)
        assert Q is not None
        # The literal route needs `inf Qre^2` to dominate; on a box holding
        # the zero that infimum is 0, so it has no room at any depth.
        assert Q.sqr().lo == 0
        # The removable form closes the same box, by mode 1, every time.
        ok, mode, margin = M.cell_verdict(a, b, F(0), y_hi, cap)
        assert ok and mode == 1 and margin > 0
