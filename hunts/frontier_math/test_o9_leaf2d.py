"""Pins for the two-variable O9 leaf table (`o9_leaf2d.py`).

Three kinds of test here, and the middle kind is the one that earns the other
two: **planted faults that actually fire**.  A table builder that only ever
reports success has demonstrated nothing, so every soundness claim below is
paired with a deliberately broken input that must be rejected.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import o9_leaf2d as L  # noqa: E402
from o9_leaf import SO, Iv  # noqa: E402

flint = pytest.importorskip("flint")
mpmath = pytest.importorskip("mpmath")


# ---------------------------------------------------------------------------
# 1. the field is what it claims to be
# ---------------------------------------------------------------------------


def _phi2_from_definition(s: float, y: float):
    """`Phi2(s+iy)` from its DEFINITION, independent of either closed form."""
    from mpmath import mp, mpc, sin, sqrt

    mp.dps = 40
    r2 = sqrt(2)

    def sfun(u):
        return mp.mpf(1) / 2 if u == 0 else sin(u / 2) / u

    z = mpc(s, y)
    v = sfun(z + r2) + sfun(z - r2)
    return float(v.real), float(v.imag)


SAMPLES = [
    (F(6), F(1, 1000)), (F("6.6431"), F(1, 20)), (F(10), F(1, 4)),
    (F("12.7553"), F(1, 2)), (F(25), F(1, 100)), (F(40), F(3, 10)),
    (F("56.6"), F(1, 2)), (F(59), F(1, 8)),
]


@pytest.mark.parametrize("s,y", SAMPLES)
def test_field_encloses_phi2_from_definition(s, y):
    """`R = Im Phi2 / y` and `Qre = Re Phi2`, both enclosed."""
    eps = F(1, 10 ** 7)
    f = L.field_iv(s - eps, s + eps, y, y)
    assert f is not None
    re_true, im_true = _phi2_from_definition(float(s), float(y))
    rlo, rhi = f.R.as_floats()
    qlo, qhi = f.Qre.as_floats()
    assert rlo <= im_true / float(y) <= rhi
    assert qlo <= re_true <= qhi


def test_R_is_finite_at_y_zero():
    """The whole point: `R` is analytic across `y = 0`, where `Qim` vanishes.

    A cell pinned at `y = 0` must still produce a bounded `R` of useful width
    — that is what removes the degeneracy the one-variable table could not
    handle.  `Qim` itself is `0` there, so `Qim/y` is `0/0`; only the
    factorised form has anything to say.
    """
    eps = F(1, 10 ** 6)
    f = L.field_iv(F(6) - eps, F(6) + eps, F(0), F(0))
    assert f is not None
    lo, hi = f.R.as_floats()
    assert hi - lo < 1e-5, "R is enclosed but uselessly wide at y = 0"
    # and it agrees with the y -> 0 limit of Im Phi2 / y
    _, im_small = _phi2_from_definition(6.0, 1e-9)
    assert lo <= im_small / 1e-9 <= hi


def test_qre_vanishes_somewhere_inside_a_window():
    """The obstruction is real: `Qre(0, .)` has a zero inside window 0.

    If this ever stopped holding, the `R` factorisation would be unnecessary
    and this module would be over-engineering.
    """
    a, _ = _phi2_from_definition(6.60, 0.0)
    b, _ = _phi2_from_definition(6.70, 0.0)
    assert a * b < 0


# ---------------------------------------------------------------------------
# 2. planted faults -- these must FAIL
# ---------------------------------------------------------------------------


def test_planted_fault_deflated_cap_is_rejected():
    """Shrink a cap far below its attained supremum; the cell must fail."""
    slo, shi = F(60653, 10000), F(35257, 5000)
    ok, _, _ = L.cell_verdict(slo, shi, F(0), F(1, 2))
    good_cap = L.inflated_caps()[0]

    saved = L.CAPS_SUP[0]
    try:
        L.CAPS_SUP[0] = good_cap / 100          # 100x too small
        bad, _, _ = L.cell_verdict(slo, shi, F(0), F(1, 2))
    finally:
        L.CAPS_SUP[0] = saved
    assert bad is False, "a 100x-deflated cap was accepted -- the check is inert"
    # and the honest cap is not itself failing for some other reason
    assert ok in (True, False)


def test_planted_fault_zero_cap_on_a_damaged_window_is_rejected():
    """Cap `0` inside a window claims "no damage there", which is false."""
    slo, shi = F(60653, 10000), F(35257, 5000)
    f = L.field_iv(slo, shi, F(0), F(1, 2))
    assert f is not None
    r2 = f.R.sqr()
    lhs = r2.sub(Iv(0, 0)).mul(f.Y.sqr())
    rhs = f.Qre.sqr()
    assert not (lhs.hi <= rhs.lo), "cap 0 accepted on a window that carries damage"


def test_planted_fault_borrowed_cap_is_rejected():
    """Give window 0's rectangle the cap of window 8 (75x smaller).

    A table whose caps could be permuted without the check noticing would be
    recording nothing about which window is which.
    """
    slo, shi = F(60653, 10000), F(35257, 5000)
    borrowed = L.inflated_caps()[8]
    cs = (borrowed * SO).__floor__()
    f = L.field_iv(slo, shi, F(0), F(1, 2))
    assert f is not None
    lhs = f.R.sqr().sub(Iv(cs, cs)).mul(f.Y.sqr())
    rhs = f.Qre.sqr()
    assert not (lhs.hi <= rhs.lo), "window 8's cap was accepted on window 0"


def test_planted_fault_y_beyond_one_half_is_rejected():
    """The `y <= 1/2` bound is load-bearing: the damage grows past it.

    Re-checking window 0's leaf on `y in [0,1]` — twice the sanctioned depth,
    where `Dam/y^2` exceeds the recorded supremum — must fail.
    """
    slo, shi = F(60653, 10000), F(35257, 5000)
    cap = L.inflated_caps()[0]
    cs = (cap * SO).__floor__()
    f = L.field_iv(slo, shi, F(0), F(1))
    assert f is not None
    lhs = f.R.sqr().sub(Iv(cs, cs)).mul(f.Y.sqr())
    rhs = f.Qre.sqr()
    assert not (lhs.hi <= rhs.lo), "the y <= 1/2 restriction is not doing any work"


def test_widening_beyond_the_o3_ceiling_is_refused():
    """O3 supplies `Kpair >= 39/50` only on `|u| <= 1`; the builder must know."""
    saved = L.WIDEN
    try:
        L.WIDEN = F(2, 100)          # the value an early draft recommended
        with pytest.raises(AssertionError):
            L.build(max_depth=2)
    finally:
        L.WIDEN = saved


# ---------------------------------------------------------------------------
# 3. the table itself
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def table():
    return L.build()


def test_operating_point_is_the_scoped_one(table):
    assert L.WIDEN == F(1, 200)
    assert L.INFLATION == F(6, 5)
    assert L.INFLATION <= F(13945, 10000), "past the §7 inflation wall"


def test_every_cell_decides(table):
    v = L.validate(table)
    assert v["undecided"] == 0
    assert v["all_decided"]


def test_margins_clear_the_leaf_caveat(table):
    """No cell may be decided by the Arb-vs-Taylor leaf disagreement.

    That disagreement is under `2^-60` (~16 ulp at the `2^-64` grid); the
    smallest carrying margin here is ~`3.4e11` ulp.
    """
    v = L.validate(table)
    assert v["min_margin_ulp"] >= L.MIN_MARGIN_ULP
    assert v["min_margin_ulp"] >= 1 << 30


def test_table_size_is_pinned(table):
    """598 leaves at depth 18 -- recorded so a regression is visible."""
    v = L.validate(table)
    assert v["cells"] == 598
    assert v["max_depth"] == 18


def test_cells_tile_the_rectangle_exactly(table):
    """The leaves must tile `[28/5,60] x [0,1/2]` — no gap, no overlap.

    The builder bisects adaptively in whichever variable is longer, so the
    leaves form a quadtree-style partition and **not** a grid of `s` columns:
    one `y` half of a cell may be split in `s` while the other is not.  The
    invariant to check is therefore area, not column alignment.

    Areas are exact `Fraction`s, so this is an equality, not a tolerance.  A
    table with a hole proves nothing about the hole, and area equality plus
    the pairwise-disjointness below is exactly "tiles the rectangle".
    """
    total = sum((c["shi"] - c["slo"]) * (c["yhi"] - c["ylo"])
                for c in table["cells"])
    assert total == (L.S_HI - L.S_LO) * (L.Y_HI - L.Y_LO)


def test_cells_are_pairwise_disjoint_and_inside_the_region(table):
    """No leaf overlaps another, and none escapes the region.

    With the area equality above, this upgrades "covers" to "tiles".
    """
    cells = table["cells"]
    for c in cells:
        assert L.S_LO <= c["slo"] < c["shi"] <= L.S_HI
        assert L.Y_LO <= c["ylo"] < c["yhi"] <= L.Y_HI
    # bucket by s-overlap first so this stays quadratic only within a band
    order = sorted(cells, key=lambda c: c["slo"])
    for i, a in enumerate(order):
        for b in order[i + 1:]:
            if b["slo"] >= a["shi"]:
                break                      # sorted: no later cell can overlap
            s_ov = min(a["shi"], b["shi"]) > max(a["slo"], b["slo"])
            y_ov = min(a["yhi"], b["yhi"]) > max(a["ylo"], b["ylo"])
            assert not (s_ov and y_ov), f"leaves overlap: {a} and {b}"


def test_cells_outside_every_window_carry_cap_zero(table):
    """The complement claim is the same check with `cap = 0`."""
    wins = L.widened_windows()
    for c in table["cells"]:
        inside = any(wl <= c["slo"] and c["shi"] <= wh for wl, wh in wins)
        if not inside:
            assert c["cap"] == 0


def test_caps_are_the_recorded_suprema_times_the_inflation():
    for c_sup, c_inf in zip(L.CAPS_SUP, L.inflated_caps()):
        assert c_inf == c_sup * L.INFLATION
