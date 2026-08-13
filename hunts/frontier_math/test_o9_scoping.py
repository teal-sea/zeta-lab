"""Pins for `o9_scoping.py`.

Run explicitly (the repo's `testpaths` is `tests/`):

    .venv/bin/python -m pytest -q hunts/frontier_math/test_o9_scoping.py
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from flint import arb  # noqa: E402

from o9_scoping import (  # noqa: E402
    ACONST,
    WIDEN,
    WINDOWS,
    Qim,
    Qim_over_y,
    Qre,
    Shq,
    complement_leaf_count,
    damage_raw,
    integer_trade,
    leaf_count,
    max_inflation,
    total_deficit,
    window_sup,
)


# ---------------------------------------------------------------------------
# The closed forms are the ones RETENTION-PROBLEM.md pins
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "got,want",
    [
        (lambda: ACONST, 0.91872537),
        (lambda: Qre(arb(0), arb(1)) ** 2, 0.78066657),
        (lambda: Qre(arb(0), arb(6)) ** 2, 0.00834800),
        (lambda: Shq(arb(1) / 2) / 2, 0.03375420),
        (lambda: damage_raw(arb(1) / 2, arb("6.517")), 0.00439642),
    ],
)
def test_closed_forms_match_the_pinned_values(got, want) -> None:
    assert float(got()) == pytest.approx(want, abs=5e-9)


def test_qre_at_the_origin_is_the_constant() -> None:
    assert float(Qre(arb(0), arb(0))) == pytest.approx(float(ACONST), abs=1e-30)


def test_qim_vanishes_at_zero_depth() -> None:
    assert float(Qim(arb(0), arb(5))) == 0.0


def test_the_removable_branch_agrees_away_from_zero() -> None:
    y, s = arb("0.37"), arb("6.4")
    assert float(Qim_over_y(y, s)) == pytest.approx(float(Qim(y, s) / y), abs=1e-30)


# ---------------------------------------------------------------------------
# The recorded caps are suprema, which is why the bare statement has no margin
# ---------------------------------------------------------------------------


def test_the_recorded_cap_is_the_supremum_not_a_bound() -> None:
    """The load-bearing observation: `c_0` is attained, so `Dam <= c_0 y^2` is tight."""
    lo, hi, cap = WINDOWS[0]
    sup, _s, y_at = window_sup(lo, hi, ns=600, ny=40)
    ratio = sup / float(cap)
    assert 0.999 < ratio <= 1.0, f"c_0 is not the attained supremum (ratio {ratio})"
    assert y_at == pytest.approx(0.5, abs=1e-9), "the maximiser sits at the deepest y"


def test_widening_a_window_does_not_raise_its_cap() -> None:
    """The added strips carry no damage, so the caps survive the widening."""
    for lo, hi, cap in WINDOWS[:3]:
        sup, _s, _y = window_sup(lo - WIDEN, hi + WIDEN, ns=300, ny=24)
        assert sup <= float(cap)


# ---------------------------------------------------------------------------
# The §7 accounting, reproduced from the caps
# ---------------------------------------------------------------------------


def test_the_final_arithmetic_reproduces_section_7() -> None:
    base = total_deficit(Fraction(1))
    assert float(base["windows"]) == pytest.approx(7.5279200e-02, rel=1e-7)
    assert float(base["far"]) == pytest.approx(3.6305145e-03, rel=1e-6)
    assert float(base["tail"]) == pytest.approx(5.4146340e-04, rel=1e-6)
    assert float(base["deficit"]) == pytest.approx(7.9451178e-02, rel=1e-7)
    assert float(base["budget"]) == pytest.approx(1.2986000e-01, rel=1e-12)
    assert float(base["surplus"]) == pytest.approx(5.0408822e-02, rel=1e-6)


def test_the_integer_trade_picks_three_in_the_first_window() -> None:
    """§7's `k=0` row: the best multiplicity is 3, worth 2.9357160e-02."""
    _lo, _hi, cap = WINDOWS[0]
    v = Fraction(1, 4)
    assert float(integer_trade(cap * v, Fraction(39, 10000))) == pytest.approx(
        2.9357160e-02, rel=1e-7
    )


def test_headroom_allows_a_cap_inflation_near_one_point_four() -> None:
    infl = max_inflation()
    assert 1.39 < float(infl) < 1.40
    assert total_deficit(infl)["surplus"] > 0
    assert total_deficit(infl * Fraction(101, 100))["surplus"] < 0


# ---------------------------------------------------------------------------
# The subdivision cost
# ---------------------------------------------------------------------------


def test_the_bare_caps_do_not_terminate() -> None:
    """At inflation 1.00x the first window exhausts the depth budget."""
    lo, hi, cap = WINDOWS[0]
    _n, _d, ok = leaf_count(lo - WIDEN, hi + WIDEN, cap, max_depth=22)
    assert not ok, "a tight inequality should not close under interval arithmetic"


def test_a_twenty_percent_inflation_closes_every_window_cheaply() -> None:
    infl = Fraction(6, 5)
    assert total_deficit(infl)["surplus"] > 0
    total = 0
    deepest = 0
    for lo, hi, cap in WINDOWS:
        n, d, ok = leaf_count(lo - WIDEN, hi + WIDEN, cap * infl, max_depth=30)
        assert ok
        total += n
        deepest = max(deepest, d)
    assert total <= 80, f"window leaves grew to {total}"
    assert deepest <= 8


def test_the_complement_closes_once_the_windows_are_widened() -> None:
    bare_n, _bare_d, bare_ok, _g = complement_leaf_count(Fraction(0), max_depth=22)
    assert not bare_ok, "the bare window edge is a tangency and should not close"

    n, d, ok, gaps = complement_leaf_count(WIDEN, max_depth=30)
    assert ok
    assert len(gaps) == 10
    assert n <= 260, f"complement leaves grew to {n}"
    assert d <= 14


def test_the_whole_object_is_smaller_than_the_band_certificate() -> None:
    """~264 leaves against the 3005 recorded integers of `BandCert/Data.lean`."""
    infl = Fraction(6, 5)
    windows = sum(
        leaf_count(lo - WIDEN, hi + WIDEN, cap * infl, max_depth=30)[0]
        for lo, hi, cap in WINDOWS
    )
    comp, _d, ok, _g = complement_leaf_count(WIDEN, max_depth=30)
    assert ok
    assert windows + comp < 400
