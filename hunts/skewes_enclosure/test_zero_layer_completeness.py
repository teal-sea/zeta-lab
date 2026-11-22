"""Pins for route 3 (issue #392): the mpmath windowed completeness cross-check.

The negative control is the point, at small scale: delete one ordinate from a
60-row local table and the windowed count fails at the right window, while the
weak count-versus-smooth |S(T)| check still passes. KIDA-Nya's original runs
the same control on Odlyzko's 100k table (zeta-audit); nothing here downloads
a table. The fixture is generated locally by route 1 and handed to route 3 as
decimal strings, in the shape of an external table. Route 3 itself reads only
zeta values through mpmath, so the control measures the check, not the fixture.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

flint = pytest.importorskip("flint")

sys.path.insert(0, str(Path(__file__).resolve().parent))
import zero_layer as zl  # noqa: E402

#: Window placement for the control: three 10-row windows, 0-based starts.
STARTS = [5, 25, 45]
ROWS = 10
#: 0-based index deleted by the negative control. It lies inside the middle
#: window (rows 25 to 34) and outside the other two.
DELETED = 30


@pytest.fixture(scope="module")
def zeros60():
    g, _ = zl.arb_zeros(1, 60, batch=60)
    return g


@pytest.fixture(scope="module")
def table60(zeros60):
    """The first 60 ordinates as decimal strings, an external-table shape."""
    return [g.mid().str(30, radius=False) for g in zeros60]


def test_fixture_is_the_first_60_ordinates(table60):
    assert len(table60) == 60
    assert abs(float(table60[0]) - 14.134725141734694) < 1e-12
    assert abs(float(table60[2]) - 25.010857580145689) < 1e-12
    assert all(float(a) < float(b) for a, b in zip(table60, table60[1:]))


def test_intact_table_agrees_in_every_window(table60):
    r = zl.check_completeness_mpmath(table60, window_rows=ROWS, starts=STARTS)
    assert r["all_agree"] and r["failures"] == []
    assert [w["independent_count"] for w in r["windows"]] == [ROWS] * 3
    assert all(w["seconds"] > 0 for w in r["windows"]) and r["seconds"] > 0
    # The honest labels are part of the result, so they cannot quietly lapse.
    assert "second opinion" in r["grade"] and "not a certificate" in r["grade"]
    assert "sampled windows only" in r["coverage"]


def test_negative_control_one_deleted_ordinate(table60):
    """Delete one row inside the middle window: only that window fails, and
    the weak |S(T)| < 3 sanity check does not catch the hole at all."""
    holed = table60[:DELETED] + table60[DELETED + 1:]
    assert len(holed) == 59 and holed[DELETED] == table60[DELETED + 1]

    r = zl.check_completeness_mpmath(holed, window_rows=ROWS, starts=STARTS)
    assert not r["all_agree"] and r["failures"] == [25]
    assert [w["agree"] for w in r["windows"]] == [True, False, True]
    middle = r["windows"][1]
    assert middle["table_count"] == ROWS and middle["independent_count"] == ROWS + 1

    weak_intact = zl.count_vs_smooth(table60)
    weak_holed = zl.count_vs_smooth(holed)
    assert weak_intact["count"] == 60 and weak_holed["count"] == 59
    assert weak_intact["abs_S_lt_3"] and weak_holed["abs_S_lt_3"]
    shift = float(weak_intact["S_implied"]) - float(weak_holed["S_implied"])
    assert abs(shift - 1.0) < 1e-9  # one missing zero moves S by exactly 1


def test_hole_outside_the_sampled_windows_is_missed(table60):
    """The sampled limitation, pinned: a deletion between windows passes."""
    holed = table60[:20] + table60[21:]
    r = zl.check_completeness_mpmath(holed, window_rows=ROWS, starts=STARTS)
    assert r["all_agree"]


def test_default_sampled_starts_agree_on_intact(table60):
    r = zl.check_completeness_mpmath(table60, windows=3, window_rows=ROWS)
    assert r["all_agree"] and len(r["windows"]) == 3


def test_windows_accept_arb_balls(zeros60):
    """The shard shape: gammas straight from arb_zeros, midpoints read off."""
    r = zl.check_completeness_mpmath(zeros60, window_rows=ROWS, starts=STARTS)
    assert r["all_agree"]


def test_count_vs_smooth_honours_a_shard_offset(table60):
    full = zl.count_vs_smooth(table60)
    tail = zl.count_vs_smooth(table60[10:], n0=11)
    assert tail["count"] == full["count"] == 60
    assert abs(float(tail["S_implied"]) - float(full["S_implied"])) < 1e-9


def test_midpoints_are_strictly_between_ordinates(table60):
    w = zl.mpmath_window_count(table60, 25, ROWS)
    assert float(table60[24]) < float(w["lo"]) < float(table60[25])
    assert float(table60[34]) < float(w["hi"]) < float(table60[35])


def test_nzeros_at_an_ordinate_is_unreliable(table60):
    """Why route 3 never evaluates there: at gamma_1 and gamma_3 the count
    comes back one short, while the midpoint after gamma_3 counts 3."""
    import mpmath

    with mpmath.workdps(30):
        g = [mpmath.mpf(s) for s in table60[:10]]
        assert int(mpmath.nzeros(g[0])) == 0
        assert int(mpmath.nzeros(g[2])) == 2
        assert int(mpmath.nzeros(g[9])) == 10  # gamma_10 happens to round up
        assert int(mpmath.nzeros((g[2] + g[3]) / 2)) == 3


def test_refuses_windows_without_an_outer_ordinate(table60):
    with pytest.raises(ValueError):
        zl.mpmath_window_count(table60, 0, ROWS)
    with pytest.raises(ValueError):
        zl.mpmath_window_count(table60, 50, ROWS)  # no ordinate past the window
    with pytest.raises(ValueError):
        zl.check_completeness_mpmath(table60, window_rows=59, starts=STARTS)
    with pytest.raises(ValueError):
        zl.check_completeness_mpmath(table60, window_rows=ROWS, starts=[])


def test_refuses_a_duplicated_boundary_ordinate(table60):
    dup = list(table60)
    dup[25] = dup[24]  # midpoint would land on the ordinate itself
    with pytest.raises(ValueError):
        zl.mpmath_window_count(dup, 25, ROWS)
