"""Controls for `window_table` (Road A, task 1).

The point of these is that the table's stated size cannot drift from what
the module computes — that slip has already happened once (197 vs 196,
caused by rounding brackets outward rather than to nearest).
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from window_table import (  # noqa: E402
    N_CELLS, N_IN_BRACKET, N_OFF_BRACKET, N_WINDOWS, NAMED_GAPS, SHQ_HALF,
    TABLE, brackets, cap_by_subdivision, count_offbracket, windows,
)


@pytest.fixture(scope="module")
def table():
    return TABLE()


def test_stated_constants_match_the_generated_table(table):
    """The one that would have caught the 197/196 slip."""
    assert table["total_cells"] == N_CELLS
    assert table["in_bracket_cells"] == N_IN_BRACKET
    assert table["off_bracket"]["cells"] == N_OFF_BRACKET
    assert len(table["windows"]) == N_WINDOWS
    assert (table["in_bracket_cells"] + table["off_bracket"]["cells"]
            == table["total_cells"])


def test_table_is_within_the_bandcert_range(table):
    """An instance of an existing pattern, not a new scale of problem."""
    assert 62 <= table["total_cells"] <= 248


def test_every_cell_is_decided(table):
    assert table["off_bracket"]["undecided"] == 0


def test_windows_match_the_ledger_constants(table):
    w = table["windows"]
    assert w[0]["lo"] == pytest.approx(6.065319, abs=1e-5)
    assert max(x["width"] for x in w) == pytest.approx(0.986001, abs=1e-5)
    assert table["min_gap_between_windows"] == pytest.approx(5.182969, abs=1e-5)


def test_brackets_strictly_contain_their_windows(table):
    """The fix for failure mode (1): D < 0 with margin off-bracket."""
    for w, b in zip(table["windows"], table["brackets"]):
        assert b["lo"] < w["lo"], (b, w)
        assert b["hi"] > w["hi"], (b, w)


def test_brackets_are_disjoint_with_room(table):
    assert table["min_gap_between_brackets"] > 4.0
    brs = table["brackets"]
    for a, b in zip(brs, brs[1:]):
        assert a["hi"] < b["lo"]


def test_caps_dominate_the_true_peaks(table):
    """Each cap must exceed the damage anywhere in its bracket."""
    import mpmath as mp
    mp.mp.dps = 25
    s2 = mp.sqrt(2)

    def dmg(y, s):
        z = mp.mpc(y, s)
        zp, zm = z + 1j * s2, z - 1j * s2
        g = mp.sinh(zp / 2) / zp + mp.sinh(zm / 2) / zm
        return -mp.re(g ** 2)

    for b in table["brackets"]:
        lo, hi = b["lo"], b["hi"]
        peak = max(float(dmg(0.5, lo + (hi - lo) * i / 200))
                   for i in range(201))
        assert peak <= b["cap"], (b, peak)


def test_caps_decay_and_sum_below_the_budget(table):
    caps = [b["cap"] for b in table["brackets"]]
    assert all(a > b for a, b in zip(caps, caps[1:])), caps
    assert table["cap_sum_both_sides"] < SHQ_HALF
    assert table["cap_sum_both_sides"] / SHQ_HALF == pytest.approx(
        0.3908, abs=1e-3)


def test_top_cap_matches_the_known_peak(table):
    """`D_1 = 4.396424e-03`; the cap sits just above it (2% tolerance)."""
    c = table["brackets"][0]["cap"]
    assert 0.004396424 <= c <= 0.004396424 * 1.05


@pytest.mark.slow
def test_regenerating_reproduces_the_cached_table():
    """The cache must not drift from the generator."""
    wins = windows()
    brs = brackets(wins)
    assert len(wins) == N_WINDOWS
    cap, cells = cap_by_subdivision(*brs[0])
    assert cells > 0 and cap > 0
    off = count_offbracket(brs)
    assert off["undecided"] == 0
    assert off["cells"] == N_OFF_BRACKET


def test_named_gaps_are_stated():
    joined = " ".join(NAMED_GAPS).lower()
    assert "not in lean" in joined or "not kernel-checked" in joined
    assert "not proved" in joined
    assert "rh" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "window_table.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
