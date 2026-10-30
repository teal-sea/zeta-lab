"""Pins for arch_cover's recorded numbers (added at landing, 2026-10-30).

The first write-up printed a closed form and a table row that its own
`results.json` contradicts; these tests read the record, so prose and record
cannot drift apart again unnoticed.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
GAMMA_1 = 14.134725141734694
ROWS = json.loads((HERE / "results.json").read_text())["rows"]


def _gaussian(a: float) -> dict:
    (row,) = [r for r in ROWS if r["kind"] == "gaussian" and r["param"] == a]
    return row


def test_depth_is_a_times_gamma1_squared_plus_a_quarter_over_ln10() -> None:
    """Where one zero dominates the zero side (a >= 0.15) and the enclosure
    resolves W (a <= 0.45), the cancellation depth is a (gamma_1^2 + 1/4) / ln 10:
    the pole term 2 e^{a/4} over W = 2 e^{-a gamma_1^2}."""
    for a in (0.15, 0.2, 0.3, 0.45):
        want = a * (GAMMA_1**2 + 0.25) / math.log(10)
        assert abs(_gaussian(a)["cancel_digits"] - want) < 1e-3, a


def test_the_form_first_written_fails_the_kill_condition() -> None:
    """Planted fault: a gamma_1^2 / ln 10, the form first written, misses the
    measured depth at a = 0.2 by more than the printed digits allow."""
    a = 0.2
    wrong = a * GAMMA_1**2 / math.log(10)
    assert abs(_gaussian(a)["cancel_digits"] - wrong) > 0.02


def test_the_a_045_row_and_the_table_agree() -> None:
    r = _gaussian(0.45)
    assert round(r["pole"], 3) == 2.238
    assert round(r["arch"], 3) == -1.230
    assert round(r["prime"], 3) == -1.008
    text = (HERE / "RESULTS.md").read_text()
    assert "| gaussian a=0.45 | +2.238 | -1.230 | -1.008 |" in text


def test_the_a_065_row_is_the_truncation_floor_not_a_sign() -> None:
    r = _gaussian(0.65)
    assert r["sign"] == 0 and r["W_lo"] < 0 < r["W_hi"]
    assert r["W_hi"] - r["W_lo"] < 1e-32
