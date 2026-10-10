"""Which functional the published third-autocorrelation verifier computes (issue #123).

AlphaEvolve's verification cell scores a step function by
``abs(2 * len(h) * max(convolution) / sum(h)**2)``, while the inequality
printed above it in November 2025 read ``max|f*f| >= C_3 (int f)^2``.  Hunt
#88 (``hunts/r_8539dc/``) settled the reading: the outer ``abs`` is a no-op,
so the cell computes ``A = max f*f / (int f)^2``, not
``B = max|f*f| / (int f)^2``; ``1.4557`` is a bound on ``A`` and ``1.4688`` one
on ``B``; and arXiv v2 restated the problem to match.  The hunt's numbers were
stated in ``hunts/README.md`` and ``hunts/r_8539dc/RESULTS.md`` with nothing in
CI behind them.  This file is that pin, in exact rational arithmetic on the
published ten-place heights.

The cell is re-implemented literally below and compared with both functionals,
so the statement "the verifier computes A" is a measured equality, and the
alternative verifier (``abs`` inside the max) is shown to give a different
number on the n = 400 witness, so the test can tell the two apart.
"""

from __future__ import annotations

import importlib.util
from fractions import Fraction
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PROBE = ROOT / "hunts" / "r_8539dc" / "probe.py"


@pytest.fixture(scope="module")
def probe():
    spec = importlib.util.spec_from_file_location("r_8539dc_probe", PROBE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def sequences(probe):
    import json

    raw = json.loads(probe.DATA.read_text())
    return {key: probe.exact_heights(raw[key]) for key in ("height_sequence_3", "height_sequence_4")}


def _published_cell(h: list[Fraction]) -> Fraction:
    """``abs(2 * len(h) * max(convolution) / sum(h)**2)``, exactly as written."""
    n = len(h)
    convolution = [Fraction(0)] * (2 * n - 1)
    for i, x in enumerate(h):
        for j, y in enumerate(h):
            convolution[i + j] += x * y
    return abs(2 * n * max(convolution) / sum(h) ** 2)


def _abs_inside(h: list[Fraction]) -> Fraction:
    """The verifier the printed inequality would need: ``max(abs(convolution))``."""
    n = len(h)
    convolution = [Fraction(0)] * (2 * n - 1)
    for i, x in enumerate(h):
        for j, y in enumerate(h):
            convolution[i + j] += x * y
    return 2 * n * max(abs(c) for c in convolution) / sum(h) ** 2


def test_the_published_cell_computes_A_not_B(probe, sequences):
    for heights in sequences.values():
        r = probe.functionals(heights)
        assert _published_cell(heights) == r["A"]
        assert _abs_inside(heights) == r["B"]


def test_the_n400_witness_scores_1_4557_under_A_only(probe, sequences):
    heights = sequences["height_sequence_3"]
    r = probe.functionals(heights)
    assert len(heights) == 400
    assert probe.fmt(r["A"]) == "1.455642795374540494110788362985"
    assert probe.fmt(r["B"]) == "4.334046524387984273610361795864"
    # the extreme knot is negative: knot 215 against the positive peak at 176
    assert (r["min_b_index"], r["max_b_index"]) == (215, 176)
    assert r["negative_side_dominates"]
    # an improvement on the prior 1.45810 under A, and on nothing under B
    assert r["A"] < Fraction("1.4581") and r["A"] <= Fraction("1.4557")
    assert r["B"] > Fraction("1.4993")


def test_the_n150_witness_scores_the_same_under_both(probe, sequences):
    """The control that keeps the discretisation honest: it reproduces 1.4688."""
    heights = sequences["height_sequence_4"]
    r = probe.functionals(heights)
    assert len(heights) == 150
    assert r["A"] == r["B"]
    assert probe.fmt(r["A"]) == "1.468762069741021809514483638412"
    assert not r["negative_side_dominates"]
    assert r["B"] < Fraction("1.4993") and r["B"] <= Fraction("1.4688")


def test_the_two_verifiers_disagree_where_it_matters(sequences):
    """A planted alternative: moving the abs inside changes the n = 400 score."""
    heights = sequences["height_sequence_3"]
    assert _abs_inside(heights) > 2 * _published_cell(heights)
