"""Controls for `mean_damage` (Road B, step 1)."""

from __future__ import annotations

import sys
from pathlib import Path

import mpmath as mp
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from mean_damage import (  # noqa: E402
    A_CONST, C2_ZERO, MEAN_DAMAGE, NAMED_GAPS, c2, c2_zero, damage,
    ghat, integral_ladder, integral_of_damage, mean_collection,
)


def test_c2_zero_closed_form():
    """`c2(0) = 1/2 + sin(sqrt2)/(2 sqrt2)`, against quadrature."""
    assert abs(float(c2(0)) - float(c2_zero())) < 1e-16
    assert float(c2_zero()) == pytest.approx(C2_ZERO, abs=1e-15)


def test_recorded_constant_matches_the_closed_form():
    assert MEAN_DAMAGE == pytest.approx(
        float(-2 * mp.pi * c2_zero()), abs=1e-13)


def test_c2_is_supported_in_the_unit_interval():
    assert float(c2(1.0)) == pytest.approx(0.0, abs=1e-18)
    assert float(c2(1.5)) == 0.0
    assert float(c2(0.5)) > 0.0


@pytest.mark.slow
def test_integral_is_flat_in_depth():
    """The identity's content: no `y` on the right-hand side."""
    lad = integral_ladder(S=1500.0)
    assert lad["y_spread"] < 1e-3, lad
    for r in lad["rows"]:
        assert r["diff_from_closed_form"] < 5e-3, r


@pytest.mark.slow
def test_integral_tail_shrinks_like_one_over_S():
    """The residual is truncation, not an error in the identity."""
    target = float(-2 * mp.pi * c2_zero())
    d1 = abs(float(integral_of_damage(0.5, 500.0)) - target)
    d2 = abs(float(integral_of_damage(0.5, 1500.0)) - target)
    assert d2 < d1, (d1, d2)
    assert d1 < 2e-2 and d2 < 1e-2


def test_integral_is_negative_at_every_depth():
    for y in (0.05, 0.25, 0.5):
        assert float(integral_of_damage(y, 400.0)) < -5.0


@pytest.mark.slow
@pytest.mark.parametrize("xs", [[0.0], [0.0] * 3, [0.0] * 8,
                                [-70.0, -50, -30, -10, 10, 30, 50, 70]])
def test_mean_collection_matches_prediction(xs):
    """Mean over placements = n * int D / (2L), coincident or spread."""
    m = mean_collection(xs)
    assert m["measured"] < 0.0
    assert m["rel_error"] < 5e-3, m


def test_mean_collection_scales_with_n():
    a = mean_collection([0.0], L=300.0)
    b = mean_collection([0.0] * 4, L=300.0)
    assert b["measured"] / a["measured"] == pytest.approx(4.0, rel=0.02)


def test_damage_and_ghat_agree_with_the_tree_constants():
    assert A_CONST == pytest.approx(0.9187253698655684, abs=1e-15)
    assert float(damage(0.5, 6.516999776)) == pytest.approx(0.004396424, abs=1e-8)
    assert float(damage(0.5, 0.0)) < 0.0
    assert abs(complex(ghat(0)) .real - A_CONST) < 1e-15


def test_positive_damage_is_the_exception_not_the_rule():
    """The qualitative content: most placements collect nothing."""
    pos = sum(1 for i in range(4000)
              if float(damage(0.5, 5.6 + i * (60 - 5.6) / 4000)) > 0)
    assert pos / 4000 < 0.20


def test_named_gaps_are_stated():
    joined = " ".join(NAMED_GAPS).lower()
    assert "not written in lean" in joined
    assert "not road b" in joined
    assert "rh" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "mean_damage.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
