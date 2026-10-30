"""Pins for decay_law. Formulas are checked directly. The recorded table is
checked against the kill arithmetic, not trusted as a printout."""

from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp
import pytest

from hunts.decay_law.decay import (
    TOLERANCE,
    endpoint_alpha,
    rect_g,
    rect_h,
    tent_g,
    tent_h,
)

HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results.json").read_text())
ROWS = RESULTS["rows"]
SUMMARY = RESULTS["summary"]


def _partnership(g, h, b, points) -> float:
    """h(r) = int g cos, with a break at the origin: the rectangle's g has a kink there, and an unsplit quadrature reports a false 1e-4."""
    worst = 0.0
    with mp.workdps(25):
        bb = mp.mpf(b)
        for r in points:
            rr = mp.mpf(r)
            integral = mp.quad(lambda u: g(b, u) * mp.cos(rr * u), [-bb, 0, bb])
            worst = max(worst, float(abs(integral - h(b, rr))))
    return worst


def test_both_families_are_normalized_at_the_origin() -> None:
    with mp.workdps(25):
        for b in (2, 4.5, 8):
            assert rect_g(b, 0) == 1
            assert tent_g(b, 0) == 1
            assert rect_h(b, 0) == b
            assert tent_h(b, 0) == 3 * mp.mpf(b) / 4


def test_the_tent_is_a_fourier_partner_of_its_cubic() -> None:
    """h(r) = int g(u) cos(r u) du, the convention of zeta.weil."""
    worst = _partnership(tent_g, tent_h, 3.0, (0, 0.4, 1.7, 6.0))
    assert worst < 1e-8, worst


def test_the_rectangle_is_a_fourier_partner_of_its_triangle() -> None:
    worst = _partnership(rect_g, rect_h, 3.0, (0, 0.4, 1.7, 6.0))
    assert worst < 1e-8, worst


def test_the_margin_is_w_over_the_prime_cost_on_every_row() -> None:
    for r in ROWS:
        assert abs(r["margin"] - r["W_zeros"] / r["cost"]) < 1e-12 * r["margin"], r["b"]
        assert abs(r["place_gap"]) < 1e-12 * r["cost"], (r["family"], r["b"])


def test_the_recomputed_rectangle_matches_the_landed_table() -> None:
    landed = {
        r["b"]: r
        for r in json.loads((HERE.parent / "weil_split" / "results.json").read_text())
    }
    got = {r["b"]: r for r in ROWS if r["family"] == "rectangle"}
    for b, L in landed.items():
        rel_W = abs(got[b]["W_zeros"] - L["W_from_zeros"]) / L["W_from_zeros"]
        rel_C = abs(got[b]["cost"] - L["cost_sum"]) / L["cost_sum"]
        assert rel_C < 1e-12, b
        assert rel_W < 1e-8, (b, rel_W)


def test_the_kill_arithmetic_matches_the_rows() -> None:
    """The recorded fire/no-fire is recomputed from the rows and the landed
    rectangle exponents. A hand edit of the summary cannot pass this."""
    landed = SUMMARY["landed_alphas"]
    tent = [r for r in ROWS if r["family"] == "tent"]
    diffs = {
        "alpha_m": endpoint_alpha(tent, "margin") - landed["alpha_m"],
        "alpha_W": endpoint_alpha(tent, "W_zeros") - landed["alpha_W"],
        "alpha_C": endpoint_alpha(tent, "cost") - landed["alpha_C"],
    }
    fired_on = [k for k, d in diffs.items() if abs(d) > TOLERANCE]
    assert SUMMARY["kill"]["fired"] == bool(fired_on)
    assert set(SUMMARY["kill"]["fired_on"]) == set(fired_on)
    for key, d in diffs.items():
        assert abs(SUMMARY["kill"]["tent_minus_landed"][key] - d) < 1e-9


def test_the_kill_tolerance_in_mission_is_the_one_the_table_uses() -> None:
    text = (HERE / "MISSION.md").read_text()
    assert "more than 0.5" in text
    assert "ln(X(2)/X(8))/ln(4)" in text
    assert SUMMARY["tolerance"] == 0.5
