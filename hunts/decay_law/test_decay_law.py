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


# --- pins added at landing, 2026-10-30 -----------------------------------------
# RESULTS.md sections 3 to 6 quoted numbers no test read; three had drifted from
# results.json. These read the record and the prose together, and recompute the
# tent's endpoint rows from the formulas.

TEXT = " ".join((HERE / "RESULTS.md").read_text().split())


def _family(name: str) -> list[dict]:
    return sorted((r for r in ROWS if r["family"] == name), key=lambda r: r["b"])


def _local(rows: list[dict], key: str) -> list[float]:
    return [math.log(rows[i][key] / rows[i + 1][key]) / math.log(rows[i + 1]["b"] / rows[i]["b"])
            for i in range(len(rows) - 1)]


def test_the_printed_local_margin_exponents_are_the_record() -> None:
    for name in ("rectangle", "tent"):
        printed = ", ".join(f"{x:.1f}" for x in _local(_family(name), "margin"))
        assert printed.replace("-0.0", "0.0") in TEXT.replace("-0.0", "0.0"), name


def test_the_prime_cost_exponent_ranges_and_shares_are_the_record() -> None:
    rect, tent = _family("rectangle"), _family("tent")
    lc_r, lc_t = _local(rect, "cost"), _local(tent, "cost")
    assert f"{max(lc_r):.2f} to {min(lc_r):.2f}" in TEXT          # -2.04 to -3.37
    assert f"{max(lc_t):.2f} to {min(lc_t):.2f}" in TEXT          # -2.09 to -2.66
    assert f"never carry more than {max(r['first3_share'] for r in rect):.3f}" in TEXT


def test_the_rectangle_margin_is_not_monotone() -> None:
    """Hunt #157's "the cover margin collapses" holds endpoint to endpoint only."""
    rect = _family("rectangle")
    rises = [r["b"] for r, s in zip(rect, rect[1:]) if s["margin"] > r["margin"]]
    assert rises == [3.5, 4.0, 5.75, 6.25, 7.5]
    assert rect[-1]["margin"] < rect[0]["margin"]


def test_the_endpoint_statistic_swings_with_phase() -> None:
    import itertools

    R = {r["b"]: r["margin"] for r in _family("rectangle")}
    T = {r["b"]: r["margin"] for r in _family("tent")}
    diffs = [
        math.log(T[a] / T[c]) / math.log(c / a) - math.log(R[a] / R[c]) / math.log(c / a)
        for a, c in itertools.combinations(sorted(R), 2) if c / a >= 2.5
    ]
    assert len(diffs) == 39 and sum(abs(x) < 0.5 for x in diffs) == 3
    assert round(min(diffs), 2) == -0.17 and round(max(diffs), 2) == 4.00


def test_the_tent_endpoint_rows_recompute_from_the_formulas() -> None:
    from hunts.decay_law import decay as D

    gammas = [float(g) for g in D.zero_ordinates(t_max=D.GAMMA_MAX)]
    tent = {r["b"]: r for r in _family("tent")}
    with mp.workdps(D.DPS):
        powers = D.prime_powers(int(math.exp(8.0)) + 1)
    for b in (2.0, 8.0):
        row = D.row_fast("tent", b, gammas, powers)
        assert abs(row["W_zeros"] / tent[b]["W_zeros"] - 1) < 1e-9, b
        assert abs(row["cost"] / tent[b]["cost"] - 1) < 1e-12, b
