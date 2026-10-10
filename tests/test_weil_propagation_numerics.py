"""Headline numbers of ``hunts/weil_propagation/numerics/RESULTS.md``, pinned to their JSON.

CI collects only ``tests/``, so the hunt's own records are pinned here. Every
assertion reads a committed JSON beside RESULTS.md (``crossing.json``,
``epstein_crossing.json``, ``epstein_offline.json``) and checks it against the
value RESULTS.md states, and checks that RESULTS.md still states it. Nothing is
recomputed except the three-point extrapolation fit, which is arithmetic on
the stored brackets. No mathematics runs; the file is fast.

Grades are RESULTS.md's: the DH and Epstein bracket ends are hardened at each
N, the continuum statements add the nesting argument (Fact B, ordinary
argument, unreviewed), and the continuum lower side of the DH crossing, the
extrapolation and the Epstein zero are measured.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from pathlib import Path

import pytest

NUMERICS = Path(__file__).resolve().parents[1] / "hunts" / "weil_propagation" / "numerics"
RESULTS = NUMERICS / "RESULTS.md"


def _load(name: str) -> dict:
    with open(NUMERICS / name, encoding="utf-8") as f:
        return json.load(f)


def _results_text() -> str:
    # RESULTS.md writes minus signs as U+2212; compare in ASCII.
    return RESULTS.read_text(encoding="utf-8").replace("−", "-")


def _half_up(x: float, digits: int = 0) -> float:
    q = 10 ** digits
    return math.floor(x * q + 0.5) / q


# --------------------------------------------------------------------------
# DH crossing (RESULTS s3.2 table, lines 2 and 4)
# --------------------------------------------------------------------------

# N: (c_pos, c_neg) as RESULTS s3.2 prints them, and the bracket midpoint c*(N).
DH_ROWS = {
    64: ("30.817383", "30.818359", "30.818"),
    96: ("30.695312", "30.696289", "30.696"),
    128: ("30.646484", "30.647461", "30.647"),
    192: ("30.628906", "30.629883", "30.629"),
    256: ("30.616211", "30.617188", "30.617"),
}


@pytest.mark.parametrize("N", sorted(DH_ROWS))
def test_dh_crossing_brackets_match_results(N):
    row = _load("crossing.json")["by_N"][str(N)]
    c_pos, c_neg, mid = DH_ROWS[N]
    pos = Fraction(row["c_pos"])
    neg = Fraction(row["c_neg"])
    assert float(pos) == row["c_pos_float"] and float(neg) == row["c_neg_float"]
    assert f"{float(pos):.6f}" == c_pos
    assert f"{float(neg):.6f}" == c_neg
    assert f"{float(pos + neg) / 2:.3f}" == mid
    # Both ends strictly inside (30, 31), where the coefficient set is n <= 30,
    # and the bisection reached 2^-10.
    assert 30 < pos < neg < 31
    assert neg - pos == Fraction(1, 1024)
    # Hardened at this N: ball LDL^T at c_pos has no negative pivot, the ball
    # Rayleigh upper bound at c_neg is negative; zeta is positive there.
    assert row["hardened_positive"] is True and row["hardened_negative"] is True
    assert row["c_pos_ldl"]["inertia_at_0"] == [N + 1, 0, True]
    assert float(row["c_neg_rq_upper"]) < 0
    assert row["zeta_control_at_c_neg"]["ldl"]["inertia_at_0"] == [N + 1, 0, True]
    # The finite-N positivity at c = 30 that the measured lower side leans on.
    path = dict(row["bisection_path"])
    assert path["30"] > 0 and path["31"] < 0
    text = _results_text()
    assert f"| {N} | {c_pos} | {c_neg} | ({N + 1}, 0), positive |" in text


def test_dh_headline_line_is_qualified():
    lines = _results_text().splitlines()
    line2 = lines[1]
    mids = ", ".join(DH_ROWS[N][2] for N in sorted(DH_ROWS))
    assert line2.startswith("2. **Found:**")
    assert "every window c ≥ 30.617188" in line2
    assert f"c*(N) = {mids} for N = 64..256" in line2
    assert "at each N ≤ 256 hardened" in line2
    assert "continuum lower side measured" in line2
    assert "extrapolation to ≈ 30.61" in line2
    # The unqualified reading withdrawn on review must not come back.
    assert "strictly between the coefficients n = 30 and 31, so positivity is lost" not in line2
    assert str(Fraction(_load("crossing.json")["by_N"]["256"]["c_neg"])) == "3919/128"


def test_dh_extrapolation_fit_matches_results():
    """c* = c_inf + a N^-p through the midpoints at N = 64, 128, 256 (measured)."""
    by_n = _load("crossing.json")["by_N"]
    mid = {
        N: float(Fraction(by_n[str(N)]["c_pos"]) + Fraction(by_n[str(N)]["c_neg"])) / 2
        for N in DH_ROWS
    }
    d1 = mid[64] - mid[128]
    d2 = mid[128] - mid[256]
    p = math.log2(d1 / d2)
    c_inf = mid[256] - d2 / (2**p - 1)
    a = (mid[64] - c_inf) * 64**p
    assert f"{p:.2f}" == "2.50"
    assert f"{c_inf:.3f}" == "30.610"
    assert f"{c_inf + a * 96**-p:.3f}" == "30.686"
    assert f"{c_inf + a * 192**-p:.3f}" == "30.624"
    text = _results_text()
    assert "p = 2.50, c∞ = 30.610" in text
    assert "predicts 30.686 and 30.624 at N = 96 and 192" in text


# --------------------------------------------------------------------------
# Epstein (1,1,6) crossing (RESULTS s9.2 table, line 4, s9.3)
# --------------------------------------------------------------------------

# (N, sector): (last positive c, first negative c, lambda_min at first negative)
EPSTEIN_ROWS = {
    (64, "odd"): ("27.804688", "27.805176", "-7.932242799e-7"),
    (128, "odd"): ("27.741211", "27.741699", "-1.292835817e-6"),
    (64, "even"): ("29.340820", "29.341309", "-1.236643810e-6"),
    (128, "even"): ("29.303711", "29.304199", "-4.219861683e-6"),
}


@pytest.mark.parametrize("key", sorted(EPSTEIN_ROWS))
def test_epstein_crossing_rows_match_results(key):
    N, sector = key
    row = _load("epstein_crossing.json")["runs"][f"{N}|{sector}"]
    c_pos, c_neg, lam = EPSTEIN_ROWS[key]
    pos = Fraction(row["c_pos"])
    neg = Fraction(row["c_neg"])
    assert f"{float(pos):.6f}" == c_pos
    assert f"{float(neg):.6f}" == c_neg
    assert 0 < neg - pos <= Fraction(1, 1024)
    assert row["n_neg_at_c_pos"] == 0 and row["n_neg_at_c_neg"] == 1
    assert row["hardened_negative_two_routes"] is True
    assert row["rq_upper_at_c_neg"] == lam and float(lam) < 0
    assert row["lam1_at_c_neg"].startswith(f"[{lam} +/- ")
    assert row["dedekind_n_neg_at_c_neg"] == 0
    # No return to positivity on the grid after the first negative cell.
    assert row["positive_grid_cells_after_first_negative"] == []
    assert f"| {N} | {sector} | {c_pos} | {c_neg} | {lam} | positive definite |" in _results_text()


def test_epstein_rounded_values_quoted_in_the_text():
    runs = _load("epstein_crossing.json")["runs"]
    odd128 = float(Fraction(runs["128|odd"]["c_neg"]))
    even128 = float(Fraction(runs["128|even"]["c_neg"]))
    even64 = float(Fraction(runs["64|even"]["c_neg"]))
    assert f"{odd128:.4f}" == "27.7417"
    assert f"{even128:.3f}" == "29.304" and f"{even128:.4f}" == "29.3042"
    assert f"{even64:.4f}" == "29.3413"
    text = _results_text()
    assert "negative on every window c ≥ 27.7417" in text
    assert "every window c ≥ 27.741699" in text
    assert "turns negative at c = 29.3042 (N = 128; 29.3413 at N = 64)" in text
    assert "Epstein's even pole capacity fails at c = 29.304" in text


# --------------------------------------------------------------------------
# Epstein off-line zero, independent route (RESULTS s9.2, line 4; measured)
# --------------------------------------------------------------------------


def test_epstein_offline_zero_matches_results():
    d = _load("epstein_offline.json")
    assert d["meta"]["form"] == [1, 1, 6] and d["meta"]["dps"] == 20
    boxes = d["boxes"]
    assert boxes["[0.51,1.3]x[14,20]"]["count"] == 1
    assert boxes["[0.51,1.3]x[7,14]"]["count"] == 0
    assert boxes["[0.51,1.3]x[0.5,7]"]["count"] == 0
    assert _half_up(boxes["[0.51,1.3]x[0.5,7]"]["elapsed_s"]) == 159
    assert _half_up(boxes["[0.51,1.3]x[7,14]"]["elapsed_s"]) == 273
    (root,) = d["roots"]
    beta, gamma = root["root"]
    assert (beta, gamma) == ("0.953260474794661", "16.2902157203904")
    assert 0.51 <= float(beta) <= 1.3 and 14 <= float(gamma) <= 20
    assert f"{float(root['abs_value']):.1e}" == "1.4e-32"
    assert f"{float(beta) - 0.5:.3f}" == "0.453"
    text = _results_text()
    assert f"ρ₁ = {beta} + {gamma} i,   |Λ_Q(ρ₁)| = 1.4e-32 (dps 20)" in text
    assert f"its off-line zero {float(beta):.3f} + {float(gamma):.3f}i" in text
    assert "δ = β - 1/2 = 0.453" in text
    assert "no zeros in [0.51, 1.3] × [0.5, 7] and none in" in text
    assert "(159 s and 273 s)" in text
