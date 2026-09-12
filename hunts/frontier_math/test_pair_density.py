"""Controls for level 6b: pair density and the joint budget.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_pair_density.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pair_density import HARDENED_CAPFRAC, PairDensity, capfrac  # noqa: E402

PD = PairDensity()


def test_stacking_floor_is_positive_at_the_working_width() -> None:
    """Same-window pairs pay, one-sided, at every depth pair."""
    rec = PD.stacking_floor(delta_p=0.2)
    assert rec["positive"]
    assert rec["floor"] > 2.0


def test_stacking_floor_boundary_is_mapped() -> None:
    """The floor dies by delta_p = 0.3 (deep pairs), the honest edge."""
    rec = PD.stacking_floor(delta_p=0.3)
    assert not rec["positive"]
    assert rec["at_depths"][0] > 0.4  # it dies at the strip edge, not shallow


def test_separable_budget_breaks_where_expected() -> None:
    """The separable global assembly fails at mid-density deep lattices,
    the honest record that motivates the joint accounting."""
    rows = PD.global_verdict()
    worst_margin, worst_name, _ = rows[0]
    assert worst_margin < 0
    assert "y=0.49" in worst_name or "y=0.45" in worst_name


def test_compensation_collapses_with_density() -> None:
    """chi drops by ~10x from nu_p = 1 to nu_p = 2: dense pair clusters
    are nearly immune to on-line attack."""
    chi1 = PD.joint_compensation(0.45, 1.0)["chi"]
    chi2 = PD.joint_compensation(0.45, 2.0)["chi"]
    assert chi1 < 0.25
    assert chi2 < 0.05
    assert chi2 < chi1 / 3


def test_joint_budget_holds_across_the_density_sweep() -> None:
    """The level-6b headline: worst joint margin positive at every tested
    (nu_p, depth), including the pinch at nu ~ 1.25-1.5 deep."""
    pe = PD.pe
    worst = 1e9
    for nu_p in (0.75, 1.0, 1.25, 1.5, 2.0, 3.0):
        for y in (0.35, 0.45, 0.49):
            spacing = 1.0 / nu_p
            pairs = [(k * spacing, y) for k in range(int(10.0 / spacing))]
            g = PD.global_margin(pairs)
            jc = PD.joint_compensation(y, nu_p)
            slack_total = sum(pe.slack(yy) for _, yy in pairs)
            used = jc["joint_profit"] / slack_total - g["t_signed_over_slack"]
            worst = min(worst, 1.0 - used)
    assert worst > 0.05


def test_capfrac_lookup_matches_the_level6a_table() -> None:
    assert capfrac(0.45) == HARDENED_CAPFRAC[0.45]
    assert capfrac(0.44) == HARDENED_CAPFRAC[0.45]
    assert all(0.5 < v < 0.75 for v in HARDENED_CAPFRAC.values())
