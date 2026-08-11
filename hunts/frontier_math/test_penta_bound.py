"""Controls for level 6a: the pentadiagonal dual and theta_full.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_penta_bound.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from counting_bound import CountingBound  # noqa: E402
from pair_energy import PairEnergy  # noqa: E402
from penta_bound import PentaBound, eta_optimal, hardened_assembly  # noqa: E402
from theta_recovery import Recovery  # noqa: E402

PB = PentaBound()
CB = CountingBound()
PE = PairEnergy()
REC = Recovery()


# -- the charge triples -------------------------------------------------------


def test_charges_are_ordered_and_one_sided() -> None:
    for d in PB.delta_choices:
        K1, K2, K3 = PB.charges(d)
        assert K1 > K2 > K3 >= 0
        # one-sided against direct samples in each range
        for r in (d / 2, d):
            assert REC.omega_sq(r) >= K1 - 1e-12
        for r in (d, 1.5 * d, 2 * d):
            assert REC.omega_sq(r) >= K2 - 1e-12
        for r in (1.2 * d, 2 * d, 3 * d):
            assert REC.omega_sq(r) >= K3 - 1e-12


def test_third_range_dies_past_omega_first_stretch() -> None:
    assert PB.K_range(0.35, 1.05) == 0.0


# -- the DP -------------------------------------------------------------------


def test_penta_reduces_to_tri_when_K3_vanishes() -> None:
    """With the third range past omega's first stretch, K3 = 0 exactly and
    the DPs must agree (delta = 0.3125 keeps per_cell integral)."""
    assert PB.K_range(0.3125, 3 * 0.3125) == 0.0
    y = 0.3
    y2 = y * 1.001
    sups = CB.fine_sups(y, y2)  # same fine grid spec
    penta = PB.lambda_bar_from_sups(0.0, sups, y2, 0.3125)
    tri = CB.lambda_bar_from_sups(0.0, sups, y2, 0.3125)
    assert abs(penta - tri) < 1e-6


def test_penta_never_exceeds_tri_on_the_shared_ladder() -> None:
    """More charges can only lower the adversary's value."""
    for y in (0.15, 0.35):
        y2 = y * 1.01
        sups = CB.fine_sups(y, y2)
        for d in (0.25, 0.3):
            penta = PB.lambda_bar_from_sups(0.1, sups, y2, d)
            tri = CB.lambda_bar_from_sups(0.1, sups, y2, d)
            assert penta <= tri + 1e-9


def test_penta_dominates_measured_adversaries() -> None:
    """The projection rule, applied to the sharpened bound."""
    for y in (0.15, 0.35, 0.45):
        y2 = y * 1.01
        sups = PB.fine_sups(y, y2)
        cap = min(
            PB.lambda_bar_from_sups(0.0, sups, y2, d) for d in PB.delta_choices
        )
        measured = max(
            REC.slack(y) - REC.lattice_net(0.0, y, sp) for sp in (1.0, 0.5, 0.25)
        )
        measured = max(measured, REC.slack(y) - REC.greedy_net(0.0, y, 8, kmax=8))
        assert measured <= cap + 1e-9


def test_penta_gains_where_the_level5_deficit_lived() -> None:
    """Mid depths were the overdraw's home; the gain must be real there."""
    y = 0.25
    y2 = y * 1.01
    sups_p = PB.fine_sups(y, y2)
    sups_t = CB.fine_sups(y, y2)
    penta = min(PB.lambda_bar_from_sups(0.0, sups_p, y2, d) for d in PB.delta_choices)
    tri = min(CB.lambda_bar_from_sups(0.0, sups_t, y2, d) for d in CB.delta_choices)
    assert penta < 0.85 * tri


# -- the optimal split --------------------------------------------------------


def test_eta_optimal_beats_the_proportional_split_max() -> None:
    grid = (0.05, 0.15, 0.25, 0.35, 0.45, 0.49)
    etas = eta_optimal(PE, 1.0, y_grid=grid)
    proportional_max = max(PE.eta_by_depth(1.0, grid).values())
    assert max(etas.values()) <= proportional_max + 1e-9
    assert max(etas.values()) < 0.35


def test_shallow_pairs_are_charged_nothing() -> None:
    grid = (0.01, 0.25, 0.45)
    etas = eta_optimal(PE, 1.0, y_grid=grid)
    assert etas[0.01] < 0.05


# -- theta_full ---------------------------------------------------------------


def test_assembly_closes_at_theta_002_float() -> None:
    grid = (0.05, 0.25, 0.45)
    etas = eta_optimal(PE, 1.0, y_grid=grid)
    for y, eta in etas.items():
        y2 = y * 1.01
        sups = PB.fine_sups(y, y2)
        cap = min(
            PB.lambda_bar_from_sups(0.02, sups, y2, d) for d in PB.delta_choices
        )
        assert cap / PB.slack(y) + eta <= 1.0, (y, cap / PB.slack(y), eta)


def test_assembly_open_at_a_larger_theta() -> None:
    """The verdict has power: theta = 0.3 must fail at the binding depth
    (with eta from the full depth grid, as in the delivered verdict)."""
    y = 0.45
    y2 = y * 1.01
    etas = eta_optimal(PE, 1.0, y_grid=(0.01, 0.05, 0.15, 0.25, 0.35, 0.45, 0.49))
    sups = PB.fine_sups(y, y2)
    cap = min(
        PB.lambda_bar_from_sups(0.3, sups, y2, d) for d in PB.delta_choices
    )
    assert cap / PB.slack(y) + etas[0.45] > 1.0


def test_hardened_assembly_closes_at_probe_depths() -> None:
    """Ball-hardened caps + measured-optimal eta at two probe depths."""
    rows = hardened_assembly(theta=0.02, y_grid=(0.25, 0.45))
    for y, row in rows.items():
        assert row["closed"], (y, row)
        assert row["combined"] <= 1.0
