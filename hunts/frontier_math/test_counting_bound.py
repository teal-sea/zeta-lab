"""Controls for level 4: the configuration-free counting bound.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_counting_bound.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from counting_bound import CountingBound, lesion_no_inflation, pair_layer_audit  # noqa: E402
from theta_recovery import Recovery  # noqa: E402

CB = CountingBound()
REC = Recovery()


# -- the repulsion floor ------------------------------------------------------


def test_K_delta_is_one_sided_and_decreasing() -> None:
    ladder = [CB.K_delta(d) for d in (0.25, 0.3, 0.35, 0.4, 0.45)]
    assert all(k > 0 for k in ladder)
    assert ladder == sorted(ladder, reverse=True)
    # one-sided against direct samples of omega^2 inside the range
    for d, k in zip((0.25, 0.45), (ladder[0], ladder[-1])):
        for r in (d / 3, d / 2, d):
            assert REC.omega_sq(r) >= k - 1e-12


def test_K_delta_vanishes_past_the_first_omega_zero() -> None:
    assert CB.K_delta(1.0) == 0.0


# -- one-sided cells ----------------------------------------------------------


def test_cell_sups_majorise_true_damage() -> None:
    """Fine sups vs true f+ on a dense probe grid: never below."""
    y = 0.3
    sups = CB.fine_sups(y, y * 1.0001)
    worst = 0.0
    g = -CB.fine_g_max + 1e-9
    while g < CB.fine_g_max:
        f_true = 2 * max(0.0, -REC.W(g, y))
        i = min(int((g + CB.fine_g_max) / CB.fine_step), len(sups) - 1)
        worst = max(worst, f_true - sups[i])
        g += 0.0293  # incommensurate step probes bin interiors
    assert worst <= 1e-9


def test_lesion_without_inflation_fires() -> None:
    """Dropping the inflation must produce a genuine sup violation."""
    row = lesion_no_inflation(CB, 0.3)
    assert row["lesion_fires"]
    assert row["worst_sup_violation"] > 0.05


def test_tail_majorant_scales_with_depth() -> None:
    """psi_S ~ y as y -> 0: the far tail cannot outlive the slack."""
    assert CB.psi_S(0.001) < 0.2
    assert CB.tail_sup_damage(CB.fine_g_max, 0.001) < 1e-7
    # and the ratio tail/slack stays bounded in the shallow limit
    for y in (0.002, 0.01):
        assert CB.tail_sup_damage(CB.fine_g_max, y) < CB.slack(y)


# -- domination of every lower level ------------------------------------------


def test_bound_dominates_level3_adversaries() -> None:
    """The projection rule: measured profits sit under the level-4 cap."""
    for y in (0.1, 0.3, 0.45):
        sups = CB.fine_sups(y, y * 1.0001)
        cap = min(
            CB.lambda_bar_from_sups(0.3, sups, y * 1.0001, d)
            for d in CB.delta_choices
        )
        measured = max(
            REC.slack(y) - REC.lattice_net(0.3, y, sp) for sp in (0.5, 0.25)
        )
        measured = max(measured, REC.slack(y) - REC.greedy_net(0.3, y, 8, kmax=8))
        assert measured <= cap + 1e-9


def test_bound_dominates_the_level2_cluster() -> None:
    """The +-g* cluster (level 2's escaping family) sits under the cap."""
    y = 0.3
    profit = REC.slack(y) - REC.lattice_net(0.0, y, 0.0625)
    sups = CB.fine_sups(y, y * 1.0001)
    cap = min(
        CB.lambda_bar_from_sups(0.0, sups, y * 1.0001, d) for d in CB.delta_choices
    )
    assert profit <= cap + 1e-9


def test_single_point_reduces_to_law_i_scale() -> None:
    """One adversary point: the cap is at least the worst single cell, and
    within the LAW I envelope's reach."""
    y = 0.3
    sups = CB.fine_sups(y, y * 1.0001)
    worst_cell = max(sups)
    m0 = REC.cell.m0()
    assert worst_cell <= 2 * (1 + m0) * CB.sigma_sq(y) * 1.1  # f = -2W <= 2(1+m0)s^2
    cap = CB.lambda_bar_from_sups(0.0, sups, y * 1.0001, 0.25)
    assert cap >= worst_cell


# -- the securing scan ------------------------------------------------------------


def test_secured_positive_margin_on_a_probe_ladder() -> None:
    """theta = 0 secures on representative depth cells (fine ladder)."""
    for y in (0.05, 0.15, 0.25, 0.35, 0.45):
        y2 = y * 1.01
        sups = CB.fine_sups(y, y2)
        cap = min(
            CB.lambda_bar_from_sups(0.0, sups, y2, d) for d in CB.delta_choices
        )
        assert cap <= CB.slack(y), (y, cap, CB.slack(y))


def test_chain_charge_beats_the_plain_bound() -> None:
    """The adjacent-cell charge is what makes the securing scan possible."""
    y = 0.45
    y2 = y * 1.0001
    sups = CB.fine_sups(y, y2)
    chained = CB.lambda_bar_from_sups(0.0, sups, y2, 0.3)
    # plain = chain with the adjacent charge zeroed: emulate via delta whose
    # doubled range passes the first omega zero (K2 = 0)
    plain = CB.lambda_bar_from_sups(0.0, sups, y2, 0.75)
    assert chained < plain


def test_theta_one_is_unsecurable() -> None:
    """c = 0 removes every repulsion charge: the cap is infinite, as the
    level-3 dense-regime failure requires."""
    import math

    sups = CB.fine_sups(0.3, 0.30003)
    assert math.isinf(CB.lambda_bar_from_sups(1.0, sups, 0.30003, 0.3))


# -- gap 2 frame --------------------------------------------------------------


def test_halved_slack_partition_covers_measured_dipoles() -> None:
    rows, stacked = pair_layer_audit(CB)
    assert all(row["fits"] for row in rows)
    assert all(s > 0 for s in stacked)
