"""Controls for level 3: the recovery coefficient after off-line cancellation.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_theta_recovery.py
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from theta_recovery import Recovery, internal_kernel_is_positive_definite  # noqa: E402

REC = Recovery()
M0 = REC.cell.m0()


# -- LAW K ------------------------------------------------------------------


def test_law_k_spectrum_is_exact() -> None:
    """Pair block eigenvalues are {2(1+s^2), -2s^2}, and x is orthogonal to y."""
    for y in (0.1, 0.3, 0.45):
        r = REC.law_k_check(y, K=200, dps=18)
        assert r["eig_minus"] == pytest.approx(r["eig_minus_pred"], abs=1e-7)
        assert r["eig_plus"] == pytest.approx(r["eig_plus_pred"], abs=1e-7)
        assert abs(r["x_dot_y"]) < 1e-10


def test_law_k_slack_formula() -> None:
    """(l+ - 2)^2 + (l- - 2)^2 - 4 ... reduces to 8 s^2 + 8 s^4 exactly."""
    for y in (0.1, 0.3, 0.45):
        s2 = REC.sigma_sq(y)
        lp, lm = 2 * (1 + s2), -2 * s2
        baseline = 4 * (lp + lm) - 4  # 4 tr - 4 for one positive-index block
        assert lp * lp + lm * lm - baseline == pytest.approx(8 * s2 + 8 * s2 * s2)


def test_law_k_negative_eigenvalue_is_the_depth_envelope() -> None:
    """The pair's negative eigenvalue equals LAW E's per-cell floor / 2."""
    for y in (0.1, 0.3, 0.45):
        assert -2 * REC.sigma_sq(y) == pytest.approx(
            REC.law_k_check(y, K=200, dps=18)["eig_minus"], abs=1e-7
        )


# -- the proved fragment -----------------------------------------------------


def test_three_zero_lemma_margin_is_positive() -> None:
    """6(1+m0) < 8: three band zeros cannot sink a pair, even at theta = 1."""
    assert 0 < M0 < 1 / 3
    assert REC.three_zero_margin(M0) > 0.7


# -- the theta scan ----------------------------------------------------------


def test_recovery_net_stays_positive_through_high_theta() -> None:
    """The level-3 headline at the single-pair reduction."""
    nets = REC.theta_star_scan(thetas=(0.0, 0.5, 0.9))
    for theta, net in nets.items():
        assert net > 0, (theta, net)
    # monotone: retaining more rigidity mass cannot help the defender
    assert nets[0.0] >= nets[0.5] >= nets[0.9]


def test_theta_equal_one_fails_in_the_dense_regime() -> None:
    """Sanity that the scan has power: theta = 1 must be violated."""
    worst = min(
        REC.lattice_net(1.0, y, sp)
        for y in (0.3, 0.4)
        for sp in (0.125, 0.0625)
    )
    assert worst < 0


def test_dense_attack_is_real_but_self_defeating() -> None:
    """Damage exceeds slack at fine spacing; internal cost dwarfs both."""
    y, sp = 0.35, 0.0625
    pos = [g for g in [x * sp for x in range(-256, 256)] if REC.W(g, y) < 0]
    damage = -2 * sum(REC.W(g, y) for g in pos)
    internal = 2 * sum(
        REC.omega_sq(pos[i] - pos[j])
        for i in range(len(pos))
        for j in range(i + 1, len(pos))
    )
    assert damage > REC.slack(y)  # the attack beats the bare slack ...
    assert internal > 10 * damage  # ... but drowns in its own packing mass


def test_shallow_depth_scaling_is_safe() -> None:
    """As y -> 0 net ~ (8 - D/s2) s2 with D/s2 bounded well below 8."""
    for y in (0.02, 0.05):
        s2 = REC.sigma_sq(y)
        net = REC.lattice_net(0.9, y, 1.0)
        assert net > 0
        assert net < 10 * s2  # everything scales down together


# -- the certificate seed ----------------------------------------------------


def test_internal_kernel_is_positive_definite() -> None:
    """FT[omega^2] >= 0: the packing form cannot be driven negative."""
    for xi, ft in internal_kernel_is_positive_definite(samples=1024):
        assert ft >= -1e-6, (xi, ft)


# -- pair-pair terms ---------------------------------------------------------


def test_dipole_negativity_is_covered_by_the_pairs_own_slacks() -> None:
    for y1, y2 in ((0.3, 0.3), (0.45, 0.45), (0.49, 0.2)):
        r = REC.dipole_worst(y1, y2)
        assert r["covered"]
        assert r["cover_factor"] > 2.5


def test_stacked_pairs_are_positive() -> None:
    for y1, y2 in ((0.3, 0.3), (0.45, 0.44)):
        assert REC.pair_pair(0.0, y1, y2) > 0


# -- extremal battery (Phase 5) ----------------------------------------------


def test_periodic_word_yields_no_damage_at_all() -> None:
    """LAW J: the periodic marked word's total is positive, so net > slack."""
    total = REC.cell.periodic_total(0.3, 0.0, half_width=300)
    assert total > 2.0


def test_max_depth_pair_is_quartically_secured() -> None:
    """At the strip edge the sigma^4 term dominates any linear damage."""
    y = 0.49
    s2 = REC.sigma_sq(y)
    assert 8 * s2 * s2 > 2 * (1 + M0) * s2 * 4  # slack beats 4 worst zeros


def test_cluster_attack_is_the_qp_dense_case() -> None:
    """The level-2 escaping family enters here and stays covered."""
    assert REC.lattice_net(0.9, 0.3, 0.0625) > 0
