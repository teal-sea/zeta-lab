"""Controls for the marked two-gap coexistence question.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_two_gap_marked.py
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest
from mpmath import mp, mpc, mpf

sys.path.insert(0, str(Path(__file__).resolve().parent))
from incidence_law import Window  # noqa: E402
from two_gap_marked import (  # noqa: E402
    MarkedCell,
    cluster_collapse,
    epsilon_robustness,
    lesion_broken_spacing,
    lesion_hermitian_geometry,
    lesion_independent_cells,
    lesion_independent_depths,
    mirror_collapse,
    separation_penalty,
    two_cell_penalty,
)

CELL = MarkedCell()
M0 = CELL.m0()


# -- Phase 1: the exact decomposition and its symmetries --------------------


def test_cell_value_matches_the_mpmath_kernel() -> None:
    """W = 2 Re(Phi2(g+iy)^2)/(aL)^2, against the level-1 closed form."""
    window = Window(8, 1)
    with mp.workdps(25):
        for g, y in ((0.4, 0.3), (1.9, 0.12), (0.0, 0.45)):
            ref = float(2 * mp.re((window.Phi2(mpc(g, y)) / window.aL) ** 2))
            assert abs(CELL.cell(g, y) - ref) < 1e-9


def test_cell_is_even_in_offset_and_in_depth() -> None:
    """Translation covariance plus the rho <-> 1 - conj(rho) symmetry."""
    for g, y in ((0.7, 0.3), (2.4, 0.45), (0.1, 0.05)):
        assert abs(CELL.cell(g, y) - CELL.cell(-g, y)) < 1e-12
        assert abs(CELL.cell(g, y) - CELL.cell(g, -y)) < 1e-12


def test_no_negativity_without_depth() -> None:
    for g in (0.0, 0.5, 1.3, 4.0):
        assert CELL.cell(g, 0.0) >= -1e-12


# -- the immediate question -------------------------------------------------


def test_the_level_one_floor_is_never_attained() -> None:
    """The headline: no cell saturates level 1, at any offset or depth."""
    for y in (0.05, 0.2, 0.3, 0.49):
        _, best = CELL.sharp_cell(y)
        assert best > CELL.level1_floor(y)
        # and by a wide margin, not a rounding one
        assert best > 0.55 * CELL.level1_floor(y)


def test_saturation_would_need_an_impossible_proportionality() -> None:
    """Cauchy-Schwarz equality needs sin(gu) ~ sinh(yu); the defect persists."""
    for g in (1e-6, 0.3, 0.767463, 2.0):
        assert CELL.cauchy_schwarz_defect(g, 0.3) > 0.01
    # at g = 0 the floor is missed for a different and simpler reason
    assert CELL.cell(0.0, 0.3) >= 0


# -- LAW I ------------------------------------------------------------------


def test_law_i_holds_pointwise_over_a_dense_grid() -> None:
    """W(g,y) >= -(1+m0) sigma^2(y) everywhere, not merely at the optimum."""
    for i in range(60):
        g = 40.0 * i / 59
        for y in (0.05, 0.2, 0.35, 0.49):
            assert CELL.cell(g, y) >= CELL.proved_floor(y, M0) - 1e-12


def test_law_i_pointwise_form_is_sharper_than_its_cap() -> None:
    """-sigma^2 (1 - omega(2g)) implies the constant cap and can beat it."""
    for g in (0.3, 0.9, 1.5, 3.0):
        for y in (0.1, 0.3, 0.49):
            assert CELL.cell(g, y) >= CELL.pointwise_floor(g, y) - 1e-12
            assert CELL.pointwise_floor(g, y) >= CELL.proved_floor(y, M0) - 1e-12


def test_law_i_beats_level_one_by_a_uniform_factor() -> None:
    assert 0 < M0 < 1
    assert 2 / (1 + M0) > 1.6
    for y in (0.01, 0.1, 0.3, 0.49):
        assert CELL.proved_floor(y, M0) > CELL.level1_floor(y)


def test_measured_looseness_stays_inside_the_proved_cap() -> None:
    cap = (1 + M0) / 2
    for y in (0.01, 0.1, 0.3, 0.49):
        r = CELL.looseness(y)
        assert 0.25 < r < cap


# -- LAW J ------------------------------------------------------------------


def test_periodic_word_gives_the_exact_constant_at_every_depth_and_offset() -> None:
    """Phase 4's periodic near-obstruction lesion: no negativity at all."""
    constant = CELL.periodic_constant()
    assert constant > 0
    for y in (0.0, 0.15, 0.3, 0.49):
        for offset in (0.0, 0.37, 1.9):
            total = CELL.periodic_total(y, offset, half_width=400)
            assert abs(total - constant) < 1e-6


def test_periodic_constant_is_two_b_over_a_squared() -> None:
    """The constant is built from the paper's own (2.14) a and b."""
    window = Window(8, 1)
    a = float(window.aL) / 8.0
    assert CELL.periodic_constant() == pytest.approx(2 * 0.8317481182 / (a * a), rel=1e-6)


# -- Phase 2/3: the collapse ------------------------------------------------


def test_mirror_pair_attains_two_cells_with_zero_penalty() -> None:
    """OUTCOME B: coexistence alone yields no positive Delta."""
    for y in (0.1, 0.3, 0.49):
        rec = mirror_collapse(CELL, y)
        assert abs(rec["penalty"]) < 1e-9
        assert rec["mirror_gap"] == pytest.approx(2 * rec["g_star"], rel=1e-12)


def test_two_cell_penalty_is_nonnegative_and_generically_positive() -> None:
    for gap in (0.4, 1.0, 3.0):
        assert two_cell_penalty(CELL, gap, 0.3) > 1e-3
    # but it vanishes at the mirror gap, which is the escaping family
    mirror = mirror_collapse(CELL, 0.3)["mirror_gap"]
    assert abs(two_cell_penalty(CELL, mirror, 0.3)) < 1e-9


def test_cluster_penalty_vanishes_as_the_spacing_does() -> None:
    """The escaping family, pinned: distinctness alone constrains nothing."""
    previous = math.inf
    for delta in (0.1, 0.01, 0.001):
        rec = cluster_collapse(CELL, 0.3, 5, delta)
        assert rec["penalty_per_cell"] >= 0
        assert rec["penalty_per_cell"] < previous
        previous = rec["penalty_per_cell"]
    assert previous < 1e-4


def test_separation_restores_a_positive_penalty() -> None:
    """Consistency plus density has force; consistency alone does not."""
    assert separation_penalty(CELL, 0.3, 5, 0.5) > 0.1
    assert separation_penalty(CELL, 0.3, 5, 0.001) < 1e-4


# -- Phase 5 ----------------------------------------------------------------


def test_epsilon_robustness_band_is_positive_and_uniform() -> None:
    for y in (0.05, 0.2, 0.49):
        rec = epsilon_robustness(CELL, y, M0)
        assert rec["excluded_band"] > 0
        assert rec["proved_floor"] > rec["level1_floor"]
        # the band is a fixed fraction of the level-1 floor, at every depth
        assert rec["excluded_band"] == pytest.approx(
            (1 - M0) * CELL.sigma_sq(y), rel=1e-12
        )


# -- Phase 4 lesions --------------------------------------------------------


def test_independent_cells_lesion_buys_the_adversary_something() -> None:
    rec = lesion_independent_cells(CELL, 0.3, 0.7854)
    assert rec["coupled_is_higher"]
    assert rec["coupled"] - rec["independent"] > 0.1


def test_independent_depths_is_a_negative_lesion() -> None:
    """Recorded honestly: shared depth is not the binding half of pairing."""
    rec = lesion_independent_depths(CELL, 0.2, 0.4)
    assert not rec["mixing_helps"]


def test_hermitian_geometry_destroys_every_sign() -> None:
    """The geometry CLEAN-KILL withdrew: 2|B|^2 can never be negative."""
    rec = lesion_hermitian_geometry(CELL, 0.3, samples=200)
    assert rec["worst_true"] < -0.1
    assert rec["worst_hermitian"] >= -1e-9


def test_broken_spacing_breaks_the_periodic_identity() -> None:
    rec = lesion_broken_spacing(CELL, 0.3)
    assert abs(rec["total"] - rec["exact_constant"]) > 1e-3
