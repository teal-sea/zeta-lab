"""Permanent controls for the withdrawn frontier-math transplant."""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import numpy as np


FRONTIER = Path(__file__).resolve().parents[1] / "hunts" / "frontier_math"
sys.path.insert(0, str(FRONTIER))

import blockpos  # noqa: E402
import clean_kill  # noqa: E402
import configuration_lp  # noqa: E402
import gap_lp  # noqa: E402


def test_exact_transpose_obstruction_withdraws_additive_bound() -> None:
    result = clean_kill.audit()
    assert result == {
        "correct_off_pair": -2,
        "old_instrument_off_pair": 2,
        "cross_trace": -2,
        "frobenius_sq": 9,
        "proposed_rhs": 13,
        "defect": -4,
    }


def test_correct_zero_side_has_a_negative_on_off_block() -> None:
    """The former conjugate-transpose implementation made this impossible."""

    tau = np.arange(48, dtype=float)
    x = 24.0
    z = 24.0 + 6.0 * np.pi + 0.49j
    kernel = blockpos.B(x, z, tau)
    correct = 2.0 * np.real(kernel**2)
    old_formula = 2.0 * abs(kernel) ** 2
    assert correct < -6.9e-5
    assert old_formula > 7.2e-5


def test_block_decomposition_matches_correct_transpose_matrix() -> None:
    classes = [("on", 24.0, 1), ("off", 24.0 + 6.0 * np.pi, 0.49, 1)]
    result = blockpos.block_sums(classes, d=48)
    assert result["hermiticity_defect"] < 1e-12
    assert abs(result["frobenius"] - result["block_total"]) < 1e-10
    assert result["min_block"] < 0.0


def test_configuration_type_elimination_coefficient() -> None:
    """A triple point has correction m^2-2m=3, not the former value 2."""

    assert configuration_lp.reconstruct_p1({3: Fraction(1, 3)}) == 0


def test_finite_chain_floor_includes_endpoint_loss() -> None:
    assert gap_lp.finite_linear_chain_floor(n_gaps=1, n_in_cell=1, level=2) == 0


def test_known_kernel_root_cell_is_never_given_positive_cost() -> None:
    table = gap_lp._GTable(hi=3.0)
    assert table.minimum(1.055, 1.060) == 0.0
