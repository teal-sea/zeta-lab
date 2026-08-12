"""Controls for the transplant-lemma dissection."""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from transplant_lemma import (  # noqa: E402
    hann_law_d, hann_zeros, hunt_floor, hunt_zeros, mt_entry_card,
    mt_kernel_identity, mt_law_d,
)


def test_hunt_kernel_is_cg_degenerate():
    fl, roots = hunt_floor()
    assert abs(roots[1] / roots[0] - 2) < 5e-4      # arithmetic to ~1e-4
    assert fl is not None and fl < 1e-8             # the floor is dead


def test_hann_grid_law_d_is_alias_free():
    assert hann_law_d() < 1e-6


def test_hann_kernel_degeneracy_is_exact():
    hz = hann_zeros()
    assert abs(hz[0] - 6 * math.pi) < 1e-9
    assert abs(2 * hz[0] - hz[3]) < 1e-9            # 2 lambda_1 = lambda_4


def test_mt_kernel_is_the_sqrt2_box_window():
    assert mt_kernel_identity() < 1e-12


def test_mt_grid_alias_defect_is_small_but_nonzero():
    d = mt_law_d()
    assert 1e-4 < d < 2e-2                          # ~0.5%: must be carried


def test_mt_entry_card_is_friendlier_than_the_hunt_window():
    card = mt_entry_card(ys=(0.3, 0.49))
    for y, row in card.items():
        assert row["minW"] < 0                      # damage exists
        assert row["ratio"] > -0.5                  # envelope ~ -0.43 sigma^2
        # the negative band sits at the lambda_1 geometry (~1.1 mean gaps)
        assert 1.0 < row["at_g"] / (2 * math.pi) < 1.2
