"""The O9 cell counts, on the kernel's leaves and on the refuted Arb model (issue #23).

`o9_leaf.py` once predicted a `decide +kernel` verdict from leaves computed
with Arb, under a LEAF CAVEAT that said the two agree. They do not on wide
cells (the kernel's `sinCosIv` doubles an interval twice), the kernel refuted
the Arb-model table, and both generators now compute their leaves the way
`Leaves.lean` does (`o9_leaves_kernel`, pinned integer for integer by
`test_o9_leaves_kernel.py`).

The counts built on the old caveat outlived it in prose and in hunt-local
tests that CI never collects (`testpaths = ["tests"]`). This file pins the
counts the generators produce now, and pins the Arb model's counts beside
them, so the direction of the error stays on the record: in every case the
model with tighter arithmetic than the checker undercounts the checker's work.

Every count is a statement about the Python generators, measured, one route.
None is a Lean build.
"""

from __future__ import annotations

import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

FM = Path(__file__).resolve().parent.parent / "hunts" / "frontier_math"
sys.path.insert(0, str(FM))

pytest.importorskip("flint", reason="o9_leaf imports python-flint at module scope")

import o9_leaf as one_d  # noqa: E402
import o9_leaf2d as two_d  # noqa: E402


def _count(module, **kwargs):
    v = module.validate(module.build(**kwargs))
    assert v["undecided"] == 0 and v["all_decided"], v
    return v["cells"], v["max_depth"]


def test_the_1d_table_on_kernel_leaves_is_476_cells():
    assert _count(one_d) == (476, 22)
    assert one_d.N_CELLS_KERNEL == 476


def test_the_1d_arb_model_undercounts_it(monkeypatch):
    """The refuted 344: the same walk with `leaves` swapped back to Arb."""
    monkeypatch.setattr(one_d, "leaves", one_d.leaves_arb)
    cells, _ = _count(one_d)
    assert cells == 344
    assert cells < one_d.N_CELLS_KERNEL


@pytest.mark.parametrize(
    "inflation, kernel, arb",
    [
        # the 2-D route's recommended operating point
        (F(6, 5), (699, 18), (339, 17)),
        # the inflation the 1-D table is built at
        (F(21, 20), (1705, 18), (601, 17)),
    ],
)
def test_the_2d_table_on_kernel_leaves_and_on_the_arb_model(monkeypatch, inflation, kernel, arb):
    assert _count(two_d, inflation=inflation) == kernel
    monkeypatch.setattr(two_d, "leaves2d", two_d.leaves2d_arb)
    assert _count(two_d, inflation=inflation) == arb
    assert arb[0] < kernel[0]
