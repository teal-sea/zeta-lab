"""Pins for the depth bang-bang probe.

The load-bearing test here is the control one: a sweep reporting "no interior
minimum" says nothing unless the same detector is shown to find a planted one.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))

import depth_bangbang as B  # noqa: E402


def test_the_detector_finds_a_planted_interior_minimum():
    """Full power, or the clean sweeps below mean nothing.

    An earlier version of this control planted a fixed-height bump and fired
    on 3 of 60 cases, because the bump was smaller than the variation it
    competed with.  Scaling it to each scan's range is what gives it power.
    """
    out = B.planted_fault_control(trials=30)
    assert out["fired"] == out["trials"]


def test_a_fixed_height_bump_is_the_underpowered_control():
    """Pins WHY the first control was worthless, so it is not reintroduced."""
    import math
    import random

    rng = random.Random(99)
    fired = 0
    for _ in range(30):
        xs, ts, ys, k = B._random_config(rng)
        vals = B.scan_depth(xs, ts, ys, rng.randrange(k))
        bumped = [
            vals[j] - 0.05 * math.exp(-((B.GRID[j] - 0.25) / 0.04) ** 2)
            for j in range(len(B.GRID))
        ]
        if B.has_interior_minimum(bumped):
            fired += 1
    assert fired < 15, "a fixed bump should NOT reliably dominate the scan"


def test_no_interior_minimum_over_random_configurations():
    assert B.sweep(trials=60)["interior"] == 0


def test_no_interior_minimum_over_lattice_configurations():
    assert B.sweep(trials=60, seed=7, structured=True)["interior"] == 0


@pytest.mark.slow
def test_no_interior_minimum_on_a_finer_grid():
    """241 points rather than 61, in case 61 was straddling a shallow dip."""
    assert B.sweep(trials=40, fine=True)["interior"] == 0


def test_the_depth_floor_is_a_floor_not_zero():
    """`y = 0` degenerates the pair; the probe must not pretend otherwise."""
    assert B.Y_LO > 0
    assert B.GRID[0] == B.Y_LO and B.GRID[-1] == B.Y_HI


def test_has_interior_minimum_is_strict_about_endpoints():
    assert not B.has_interior_minimum([0.0, 1.0, 2.0])
    assert not B.has_interior_minimum([2.0, 1.0, 0.0])
    assert B.has_interior_minimum([1.0, 0.0, 1.0])
    assert not B.has_interior_minimum([1.0, 1.0, 1.0])
