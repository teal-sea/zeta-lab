"""Pins of crossover.py (post-hoc, not in PREREG): the uniform eps below which
the rule of PREREG (c) gives outcome 1 at c = 2.9, and the large-eps artifact
that the pre-registered test cannot tell from growth."""

from __future__ import annotations

import functools
import json
import os

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "crossover.json")


@functools.lru_cache(maxsize=None)
def _x():
    if not os.path.exists(OUT):
        pytest.skip("crossover.json absent (run crossover.py)")
    with open(OUT) as fh:
        return json.load(fh)


def _t(L):
    return tuple(L[k] for k in ("8", "16", "32"))


@pytest.mark.parametrize("space,first,last20,artifact", [
    ("V4", "1.50e-02", "1.18e-02", ("7.40e-02", "7.55e-02")),
    ("full", "1.52e-02", "1.21e-02", ("1.14e-01", "1.21e-01")),
])
def test_crossover_pinned(space, first, last20, artifact):
    r = _x()["spaces"][space]
    assert _x()["c"] == "2.9"
    assert "%.2e" % r["eps_first_float"] == first
    # confirmed by exact counts at eps_first (1 -+ 1e-6): growth by one eigenvalue, then none
    assert _t(r["L_at_lo"]) == (2, 8, 9) and _t(r["L_at_hi"]) == (2, 8, 8)
    assert _t(r["float_L_at_lo"]) == _t(r["L_at_lo"]) and _t(r["float_L_at_hi"]) == _t(r["L_at_hi"])
    # every interval below eps_first grows (it is the first failure)
    assert all(t[2] > t[1] for a, b, t in r["profile"] if b <= r["eps_first_float"])
    # L*_32 keeps s7.9's 20 up to about 1.2e-2 (float profile)
    assert "%.2e" % max(b for a, b, t in r["profile"] if t[2] >= 20) == last20
    # the artifact: growth 0, 0, 1 again at large eps, the deepest eigenvalue deepening with N
    (a, b, t), = r["regrowth_float"]
    assert ("%.2e" % a, "%.2e" % b) == artifact and t == [0, 0, 1]
