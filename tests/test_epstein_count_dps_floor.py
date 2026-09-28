"""The Epstein rival's zero count runs at a precision the box height sets.

Removing the ``min(dps, 20)`` clamp (see ``test_interface_dps_is_honoured``)
left the default at 20 digits, and hunts/gate5_p6_b, hunts/gate5_p6_c and
hunts/r_f7cd45 each lost about an hour to the same thing afterwards: above
t ~ 30 the completed Epstein zeta cancels ``0.6822 t`` digits, the winding
still lands on an integer, and the integer is wrong.  Three independent
measurements of one defect is a rule, not a footnote, so the floor now lives
in ``zeta.epstein.epstein_count_dps`` and ``epstein_interface`` applies it.

Two checks: the floor is the preregistered rule, and the interface actually
uses it (read off the closure, like its sibling test; no counting is run).
"""
from __future__ import annotations

import inspect
import math

import mpmath
import pytest

from zeta import epstein


def test_the_floor_is_the_preregistered_rule():
    # hunts/gate5_p6_b: 28 for a box topping out at t = 11, 79 at t = 85.7.
    assert epstein.epstein_count_dps(0.6 + 0j, 1.4 + 11j) == 20 + math.ceil(0.6822 * 11)
    assert epstein.epstein_count_dps(0.6 + 0j, 1.4 + 85.7j) == 20 + math.ceil(0.6822 * 85.7)
    # symmetric in the corners and in the sign of the height
    assert epstein.epstein_count_dps(1.4 - 85.7j, 0.6 + 0j) == epstein.epstein_count_dps(
        0.6 + 0j, 1.4 + 85.7j
    )
    # a low box costs nothing beyond the guard
    assert epstein.epstein_count_dps(0.6 + 0j, 1.4 + 0.5j) == 21


@pytest.mark.parametrize("asked, t_max", [(20, 85.7), (60, 85.7), (200, 85.7), (20, 3.0)])
def test_the_interface_counts_at_the_larger_of_asked_and_floor(monkeypatch, asked, t_max):
    seen = {}

    def fake_count(s0, s1, dps=20, fn=None, step=None):
        seen["dps"] = dps
        return 0

    monkeypatch.setattr(epstein, "count_zeros_box", fake_count)
    iface = epstein.epstein_interface((2, 1, 3), dps=asked)
    iface["count_zeros_box"](mpmath.mpc(0.6, 0), mpmath.mpc(1.4, t_max))
    floor = epstein.epstein_count_dps(0.6, 1.4 + 1j * t_max)
    assert seen["dps"] == max(asked, floor)


def test_the_closure_still_captures_the_callers_dps():
    """The sibling test reads ``_d`` off the closure; keep that contract."""
    iface = epstein.epstein_interface((2, 1, 3), dps=60)
    defaults = {
        n: p.default
        for n, p in inspect.signature(iface["count_zeros_box"]).parameters.items()
        if p.default is not inspect.Parameter.empty
    }
    assert defaults["_d"] == 60
