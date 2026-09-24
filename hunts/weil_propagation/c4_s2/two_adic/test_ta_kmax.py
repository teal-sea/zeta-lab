"""The w-range rule for the asymptotic tail of the prolate Mellin data: pinned.

kmax_for(nvec) is the smallest Kmax >= 10 with 2^Kmax >= (nvec - 1)^2 / (2 pi);
hats_modes refuses a Kmax whose tail term ratio (2(n-1))^2 / (4 pi 2^Kmax)
exceeds 2, before it evaluates anything. At Kmax = 10 the ratio is 4.4, 5.2 and
12.3 for 120, 130 and 200 modes, so the Kmax = 10 rows of those configurations
were computed past the rule.
"""

from __future__ import annotations

import math
import os
import sys
from types import SimpleNamespace

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_prolate as TP  # noqa: E402


class _PastGuard(Exception):
    pass


def _stub(nvec: int):
    """Only nvec is real: anything past the guard raises _PastGuard."""

    def boom(w):
        raise _PastGuard

    return SimpleNamespace(nvec=nvec, zeta=boom)


def test_kmax_for_mission_values():
    assert TP.kmax_for(80) == 10
    assert TP.kmax_for(120) == 12
    assert TP.kmax_for(130) == 12
    assert TP.kmax_for(200) == 13
    assert TP.kmax_for(16) == TP.kmax_for(40) == 10


def test_ratio_at_kmax_10_for_the_rerun_configurations():
    r = {n: (2 * (n - 1)) ** 2 / (4 * math.pi * 2.0**10) for n in (120, 130, 200)}
    assert np.allclose([r[120], r[130], r[200]], [4.40, 5.17, 12.31], atol=5e-3)


@pytest.mark.parametrize("nvec", [80, 120, 130, 200])
def test_guard_raises_below_kmax_for(nvec):
    k = TP.kmax_for(nvec)
    s = np.array([0.0, 1.0])
    with pytest.raises(_PastGuard):  # passes the guard at kmax_for
        TP.hats_modes(_stub(nvec), s, 1.0, Kmax=k)
    with pytest.raises(_PastGuard):  # default Kmax is kmax_for
        TP.hats_modes(_stub(nvec), s, 1.0)
    with pytest.raises(ValueError, match="too small"):  # kmax_for is the smallest that passes
        TP.hats_modes(_stub(nvec), s, 1.0, Kmax=k - 1)


def test_guard_rejects_the_old_kmax_10_for_200_modes():
    with pytest.raises(ValueError, match="too small"):
        TP.hats_modes(_stub(200), np.array([0.0]), 1.0, Kmax=10)
