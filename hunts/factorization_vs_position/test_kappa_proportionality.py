"""Pin the proportionality DIAGNOSIS.md states for the kappa scanner.

The scanner returns the real part of one fixed rotation times ``f_kappa``.
That real part is ``(1 + KAPPA_REF * kappa)`` times the kappa = 0 value, so
its sign changes cannot depend on kappa. This checks the identity at the
heights named in the diagnosis, at the precision the diagnostic prints.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest
from mpmath import mp

_HERE = Path(__file__).resolve().parent
if str(_HERE) not in sys.path:
    sys.path.insert(0, str(_HERE))

from family import Z_kappa  # noqa: E402
from zeta.epstein import KAPPA_REF  # noqa: E402

_HEIGHTS = (4.0, 12.3, 30.3, 50.0, 77.7)


@pytest.mark.parametrize("t", _HEIGHTS)
def test_scanner_output_is_one_fixed_function_times_kappa(t: float) -> None:
    kappa_dh = mp.mpf(KAPPA_REF)
    z0 = Z_kappa(t, 0.0, dps=25)
    z1 = Z_kappa(t, 1.0, dps=25)
    assert z0 != 0
    assert z1 / z0 == pytest.approx(float(1 + kappa_dh), rel=1e-12, abs=0)
