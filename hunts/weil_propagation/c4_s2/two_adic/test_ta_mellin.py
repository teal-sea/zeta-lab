"""zeta^ of the Mellin route against Tate's local functional equation (synthetic xi).

xi = (1 - y^2)^2. Measured deviation at s in {0, 0.7, 3.3, 17, 60, 250}:
<= 1.4e-17 absolute (values of size 1e-4 to 1e-2); tolerance 1e-15.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_mellin as M  # noqa: E402


def _tate(s):
    with mp.workdps(30):
        z = mp.mpf(1) / 2 - 1j * mp.mpf(s)
        a = [1, -2, 1]
        Mxi = sum(a[j] / (2 * j + 1 - z) for j in range(3))
        first = 2 * mp.gamma(z) * mp.cos(mp.pi * z / 2) * (2 * mp.pi) ** (-z) * Mxi
        sec = 0
        for j in range(3):
            for k in range(60):
                sec += 2 * a[j] * (-1) ** k * (2 * mp.pi) ** (2 * k) / (mp.factorial(2 * k) * (2 * j + 2 * k + 1) * (2 * k + z))
        return complex(first - sec)


def test_closed_form_F_matches_quadrature():
    xi = M.EvenPoly([1, -2, 1])
    for w in (1.0, 1.37, 5.2):
        with mp.workdps(30):
            d = 2 * mp.quad(lambda y: (1 - y**2) ** 2 * mp.cos(2 * mp.pi * w * y), [0, 1])
        assert abs(xi.F(np.array([w]))[0] - float(d)) < 1e-15


def test_zeta_hat_matches_tate():
    xi = M.EvenPoly([1, -2, 1])
    ss = np.array([0.0, 0.7, 3.3, 17.0, 60.0, 250.0])
    zh, _ = M.hats(xi, ss, 1.0, Kmax=12)
    for s0, z0 in zip(ss, zh):
        assert abs(z0 - _tate(s0)) < 1e-15
