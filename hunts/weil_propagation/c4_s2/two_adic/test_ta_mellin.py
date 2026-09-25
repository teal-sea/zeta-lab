"""zeta^ of the Mellin route against Tate's local functional equation (synthetic xi).

xi = (1 - y^2)^2. Measured deviation at s in {0, 0.7, 3.3, 17, 60, 250}:
<= 1.4e-17 absolute (values of size 1e-4 to 1e-2); tolerance 1e-15. Below the
Tate checks: rho (QR of the Gram factor, follow-up 3) against rho_inv and a
60-digit reference, RESULTS.md s10.3.
"""

from __future__ import annotations

import math
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


# ---- rho (follow-up 3, RESULTS.md s10): the QR route against rho_inv and a 60-digit reference ----


def _family(n, m, cond_F, seed):
    """Random F (m x n) with prescribed singular values 1 .. 1/cond_F, and hats H (n x k)."""
    rng = np.random.default_rng(seed)
    U, _ = np.linalg.qr(rng.normal(size=(m, n)) + 1j * rng.normal(size=(m, n)))
    V, _ = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
    F = (U * np.logspace(0, -math.log10(cond_F), n)) @ V.conj().T
    H = rng.normal(size=(n, 7)) + 1j * rng.normal(size=(n, 7))
    return F, H


def _rho_ref(F, H, dps=60):
    with mp.workdps(dps):
        Fm = mp.matrix([[mp.mpc(complex(x)) for x in row] for row in F])
        G = Fm.H * Fm
        out = []
        for j in range(H.shape[1]):
            x = mp.matrix([mp.mpc(complex(v)).conjugate() for v in H[:, j]])
            y = mp.lu_solve(G, x)
            out.append(float(mp.re((x.H * y)[0])))
        return np.array(out)


def test_rho_is_keyword_only_on_the_factor():
    F, H = _family(4, 9, 10.0, 0)
    with pytest.raises(TypeError):
        M.rho(H, F)  # a Gram matrix passed positionally must not be taken for a factor


def test_rho_matches_rho_inv_when_well_conditioned():
    """cond(G) = 1e6: measured 1.1e-11 relative (eps cond(G) = 2.2e-10); tolerance 1e-9."""
    F, H = _family(12, 40, 1e3, 1)
    a, b = M.rho(H, factor=F), M.rho_inv(H, np.conj(F.T) @ F)
    assert np.abs(a - b).max() < 1e-9 * np.abs(b).max()


def test_rho_survives_cond_G_1e20_where_rho_inv_does_not():
    """cond(F) = 1e10, cond(G) = 1e20: measured deviations from the 60-digit reference
    (seed 2), relative to max |rho|: QR route 9.5e-8 (eps cond(F) = 2.2e-6), rho_inv
    1.0; tolerances 1e-4 and >= 1e-2."""
    F, H = _family(10, 30, 1e10, 2)
    ref = _rho_ref(F, H)
    new = M.rho(H, factor=F)
    old = M.rho_inv(H, np.conj(F.T) @ F)
    scale = np.abs(ref).max()
    assert np.abs(new - ref).max() < 1e-4 * scale
    assert np.abs(old - ref).max() > 1e-2 * scale


def test_rho_at_the_nodes_is_a_leverage():
    """At the quadrature nodes rho(s) w_s / 2pi is the diagonal of an orthogonal projection:
    in [0, 1], summing to the rank (measured 6.1e-10 off at cond(F) = 1e8; tolerance 1e-6)."""
    F, _ = _family(10, 50, 1e8, 3)
    w = np.full(50, 0.5)
    H = (F / np.sqrt(w / M.TWO_PI)[:, None]).T  # the hats whose weighted samples are F's rows
    lev = M.rho(H, factor=F) * w / M.TWO_PI
    assert lev.min() > -1e-12 and lev.max() < 1 + 1e-9
    assert abs(lev.sum() - 10) < 1e-6
