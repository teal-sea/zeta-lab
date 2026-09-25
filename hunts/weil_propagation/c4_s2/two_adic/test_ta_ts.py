"""T_S assembly: order of refusals, framework limit, and the composition
algebra on SYNTHETIC mode families (no value here is a value of T_S).

Float64 on a grid; tolerances are measured deviations (RESULTS.md s5):
  place-2-off Delta_T                         measured 0.0,             tol 1e-12
  direct route vs FFT route, one mode (rel.)  measured 5.9e-16,         tol 1e-12
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_data as D  # noqa: E402
import ta_ts as T  # noqa: E402


def test_refusal_comes_before_everything():
    for bad in (D.W_A_QUARTER, ("tower", D.EPSTEIN_116_TOWER[1], 2)):
        with pytest.raises(D.NonUnitaryLocalData):
            T.T_S_matrix(2.5, 8, 40, bad, "Gamma_R")
        with pytest.raises(D.NonUnitaryLocalData):
            T.T_S_matrix(2.5, 8, 40, bad, "Gamma_C")


def test_gamma_C_is_a_framework_limit_not_a_number():
    with pytest.raises(T.FrameworkLimit, match="23 in S"):
        T.T_S_matrix(2.5, 8, 40, D.DEDEKIND_Q_SQRT_M23, "Gamma_C")


def test_zeta_and_place_2_off_pass_the_checks():
    assert T.T_S_matrix(2.5, 8, 40, D.ZETA, "Gamma_R", dry_run=True) == "ok"
    assert T.T_S_matrix(2.5, 8, 40, None, "Gamma_R", dry_run=True) == "ok"


def _synthetic(grid, n=4):
    x = grid.x
    Z = []
    for k in range(1, n + 1):
        z = np.where(x > 0, x**k * np.exp(-0.7 * x) * np.cos(1.3 * k * x), 0.0)
        Z.append(z)
    return np.array(Z, dtype=complex)


@pytest.fixture(scope="module")
def setup():
    L = float(np.log(2.5))
    g = T.Grid(16, -L - 8.0, 45.0)
    return g, L, _synthetic(g)


def test_place_2_off_gives_zero_delta(setup):
    g, L, Z = setup
    dT, Mi, Ms = T.delta_T_matrix(g, Z, 0.0, L, 3)
    assert np.abs(dT).max() < 1e-12


def test_pieces_are_hermitian_psd(setup):
    g, L, Z = setup
    for alpha in (1.0, 1j, -1.0):
        dT, Mi, Ms = T.delta_T_matrix(g, Z, alpha, L, 3)
        for M in (Mi, Ms):
            assert np.abs(M - M.conj().T).max() < 1e-12
            assert np.linalg.eigvalsh((M + M.conj().T) / 2).min() > -1e-12


def test_direct_route_matches_fourier_route_for_one_mode(setup):
    g, L, Z = setup
    e = Z[0] / np.sqrt(np.sum(np.abs(Z[0]) ** 2) * g.dx)
    M = T.trace_matrix_direct(g, e[None, :], L, 3)
    rng = np.random.default_rng(1)
    v = rng.normal(size=7) + 1j * rng.normal(size=7)
    direct = np.real(np.conj(v) @ M @ v)
    # ||theta(g) e||^2 with g = sum v_n V_n: convolution by FFT, independent code
    Vw, js = T.window_basis(g, L, 3)
    gw = v @ Vw  # samples of g times dx at t = js dx
    npad = g.n + js.size
    conv = np.fft.ifft(np.fft.fft(e, npad) * np.fft.fft(gw, npad))
    fourier = np.sum(np.abs(conv) ** 2) * g.dx
    assert abs(direct - fourier) < 1e-12 * abs(fourier)
