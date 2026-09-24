"""T_S = T_inf (kernel/) + Delta_T (this folder), zeta, mission cells: pinned.

Float64, measured grade. Numbers come from ta_ts_prolate.json (written by
ta_run_prolate.py, about 5 minutes); the tests check its content, recompute
one small configuration, and re-derive zeta^ against kernel/'s closed form.
Tolerances: zeta^ against kernel/'s Tate route, measured 9e-14, tol 1e-12;
leading residual eigenvalues across truncations, measured spread <= 5e-3
(N = 16) and <= 1.1e-2 (N = 16 against N = 32), tol 1e-2 and 2e-2.
"""

from __future__ import annotations

import json
import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_data as D  # noqa: E402
import ta_prolate as TP  # noqa: E402
import ta_run_prolate as R  # noqa: E402
import ta_ts as T  # noqa: E402

COUNTS = {"2.2": 1, "2.5": 2, "2.9": 3}
CONVERGED = {(80, 1200.0, 8), (80, 1200.0, 16), (120, 1600.0, 16), (200, 2400.0, 32)}


@pytest.fixture(scope="module")
def js():
    with open(os.path.join(HERE, "ta_ts_prolate.json")) as fh:
        return json.load(fh)


def _row(js, nvec, S, N, c):
    return next(r for r in js["rows"] if r["nvec"] == nvec and r["S"] == S and r["N"] == N and r["c"] == c)


def test_zeta_hat_matches_kernel_closed_form():
    pm = TP.ProlateModes(nvec=16, dps=20)
    ss = np.array([0.0, 7.5, 60.0])
    Z, _ = TP.hats_modes(pm, ss, 1.0, Kmax=10)
    for j, s0 in enumerate(ss):
        ref = TP.sonin.zeta_mellin_all(float(s0), 20, 0, 16)
        assert max(abs(complex(ref[n]) - Z[n, j]) for n in range(16)) < 1e-12


def test_json_tate_check(js):
    assert js["tate_check_max_abs"] < 1e-12


def test_T_S_has_no_eigenvalue_below_minus_002(js):
    for r in js["rows"]:
        assert r["T_S_n_below_m002"] == 0, r


def test_residual_has_bounded_count_beyond_01_on_converged_runs(js):
    """Delta_T + Wp: 1, 2, 3 pairs beyond +-0.1 at c = 2.2, 2.5, 2.9, for N = 8, 16, 32."""
    for (nvec, S, N) in CONVERGED:
        for c, k in COUNTS.items():
            r = _row(js, nvec, S, N, c)
            assert (r["resid_n_above_01"], r["resid_n_below_m01"]) == (k, k), r


def test_leading_residual_eigenvalues_are_stable(js):
    for c, k in COUNTS.items():
        a = np.sort(np.abs(_row(js, 80, 1200.0, 16, c)["resid_top8"]))[::-1][: 2 * k]
        b = np.sort(np.abs(_row(js, 120, 1600.0, 16, c)["resid_top8"]))[::-1][: 2 * k]
        d = np.sort(np.abs(_row(js, 200, 2400.0, 32, c)["resid_top8"]))[::-1][: 2 * k]
        assert np.abs(a - b).max() < 1e-2
        assert np.abs(b - d).max() < 2e-2


def test_one_configuration_reproduces(js):
    rows = R.run_config(40, 800.0, (8,), T.KernelProvider())
    for r in rows:
        old = _row(js, 40, 800.0, 8, r["c"])
        assert np.allclose(r["resid_top8"], old["resid_top8"], atol=1e-9)
        assert np.allclose(r["T_S_eig_low3"], old["T_S_eig_low3"], atol=1e-9)


def test_T_S_matrix_is_wired_to_kernel():
    prov = T.KernelProvider(nvec=30, S=400.0)
    M = T.T_S_matrix(2.5, 4, 40, D.ZETA, "Gamma_R", s_inf=prov)
    assert M.shape == (9, 9) and np.abs(M - M.T).max() < 1e-12
    assert np.linalg.eigvalsh(M).min() > -0.02
    off = T.T_S_matrix(2.5, 4, 40, None, "Gamma_R", s_inf=prov)
    assert np.abs(off - prov.T_inf_matrix(2.5, 4, 40)).max() == 0.0


def test_results_table_matches_json(js):
    """RESULTS.md s5b table is the JSON (4 decimals for T_S, 3 for residuals)."""
    with open(os.path.join(HERE, "RESULTS.md"), encoding="utf-8") as fh:
        rows = [ln for ln in fh if ln.startswith("| ") and ln.count("|") == 10 and ln[2].isdigit()]
    assert len(rows) == len(js["rows"]) == 18
    for ln in rows:
        p = [x.strip().replace("−", "-") for x in ln.strip().strip("|").split("|")]
        r = _row(js, int(p[0]), float(p[1]), int(p[2]), p[3])
        assert abs(float(p[4]) - r["T_inf_eig_min"]) < 1e-5
        assert np.allclose([float(x) for x in p[5].split(",")], r["T_S_eig_low3"], atol=6e-5)
        assert np.allclose([float(x) for x in p[7].split(",")], r["resid_top8"][:6], atol=6e-4)
        a, b = p[8].split("+")
        assert (int(a), int(b)) == (r["resid_n_above_01"], r["resid_n_below_m01"])


def test_stated_values_in_the_headline(js):
    r = _row(js, 200, 2400.0, 32, "2.9")
    assert np.allclose(np.round(r["resid_top8"][:6], 2), [0.48, -0.46, 0.38, -0.32, 0.17, -0.16])  # -0.31 before the Kmax 13 rerun
    # the next pairs are near 0.08 and stable
    for c in COUNTS:
        k = COUNTS[c]
        nxt = np.abs(_row(js, 120, 1600.0, 16, c)["resid_top8"][2 * k : 2 * k + 2])
        assert np.all((nxt > 0.07) & (nxt < 0.1)), (c, nxt)
    # 130 modes at N = 32 leave spurious pairs that 200 modes remove
    assert _row(js, 130, 1800.0, 32, "2.2")["resid_n_above_01"] == 3
    lows = [x for r in js["rows"] if (r["nvec"], r["S"], r["N"]) in CONVERGED for x in r["T_S_eig_low3"][:1]]
    assert 1.5e-3 < min(lows) and max(lows) < 3.6e-3
