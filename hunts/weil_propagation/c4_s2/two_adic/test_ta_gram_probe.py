"""Accuracy item on c = 2.2, N = 8 (ta_gram_probe.py, ta_gram_probe.json): pinned.

Float64, measured grade. The band is a spectral norm (see ta_gram_probe's
docstring, where it was fixed before the S = 4800 runs were read). Tolerances:
stored values to 1e-12 where they are recomputed, and to the printed digits
of RESULTS.md s7 where they are quoted.
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

import ta_gram_probe as G  # noqa: E402


@pytest.fixture(scope="module")
def js():
    with open(os.path.join(HERE, "ta_gram_probe.json")) as fh:
        return json.load(fh)


def _dT(js, key):
    return np.array(js["runs"][key]["dT"])


def band(js):
    s_resp = np.linalg.norm(_dT(js, "80,4800") - _dT(js, "80,2400"), 2)
    n_resp = np.linalg.norm(_dT(js, "100,4800") - _dT(js, "80,4800"), 2)
    probe = js["runs"]["80,4800"]["dT_probe_norm2"]
    return s_resp, n_resp, probe


def test_target_is_checkers_Q_low():
    assert abs(G.q_low() - 2.5738e-4) < 5e-9
    # the 2.33e-4 quoted for c = 2.2 is N = 32
    with open(os.path.join(HERE, "..", "checker", "checker_q_cells.json")) as fh:
        q = json.load(fh)["cells"]["2.2"]
    assert abs(float(q["full_N32_dps40"][0]) - 2.33e-4) < 5e-7


def test_converged_run_matches_the_prolate_table(js):
    """(80, 1200) here is the (80, 1200, 8, 2.2) row of ta_ts_prolate.json."""
    with open(os.path.join(HERE, "ta_ts_prolate.json")) as fh:
        row = next(r for r in json.load(fh)["rows"] if (r["nvec"], r["S"], r["N"], r["c"]) == (80, 1200.0, 8, "2.2"))
    assert np.allclose(js["runs"]["80,1200"]["TS_low3"], row["T_S_eig_low3"], atol=1e-9)
    assert abs(js["runs"]["80,1200"]["dT_probe_maxentry"] - row["gram_sensitivity"]) < 1e-9


def test_s_side_gram_error_falls_with_S_at_fixed_nvec(js):
    """80 modes: probe 3.8e-3, 4.9e-4, 2.5e-5 and max |G_z^s - I| 8.9e-2, 3.5e-2, 8.4e-3 at S = 1200, 2400, 4800."""
    r = js["runs"]
    probe = [r[f"80,{S}"]["dT_probe_norm2"] for S in (1200, 2400, 4800)]
    gz = [r[f"80,{S}"]["gz_dev"] for S in (1200, 2400, 4800)]
    assert np.allclose(probe, [3.81e-3, 4.90e-4, 2.50e-5], rtol=5e-3)
    assert np.allclose(gz, [8.92e-2, 3.53e-2, 8.42e-3], rtol=5e-3)
    s1 = np.linalg.norm(_dT(js, "80,2400") - _dT(js, "80,1200"), 2)
    assert abs(s1 - 6.53e-4) < 5e-6


def test_band_is_nvec_bound_and_above_target(js):
    """band(80, 4800) = 4.48e-3 (the nvec response) > Q_low = 2.574e-4: the accuracy target is not met."""
    s_resp, n_resp, probe = band(js)
    assert abs(s_resp - 1.07e-4) < 5e-6
    assert abs(n_resp - 4.48e-3) < 5e-6
    assert abs(probe - 2.50e-5) < 5e-7
    b = max(s_resp, n_resp, probe)
    assert b == n_resp and b > js["Q_low"]


def test_nvec_response_and_lowest_eigenvalue_drift(js):
    """S = 4800: ||dT(120) - dT(100)||_2 = 1.60e-3; T_S lowest 3.486e-3, 3.001e-3, 2.671e-3 at 80, 100, 120 modes."""
    d = np.linalg.norm(_dT(js, "120,4800") - _dT(js, "100,4800"), 2)
    assert abs(d - 1.60e-3) < 5e-6
    low = [js["runs"][f"{n},4800"]["TS_low3"][0] for n in (80, 100, 120)]
    assert np.allclose(low, [3.486e-3, 3.001e-3, 2.671e-3], atol=5e-7)
    assert low[0] > low[1] > low[2] > 0
    # adding modes lowers Delta_T: the difference 80 -> 120 is negative definite
    assert np.linalg.eigvalsh(_dT(js, "120,4800") - _dT(js, "80,4800")).max() < 0


def test_section_7b_table(js):
    """RESULTS.md s7b table: probe (2-norm), max |G_z^s - I| and T_S lowest per run, to the printed digits."""
    table = {
        "80,1200": (3.8e-3, 8.9e-2, 3.523e-3),
        "80,2400": (4.9e-4, 3.5e-2, 3.500e-3),
        "80,4800": (2.5e-5, 8.4e-3, 3.486e-3),
        "100,4800": (1.2e-4, 1.8e-2, 3.001e-3),
        "120,4800": (3.3e-4, 2.8e-2, 2.671e-3),
    }
    for key, (probe, gz, low) in table.items():
        r = js["runs"][key]
        assert abs(r["dT_probe_norm2"] - probe) <= 0.05 * probe, key
        assert abs(r["gz_dev"] - gz) <= 0.05 * gz, key
        assert abs(r["TS_low3"][0] - low) < 5e-7, key
        assert r["Kmax"] == {80: 10, 100: 11, 120: 12}[r["nvec"]]
