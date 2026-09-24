"""Follow-up 3, step 3: the QR route of ta_mellin.rho against the acceptance of RESULTS.md s10.2.

Reads ta_rho_check.json (ta_rho_check.py, one part per process; the
acceptance was committed in 5b5a311 before any part ran) and recomputes one
small configuration through ta_prolate.delta_T_cells. Every threshold marked
"acceptance" is s10.2's, unchanged; the others pin measured values (float64,
measured grade; A2's reference is Arb at 256 bits on kernel/'s closed form).
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

import ta_mellin as TM  # noqa: E402
import ta_prolate as TP  # noqa: E402

CELLS = ("2.2", "2.5", "2.9")


@pytest.fixture(scope="module")
def js():
    with open(os.path.join(HERE, "ta_rho_check.json")) as fh:
        return json.load(fh)


def test_A1_agreement_with_rho_inv_within_the_acceptance(js):
    for key in ("80,1200", "120,1600", "200,2400"):
        r = js["A1"][key]
        for part in ("z", "b"):
            assert r[part]["max_dev"] <= r[part]["bound"], (key, part)  # acceptance
            assert r[part]["ratio_to_eps_condG_rho"] < 0.2, (key, part)


def test_A1_pinned_values(js):
    a = js["A1"]
    assert a["200,2400"]["cond_Fz"] == pytest.approx(8.706e5, rel=1e-3)
    assert a["200,2400"]["cond_Fb"] == pytest.approx(6.225e4, rel=1e-3)
    assert a["200,2400"]["z"]["max_dev"] == pytest.approx(1.98e-6, rel=5e-2)
    assert max(a["80,1200"]["dT_change_norm2"].values()) < 2e-14
    assert max(a["120,1600"]["dT_change_norm2"].values()) < 3e-13
    d = a["200,2400"]["dT_change_norm2"]
    assert 1.7e-7 < min(d.values()) and max(d.values()) < 2.1e-7


def test_A2_end_to_end_reference(js):
    a = js["A2"]
    r = a["300"]
    assert r["cond_Fz"] == pytest.approx(5.077e7, rel=1e-3)
    assert r["new_max_rel_dev"] <= 1e-4  # acceptance
    assert r["new_max_rel_dev"] < 1e-8
    assert r["old_max_rel_dev"] > 1e-2
    for k in ("300", "200", "150", "120"):
        assert a[k]["sample_max_abs_dev"] < 3.1e-13
        assert max(a[k]["J_max_abs_dev"], a[k]["A_max_abs_dev"]) < 2e-12
        assert a[k]["n_compared"] == 64


def test_A2_where_it_stops(js):
    a = js["A2"]
    new = [a[k]["new_max_rel_dev"] for k in ("300", "200", "150", "120")]
    old = [a[k]["old_max_rel_dev"] for k in ("300", "200", "150", "120")]
    cf = [a[k]["cond_Fz"] for k in ("300", "200", "150", "120")]
    assert all(x < y for x, y in zip(cf, cf[1:]))
    assert new[1] < 2e-5 and new[2] > 5e-2 and new[3] > 0.2  # survives cond(F) 6.7e11, not 3.8e14
    assert all(n < o for n, o in zip(new, old))
    assert old[1] > 0.25


def test_A3_the_drift_comes_from_the_inverse(js):
    a = js["A3"]
    for c in CELLS:
        assert 1e-8 <= a["old"][c] <= 1e-5  # acceptance
        assert a["new"][c] <= a["old"][c] / 100  # acceptance
    assert 1.7e-7 < min(a["old"].values()) and max(a["old"].values()) < 2.3e-7
    assert max(a["new"].values()) < 3.3e-12


def test_A4_prediction_refuted(js):
    """s10.2 predicted eigenvalues below -band for the new route at (200, 1200): none."""
    a = js["A4"]
    assert a["cond_Fz"] == pytest.approx(8.84e12, rel=1e-2)
    assert a["cond_Fb"] == pytest.approx(1.41e8, rel=1e-2)
    for c in CELLS:
        r = a["cells"][c]
        assert r["new_n_below_band"] == 0 and r["old_n_below_band"] == 0
        assert r["new_low3"][0] > 1.8e-3
        assert -1.7e-2 < r["old_low3"][0] < -1.3e-2
        assert 5e-3 < r["new_S_response_norm2"] < 8.1e-3


def test_delta_T_cells_reports_the_factor_conditions():
    pm = TP.ProlateModes(nvec=40, dps=20)
    out, diag = TP.delta_T_cells(pm, ["2.2"], 8, S=400.0)
    assert set(diag) == {"gram_z_offI", "cond_Gb", "cond_Fz", "cond_Fb"}
    assert diag["cond_Gb"] == pytest.approx(diag["cond_Fb"] ** 2, rel=1e-6)
    # the QR route against the explicit inverse on a well-conditioned case
    s, sw = TM.s_grid(400.0, width=1.0, per_panel=8)
    Z, B = TP.hats_modes(pm, s, 1.0)
    jz, jb = TP.jumps(pm, 1.0)
    A = pm.derivs[:, 0] * pm.norm
    Fz = TP.gram_factor_s(Z, sw, jz, 400.0, A, 1.0)
    assert np.allclose(np.conj(Fz.T) @ Fz, TP.gram_s(Z, sw, jz, 400.0, A, 1.0), rtol=0, atol=1e-13)
    a, b = TM.rho(Z, factor=Fz), TM.rho_inv(Z, TP.gram_s(Z, sw, jz, 400.0, A, 1.0))
    assert np.abs(a - b).max() < 1e-10 * np.abs(b).max()


def test_gram_probe_json_is_unaffected_at_its_stated_digits(js):
    """ta_gram_probe.json was not regenerated: at three of its local truncations the QR
    route moves its Delta_T by at most 2.6e-14 (measured), and reproduces the committed dT
    to 1.1e-14."""
    g = js["gram_probe_dependence"]
    assert set(g) == {"80,1200", "80,4800", "100,4800"}
    for r in g.values():
        assert r["dT_new_minus_old_norm2"] < 3e-14
        assert r["dT_new_minus_committed_max_abs"] < 2e-14
        assert r["cond_Fz"] < 20 and r["cond_Fb"] < 20


def test_ts_prolate_json_was_regenerated_under_the_QR_route():
    with open(os.path.join(HERE, "ta_ts_prolate.json")) as fh:
        rows = json.load(fh)["rows"]
    assert all("cond_Fz" in r and "cond_Fb" in r for r in rows)
    r = next(r for r in rows if r["nvec"] == 200 and r["N"] == 32 and r["c"] == "2.2")
    assert r["cond_Fz"] == pytest.approx(8.706e5, rel=1e-3) and r["cond_Fb"] == pytest.approx(6.225e4, rel=1e-3)


def test_regeneration_changes_against_the_previous_json():
    """s10.5's table: ta_ts_prolate.json against its version at 5b5a311 (before the QR route)."""
    import subprocess

    root = os.path.normpath(os.path.join(HERE, *[".."] * 4))
    rel = os.path.relpath(os.path.join(HERE, "ta_ts_prolate.json"), root)
    try:
        old = json.loads(subprocess.run(["git", "show", f"5b5a311:{rel}"], cwd=root, capture_output=True,
                                        check=True, text=True).stdout)["rows"]
    except (OSError, subprocess.CalledProcessError):
        pytest.skip("git history not available")
    with open(os.path.join(HERE, "ta_ts_prolate.json")) as fh:
        new = json.load(fh)["rows"]
    key = lambda r: (r["nvec"], r["S"], r["N"], r["c"])  # noqa: E731
    O = {key(r): r for r in old}
    worst = {}
    for r in new:
        q = O[key(r)]
        for k in ("T_S_n_below_m002", "resid_n_above_01", "resid_n_below_m01"):
            assert r[k] == q[k]
        d = max([abs(a - b) for a, b in zip(r["T_S_eig_low3"] + r["resid_top8"], q["T_S_eig_low3"] + q["resid_top8"])]
                + [abs(r["T_S_eig_max"] - q["T_S_eig_max"]), abs(r["gram_sensitivity"] - q["gram_sensitivity"])])
        worst[(r["nvec"], r["S"])] = max(worst.get((r["nvec"], r["S"]), 0.0), d)
    assert worst[(40, 800.0)] < 2e-15 and worst[(80, 1200.0)] < 1.1e-14
    assert worst[(120, 1600.0)] < 1.3e-13 and worst[(130, 1800.0)] < 2.2e-13
    assert 1.4e-7 < worst[(200, 2400.0)] < 1.6e-7


def test_modal_estimates_node_products():
    """s10.5's estimates: s-nodes x w-nodes of delta_T_cells' grids, and s10.4's 2 pi / w_s range."""
    def prod(nvec, S, spp=8, wpp=12, K=None):
        s, _ = TM.s_grid(S, width=1.0, per_panel=spp)
        w, _, _ = TM.w_nodes(K or TP.kmax_for(nvec), S, wpp)
        return s.size * w.size

    for (nvec, S), v in {(280, 3136.0): 1.28e10, (319, 4070.0): 1.77e10, (364, 5300.0): 4.23e10,
                         (280, 4532.0): 2.04e10}.items():
        assert prod(nvec, S) == pytest.approx(v, rel=5e-3)
    assert prod(240, 2400.0, spp=12) * 9e-8 == pytest.approx(1250, rel=1e-2)
    assert prod(240, 2400.0, wpp=16) * 9e-8 == pytest.approx(1110, rel=1e-2)
    assert prod(240, 2400.0, K=15) * 9e-8 == pytest.approx(1520, rel=1e-2)
    _, sw = TM.s_grid(2400.0, width=1.0, per_panel=8)
    r = 2 * np.pi / sw
    assert r.min() == pytest.approx(34.6, rel=1e-2) and r.max() == pytest.approx(124.1, rel=1e-2)
