"""Follow-up 3, step 1: the diagnosis of cond(G) in rho (RESULTS.md s10.1), pinned.

Reads ta_rho_diag.json (written by ta_rho_diag.py, one part per process,
before ta_mellin.rho was changed); recomputes the node counts and checks the
compression bound of the exact G_b on a synthetic family on the grid of
ta_ts.py (exact shifts). Float64: measured grade.
"""

from __future__ import annotations

import json
import math
import os
import sys

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_rho_diag as RD  # noqa: E402
import ta_ts as T  # noqa: E402

INV_EPS = 1.0 / np.finfo(float).eps


@pytest.fixture(scope="module")
def js():
    with open(os.path.join(HERE, "ta_rho_diag.json")) as fh:
        return json.load(fh)


def _row(scan, S):
    return next(r for r in scan["rows"] if r["S"] == S)


def test_toeplitz_ratio():
    assert abs(RD.TOEPLITZ - 33.970562748) < 1e-8


def test_compression_bound_on_a_synthetic_family():
    """sigma of b = (1 - P) Theta^{*-1} zeta on span{zeta} inside [1/(1 + 2^-1/2), 1/(1 - 2^-1/2)]."""
    rng = np.random.default_rng(3)
    g = T.Grid(16, -12.0, 14.0)
    x = g.x
    Z = np.array([np.where(x >= 0, np.exp(-((x - m) ** 2) / (2 * w**2)) * np.cos(k * x), 0.0)
                  for m, w, k in zip(rng.uniform(0.5, 6, 12), rng.uniform(0.3, 1.5, 12), rng.uniform(0, 9, 12))])
    Q, _ = np.linalg.qr((Z * math.sqrt(g.dx)).T)  # orthonormal columns in l^2(dx)
    onb = Q.T / math.sqrt(g.dx)
    Bm = np.stack([T.theta_star_inv(g, z, 1.0) for z in onb])
    Bm[:, x < 0] = 0.0
    sv = np.linalg.svd(Bm * math.sqrt(g.dx), compute_uv=False)
    assert sv.min() >= 1 / (1 + 2**-0.5) - 1e-12 and sv.max() <= 1 / (1 - 2**-0.5) + 1e-12


def test_refinement_inside_S_does_not_move_cond_but_S_does(js):
    rows = {r["label"]: r for r in js["refine"]["rows"]}
    for part in ("z", "b"):
        base = rows["base"][part]["cond_F_sq"]
        for lab in ("s_per_panel_12", "w_per_panel_16", "Kmax_plus_1"):
            assert abs(math.log10(rows[lab][part]["cond_F_sq"] / base)) < 1e-3, (lab, part)
        assert rows["S_doubled"][part]["cond_F_sq"] < base / 1e3, part
    assert rows["base"]["z"]["cond_F_sq"] == pytest.approx(2.577e15, rel=1e-3)
    assert rows["S_doubled"]["z"]["cond_F_sq"] == pytest.approx(5.615e6, rel=1e-3)


def test_cond_falls_with_S(js):
    for key in ("scan80", "scan200"):
        for part in ("z", "b"):
            c = [r[part]["cond_F_sq"] for r in js[key]["rows"]]
            assert all(a > b for a, b in zip(c, c[1:])), (key, part, c)


def test_pinned_scan_values(js):
    s80, s200 = js["scan80"], js["scan200"]
    assert _row(s80, 2400.0)["z"]["cond_F_sq"] == pytest.approx(4.554, rel=1e-3)
    assert _row(s80, 2400.0)["b"]["cond_F_sq"] == pytest.approx(13.22, rel=1e-3)
    assert _row(s80, 300.0)["b"]["cond_F_sq"] == pytest.approx(1.084e10, rel=1e-3)
    assert _row(s80, 200.0)["z"]["cond_F_sq"] == pytest.approx(4.49e23, rel=1e-2)
    assert _row(s200, 2400.0)["z"]["cond_F_sq"] == pytest.approx(7.580e11, rel=1e-3)
    assert _row(s200, 2400.0)["b"]["cond_F_sq"] == pytest.approx(3.875e9, rel=1e-3)
    assert _row(s200, 1200.0)["z"]["cond_F_sq"] == pytest.approx(7.82e25, rel=1e-2)
    assert _row(s200, 1200.0)["b"]["cond_F_sq"] == pytest.approx(1.99e16, rel=1e-2)
    # at S = 2400 and 80 modes the s-side G_b is within the exact bound's reach
    assert _row(s80, 2400.0)["b"]["cond_F_sq"] < RD.TOEPLITZ


def test_formed_G_reads_cond_only_below_one_over_eps(js):
    """Formed in float64, G's eigenvalue ratio agrees with cond(F)^2 while that is
    below about 1e14 and saturates near 1/eps above it."""
    for key in ("scan80", "scan200"):
        for r in js[key]["rows"]:
            for part in ("z", "b"):
                d = r[part]
                if d["cond_F_sq"] < 1e14:
                    assert d["cond_formed"] == pytest.approx(d["cond_F_sq"], rel=2e-2)
                if d["cond_F_sq"] > 1e20:
                    assert d["cond_formed"] < 1e3 * INV_EPS


def test_lowest_direction_lives_near_and_beyond_S(js):
    d = js["lowdir"]
    e = list(d["energy_by_abs_s"].values())
    assert all(a < b for a, b in zip(e, e[1:]))
    assert d["abs_A_dot_u"] < 1e-3
    assert d["eig_min"] == pytest.approx(0.02457, rel=1e-3)


def test_hats_sample_error(js):
    h = js["hats_accuracy"]
    assert h["max_abs"] < 3e-13
    assert h["nodes"][0]["max_rel"] < 2e-13


def test_node_counts_reproduce(js):
    assert RD.node_counts() == js["node_counts"]
    for r in js["node_counts"][2:]:
        assert r["S_over_nvec2"] < 0.03
