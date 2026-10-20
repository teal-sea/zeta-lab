"""Pins for hunt #135's Davenport-Heilbronn rival gate (`hunts/jensen_wedge/dh_gate.py`).

Instrument tests first: the relative-cutoff omega against jensen_clock's where its
floor does not act, the floor itself where it does, route B's Laplace series against
phase 0's at zeta's constants, and `moments` against `gammas_from_nodes`. Then a live
recomputation at n = 400 on both routes against `results_dh.json`, so a stale JSON
cannot pass on its own. Then two planted faults that must turn the gate red: the
jensen_clock floor put back into the table, and an alternating error in log gamma.
Then the record, re-graded from the JSON. Nothing here assigns evidentiary status.

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/jensen_wedge
"""

from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from mpmath import mp, mpf

from hunts.jensen_clock import probe as jc
from hunts.jensen_wedge import dh_gate as g
from hunts.jensen_wedge import probe as p0
from hunts.jensen_wedge import probe_phase1 as p1

HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results_dh.json").read_text())
DPS = 60
W = DPS + g.GUARD


# ---------------------------------------------------------------------------
# instruments
# ---------------------------------------------------------------------------


def test_relative_cutoff_omega_agrees_with_jensen_clock_where_its_floor_is_idle():
    kap = g.kap_at(W)
    with mp.workdps(W):
        for x in ("1", "3", "10", "30", "100"):
            a, b = jc.omega_dh_absolute_floor(mpf(x), kap), g.omega_dh_rel(mpf(x), kap)
            assert abs(a / b - 1) < mpf(10) ** -(W - 3), x


def test_jensen_clock_floor_zeroes_the_weight_where_the_large_n_peaks_sit():
    """At dps 75 jc.omega_dh_absolute_floor is exactly 0 from u = 2.86; the n = 3200
    peak is at u = L_DH/2 = 3.62, where the true weight is about 1e-370."""
    kap = g.kap_at(W)
    with mp.workdps(W):
        u = g.L_dh(3200) / 2
        assert u > 3.6
        x = mp.exp(2 * u)
        assert jc.omega_dh_absolute_floor(x, kap) == 0
        assert g.omega_dh_rel(x, kap) > 0
        assert abs(g.omega_dh_rel(x, kap) / mp.exp(-mp.pi * x / 5) - 1) < mpf(10) ** -(W - 3)


def test_route_B_series_is_phase_0s_at_zetas_constants():
    with mp.workdps(W):
        for y in (50, 400, 3200):
            assert g.log_I_laplace_gen(y, 6, mpf(1) / 4, mp.pi) == p0.log_I_laplace(y, 6)
            assert g.saddle_gen(y, mpf(1) / 4, mp.pi) == p0.saddle(y)


def test_L_dh_solves_its_equation():
    with mp.workdps(40):
        for n in (50, 3200, 10 ** 20):
            L = g.L_dh(n)
            assert abs(mp.pi / 5 * mp.exp(L) - mpf(3) / 4 - 2 * mpf(n) / L) < mpf(10) ** -30 * n


def test_moments_reproduce_gammas_from_nodes_on_the_same_nodes():
    dps = 40
    nodes = g.dh_nodes(dps, *g.QUADS[0])
    G = jc.gammas_from_nodes(nodes, 30, dps)
    M = g.moments(nodes, 0, 30, dps)
    with mp.workdps(dps):
        for m in range(31):
            mine = mp.factorial(m) / mp.factorial(2 * m) * M[m]
            assert abs(mine / G[m] - 1) < mpf(10) ** -(dps - 3), m


# ---------------------------------------------------------------------------
# live recomputation at n = 400, both routes
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def live_400():
    n = 400
    ell, dev = g.route_A(DPS, n, n + g.J6)
    with mp.workdps(W):
        lrA = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, g.J6 + 1)]
        lrB = {M: g.lr_B(n, M) for M in (6, 5, 4)}
        Ln = g.L_dh(n)
        cA = g.construction(lrA, n, Ln)
        cB = g.construction(lrB[6], n, Ln, None, cA["pade"]["x"])
        return {"n": n, "Ln": Ln, "ell": ell, "dev": dev, "lrA": lrA, "lrB": lrB, "cA": cA, "cB": cB}


def test_live_node_sets_agree_and_route_B_sits_inside_its_stated_error(live_400):
    assert live_400["dev"] < mpf(10) ** -(DPS + 5)
    lrA, lrB = live_400["lrA"], live_400["lrB"]
    for j in range(1, g.J6 + 1):
        stated = max(abs(lrB[6][j] - lrB[5][j]), abs(lrB[5][j] - lrB[4][j]))
        assert abs(lrA[j] - lrB[6][j]) <= stated, j


def test_every_predicted_item_holds_live_on_both_routes(live_400):
    for c in (live_400["cA"], live_400["cB"]):
        assert all(g.prediction_at(c).values()), g.prediction_at(c)


def test_live_route_A_reproduces_the_recorded_row(live_400):
    row = {r["n"]: r for r in RESULTS["subgrid"]}[400]
    c = live_400["cA"]
    with mp.workdps(W):
        for a, k in (("lag", "D3"), ("jac", "E_J4"), ("ff", "E_F5"), ("pade", "E_S6")):
            assert abs(c[a][k] / mpf(row[f"{k}_A"]) - 1) < mpf(10) ** -10, k


def test_live_theta_star_is_the_pade_point_and_matches_the_record(live_400):
    c, n = live_400["cA"], live_400["n"]
    with mp.workdps(W):
        BJ = c["jac"]["B_J"]
        half = p1.family_from_holland(c["lq"], n, BJ, c["ff"])
        m = p1.family_map(c["lq"], n, BJ, half, tuple(f"0.{k}" for k in range(85, 96)))
        row = {r["n"]: r for r in RESULTS["theta_map_route_A"]}[400]
        assert abs(m["theta_star"] - mpf(row["theta_star"])) < mpf(10) ** -10
        assert abs(m["theta_inf"] - mpf(row["theta_inf"])) < mpf(10) ** -10
        assert abs(m["theta_star"] - c["pade"]["D"] / BJ) < mpf(10) ** -10


# ---------------------------------------------------------------------------
# planted faults: each must turn the gate red
# ---------------------------------------------------------------------------


def test_planted_jensen_clock_floor_is_caught_by_both_checks():
    """The literal jc.omega_dh_absolute_floor, put back: the two node sets disagree
    (the check raises), and route A leaves route B's stated error by orders of
    magnitude."""
    n = 1600
    ell, dev = g.route_A(DPS, n, n + 2, floor=True)
    with pytest.raises(RuntimeError, match="node sets disagree"):
        g.check_two_quadratures(dev, DPS)
    with mp.workdps(W):
        lrA = [mpf(0)] + [ell[n + j] - ell[n] for j in (1, 2)]
        lrB = g.lr_B(n, 6, top=2)
        assert abs(lrA[1] - lrB[1]) > mpf(10) ** -6


def test_planted_alternating_error_in_log_gamma_turns_the_gate_red(live_400):
    """An alternating error of 1e-12 in log gamma at n = 400 (E_F(5) is -2.7e-11
    there): the construction no longer solves, where the same call on the true
    table is green (live_400). At 1e-14 every fit still solves and the Pade model's
    R_6 defect, -1.8e-14, changes sign."""
    n, ell, Ln = live_400["n"], live_400["ell"], live_400["Ln"]
    assert all(g.prediction_at(live_400["cA"]).values())

    def planted(delta):
        bad = {m: v + delta * (-1) ** m for m, v in ell.items()}
        return [mpf(0)] + [bad[n + j] - bad[n] for j in range(1, g.J6 + 1)]

    with mp.workdps(W):
        with pytest.raises(ValueError):
            g.construction(planted(mpf(10) ** -12), n, Ln)
        c = g.construction(planted(mpf(10) ** -14), n, Ln)
    assert live_400["cA"]["pade"]["E_S6"] < 0 < c["pade"]["E_S6"]


def test_planted_sign_flip_in_the_record_turns_the_verdict_red():
    assert g.verdict(RESULTS)["prediction_held"] is True
    for path in (("dense_route_A", "laguerre_D3", "negative"),
                 ("dense_route_A", "jacobi_E_J4", "positive"),
                 ("dense_route_A", "finite_free_E_F5_theta_half", "positive")):
        bad = copy.deepcopy(RESULTS)
        node = bad
        for key in path[:-1]:
            node = node[key]
        node[path[-1]] = 1
        assert g.verdict(bad)["prediction_held"] is False, path
    bad = copy.deepcopy(RESULTS)
    bad["dense_route_A"]["pade_positive_A_gt_B_C_gt_D_at_every_n"] = False
    assert g.verdict(bad)["prediction_held"] is False
    bad = copy.deepcopy(RESULTS)
    bad["theta_map_route_A"][0]["theta_inf"] = None
    assert g.verdict(bad)["prediction_held"] is False


# ---------------------------------------------------------------------------
# the record
# ---------------------------------------------------------------------------


def test_the_recorded_verdict_is_what_the_record_grades_to():
    assert RESULTS["verdict"] == g.verdict(RESULTS)
    assert RESULTS["verdict"]["prediction_held"] is True
    assert all(RESULTS["verdict"]["prediction_items"].values())


def test_route_A_table_and_the_jensen_clock_floor():
    a = RESULTS["route_A"]
    assert a["m_range"] == [g.K_LO, g.K_HI] and a["node_sets"] == [list(q) for q in g.QUADS]
    assert float(a["max_abs_dlog_gamma_between_node_sets"]) < 1e-60
    f = RESULTS["jensen_clock_floor"]
    assert abs(float(f["u_where_jc_omega_dh_turns_zero"]) - 2.86) < 0.01
    assert f["jc_omega_dh_just_below_and_above"][1] == "0.0"
    d = {int(m): abs(float(v)) for m, v in f["literal_minus_relative_log_gamma"].items()}
    assert d[50] < 1e-40 and d[1600] > 1e-3 and d[3200] > 1e-3
    assert float(f["gammas_from_nodes_reproduced_m50_60_max_abs_dlog"]) < 1e-70


def test_the_sign_facts_and_both_matches_at_every_n_on_route_A():
    d = RESULTS["dense_route_A"]
    assert d["n_count"] == 3151
    assert (d["laguerre_D3"]["positive"], d["laguerre_D3"]["sign_changes_at_n"]) == (3151, [])
    assert (d["jacobi_E_J4"]["negative"], d["jacobi_E_J4"]["sign_changes_at_n"]) == (3151, [])
    ef5 = d["finite_free_E_F5_theta_half"]
    assert (ef5["negative"], ef5["sign_changes_at_n"]) == (3151, [])
    assert (d["pade_E_S6"]["negative"], d["pade_E_S6"]["sign_changes_at_n"]) == (3151, [])
    assert d["holland_parameters_positive_C_gt_D_at_every_n"] is True
    assert d["pade_positive_A_gt_B_C_gt_D_at_every_n"] is True
    assert float(d["max_match_residual"]) < 1e-60


def test_route_B_agrees_in_sign_resolves_it_and_sits_inside_its_error_on_the_subgrid():
    rows = RESULTS["subgrid"]
    assert [r["n"] for r in rows] == list(g.SUBGRID)
    for r in rows:
        assert all(r["signs_agree_A_B_D3_EJ4_EF5_ES6"]), r["n"]
        assert all(r["B_resolves_sign_D3_EJ4_EF5_ES6"]), r["n"]
        assert r["route_B_within_stated_error"], r["n"]
        assert all(r["prediction_items_A"].values()) and all(r["prediction_items_B"].values()), r["n"]


def test_the_theta_map_has_zetas_shape_at_every_subgrid_n():
    rows = RESULTS["theta_map_route_A"]
    assert [r["n"] for r in rows] == list(g.SUBGRID)
    stars = []
    for r in rows:
        ts, ti = float(r["theta_star"]), float(r["theta_inf"])
        assert r["failed"] == {} and ts < ti, r["n"]
        # the crossing is the Pade point, as for zeta (RESULTS.md section 11.3)
        assert abs(ts - float(r["pade_D_over_B_J"])) < 1e-10, r["n"]
        stars.append(ts)
    assert stars == sorted(stars)
    for r in RESULTS["theta_map_route_B"]:
        assert r["failed"] == {} and float(r["abs_theta_star_A_minus_B"]) < 1e-8, r["n"]


def test_large_n_constants_approach_the_leading_order_values_with_L_DH():
    """Holland's 1, 1, 6/5, 1/3, 1/24 and phase 1's -12, 3, 1/3, 2/3, -2: each
    column moves toward its limit over n = 1e4..1e20."""
    rows = RESULTS["large_n_route_B"]
    assert [r["n"] for r in rows] == list(g.LARGE_NS)
    cols = {
        "D3": ([float(r["n2L_D3_over_2"]) for r in rows], 1.0),
        "EJ4": ([float(r["minus_n3L_EJ4_over_2"]) for r in rows], 1.0),
        "A": ([float(r["A_over_A_J"]) for r in rows], 1.2),
        "B": ([float(r["B_minus_B_J_times_L_over_n"]) for r in rows], 1 / 3),
        "C": ([float(r["C_minus_D_times_L_over_n"]) for r in rows], 1 / 24),
        "EF5": ([float(r["family"]["0.5"]["n4L_E_F5"]) for r in rows], -12.0),
        "PA": ([float(r["pade"]["A_over_nL"]) for r in rows], 3.0),
        "PD": ([float(r["pade"]["D_minus_n_L_over_n"]) for r in rows], 1 / 3),
        "star": ([float(r["one_minus_theta_star_times_L"]) for r in rows], 2 / 3),
        "ES6": ([float(r["pade"]["n5L_E_S6"]) for r in rows], -2.0),
    }
    for key, (vals, limit) in cols.items():
        gaps = [abs(v - limit) for v in vals]
        assert gaps == sorted(gaps, reverse=True), key
        assert gaps[-1] < gaps[0], key
    for r in rows:
        assert all(r["prediction_items"].values()), r["n"]
        assert r["theta_map_failed"] == {}, r["n"]


def test_dh_jensen_polynomials_are_real_rooted_at_the_measured_wedge_cells():
    geo = RESULTS["root_geometry"]
    for key, ds in (("n3200", g.ROOT_DS), ("n50", g.ROOT_DS_LOW)):
        assert float(geo[key]["max_abs_dlog_gamma_vs_dps60_table"]) < 1e-65
        for name, through in (("holland_theta_half", 4), ("pade", 5)):
            assert [r["d"] for r in geo[key][name]["by_d"]] == list(ds)
            for r in geo[key][name]["by_d"]:
                assert r["model_real_roots"] == r["d"] and r["jensen_real_roots"] == r["d"], (key, name)
                assert r["c_minus_1_vanishes_through_j"] == through, (key, name, r["d"])


def test_the_contrast_dh_is_non_hyperbolic_only_at_n_zero():
    con = RESULTS["contrast_n0"]
    assert float(con["table_max_rel_dev_literal_vs_relative_cutoff"]) < 1e-30
    assert float(con["pair2_table_dps180_j400_max_rel_dev_literal_vs_relative_cutoff"]) < 1e-50
    cells = {(c["d"], c["n"]): c for c in con["cells"]}
    assert cells[(22000, 0)]["relative_cutoff"]["complex_pair_present"] is True
    assert cells[(20000, 0)]["relative_cutoff"]["complex_pair_present"] is False
    assert cells[(30000, 1)]["relative_cutoff"]["complex_pair_present"] is False
    assert abs(float(con["jensen_clock_record"]["pair1_dstar"]) - 20785.13) < 0.01
    v = RESULTS["verdict"]["contrast"]
    assert v["no_overlap"] is True and v["non_hyperbolic_cells_found_at_n"] == [0]
