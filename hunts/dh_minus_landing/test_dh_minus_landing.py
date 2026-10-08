"""Pins for hunt #122 (`hunts/dh_minus_landing/`).

Every number cited in RESULTS.md is read from `results.json` here; the cheap
instruments are also re-run live (one Arb disk at the top rung, the exact
polynomial tracker control, the clipped-contour refusal), so that a stale
JSON cannot pass on its own. Nothing here assigns evidentiary status.

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/dh_minus_landing
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
from scipy.optimize import brentq

from hunts.dh_minus_heat import odd_ball
from hunts.dh_minus_landing import probe

HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results.json").read_text())

T_C_DIGITS = "1.08763600022958693221796415445"   # route A, dps 50, 30 significant digits
X_C_DIGITS = "7.53994424216733522475507579"
TOP_RUNG = Fraction(10876359, 10000000)


def _frac(text) -> Fraction:
    return Fraction(text)


# ---------------------------------------------------------------------------
# recorded controls
# ---------------------------------------------------------------------------


def test_known_values_through_the_same_libraries():
    k = RESULTS["known_value_controls"]
    assert float(k["zeta2_minus_pi2_over_6"]) < 1e-28
    assert float(k["gamma1_minus_reference"]) < 1e-14
    assert float(k["Xi0_minus_reference"]) < 1e-9


def test_the_recorded_217_over_200_disk_is_reproduced():
    r = RESULTS["recorded_disk_reproduced"]
    assert r["decided"] is True
    assert all(v is True for k, v in r["coarse"].items() if k != "written_margin")
    assert _frac(r["margin"]["lower"]) > 0
    assert _frac(r["coarse"]["written_margin"]) == Fraction(559961, 2000000000000000)


def test_zero_time_gate_reproduces_both_pilot_zeros():
    g = RESULTS["zero_time_gate"]
    for label in ("pair1", "pair2"):
        assert g[label]["converged"] is True
        assert g[label]["abs_difference"] < 1e-8
    assert float(g["hurwitz_identity_defect_dps30"]) < 1e-28


def test_tracker_hits_the_closed_form_landings():
    c = RESULTS["tracker_known_value_controls"]
    assert c["isolated_pair"]["abs_error"] < 1e-12
    assert abs(c["isolated_pair"]["expected_y0sq_over_2"] - 0.18) < 1e-15
    assert c["quartic"]["abs_error"] < 1e-12


# ---------------------------------------------------------------------------
# the landing time, two routes
# ---------------------------------------------------------------------------


def test_route_a_digits_and_precision_response():
    a = RESULTS["route_a"]
    assert a["dps50"]["t_c"].startswith(T_C_DIGITS)
    assert a["dps50"]["x_c"].startswith(X_C_DIGITS)
    assert a["dps30"]["t_c"][:26] == a["dps50"]["t_c"][:26]
    assert float(a["precision_response_t_c"]) < 1e-24
    assert float(a["dps50"]["residual_H"]) < 1e-45
    assert float(a["dps50"]["residual_Hprime"]) < 1e-45
    # the double zero is non-degenerate: H'' is not small there
    assert float(a["dps50"]["second_derivative_at_double_zero"]) > 0.03


def test_route_b_agrees_with_route_a_and_with_its_own_refinement():
    b = RESULTS["route_b"]
    t_a = float(RESULTS["route_a"]["dps50"]["t_c"])
    assert abs(b["grid480_nodes128"]["t_c"] - t_a) < 1e-12
    assert abs(b["grid960_nodes256"]["t_c"] - t_a) < 1e-12
    assert b["resolution_response"] < 1e-12
    assert float(RESULTS["agreement"]["route_a_dps50_vs_route_b_grid480"]) < 1e-12
    # the scout rows change sign exactly once, between 1.0876 and 1.0877
    signs = [np.sign(r["discriminant"]) for r in b["scout_rows"]]
    assert signs == [-1, -1, -1, -1, 1, 1]


def test_the_real_zeros_keep_separating_after_the_landing():
    rows = RESULTS["after_landing"]
    seps = [r["separation"] for r in rows]
    assert all(r["discriminant"] > 0 for r in rows)
    assert seps == sorted(seps)


# ---------------------------------------------------------------------------
# the ladder of rational heat times
# ---------------------------------------------------------------------------


def test_every_rung_is_decided_on_every_configuration():
    rungs = [r for r in RESULTS["disk_ladder"] if "skipped" not in r]
    assert len(rungs) == 5
    times = [_frac(r["t"]) for r in rungs]
    assert times == sorted(times)
    t_c = _frac(RESULTS["route_a"]["dps50"]["t_c"])
    for r in rungs:
        assert _frac(r["t"]) > Fraction(217, 200)
        assert _frac(r["t"]) < t_c
        assert r["decided_all_configs"] is True
        assert len(r["configs"]) == 4
        for c in r["configs"]:
            assert c["decided"] is True
            assert _frac(c["margin"]["lower"]) > 0
        assert r["written_margin_positive"] is True
        assert _frac(r["written_margin"]) > 0
        # the coarse bounds are in the safe direction of every configuration
        for c in r["configs"]:
            assert _frac(c["H_abs_upper"]) <= _frac(r["coarse"]["H_abs_below"])
            assert _frac(c["Hprime_abs_lower"]) >= _frac(r["coarse"]["Hprime_abs_above"])
            assert _frac(c["M2_upper"]) <= _frac(r["coarse"]["M2_below"])
    assert times[-1] == TOP_RUNG
    assert abs(rungs[-1]["delta_to_t_c"] - 1.002e-7) < 1e-9


def test_top_rung_disk_rerun_live_at_128_bits():
    rung = [r for r in RESULTS["disk_ladder"] if "skipped" not in r][-1]
    row = odd_ball.rouche(tuple(rung["centre"]), Fraction(1, 10**7), t=rung["t"], prec=128)
    assert row["decided"] is True
    assert _frac(row["margin"]["lower"]) > 0
    # the written rational inequality of RESULTS.md, from the coarse bounds
    r = Fraction(1, 10**7)
    coarse = rung["coarse"]
    assert r * _frac(coarse["Hprime_abs_above"]) > _frac(coarse["H_abs_below"]) + r * r * _frac(coarse["M2_below"]) / 2


def test_bracket_after():
    b = RESULTS["bracket_after"]
    assert b["strict_lower_rational"] == str(TOP_RUNG)
    assert b["upper_unchanged"] == "567009/320000"
    assert _frac(b["wide_frame_strict_lower"]) == 4 * TOP_RUNG
    t_c = _frac(RESULTS["route_a"]["dps50"]["t_c"])
    assert abs(b["door_value_for_this_pair"] - float(t_c - Fraction(217, 200))) < 1e-15
    assert abs(b["remaining_below_t_c"] - float(t_c - TOP_RUNG)) < 1e-15
    assert 0.0038 < b["fraction_of_recorded_gap"] < 0.0039


# ---------------------------------------------------------------------------
# controls run live
# ---------------------------------------------------------------------------


def test_isolated_pair_control_live():
    x0, y0 = 0.3, 0.6

    def evaluate(z, t, k=0):
        p = np.polynomial.polynomial.Polynomial([x0 * x0 + y0 * y0 - 2 * t, -2 * x0, 1.0])
        return p(z) if k == 0 else p.deriv()(z)

    t_star = brentq(lambda t: probe.discriminant(evaluate, t, x0, 1.0)[0], 0.05, 0.3, xtol=1e-15)
    assert abs(t_star - y0 * y0 / 2) < 1e-12


def test_clipped_contour_refuses_live():
    evaluate = probe.float_grid(480)
    with pytest.raises(probe.WindingError):
        probe.discriminant(evaluate, 1.08, 7.549, 0.05)
    # and the honest contour at the same time reports a pair
    delta, _ = probe.discriminant(evaluate, 1.08, 7.549, 0.3)
    assert delta < 0


def test_lesions_fired_as_recorded():
    L = RESULTS["lesions"]
    assert L["clipped_contour"]["refused"] is True
    assert L["displaced_centre"]["decided"] is False
    assert L["underresolved_series"]["decided"] is False
    fault = L["shared_layer_kernel_fault"]
    assert fault["pair_found"] is True
    # the two routes agree with each other on the wrong function ...
    assert fault["routes_abs_difference"] < 1e-9
    # ... which sits far from the true landing time ...
    assert float(fault["shift_from_true_t_c"]) > 1e-3
    # ... and only the zero-time Hurwitz identity sees the fault
    assert float(fault["hurwitz_identity_defect"]) > 1e-4
    assert float(RESULTS["zero_time_gate"]["hurwitz_identity_defect_dps30"]) < 1e-28


def test_second_pair_lands_well_before_the_first():
    s = RESULTS["second_pair"]
    t_first = float(RESULTS["route_a"]["dps50"]["t_c"])
    assert s["route_b"]["t_c"] < t_first - 0.4
    assert abs(s["route_b"]["t_c"] - 0.63095343954) < 1e-9
    assert s["routes_abs_difference"] < 1e-8
    assert s["resolution_response"] < 1e-8


def test_no_kill_condition_fired():
    assert all(v is False for v in RESULTS["kill_conditions"].values())
