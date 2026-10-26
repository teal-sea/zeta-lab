"""Pins for hunt #151.  Run: .venv/bin/python -m pytest -q -n0 hunts/li_dh_onset_hardened

The artifact tests read the committed JSON; the recomputation tests rerun the
cheap pieces (a box count, a located square, the aliasing bound, the branch
refusal, the xi control, two iv nodes) so a regression in the code shows up
without rerunning the first wave.
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction as Q

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from flint import arb  # noqa: E402

import admissibility as adm  # noqa: E402
from balls import S_tail, prec_guard, q_arb  # noqa: E402
from trapezoid import (DHModel, bound_M, li_balls, nodes_needed,  # noqa: E402
                       sample_upper)

ART = os.path.join(HERE, "artifacts")


def _load(name):
    return json.load(open(os.path.join(ART, name)))


# ---------------------------------------------------------------------------
# step 1: admissibility
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,N_box,N_line", [("admissibility.json", 98, 94),
                                               ("admissibility_T133.json", 78, 74)])
def test_the_completeness_equality_closes_and_the_faults_break_it(name, N_box, N_line):
    a = _load(name)
    e = a["equality"]
    assert (e["N_box"], e["N_line"], e["two_q"]) == (N_box, N_line, 4)
    assert e["closes"] and a["q"] == 2
    assert [L["label"] for L in a["located"]] == ["pair1", "pair2"]
    assert all(L["count"] == 1 for L in a["located"])
    assert a["faults"]["drop_one_quadruple_closes"] is False
    assert a["faults"]["displaced_square"] == 0
    assert a["faults"]["displaced_square_closes"] is False
    assert a["half_plane"]["no_zero_re_ge_3/2"] and a["real_axis"]["f_positive_on_[1/2,sigma_h]"]


def test_the_radius_numbers():
    rad = _load("admissibility.json")["radius"]
    assert rad["binding_zero"] == "pair1"
    assert rad["R_a_lower"] == pytest.approx(0.9999579956, abs=1e-10)
    assert rad["r_below_R_a"] and rad["one_minus_r"] == pytest.approx(1.0e-4, rel=1e-3)
    # the judge's c = 1e4 statement: the midpoint circle (1 + r)/2 lies beyond R_a
    assert rad["c_1e4_midpoint_circle_beyond_R_a"] is True
    # at T = 133 the above-T bound, not pair1, sets the lower bound
    assert _load("admissibility_T133.json")["radius"]["R_a_lower"] < rad["R_a_lower"]


def test_the_box_count_agrees_with_hunt_128_at_height_100():
    """#128's mpmath argument principle (zero_side.json) measured 54 at T = 100."""
    assert adm.box_count(Q(100))["N_box"] == 54


def test_a_located_square_counts_one_and_a_displaced_one_counts_zero():
    b, g = Q("0.8085171824566373855533519606068441278507"), Q("85.69934848537759217192926770894172903799")
    assert adm.locate(b, g)["count"] == 1
    assert adm.locate(b + 10 * adm.DELTA, g)["count"] == 0


def test_the_half_plane_sum_matches_hunt_128():
    """#128 pinned sum_{n>=2} |a_n| n^{-sigma} = 1 at sigma = 1.3951."""
    assert S_tail(Q(3, 2), 128) < 1
    with prec_guard(128):
        assert S_tail(Q("1.3950"), 128) > 1 and S_tail(Q("1.3952"), 128) < 1


# ---------------------------------------------------------------------------
# step 3: the aliasing bound and the branch step
# ---------------------------------------------------------------------------

def test_the_aliasing_bound_holds_and_is_not_vacuous():
    """Coarse N with the aliasing term switched off (M = 0) against a fine
    reference: the true error must sit below bound (A).  With rho = 0.999, near
    the true analyticity radius, the bound must also be within 1e4 of the error
    (at rho = 0.95 it is valid but 1e10 too large, because the coefficients
    really decay like R_a^{-m} with R_a near 1, not like 0.95^{-m})."""
    n, P = 40, 160
    with prec_guard(P):
        r, rho = q_arb(Q(9, 10)), q_arb(Q(999, 1000))
    M = bound_M(rho, P)["M_upper"]
    N_ref = 1200
    ref = li_balls(DHModel(), r, N_ref, n, P, rho, M)["lambda"]
    assert all(float(x.rad()) < 1e-35 for x in ref)
    N_c = 400
    coarse = li_balls(DHModel(), r, N_c, n, P, rho, 0.0)["lambda"]
    with prec_guard(P):
        x = (r / rho) ** N_c
        worst_ratio = 0.0
        for k in (1, 10, 20, 40):
            bound = arb(k) * q_arb(Q(M)) * rho ** (-k) * x / (1 - x)
            err = abs(coarse[k - 1] - ref[k - 1])
            assert err.upper() < bound.upper(), (k, err, bound)
            worst_ratio = max(worst_ratio, float((err.upper() / bound.upper()).mid()))
    assert worst_ratio > 1e-4, worst_ratio


class _ZeroOnContour(DHModel):
    """h(s) = s - s0 with s0 on the sampling circle between nodes 3 and 4."""
    name = "planted"

    def __init__(self, s0):
        super().__init__()
        self.s0 = s0

    def L(self, s, prec):
        return s * 0

    def h(self, s, prec):
        return s - self.s0

    def principal(self, s):
        return bool(s.real > 1000)


def test_the_branch_step_refuses_a_zero_on_the_contour():
    """A zero of h on the circle between two nodes: the step must be refused,
    not unwrapped by guesswork."""
    from flint import acb
    from trapezoid import s_of
    with prec_guard(128):
        r = q_arb(Q(9, 10))
        x = q_arb(Q(7, 64))                      # between nodes 3 and 4 of N = 64
        s0 = s_of(acb(r * x.cos_pi(), r * x.sin_pi()))
    with pytest.raises(RuntimeError):
        sample_upper(_ZeroOnContour(s0), r, 64, 128)


def test_coarse_sampling_is_bridged_not_refused():
    """Neighbouring nodes too far apart for one ball step are chained through
    points between them (arc bisection), and the branch still closes."""
    with prec_guard(128):
        r = q_arb(Q(99, 100))
    _, stats = sample_upper(DHModel(), r, 32, 128)
    assert stats["closure_contains_0"] and stats.get("arc_bisections", 0) > 0


def test_the_branch_closes_on_a_fine_circle():
    with prec_guard(128):
        r = q_arb(Q(9, 10))
    _, stats = sample_upper(DHModel(), r, 512, 128)
    assert stats["closure_contains_0"] and stats["principal_nodes"] > 0


# ---------------------------------------------------------------------------
# step 2: evaluator, second route, controls
# ---------------------------------------------------------------------------

def test_the_xi_control_passes_and_both_faults_flip_it():
    import evaluator
    out = evaluator.xi_control()
    assert out["clean"]["passes"] and out["clean"]["contained"] == 48
    assert not out["gamma_shift"]["passes"] and not out["branch_slip"]["passes"]


def test_the_iv_route_meets_arb_at_the_off_line_heights():
    import evaluator
    keep = evaluator.IV_HEIGHTS
    try:
        evaluator.IV_HEIGHTS = (85.7, 1000)
        out = evaluator.iv_crosscheck()
    finally:
        evaluator.IV_HEIGHTS = keep
    assert out["all_meet"] and out["planted_kappa_fault_caught_at"] >= 1


def test_the_evaluator_artifact():
    ev = _load("evaluator.json")
    assert ev["iv"]["all_meet"] and len(ev["iv"]["nodes"]) == 20
    assert ev["iv"]["planted_kappa_fault_caught_at"] >= 10
    assert ev["xi_control"]["control_ok"]
    d = ev["dh_two_radii"]
    assert d["radii_intersect"] and d["max_abs_difference"] < 1e-29
    assert d["9/10"]["contains_128_table"] == 200 and d["99/100"]["contains_128_table"] == 200
    assert d["9/10"]["all_positive"] and d["99/100"]["all_positive"]
    assert d["lambda_1"].startswith("[0.0976361468095196711815489743939")
    t = {row["prec"]: row["seconds_per_node"] for row in ev["timing"]}
    assert set(t) == {200, 250} and all(0 < v < 0.05 for v in t.values())


def test_the_sizing_artifact():
    sz = _load("sizing.json")
    assert all(m["closure_contains_0"] for m in sz["M"].values())
    plans = {(p["c"], p["n_max"]): p for p in sz["plans"]}
    p = plans[(5000, 500_000)]
    assert p["N_power_of_two"] >= p["N_aliasing"] and p["N_power_of_two"] > 500_000
    assert math.log2(p["N_power_of_two"]).is_integer()
    assert sz["c_1e4"]["midpoint_circle_inside_R_a"] is False
