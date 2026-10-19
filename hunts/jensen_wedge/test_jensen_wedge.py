"""Pins for hunt #135 phase 0 (`hunts/jensen_wedge/`).

Three kinds of test. The instrument tests build exact Laguerre, Jacobi and
finite-free coefficient sequences and check that each fit recovers its own
parameters and returns a zero defect, and that a planted sign is read back
(a sign detector that cannot read the other sign is not a detector). The live
tests recompute route A and route B at n = 100 and compare them with each
other and with `results.json`, so a stale JSON cannot pass on its own. The
record tests pin the numbers RESULTS.md cites. Nothing here assigns
evidentiary status.

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/jensen_wedge
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from mpmath import mp, mpf

from hunts.jensen_wedge import probe

HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results.json").read_text())
DPS = 60


def _rows():
    return {r["n"]: r for r in RESULTS["subgrid"]}


def _log_R_jacobi(U, V, S, jmax=6):
    """log of S^j (U)_j / (U^j (V)_j), j = 0..jmax (U=None: Laguerre), as finite
    sums so that a planted negative U (with |U| > jmax) stays real."""
    out = []
    for j in range(jmax + 1):
        v = j * mp.log(S) - mp.fsum(mp.log(V + i) for i in range(j))
        if U is not None:
            v += mp.fsum(mp.log1p(i / U) for i in range(j))
        out.append(v)
    return out


# ---------------------------------------------------------------------------
# the instrument, on sequences whose answer is known
# ---------------------------------------------------------------------------


def test_laguerre_fit_recovers_its_own_sequence():
    with mp.workdps(DPS):
        B, S = mpf("812.5"), mpf("3.25")
        lag = probe.laguerre(probe.log_q_from_log_R(_log_R_jacobi(None, B, S)))
        assert abs(lag["B_L"] / B - 1) < mpf(10) ** -50
        assert abs(lag["D3"]) < mpf(10) ** -50


def test_jacobi_fit_recovers_its_own_sequence_and_the_laguerre_sign_follows_A():
    with mp.workdps(DPS):
        B, S = mpf("812.5"), mpf("3.25")
        for A, sign in ((mpf(40000), 1), (mpf(-40000), -1)):
            lq = probe.log_q_from_log_R(_log_R_jacobi(A, B, S))
            jac = probe.jacobi(lq)
            assert abs(jac["A_J"] / A - 1) < mpf(10) ** -40
            assert abs(jac["B_J"] / B - 1) < mpf(10) ** -40
            assert abs(jac["E_J4"]) < mpf(10) ** -50
            # A > 0 is exactly a positive Laguerre defect at R_3, and a planted
            # A < 0 is read back as a negative one
            assert sign * probe.laguerre(lq)["D3"] > 0


def test_finite_free_fit_recovers_a_product_of_two_jacobi_sequences():
    with mp.workdps(DPS + probe.GUARD):
        A, B, C, D, S = mpf(52000), mpf(4100), mpf(2000), mpf(1900), mpf("2.5")
        lr = [a + b for a, b in zip(_log_R_jacobi(A, B, S), _log_R_jacobi(C, D, D))]
        lq = probe.log_q_from_log_R(lr)
        jac = probe.jacobi(lq)
        theta = D / jac["B_J"]
        ff = probe.finite_free(lq, jac["B_J"], theta, (A * mpf("1.1"), B * mpf("1.01"),
                                                       C * mpf("1.001")))
        assert abs(ff["A"] / A - 1) < mpf(10) ** -30
        assert abs(ff["B"] / B - 1) < mpf(10) ** -30
        assert abs(ff["C"] / C - 1) < mpf(10) ** -30
        assert abs(ff["E_F5"]) < mpf(10) ** -50


def test_holland_L_solves_its_equation_and_tracks_the_saddle():
    with mp.workdps(40):
        for n in (50, 3200, 10**12):
            L = probe.script_L(n)
            x = 2 * n - 2
            assert abs(L * (mp.pi * mp.exp(L) + mpf(3) / 4) - x) < mpf(10) ** -30 * x
            assert abs(L - probe.saddle(n)) < 1


def test_mp_taylor_reproduces_polygammas_at_the_options_route_B_uses():
    for n, dps in ((100, 60), (10**20, 150)):
        assert probe.differentiation_check(n, dps) < mpf(10) ** -(dps - 5)


# ---------------------------------------------------------------------------
# live recomputation at n = 100, both routes
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def live_100():
    n = 100
    I, dev = probe.moments_trapezoid(n - 1, n + probe.J_MAX, DPS)
    with mp.workdps(DPS + probe.GUARD):
        ell = {m: probe.log_gamma_from_moments(I, m, DPS) for m in range(n, n + probe.J_MAX + 1)}
        lrA = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, probe.J_MAX + 1)]
        g = probe.saddle_expansion(n, DPS)
        lrB = [mpf(0)] + [probe.log_R_from_expansion(g, j, 7) for j in range(1, probe.J_MAX + 1)]
        Ln = probe.script_L(n)
        return {"n": n, "I": I, "dev": dev, "lrA": lrA, "lrB": lrB, "g": g,
                "dA": probe.defects(lrA, n, Ln), "dB": probe.defects(lrB, n, Ln)}


def test_route_A_converges_and_matches_the_check_route(live_100):
    assert live_100["dev"] < mpf(10) ** -(DPS + 5)
    with mp.workdps(DPS + probe.GUARD):
        for k in (99, 102, 105):
            assert abs(live_100["I"][k] / probe.moment_quad(k, DPS) - 1) < mpf(10) ** -(DPS - 2)


def test_both_sign_facts_hold_live_on_both_routes(live_100):
    for d in (live_100["dA"], live_100["dB"]):
        assert d["lag"]["D3"] > 0
        assert d["jac"]["E_J4"] < 0
        assert d["jac"]["A_J"] > 0


def test_live_route_A_reproduces_the_recorded_defects(live_100):
    row = _rows()[100]
    d = live_100["dA"]
    with mp.workdps(DPS):
        for got, key in ((d["lag"]["D3"], "D3_A"), (d["jac"]["E_J4"], "E_J4_A"),
                         (d["ff"]["E_F5"], "E_F5_A")):
            assert abs(got / mpf(row[key]) - 1) < mpf(10) ** -13


def test_live_route_B_sits_within_its_recorded_stated_error(live_100):
    stated = _rows()[100]["logR_B_stated_error"]
    with mp.workdps(DPS):
        for j in range(1, probe.J_MAX + 1):
            assert abs(live_100["lrA"][j] - live_100["lrB"][j]) <= mpf(stated[j - 1])


def test_a_planted_moment_fault_is_seen_by_the_check_route(live_100):
    """One moment perturbed at relative 1e-30 moves log R past the probe's guard."""
    n = live_100["n"]
    I = dict(live_100["I"])
    with mp.workdps(DPS + probe.GUARD):
        I[n + 2] *= 1 + mpf(10) ** -30
        base = probe.log_gamma_from_moments(I, n, DPS)
        moved = max(abs(probe.log_gamma_from_moments(I, n + j, DPS) - base - live_100["lrA"][j])
                    for j in range(1, probe.J_MAX + 1))
        assert moved > mpf(10) ** -(DPS - 10)


# ---------------------------------------------------------------------------
# the record
# ---------------------------------------------------------------------------


def test_route_A_reproduces_zeta_li_on_both_cached_tables():
    v50, v30 = RESULTS["validation_vs_li"]
    assert v50["m_range"] == [17, 47] and float(v50["max_abs_dlog_gamma"]) < 1e-45
    assert v30["m_range"] == [17, 127] and float(v30["max_abs_dlog_gamma"]) < 1e-25


def test_route_A_internal_and_check_route_agreement_is_recorded():
    a = RESULTS["route_A"]
    assert a["k_range"] == [49, 3205] and a["moments_computed"] == 3157
    assert float(a["max_coarse_fine_deviation"]) < 1e-65
    assert float(a["max_abs_dlogR_vs_check_route"]) < 1e-50


def test_the_two_sign_facts_hold_at_every_n_from_50_to_3200():
    dense = RESULTS["dense_route_A"]
    assert dense["n_count"] == 3151
    lag, jac = dense["laguerre_D3"], dense["jacobi_E_J4"]
    assert (lag["positive"], lag["negative"], lag["zero"]) == (3151, 0, 0)
    assert (jac["positive"], jac["negative"], jac["zero"]) == (0, 3151, 0)
    assert lag["sign_changes_at_n"] == [] and jac["sign_changes_at_n"] == []
    assert dense["all_parameters_positive_and_C_gt_D"] is True
    v = RESULTS["verdict"]
    assert v["laguerre_R3_positive_everywhere"] and v["jacobi_R4_negative_everywhere"]


def test_route_B_agrees_in_sign_and_within_stated_error_on_the_subgrid():
    v = RESULTS["verdict"]
    assert v["route_B_agrees_in_sign_on_subgrid"] is True
    assert v["route_B_within_stated_error_on_subgrid"] is True


def test_the_preset_error_rule_miss_is_kept_in_the_record():
    """The first rule (M = 4, Laplace part |M4 - M3|) missed at n = 150 only;
    the deviation there falls with M, which is what an estimator artifact does."""
    assert RESULTS["verdict"]["preset_rule_M4_misses_at_n"] == [150]
    ladder = _rows()[150]["laplace_ladder_abs_dev_j1_j5"]
    devs = [float(ladder[str(M)][0]) for M in range(2, probe.M_ROUTE_B + 1)]
    assert devs[-1] < 1e-18 and devs[0] > 1e-10
    assert devs[3] < devs[2] and devs[4] < devs[3]


def test_route_B_resolves_every_sign_it_reports():
    for r in RESULTS["subgrid"]:
        assert all(r["B_resolves_sign"]), r["n"]
        assert all(r["signs_agree_A_B"]), r["n"]


def test_holland_section_6_parameter_limits_are_approached_at_large_n():
    """A/A_J -> 6/5, (B - B_J) L/n -> 1/3, (C - D) L/n -> 1/24 (Holland Sec. 6)."""
    rows = RESULTS["large_n_route_B"]
    last = rows[-1]
    assert last["n"] == "1e20"
    assert abs(float(last["A_over_A_J"]) - 1.2) < 0.02
    assert abs(float(last["B_minus_B_J_times_L_over_n"]) - 1 / 3) < 0.02
    assert abs(float(last["C_minus_D_times_L_over_n"]) - 1 / 24) < 0.002
    for key, target in (("A_over_A_J", 1.2), ("B_minus_B_J_times_L_over_n", 1 / 3),
                        ("C_minus_D_times_L_over_n", 1 / 24)):
        gaps = [abs(float(r[key]) - target) for r in rows]
        assert gaps == sorted(gaps, reverse=True), key


def test_the_leading_constants_of_lemmas_4_3_and_5_4_are_approached_from_below():
    rows = RESULTS["large_n_route_B"]
    for key in ("n2L_D3_over_2", "minus_n3L_EJ4_over_2"):
        vals = [float(r[key]) for r in rows]
        assert vals == sorted(vals) and 0.9 < vals[-1] < 1, key


def test_the_R5_defect_is_negative_at_holland_D_on_both_routes_and_at_large_n():
    f = RESULTS["dense_route_A"]["finite_free_E_F5"]
    assert (f["positive"], f["negative"], f["sign_changes_at_n"]) == (0, 3151, [])
    assert all(float(r["E_F5_B"]) < 0 for r in RESULTS["subgrid"])
    assert all(float(r["E_F5"]) < 0 for r in RESULTS["large_n_route_B"])


def test_the_R5_sign_depends_on_the_free_choice_of_D():
    """At every recorded n the sign of E_F5 flips inside the theta grid, and at the
    crossing (C - D)/D exceeds the 1/4 of Holland's window (57)."""
    for row in RESULTS["theta_sensitivity"]:
        c = row["crossing"]
        assert c is not None, row["n"]
        assert 0.5 < float(c["theta"]) < 1
        assert float(c["C_minus_D_over_D"]) > 0.25


def test_the_theta_crossing_rises_with_n_and_is_pinned():
    got = [(r["n"], float(r["crossing"]["theta"])) for r in RESULTS["theta_sensitivity"]]
    expected = [(100, 0.819287720988), (400, 0.858347705559), (1600, 0.885407630503),
                (3200, 0.895770429343)]
    for (n, t), (n0, t0) in zip(got, expected):
        assert n == n0 and abs(t - t0) < 1e-9
    assert [t for _, t in got] == sorted(t for _, t in got)
