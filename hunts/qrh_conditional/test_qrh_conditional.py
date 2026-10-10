"""Pins for hunt #121 (`hunts/qrh_conditional/`).

Everything pinned here is conditional on QRH(theta), the hypothesis named in
MISSION.md; a pin that passes says the arithmetic is what RESULTS.md prints,
not that the hypothesis holds.  The crossover tests recompute two root
searches (about four seconds); the rest is instant.
"""
from __future__ import annotations

import json
from fractions import Fraction as Fr
from pathlib import Path

from mpmath import mp

from hunts.qrh_conditional import probe

HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results.json").read_text(encoding="utf-8"))


# --- A. exponents ----------------------------------------------------------

def test_exponents_under_the_seven_eighths_strip():
    e = probe.strip_exponents(Fr(7, 8))
    assert e["rank1_T_N_exponent"] == Fr(11, 4)
    assert e["rank1_gap_to_31"] == Fr(3, 4)
    assert e["rank1_saving_over_N3"] == Fr(1, 4)
    assert e["pointwise_level"] == Fr(1, 8)
    assert e["arc_exponent_cross_constraint"] == Fr(1, 8)
    assert e["arc_exponent_quartic_constraint"] == Fr(1, 12)
    assert e["arc_exponent"] == Fr(1, 12)
    assert e["circle_total_exponent"] == Fr(35, 12)
    assert e["circle_gap_to_target"] == Fr(11, 12)
    assert e["bootstrap_theta"] == Fr(23, 24)
    assert e["theorem_A_exponent"] == Fr(7, 4)
    assert e["theorem_A_gap_to_T"] == Fr(3, 4)
    assert e["theorem_B_cap"] == Fr(11, 4)
    assert e["frontier_M_N_exponent"] == Fr(11, 4)
    assert e["frontier_D_N_exponent"] == Fr(15, 16)
    assert e["rank3_sqrt_arc_exponent"] == Fr(13, 4)


def test_exponents_under_the_eleven_twelfths_strip():
    e = probe.strip_exponents(Fr(11, 12))
    assert e["rank1_T_N_exponent"] == Fr(17, 6)
    assert e["rank1_gap_to_31"] == Fr(5, 6)
    assert e["pointwise_level"] == Fr(1, 12)
    assert e["arc_exponent"] == Fr(1, 18)
    assert e["circle_total_exponent"] == Fr(53, 18)
    assert e["bootstrap_theta"] == Fr(35, 36)
    assert e["theorem_A_exponent"] == Fr(11, 6)


def test_the_rh_control_closes_rank_one_and_nothing_else():
    """At theta = 1/2 the strip is RH: rank 1's gap is 0, the circle route is
    still a power short (8/3 against CHHL's conditional 5/2), Theorem A is N L^4."""
    e = probe.strip_exponents(Fr(1, 2))
    assert e["rank1_gap_to_31"] == 0
    assert e["circle_total_exponent"] == Fr(8, 3) > Fr(5, 2)
    assert e["theorem_A_exponent"] == 1


def test_the_quartic_constraint_binds_for_every_strip_short_of_rh_and_the_two_routes_agree():
    for k in range(50, 100):
        theta = Fr(k, 100)
        e = probe.strip_exponents(theta)
        assert e["arc_exponent_quartic_constraint"] <= e["arc_exponent_cross_constraint"]
        a = e["arc_exponent"]
        # route 1: 5a + 4theta - 1 = 3 - a; route 2: 2a + 1 + 2theta = 3 - a; both at a
        assert 5 * a + 4 * theta - 1 == 3 - a
        assert 2 * a + 1 + 2 * theta == 3 - a


def test_the_bootstrap_never_improves_the_strip():
    """CHHL's lower bound plus E << N^c forces Theta <= (c-1)/2 = (2+theta)/3,
    which exceeds theta for every theta < 1: iterating moves away from 1/2."""
    for k in range(50, 100):
        theta = Fr(k, 100)
        e = probe.strip_exponents(theta)
        assert e["bootstrap_theta"] == (2 + theta) / 3
        assert e["bootstrap_drift"] == 2 * (1 - theta) / 3 > 0
    assert probe.strip_exponents(Fr(99, 100))["bootstrap_theta"] < 1


def test_results_json_carries_the_fresh_exponents():
    assert RESULTS["A_exponents"] == probe.exponent_table()


# --- B. crossover heights -----------------------------------------------------

def test_crossover_at_seven_eighths():
    rec = probe.crossovers(Fr(7, 8), strip_consts=(1,))["1"]["johnston_yang"]
    roots = [float(r) for r in rec["roots_u"]]
    assert len(roots) == 2
    assert abs(roots[0] - 6.8223694893590492) < 1e-9
    assert abs(roots[1] - 35.112921865597573) < 1e-9
    assert abs(float(rec["crossover_log10_x"]) - 15.249348) < 1e-5
    assert rec["sign_at_u_5000"] == "negative"
    assert rec == RESULTS["B_crossover"]["7/8"]["1"]["johnston_yang"]


def test_crossover_at_eleven_twelfths():
    rec = probe.crossovers(Fr(11, 12), strip_consts=(1,))["1"]["johnston_yang"]
    roots = [float(r) for r in rec["roots_u"]]
    assert len(roots) == 2
    assert abs(roots[1] - 98.224972268120887) < 1e-9
    assert abs(float(rec["crossover_log10_x"]) - 42.658563) < 1e-5
    assert rec == RESULTS["B_crossover"]["11/12"]["1"]["johnston_yang"]


def test_the_explicit_remainder_is_the_smaller_bound_on_the_hunts_measured_ladder():
    """SW_EFFECTIVE.md's ladder runs 1e5 <= N <= 1e7; between the two roots the
    strip-shaped bound (convention constant 1) is the larger one."""
    with mp.workdps(30):
        for n in (1e5, 1e6, 1e7):
            assert probe.log_ratio_jy(mp.log(n), mp.mpf(7) / 8, 1) > 0
            assert probe.log_ratio_jy(mp.log(n), mp.mpf(11) / 12, 1) > 0


def test_crossover_rises_with_the_convention_constant_and_the_bare_shape_is_higher():
    for name in ("7/8", "11/12"):
        row = RESULTS["B_crossover"][name]
        us = [float(row[c]["johnston_yang"]["crossover_u"]) for c in ("1", "10", "100", "10000")]
        assert us == sorted(us) and us[0] < us[-1]
        for c in ("1", "10", "100", "10000"):
            assert float(row[c]["bare_shape_K1"]["crossover_u"]) > float(row[c]["johnston_yang"]["crossover_u"])
    assert RESULTS["B_remainder_used"]["A"] == "9.39"
    assert RESULTS["B_remainder_used"]["B"] == "1.515"
    assert RESULTS["B_remainder_used"]["C"] == "0.8274"


# --- C. Li coefficients ---------------------------------------------------------

def test_the_per_zero_algebra():
    with mp.workdps(40):
        for beta, gamma in (("0.875", probe.GAMMA_1), ("0.75", "100"), ("0.51", "0.3")):
            direct = probe.r_direct(beta, gamma) ** 2 - 1
            closed = probe.r2_minus_1_closed(beta, gamma)
            assert abs(direct - closed) < mp.mpf("1e-35")
            assert closed > 0
        # on the line the factor is exactly 1
        assert abs(probe.r_direct("0.5", probe.GAMMA_1) - 1) < mp.mpf("1e-38")
        # the cap equals the direct value at beta = theta
        assert abs(probe.r_cap(mp.mpf(7) / 8, probe.GAMMA_1) - probe.r_direct("0.875", probe.GAMMA_1)) < mp.mpf("1e-38")
        # at gamma -> 0 the cap is theta/(1-theta)
        assert abs(probe.r_cap(mp.mpf(7) / 8, 0) - 7) < mp.mpf("1e-38")
        assert abs(probe.r_cap(mp.mpf(11) / 12, 0) - 11) < mp.mpf("1e-38")


def test_the_illustration_numbers():
    caps = RESULTS["C_li"]["caps"]
    g1 = caps["gamma_1"]
    assert abs(float(g1["7/8"]["r_cap_minus_1"]) - 1.87506183757e-3) < 1e-13
    assert abs(float(g1["11/12"]["r_cap_minus_1"]) - 2.08327587838e-3) < 1e-13
    assert abs(float(g1["1"]["r_cap_minus_1"]) - 2.49949831588e-3) < 1e-13
    assert abs(float(g1["7/8"]["n_at_which_r_cap_pow_n_is_2"]) - 370.012770074) < 1e-6
    assert abs(float(g1["1"]["n_at_which_r_cap_pow_n_is_2"]) - 277.660951334) < 1e-6
    # the strip's whole effect on the per-zero growth exponent is the factor 2 theta - 1
    # at gamma_1 the second-order term of log(1 + x) shifts the ratio by about 4e-4
    assert abs(float(g1["7/8"]["log_r_ratio_to_no_strip"]) - 0.7504091042) < 1e-9
    assert abs(float(g1["11/12"]["log_r_ratio_to_no_strip"]) - 0.833650751832) < 1e-9
    assert abs(float(g1["7/8"]["log_r_ratio_to_no_strip"]) - 0.75) < 1e-3
    assert abs(float(g1["11/12"]["log_r_ratio_to_no_strip"]) - 5 / 6) < 1e-3
    t0 = caps["T0_verified"]
    assert abs(float(t0["7/8"]["r_cap_minus_1"]) - 4.16666469376e-26) < 1e-36
    assert abs(float(t0["1"]["r_cap_minus_1"]) - 5.55555292502e-26) < 1e-36
    assert abs(float(t0["7/8"]["log_r_ratio_to_no_strip"]) - 0.75) < 1e-9   # stored to 12 digits
    assert abs(float(t0["7/8"]["n_at_which_r_cap_pow_n_is_2"]) / 1.66355402103e25 - 1) < 1e-9
    # fresh recomputation agrees with the file
    assert probe.li_illustration() == RESULTS["C_li"]


# --- cited, not recomputed -----------------------------------------------------

def test_the_de_bruijn_newman_consequence_is_above_the_record():
    """9/32 and 0.2 are both cited (document 38 section 6; docs/05); only the
    comparison is done here."""
    assert Fr(9, 32) > Fr(1, 5)
    assert "9/32" in RESULTS["cited_not_recomputed"]["de_bruijn_newman_under_strip_7_8"]
    assert RESULTS["cited_not_recomputed"]["verified_height_T0"] == "3e12"


# --- the hunt's own discipline --------------------------------------------------

def test_the_hunt_keeps_its_hypothesis_in_every_file():
    text = (HERE / "RESULTS.md").read_text(encoding="utf-8")
    assert text.count("Under QRH(7/8):") >= 8
    assert "void" in text
    mission = (HERE / "MISSION.md").read_text(encoding="utf-8")
    assert "withdrawn or refuted by an independent replay" in mission


def test_the_hunt_obeys_the_lexical_rules():
    """No reserved word, no em dash, no reference to a doc number the tree
    does not carry. On 2026-10-08 that last rule was a ban on `docs/38`, which
    then lived on another branch; it reached main the same day, so the rule now
    checks every referenced number against `docs/` instead of naming one."""
    import re

    reserved = "cert" + "if"
    docs = HERE.parent.parent / "docs"
    carried = {p.name[:2] for p in docs.glob("[0-9][0-9]-*.md")}
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".md", ".py", ".json"}:
            continue
        text = path.read_text(encoding="utf-8")
        assert reserved not in text.lower(), path.name
        assert chr(0x2014) not in text, path.name
        for number in re.findall(r"docs/(\d{2})\b", text):
            assert number in carried, (path.name, f"docs/{number}")
