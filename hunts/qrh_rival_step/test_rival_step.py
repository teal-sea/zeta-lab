"""Hunt #120: every number RESULTS.md states is pinned here.

Two kinds of test.  The *live* ones recompute the cheap facts from scratch on
every run (route agreement, the first rival zero on two routes, the winding
numbers, the zeta control, the inverse coefficients, the planted faults).  The
*pinned* ones read ``results.json``, which the long census runs wrote, and
check that the prose quotes it correctly; they do not re-run the census.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import probe  # noqa: E402

RESULTS = os.path.join(HERE, "results.json")

#: the first zero of zeta_Q for Q = x^2 + xy + 4y^2 (D = -15) beyond 7/8,
#: located by the census and polished on routes B and C (RESULTS.md section 3)
RHO_15_RE = "0.927460880755676711234306655417"
RHO_15_IM = "15.4966340679011306133947231821"


@pytest.fixture(scope="module")
def results():
    if not os.path.isfile(RESULTS):
        pytest.skip("results.json not present")
    with open(RESULTS) as fh:
        return json.load(fh)


# ---------------------------------------------------------------------------
# routes: derived constants, cross-route agreement, planted faults
# ---------------------------------------------------------------------------


def test_bessel_expansion_matches_the_lattice_route_and_the_direct_sum():
    """Route B's constants were derived by matching route A; this pins that
    match at 1e-18 (twenty digits), and the direct Dirichlet series at s = 3."""
    pts = [mp.mpf(3), mp.mpc("2.5", "5"), mp.mpc("1.1", "12")]
    with mp.workdps(25):
        for form in (probe.FORMS["d15"], probe.FORMS["d23"]):
            for s in pts:
                assert abs(probe.route_a(s, form, dps=20) - probe.route_b(s, form, dps=20)) < mp.mpf("1e-18")
        # the defining sum where it converges: |m|, |k| <= 300 leaves a tail ~ 1e-10
        direct = mp.fsum(
            mp.mpf(m * m + m * k + 4 * k * k) ** -3 for m in range(-300, 301) for k in range(-300, 301) if (m, k) != (0, 0)
        )
        assert abs(direct - probe.route_b(mp.mpf(3), probe.FORMS["d15"], dps=20)) < mp.mpf("1e-8")


def test_genus_character_factorization_matches_both_lattice_routes():
    """zeta_Q0 = zeta L(chi_-15) + L(chi_-3) L(chi_5) and zeta_Q1 the difference."""
    with mp.workdps(25):
        for s in (mp.mpf(3), mp.mpc("2.5", "5"), mp.mpc("1.1", "12")):
            assert abs(probe.route_c(s, dps=20) - probe.route_b(s, probe.FORMS["d15"], dps=20)) < mp.mpf("1e-18")
            assert abs(probe.route_c(s, dps=20, which=1) - probe.route_b(s, probe.FORMS["d15b"], dps=20)) < mp.mpf("1e-18")


def test_a_planted_fault_in_route_b_turns_the_cross_check_red():
    """A cross-check that cannot fail is not a cross-check."""
    with mp.workdps(25):
        s = mp.mpc("1.1", "12")
        good = probe.route_a(s, probe.FORMS["d15"], dps=20)
        assert abs(good - probe.route_b(s, probe.FORMS["d15"], dps=20, scale=4)) > mp.mpf("1e-6")
        assert abs(good - probe.route_b(s, probe.FORMS["d15"], dps=20, use_cos=False)) > mp.mpf("1e-6")


def test_flint_bessel_orientation_is_derived_not_assumed():
    acb, arb, ctx, orient = probe.flint_ctx()
    assert orient in ("z_first", "order_first")
    with ctx.workprec(128):
        v = probe._bessel_k_ball(acb(arb("1.5"), 20), acb(3))
    ref = mp.besselk(mp.mpc("1.5", "20"), 3)
    assert abs(complex(float(v.real.mid()), float(v.imag.mid())) - complex(ref)) < 1e-14


# ---------------------------------------------------------------------------
# the first rival zero beyond 7/8, hardened by two routes and balls
# ---------------------------------------------------------------------------


def test_first_rival_zero_is_beyond_seven_eighths_and_agrees_on_two_routes():
    seed = mp.mpc("0.9275", "15.4966")
    with mp.workdps(35):
        r_c = probe.refine(lambda z: probe.route_c(z, dps=30), seed, dps=30)
        r_b = probe.refine(lambda z: probe.route_b(z, probe.FORMS["d15"], dps=32), seed, dps=30)
        assert abs(r_c - r_b) < mp.mpf("1e-28")
        assert abs(r_c - mp.mpc(RHO_15_RE, RHO_15_IM)) < mp.mpf("1e-28")
        assert mp.re(r_c) > mp.mpf("0.875")
        assert abs(probe.route_c(r_c, dps=30)) < mp.mpf("1e-28")
        assert abs(probe.route_b(r_b, probe.FORMS["d15"], dps=32)) < mp.mpf("1e-28")
        # the mirror zero 1 - conj(rho) of the functional equation
        assert abs(probe.route_c(1 - mp.conj(r_c), dps=30)) < mp.mpf("1e-25")
        # a perturbed point is not a zero
        assert abs(probe.route_c(r_c + mp.mpf("1e-3"), dps=30)) > mp.mpf("1e-3")


def test_the_lattice_route_vanishes_at_the_same_point():
    """Route A at 35 digits (about 0.7 digits per unit height are needed)."""
    with mp.workdps(40):
        rho = mp.mpc(RHO_15_RE, RHO_15_IM)
        assert abs(probe.route_a(rho, probe.FORMS["d15"], dps=35)) < mp.mpf("1e-28")


def test_the_rival_zero_is_a_cancellation_of_two_nonvanishing_euler_products():
    """At rho, zeta(rho) L(rho, chi_-15) = -L(rho, chi_-3) L(rho, chi_5), both of
    modulus 0.709: the zero is consistent with each Dirichlet L-function being
    zero-free there, which is exactly what the paper's Theorem 1.1 asserts."""
    with mp.workdps(35):
        rho = mp.mpc(RHO_15_RE, RHO_15_IM)
        v, A, B = probe.route_c(rho, dps=30, parts=True)
        assert abs(A) > mp.mpf("0.7") and abs(B) > mp.mpf("0.7")
        assert abs(abs(A) - mp.mpf("0.709163334034")) < mp.mpf("1e-10")
        assert abs(A + B) < mp.mpf("1e-28")


def test_mpmath_winding_number_around_the_zero_is_one():
    from zeta import epstein

    fn = lambda z: probe.route_c(z, dps=15)  # noqa: E731
    re, im = float(RHO_15_RE), float(RHO_15_IM)
    assert epstein.count_zeros_box(mp.mpc(re - 0.05, im - 0.05), mp.mpc(re + 0.05, im + 0.05), dps=15, fn=fn) == 1
    assert epstein.count_zeros_box(mp.mpc(re + 0.1, im - 0.05), mp.mpc(re + 0.2, im + 0.05), dps=15, fn=fn) == 0


def test_ball_winding_on_route_c_is_one_with_every_segment_enclosed():
    cre = Fraction(RHO_15_RE[:14])
    cim = Fraction(RHO_15_IM[:14])
    bw = probe.ball_winding(probe.route_c_ball, cre, cim, Fraction(1, 20), 256, segs=16)
    assert bw["winding"] == 1
    assert bw["all_segments_exclude_zero"] and bw["all_quotients_right_half_plane"]
    assert bw["winding_ball"][1] - bw["winding_ball"][0] < 1e-60
    bw0 = probe.ball_winding(probe.route_c_ball, cre + Fraction(3, 20), cim, Fraction(1, 20), 256, segs=16)
    assert bw0["winding"] == 0


def test_two_ball_routes_overlap_at_the_root_and_are_tiny_there():
    cre = Fraction(RHO_15_RE[:14])
    cim = Fraction(RHO_15_IM[:14])
    pb = probe.route_b_ball(probe.FORMS["d15"], cre, cim, 380)
    pc = probe.route_c_ball(cre, cim, 380)
    assert pb.overlaps(pc)
    assert float(pb.abs_upper()) < 1e-11 and float(pc.abs_upper()) < 1e-11
    assert float(pb.real.rad()) < 1e-30


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def test_the_same_finder_recovers_gamma_1_on_zeta():
    fz = probe.evaluator("zeta", 20)
    n, _ = probe.count_box(fz, 0.3, 0.9, 10.0, 20.0, dps=15)
    assert n == 1
    roots = probe.locate_zeros(fz, 0.3, 0.9, 10.0, 20.0, 1, dps=25)
    with mp.workdps(30):
        assert abs(mp.im(roots[0]) - mp.mpf(probe.GAMMA_1)) < mp.mpf("1e-14")
        assert abs(mp.re(roots[0]) - mp.mpf("0.5")) < mp.mpf("1e-14")
    bw = probe.ball_winding(probe.zeta_ball, Fraction(1, 2), Fraction(probe.GAMMA_1).limit_denominator(10**12), Fraction(1, 20), 256, segs=64)
    assert bw["winding"] == 1


def test_zero_free_abscissa_by_the_triangle_inequality():
    """zeta_Q(sigma_1) = 4, so |zeta_Q(s)/2 - 1| < 1 for Re s > sigma_1."""
    with mp.workdps(20):
        assert abs(mp.re(probe.route_b(mp.mpf("1.52709889569"), probe.FORMS["d15"], dps=15)) - 4) < mp.mpf("1e-8")
        assert abs(mp.re(probe.route_b(mp.mpf("1.42171147228"), probe.FORMS["d23"], dps=15)) - 4) < mp.mpf("1e-8")
        assert abs(mp.re(probe.route_b(mp.mpf(2), probe.FORMS["d15"], dps=15)) - mp.mpf("2.68461677469")) < mp.mpf("1e-9")


def test_inverse_coefficients_of_the_rival_are_not_multiplicative_and_not_bounded():
    N = 20000
    r = probe.rep_counts(probe.FORMS["d15"], N)
    assert r[1] == 2 and r[2] == 0 and r[4] == 6 and r[6] == 4
    a = [0] + [r[n] // 2 for n in range(1, N + 1)]
    b = probe.dirichlet_inverse(a)
    assert b[1:13] == [1, 0, 0, -3, 0, -2, 0, 0, -1, -2, 0, 0]
    assert b[4] != b[2] ** 2 and b[6] != b[2] * b[3]
    assert max(abs(x) for x in b[1:]) > 500
    # the convolution identity a * b = delta, checked exactly
    for n in range(2, 300):
        assert sum(a[d] * b[n // d] for d in range(1, n + 1) if n % d == 0) == 0
    # the class-number-one control: zeta_K = zeta L(chi_-19) has inverse mu * mu chi,
    # bounded by the divisor function
    r1 = probe.rep_counts(probe.FORMS["h1"], N)
    b1 = probe.dirichlet_inverse([0] + [r1[n] // 2 for n in range(1, N + 1)])
    assert max(abs(x) for x in b1[1:]) <= probe._max_divisor_count(N)
    assert all(b1[m * n] == b1[m] * b1[n] for m in range(2, 40) for n in range(m + 1, 500 // m + 1) if __import__("math").gcd(m, n) == 1)


def test_the_davenport_heilbronn_pinned_zero_and_the_deepest_census_pair_are_below_seven_eighths():
    from zeta import epstein

    assert float(epstein.OFFLINE_ZERO_RE) < 0.875
    with mp.workdps(25):
        r = probe.refine(lambda s: probe.dh(s, dps=20), mp.mpc("0.86953", "240.4046"), dps=20)
        assert abs(probe.dh(r, dps=20)) < mp.mpf("1e-18")
        assert abs(mp.re(r) - mp.mpf("0.8695305796406431")) < mp.mpf("1e-12")
        assert mp.re(r) < mp.mpf("0.875")


# ---------------------------------------------------------------------------
# pins: what RESULTS.md quotes from results.json
# ---------------------------------------------------------------------------


def test_results_json_pins_the_census(results):
    p = results["parts"]
    d15 = p["census_d15"]
    assert d15["box_re"] == [0.8751, 1.6] and d15["t_range"] == [0.5, 300.5]
    assert d15["total_count"] == results["pins"]["d15_count_beyond_7_8_below_300"]
    assert len(d15["zeros"]) == d15["total_count"]
    assert all(z["inside_window"] and z["winding_square_0.1_mpmath"] == 1 for z in d15["zeros"])
    assert abs(d15["max_re_located"] - results["pins"]["d15_max_re_below_300"]) < 1e-12
    re1 = p["census_d15_re1"]
    assert re1["box_re"] == [1.0003, 1.6] and re1["t_range"] == [0.5, 300.5]
    assert re1["total_count"] == results["pins"]["d15_count_beyond_1_below_300"]
    d23 = p["census_d23"]
    assert d23["total_count"] == results["pins"]["d23_count_beyond_7_8_below_60"]
    assert abs(d23["max_re_located"] - results["pins"]["d23_max_re_below_60"]) < 1e-12
    dh = p["dh"]
    assert dh["total_count"] == 0 and dh["t_range"] == [0.0, 300.0]
    assert dh["pinned_offline_zero_below_7_8"] and dh["flow_repair_pair_below_7_8"]


def test_results_json_pins_the_confirmations(results):
    p = results["parts"]
    low_seen = 0
    for key in ("confirm_d15", "confirm_d23"):
        for z in p[key]["zeros"]:
            low = abs(z["im"]) <= 100
            # the root is rounded to twelve significant digits before the ball
            # evaluation, so |f| there is |f'| times up to 5e-10 at height 300
            assert z["ball_value_at_root_route_b"]["abs_upper"] < 2e-9
            if low:
                low_seen += 1
                assert float(z["abs_f_route_b"]) < 1e-20
                assert float(z["abs_f_route_a"]) < 1e-20
                assert float(z["abs_route_b_scale4_at_root"]) > 1e-3
                assert float(z["abs_f_route_b_at_root_plus_1e-3"]) > 1e-5
                assert z["point_winding_route_b_balls"]["winding"] == 1
                assert z["point_winding_route_b_balls"]["max_abs_increment"] < 1.0
            if key == "confirm_d15":
                assert float(z["abs_f_route_c"]) < 1e-20
                if low:
                    assert float(z["abs_root_c_minus_root_b"]) < 1e-25
                else:
                    assert float(z["abs_f_route_c_at_root_plus_1e-3"]) > 1e-5
                assert z["ball_winding_route_c"]["winding"] == 1
                assert z["ball_winding_route_c_displaced_by_0.15"]["winding"] == 0
                assert z["ball_routes_overlap_at_root"]
                assert float(z["abs_zeta_L15_at_root"]) > 0.1
    assert low_seen >= 4


def test_results_json_pins_the_controls_and_the_inverse(results):
    p = results["parts"]
    c = p["controls"]
    assert c["zeta_box_count_[0.3,0.9]x[10,20]"] == 1
    assert float(c["abs_im_minus_gamma_1"]) < 1e-14
    assert c["zeta_ball_winding_at_gamma_1"]["winding"] == 1
    assert c["zeta_ball_winding_displaced"]["winding"] == 0
    assert c["h1_control_total"] == 0
    assert c["h1_inverse_max_abs_b_below_1e5"] <= c["h1_inverse_max_divisor_count_below_1e5"]
    assert c["h1_inverse_multiplicativity_failures"][0] == 0
    for key in ("d15", "d23"):
        assert c["route_agreement_at_four_points"][key]["max_abs_a_minus_b"] < 1e-18
        assert c["route_agreement_at_four_points"][key]["min_abs_a_minus_b_fault_scale4"] > 1e-8
    inv = p["inverse_d15"]
    assert inv["nmax"] == 10**6
    assert inv["max_abs_b"] == results["pins"]["d15_inverse_max_abs_b_below_1e6"]
    assert inv["multiplicativity_failures"] > 0
    assert inv["b4_vs_b2_squared"] == [-3, 0] and inv["b6_vs_b2_b3"] == [-2, 0]
    assert abs(inv["envelope_exponent"] - results["pins"]["d15_inverse_envelope_exponent"]) < 1e-9


def test_the_pins_match_the_prose(results):
    """RESULTS.md must quote the same numbers results.json holds."""
    text = open(os.path.join(HERE, "RESULTS.md"), encoding="utf-8").read()
    pins = results["pins"]
    for key in ("d15_count_beyond_7_8_below_300", "d15_count_beyond_1_below_300", "d23_count_beyond_7_8_below_60", "d15_inverse_max_abs_b_below_1e6"):
        assert str(pins[key]) in text, key
    for key in ("d15_max_re_below_300", "d23_max_re_below_60"):
        assert f"{pins[key]:.6f}"[:7] in text, key
