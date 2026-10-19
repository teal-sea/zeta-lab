"""Tests for the independent review of hunt #135's H1_H3.md (REVIEW_H1_H3.md).

Each test checks one piece of H1_H3.md with code written for this review
(`review_h1h3.py`), never with `probe.py`, `probe_h1_h3.py` or `review/`. Exact
constants are compared as rationals; measured numbers are compared against the
hunt's own `results_h1_h3.json`, read as data. Every cross-check has a planted
fault beside it that turns it red. Nothing here bears on RH.
"""

from __future__ import annotations

import json
import random
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp
from mpmath import mp, mpf

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
for p in (str(_HERE), str(_ROOT)):
    if p not in sys.path:
        sys.path.insert(0, p)

import review_h1h3 as R  # noqa: E402

Q = sp.Rational
HUNT_JSON = _HERE.parent / "results_h1_h3.json"


@pytest.fixture(scope="module")
def hunt_json():
    return json.loads(HUNT_JSON.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def row_1e7():
    return R.analyse_n(10**7)


# ---------------------------------------------------------------------------
# H1, the exact algebra of sections 4.1 to 4.4
# ---------------------------------------------------------------------------


def test_simpson_is_the_only_zero_of_the_limit_system():
    sols = sp.solve(list(R.phi_inf()), R.XVARS, dict=True)
    assert sols == [dict(zip(R.XVARS, R.XSTAR))]


def test_jacobian_inverse_and_determinant_as_displayed():
    J, Ji = R.jacobian()
    assert J == sp.Matrix([[-1, -1, -1, 0], [0, -1, -2, -Q(4, 3)], [0, -Q(3, 4), -3, -2], [0, -Q(1, 2), -4, -2]])
    assert J.det() == -1
    assert Ji == sp.Matrix([[-1, Q(5, 2), -Q(8, 3), 1], [0, -2, Q(4, 3), 0], [0, -Q(1, 2), Q(4, 3), -1],
                            [0, Q(3, 2), -3, Q(3, 2)]])
    planted = Ji.copy()
    planted[0, 3] = Q(9, 10)
    assert J * planted != sp.eye(4)


def test_J_is_minus_diag_1234_times_phase1_moment_matrix():
    x, w1 = Q(1, 2), Q(2, 3)
    M = sp.Matrix([[1, 1, 1, 0], [0, x, 1, w1], [0, x**2, 1, 2 * w1 * x], [0, x**3, 1, 3 * w1 * x**2]])
    assert M.det() == Q(-1, 24)
    J, _ = R.jacobian()
    assert J == -sp.diag(1, 2, 3, 4) * M


def test_S_polynomials_as_displayed():
    g0, gx, g1, x, e = R.g0, R.gx, R.g1, R.xx, R.EPS
    S = R.s_vector()
    assert S[0] == 0
    assert sp.expand(S[1] - (g0**2 - g1**2)) == 0
    assert sp.expand(S[2] - (-3 * g1**2 + e * (g0**3 + gx**3 / 4 + g1**3))) == 0
    assert sp.expand(S[3] - (-6 * g1**2 + e * (4 * g1**3 + x * gx**3) + e**2 * (g0**4 - g1**4))) == 0
    # and Phi_inf = 1 - P_j(X; 0), so the decomposition of 4.2 is exact
    for j in range(4):
        assert sp.expand(1 - R.p_at_zero()[j] - R.phi_inf()[j]) == 0


def test_contraction_matrix_entries_as_displayed():
    dgx, dx = R.DVARS[1], R.DVARS[3]
    M = R.contraction_matrix()
    shown = sp.Matrix([
        [0, 4 * dx**3 - 2 * dx**2, 0, 12 * dgx * dx**2 - 4 * dgx * dx + 8 * dx**2 - Q(8, 3) * dx],
        [0, 4 * dx**2, 0, 8 * dgx * dx + Q(16, 3) * dx],
        [0, -4 * dx**3 - 2 * dx**2, 0, -12 * dgx * dx**2 - 4 * dgx * dx - 8 * dx**2 - Q(8, 3) * dx],
        [0, 6 * dx**3 - Q(3, 2) * dx, 0, 18 * dgx * dx**2 - Q(3, 2) * dgx + 12 * dx**2]])
    assert (M - shown).applyfunc(sp.expand) == sp.zeros(4, 4)


def test_kappa_and_nu_w_exact():
    assert max(R.kappa_rows()) == Q(4533, 15625)
    assert list(R.kappa_rows()) == [Q(3472, 15625), Q(177, 625), Q(1736, 15625), Q(4533, 15625)]
    assert max(R.nu_w_rows()) == Q(86, 9)
    # planted: a monomial bound that forgets one term reads lower
    dx = R.DVARS[3]
    full = R.monomial_bound(6 * dx**3 - Q(3, 2) * dx)
    assert R.monomial_bound(6 * dx**3) < full


def test_kappa_bound_dominates_a_grid_of_the_box():
    """The grid maximum 177/625 quoted in 4.3, and no grid point above kappa."""
    M = R.contraction_matrix()
    dgx, dx = R.DVARS[1], R.DVARS[3]
    best = 0
    for i in range(21):
        for k in range(21):
            a = Q(2, 25) * (Q(2 * i, 20) - 1)
            b = Q(3, 50) * (Q(2 * k, 20) - 1)
            Mv = M.subs({dgx: a, dx: b})
            rows = [sum(abs(Mv[r, c]) * R.WEIGHTS[c] for c in range(4)) / R.WEIGHTS[r] for r in range(4)]
            best = max(best, max(rows))
    assert best == Q(177, 625)
    assert best <= max(R.kappa_rows())


def test_sigma_values_quoted_in_4_3(hunt_json):
    assert abs(float(R.sigma_bar(Q(1, 32))) - 0.0777) < 5e-5
    assert abs(float(R.sigma_bar(Q(1, 16))) - 0.1609) < 5e-5
    assert abs(float(R.sigma_bar(Q(1, 8))) - 0.3439) < 5e-5
    for e, v in hunt_json["exact"]["sigma_bar_at_eps"].items():
        assert R.sigma_bar(Q(e)) == Q(v)


def test_eps_part_of_initial_residual_exact():
    v = R.eps_part_at_xstar()
    e = R.EPS
    target = [e * (1 - e) / 18, -e * (1 - e) / 9, e * (1 - e) / 18, 0]
    assert all(sp.expand(v[i] - target[i]) == 0 for i in range(4))


def test_admissibility_iff_eps_below_two_thirds():
    thr, (t1, t2) = R.admissibility_threshold()
    assert thr == Q(2, 3) and t1 == Q(11, 15) and t2 == Q(2, 3)
    assert R.corner_admissible(Q(2, 3) - Q(1, 10**9))
    assert not R.corner_admissible(Q(2, 3))


def test_first_order_configuration():
    out, dX = R.first_order_configuration()
    assert list(dX) == [-Q(2, 9), -Q(2, 9), Q(4, 9), Q(1, 4)]
    assert out["J_inv_t_first_order"] == ["1/3", "0", "-1/3", "-1/4"]
    y = sp.symbols("y")
    assert sp.sympify(out["A_over_nL"]) == 3 + 7 * y
    assert sp.sympify(out["D_minus_n_L_over_n"]) == Q(1, 3) + Q(2, 3) * y
    assert sp.sympify(out["B_minus_2n_L_over_n"]) == Q(5, 3)
    assert sp.sympify(out["C_minus_2n_L_over_n"]) == -Q(11, 3)
    assert sp.sympify(out["B_minus_C_L_over_n"]) == Q(16, 3) - Q(112, 9) * y


def test_uniform_sufficient_form_threshold_discrepancy():
    """4.3 says ||J^-1 t||_w <= 7/200 suffices; 4.5 says 9/250. With the bounds 4.3 displays
    (eps part <= eps/9, rho summed over the box) the true threshold is 0.035977, so 7/200
    holds and 9/250 does not; with the sharper eps(1 - eps)/9 and rho at X* it is 0.036473."""
    u = R.uniform_sufficient_form()
    assert u["q"] < Fraction(4574, 10000)
    assert u["room"] > Fraction(434, 10000)
    assert Fraction(7, 200) < u["max_Jinv_t_doc_bounds"] < Fraction(9, 250) < u["max_Jinv_t_sharp"]


# ---------------------------------------------------------------------------
# Lemma S, symbolically; (P2)
# ---------------------------------------------------------------------------


def test_g0_prime_identity_is_exact():
    assert R.rho_g_identity_defect() == 0


@pytest.mark.parametrize("k", range(2, 9))
def test_lemma_s_c_first_order_constant(k):
    one, c1, _ = R.lemma_s_first_order(k)
    assert one == 1 and c1 == R.harmonic(k - 2) - 1


def test_lemma_s_c_fails_under_a_planted_wrong_saddle_derivative():
    """With L' = L/(Q + N) in place of Holland's L/Q the k = 3 first-order constant is no
    longer H_1 - 1 = 0: the symbolic check reads the saddle identity, it does not assume it."""
    N, L, Qs = R.NS, R.LS, R.QS
    D = lambda f: sp.diff(f, N) + (L / (Qs + N)) * sp.diff(f, L)
    G3 = sp.factor(sp.together(D(sp.together(D(D(R.g0_symbolic()))))))
    F = sp.factor(sp.together((-N**2 * L * G3).subs({N: 1 / (R.AS * R.BS), L: 1 / R.AS})))
    c0, c1 = [sp.series(F.subs(R.BS, 0), R.AS, 0, 2).removeO().coeff(R.AS, i) for i in (0, 1)]
    assert (c0, c1) != (1, 0)


def test_lemma_s_main_term_structure_and_explicit_bound():
    """f_k(a, b) = P_k(a, b)/(c (4 + 4a - 3b)^(2k - ...)): bounded on |a| <= 1/4, |b| <= 1/8."""
    for k in range(2, 7):
        bound, m = R.lemma_s_explicit_bound(k)
        assert m == 2 * k
        assert 1 < bound < 10**4


def test_p2_fixed_point_derivation_threshold():
    with mp.workdps(30):
        s13, c13 = R.p2_fixed_point_margin(13, mp.pi / 2)
        s12, _ = R.p2_fixed_point_margin(12, mp.pi / 2)
        assert s13 > 0 and c13 < 1
        assert s12 < 0


def test_p2_numerically_on_sector():
    with mp.workdps(30):
        wl, wr = R.p2_scan(mpf(1), 346, zmax=1e12, n_r=12, n_phi=7)
        assert wl >= 4 and wr <= mpf(1) / 8
        wl50, _ = R.p2_scan(mpf("0.5"), 50, zmax=1e3, n_r=6, n_phi=5)
        assert wl50 < 4  # (P2) needs x_0 of a few hundred


def test_g0_ratios_quoted_in_section_2():
    with mp.workdps(60):
        r6, _ = R.g0_ratio(mpf(10) ** 3, 6)
        assert abs(r6 - mpf("1.127")) < mpf("5e-4")
        r, L = zip(*[R.g0_ratio(mpf(10) ** 50, k) for k in range(2, 7)])
        got = [float((r[i] - 1) * L[i]) for i in range(5)]
        for a, b in zip(got, (-0.991, -0.018, 0.477, 0.810, 1.062)):
            assert abs(a - b) < 6e-4
        worst = max(abs(abs(R.g0_ratio(mpf(10) ** 20 * mp.expj(mpf("0.5")), k)[0]) / R.g0_ratio(mpf(10) ** 20, k)[0] - 1)
                    for k in range(2, 7))
        assert mpf("2e-6") < worst < mpf("4e-6")


# ---------------------------------------------------------------------------
# The independent target route
# ---------------------------------------------------------------------------


def test_moment_route_matches_zeta_li_cauchy():
    rows = R.li_validation(20, 21, dps=40)
    assert all(r["max_rel_diff_m2_6"] < mpf(10) ** -40 for r in rows)


def test_planted_error_in_one_moment_is_seen():
    """At n = 1e7 a 1e-30 error in one log moment moves Delta^5 h by about 10 percent, while
    two quadratures at different precision and window agree to far below that."""
    with mp.workdps(110):
        logs = R.log_moment_shifts(10**7, imax=5, dps=90)
        alt = R.log_moment_shifts(10**7, imax=5, dps=110, width=50)
        d, da = R.forward_differences(logs), R.forward_differences(alt)
        bad = list(logs)
        bad[3] += mpf(10) ** -30
        db = R.forward_differences(bad)
        assert abs(db[5] - d[5]) / abs(d[5]) > mpf("0.05")
        assert abs(da[5] - d[5]) / abs(d[5]) < mpf(10) ** -20


def test_targets_agree_with_hunt_route_b(row_1e7, hunt_json):
    th = {r["n"]: r for r in hunt_json["large_n_route_B"]}["1e7"]
    with mp.workdps(40):
        for mine, theirs in zip(row_1e7["tau"], th["tau"]):
            assert abs(mine - mpf(theirs)) / mpf(theirs) < mpf(10) ** -13


def test_holland_main_term_reproduces_differences(row_1e7):
    assert max(row_1e7["holland_main_term_rel_diff"]) < mpf(10) ** -11


def test_lemma_t_expansion_through_third_order(row_1e7):
    """(tau_j L/2 - 1 - c1/L - c2/L^2) L^3 stays O(1): the symbolic expansion of Lemma S explains
    the measured targets beyond the first order H1_H3.md claims."""
    assert all(abs(v) < 6 for v in row_1e7["tau_second_order_residual_times_L3"])


# ---------------------------------------------------------------------------
# Lemma C on measured data; the system two ways; attempts to break uniqueness
# ---------------------------------------------------------------------------


def test_lemma_c_closes_at_1e7_with_the_quoted_numbers(row_1e7):
    lc = row_1e7["lemma_c"]
    assert lc["closes"]
    assert abs(lc["q"] - mpf("0.688")) < mpf("5e-4")
    assert abs(lc["d0"] - mpf("0.0215")) < mpf("5e-5")
    assert abs(lc["rhs"] - mpf("0.0250")) < mpf("5e-5")
    assert row_1e7["dX_w_norm"] < lc["radius"]
    assert abs(row_1e7["dX_w_norm"] - mpf("0.0243")) < mpf("5e-5")


def test_lemma_c_fails_at_1e6():
    res = R.analyse_n(10**6)
    assert not res["lemma_c"]["closes"] and not res["lemma_c_sharp"]["closes"]


def test_moment_form_and_quotient_form_have_the_same_root(row_1e7):
    assert row_1e7["quotient_form_rel_diff"] < mpf(10) ** -60
    assert row_1e7["phi_residual"] < mpf(10) ** -60
    assert row_1e7["ordered"]


def test_sampled_DT_stays_below_q_and_roots_coincide():
    a = R.adversarial_lemma_c(10**7, samples=20, starts=6, seed=7)
    assert a["max_DT_w_sampled"] < a["q"]
    assert a["max_T_image_w_sampled"] < a["r"]
    assert a["roots_in_B"] == a["starts"] and a["root_spread_w"] < mpf(10) ** -60


def test_planted_wrong_inverse_breaks_the_contraction():
    """With a wrong J^-1 in T the sampled ||DT||_w exceeds the lemma's q: the probe can fail."""
    saved = [row[:] for row in R.JINV_F]
    try:
        R.JINV_F[1][1] = Fraction(-3)
        a = R.adversarial_lemma_c(10**7, samples=10, starts=1, seed=3)
        assert a["max_DT_w_sampled"] > a["q"]
    finally:
        for i in range(4):
            R.JINV_F[i][:] = saved[i]


# ---------------------------------------------------------------------------
# H3, section 3.3
# ---------------------------------------------------------------------------


def test_psi5_bound_item1(hunt_json):
    with mp.workdps(30):
        for y in (1, 2, 10, 100, 10**4, 3 + 4j, 10 + 30j, 100 + 90j, 1000 + 500j):
            assert R.psi5_defect_ratio(y) <= 1
        assert abs(R.psi5_defect_ratio(1) - mpf(hunt_json["psi5_defect_samples"]["1"])) < mpf("1e-8")


def test_psi5_sum_against_gap_integral_item2(hunt_json):
    res = R.analyse_n(3200)
    with mp.workdps(60):
        it = R.item2(3200, res["ABCD"])
        assert abs(it["abs_diff_n6"] - mpf(hunt_json["psi5_sum_vs_gap_integral_n3200"]["abs_diff_n6"])) < mpf("1e-3")
        assert it["abs_diff_n6"] < it["bound_n6_each_param"] < it["bound_n6_min_param"]


def test_circle_measurement_of_p1_at_400(hunt_json):
    c = R.circle_check(400)
    th = hunt_json["h_circle"][0]
    with mp.workdps(60):
        assert abs(c["R_n"] - mpf(th["R_n"])) < mpf("1e-9")
        assert abs(c["max_R_variation_times_n"] - mpf(th["max_R_variation_on_circle_times_n"])) < mpf("1e-6")
        assert abs(c["sup_h6_inner_over_leading"] - mpf(th["sup_h6_inner_circle_over_leading"])) < mpf("1e-6")
        assert abs(c["sup_h6_inner_over_leading"] - c["sup_h6_inner_half_points"]) < mpf("1e-6")
        # Holland's (15) against the Titchmarsh-kernel moment on the real axis, Delta^2..Delta^6
        d = R.forward_differences(R.log_moment_shifts(400, imax=6, dps=60))
        for m in range(2, 7):
            assert abs(mp.re(c["delta_m_from_circle"][m - 2]) - d[m]) / abs(d[m]) < mpf(10) ** -20


def test_circle_detects_a_planted_wrong_linear_term():
    """An error in a constant of (18) hides in c_sad, but an error in a z-dependent term
    cannot: a planted extra 1e-3 z in R varies by about 1e-3 n/4 on the circle, which the
    measurement (0.028/n) would show."""
    with mp.workdps(30):
        n = mpf(400)
        zs = [n + n / 8 * mp.expj(2 * mp.pi * m / 8) for m in range(8)]
        base = []
        for z in zs:
            _, core = R.h15(z)
            base.append(core - R.g0_complex(2 * z - 2, R.saddle_L(2 * z - 2)))
        var = max(abs(a - base[0]) for a in base)
        planted = max(abs((a + mpf("1e-3") * z) - (base[0] + mpf("1e-3") * zs[0])) for a, z in zip(base, zs))
        assert var * n < mpf("0.06") < planted * n
