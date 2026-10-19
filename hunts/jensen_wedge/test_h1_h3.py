"""Pins for H1 and H3 (`hunts/jensen_wedge/H1_H3.md`, `probe_h1_h3.py`).

Each intermediate inequality of the two derivations is checked where it can fail,
and each check has a planted fault beside it that must turn it red: a tighter
1/n bound, a linear-only box bound, a planted far target for the contraction, a
wrong leading constant for h^(5) and for G_0^(6), a dropped branch correction on
the complex circle, a smaller psi^(5) constant, a sign error in the gap integral,
and a wrong first-order limit. Then live recomputations (route A at n = 400,
route B at n = 1e10, the complex circle at n = 400), so a stale JSON cannot pass
on its own. Then the record. Nothing here assigns evidentiary status.

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/test_h1_h3.py
"""

from __future__ import annotations

import itertools
import json
from fractions import Fraction as Fr
from pathlib import Path

import pytest
import sympy as sp
from mpmath import mp, mpf

from hunts.jensen_wedge import probe as p0
from hunts.jensen_wedge import probe_h1_h3 as h
from hunts.jensen_wedge import probe_phase1 as p1

HERE = Path(__file__).resolve().parent
REC = json.loads((HERE / "results_h1_h3.json").read_text())
DPS = 60
HARM = [Fr(0), Fr(1), Fr(3, 2), Fr(11, 6), Fr(25, 12)]  # H_0..H_4


def _rows_B():
    return REC["large_n_route_B"]


def _box_points(steps: int = 10):
    """The (d_gx, d_x) grid of the box: the only deviations M depends on."""
    r, w = h.R_BOX, h.WEIGHTS
    for a in range(-steps, steps + 1):
        for b in range(-steps, steps + 1):
            yield {h._D[0]: 0, h._D[1]: Fr(a, steps) * r * w[1],
                   h._D[2]: 0, h._D[3]: Fr(b, steps) * r * w[3]}


def _wnorm_rows(mat, sub) -> Fr:
    w = h.WEIGHTS
    return max(sum(abs(h.to_fr(mat[i, k].subs(sub))) * w[k] for k in range(4)) / w[i]
               for i in range(4))


# ---------------------------------------------------------------------------
# section 4.1 and 4.2: the system, exactly
# ---------------------------------------------------------------------------


def test_closed_form_u_prime_integrates_to_lambda():
    """lambda_j(n/w) = int_0^w u_j', u_j' = (j+1) t^j prod (1 + i t/n)^-1 (4.1).
    lambda_j loses about (j+1) log10(n/w) digits to cancellation, hence dps 80."""
    with mp.workdps(80):
        for n in (mpf(50), mpf(3200), mpf(10) ** 8):
            for j in range(4):
                for w in ("0.1", "0.5", "0.95"):
                    a = h.lam(j, n / mpf(w), n)
                    b = h.lam_from_integral(j, mpf(w), n)
                    assert abs(a / b - 1) < mpf(10) ** -30, (n, j, w)


def test_rho_hat_bound_holds_and_is_sharp_to_first_order():
    """-(j+1)(j+2) t/(2n) <= rhohat_j(t) <= 0; a bound half as large fails."""
    with mp.workdps(40):
        planted_fails = False
        for n in (mpf(50), mpf(3200), mpf(10) ** 6):
            for j in range(4):
                for t in ("0.01", "0.3", "0.7", "1"):
                    v = h.rho_hat(j, mpf(t), n)
                    bound = mpf((j + 1) * (j + 2)) * mpf(t) / (2 * n)
                    assert -bound <= v <= 0, (n, j, t)
                    planted_fails |= v < -bound / 2
        assert planted_fails


def _phi_decomposed(X, n, tau):
    """Phi_inf + t - eps S + beta - rho of (4.4), rho by quadrature."""
    eps = tau[0]
    g0, gx, g1, x = X
    wA, wB, wC, wD = eps * g0, x - eps * gx / 2, x + eps * gx / 2, 1 - eps * g1
    wb = n / (n + mpf(1) / 2)
    out = []
    for j in range(4):
        Pj = h._P(j)
        sub0 = {h._g0: g0, h._gx: gx, h._g1: g1, h._x: x, h._eps: 0}
        sube = dict(sub0)
        sube[h._eps] = eps
        phi_inf = 1 - mpf(str(sp.N(Pj.subs(sub0), 50)))
        eS = mpf(str(sp.N(Pj.subs(sube), 50))) - mpf(str(sp.N(Pj.subs(sub0), 50)))
        beta = (1 - wb ** (j + 1)) / eps
        f = lambda t, j=j: t ** j * h.rho_hat(j, t, n)  # noqa: E731
        rho = (j + 1) / eps * (mp.quad(f, [0, wA]) + mp.quad(f, [wB, wC]) + mp.quad(f, [wD, wb]))
        out.append(phi_inf + (tau[j] / eps - 1) - eS + beta - rho)
    return out


def test_the_decomposition_reproduces_the_exact_system():
    """(4.4) at an arbitrary point and arbitrary data agrees with Phi_n via lambda_j."""
    with mp.workdps(50):
        n = mpf(10) ** 5
        tau = [mpf("0.2"), mpf("0.21"), mpf("0.215"), mpf("0.218")]
        X = [mpf("0.17"), mpf("0.65"), mpf("0.18"), mpf("0.51")]
        a = h.phi_exact(X, n, tau)
        b = _phi_decomposed(X, n, tau)
        assert max(abs(u - v) for u, v in zip(a, b)) < mpf(10) ** -30


def test_simpson_is_the_zero_and_J_is_exact():
    phi = h.MODEL["phi_inf"]
    star = dict(zip(h._X, (sp.Rational(v.numerator, v.denominator) for v in h.X_STAR)))
    assert all(sp.simplify(p.subs(star)) == 0 for p in phi)
    # a planted configuration with the weights at 0 and x swapped is not a zero
    bad = dict(star)
    bad[h._g0], bad[h._gx] = star[h._gx], star[h._g0]
    assert any(sp.simplify(p.subs(bad)) != 0 for p in phi)
    J, Ji = h.J_exact(), h.J_inv_exact()
    assert J == [[-1, -1, -1, 0], [0, -1, -2, Fr(-4, 3)], [0, Fr(-3, 4), -3, -2], [0, Fr(-1, 2), -4, -2]]
    assert Ji == [[-1, Fr(5, 2), Fr(-8, 3), 1], [0, -2, Fr(4, 3), 0],
                  [0, Fr(-1, 2), Fr(4, 3), -1], [0, Fr(3, 2), -3, Fr(3, 2)]]
    assert sp.Matrix(J).det() == -1
    # J = -diag(1, 2, 3, 4) x phase 1's moment matrix, whose determinant is -1/24
    xs, w1 = Fr(1, 2), Fr(2, 3)
    cols = [[1, 0, 0, 0], [1, xs, xs ** 2, xs ** 3], [1, 1, 1, 1], [0, w1, 2 * w1 * xs, 3 * w1 * xs ** 2]]
    M1 = [[cols[c][r] for c in range(4)] for r in range(4)]
    assert all(J[r][c] == -(r + 1) * M1[r][c] for r in range(4) for c in range(4))
    assert sp.Matrix(M1).det() == sp.Rational(-1, 24)


# ---------------------------------------------------------------------------
# section 4.3: the box constants
# ---------------------------------------------------------------------------


def test_kappa_bounds_the_box_and_a_linear_only_bound_does_not():
    kap = h.kappa_bar()
    assert kap == Fr(4533, 15625)
    M = h.MODEL["M"]
    worst = max(_wnorm_rows(M, sub) for sub in _box_points())
    assert worst == Fr(177, 625) and worst <= kap and worst > Fr(95, 100) * kap
    # planted: keep only the monomials of degree 1 in the deviations
    lin = M.applyfunc(lambda e: sum(t for t in sp.Add.make_args(sp.expand(e))
                                    if sp.Poly(t, *h._D).total_degree() == 1) if e != 0 else 0)
    rho = [h.R_BOX * wi for wi in h.WEIGHTS]
    planted = max(h.weighted_row_sums(lin, rho, h.WEIGHTS))
    assert planted < worst


def test_sigma_bounds_sampled_points():
    D = h.MODEL["DJieS"]
    r, w = h.R_BOX, h.WEIGHTS
    for e in (Fr(1, 16), Fr(1, 8)):
        bound = h.sigma_bar(e)
        worst = Fr(0)
        for c in itertools.product((-1, 0, 1), repeat=4):
            sub = {h._D[i]: c[i] * r * w[i] for i in range(4)}
            sub[h._eps] = sp.Rational(e.numerator, e.denominator)
            worst = max(worst, _wnorm_rows(D, sub))
        assert worst <= bound and worst > Fr(4, 5) * bound, e
    assert abs(float(h.sigma_bar(Fr(1, 16))) - 0.16089356) < 1e-8
    assert abs(float(h.sigma_bar(Fr(1, 8))) - 0.34391855) < 1e-8


def test_nu_w_admissibility_and_the_exact_eps_part():
    assert h.nu_w() == Fr(86, 9)
    assert h.box_is_admissible(Fr(2, 3) - Fr(1, 10 ** 9)) and not h.box_is_admissible(Fr(2, 3))
    for e in (Fr(1, 7), Fr(1, 16), Fr(3, 100)):
        assert h.JieS_star(e) == [e * (1 - e) * v for v in (Fr(1, 18), Fr(-1, 9), Fr(1, 18), Fr(0))]


def test_the_uniform_sufficient_condition():
    """eps <= 1/16, n eps >= 1e5 and ||J^-1 t||_w <= 7/200 imply the inequality;
    9/250 would not, so the number is not loose."""
    with mp.workdps(30):
        eps = mpf(1) / 16
        n = mpf(10) ** 5 / eps
        small = h.explicit_small_terms(n, eps)
        q = h.fr_mpf(h.kappa_bar()) + h.fr_mpf(h.sigma_bar(Fr(1, 16))) + h.fr_mpf(h.nu_w()) * small["rho1_rowsum"]
        rhs = (1 - q) * h.fr_mpf(h.R_BOX)
        epart = eps / 9
        npart = h.fr_mpf(h.nu_w()) * max(small["beta"][j] + small["rho0"][j] for j in range(4))
        assert q < mpf("0.4574") and rhs > mpf("0.0434") and epart < mpf("0.0070") and npart < mpf("0.0005")
        assert mpf(7) / 200 + epart + npart <= rhs
        assert mpf(9) / 250 + epart + npart > rhs


# ---------------------------------------------------------------------------
# Lemma C on a planted two-factor sequence
# ---------------------------------------------------------------------------


def _planted(n, dX):
    """A two-Jacobi-factor sequence whose scaled configuration is X* + dX at
    eps = 2/L: its tau, and its configuration recomputed at eps = tau_0."""
    Ln = p0.script_L(n)
    e0 = 2 / Ln
    g0, gx, g1, x = (h.fr_mpf(h.X_STAR[i]) + dX[i] for i in range(4))
    wA, wB, wC, wD = e0 * g0, x - e0 * gx / 2, x + e0 * gx / 2, 1 - e0 * g1
    A, B, C, D = n / wA, n / wB, n / wC, n / wD
    lr = [mpf(0)]
    for j in range(1, h.J_TOP + 1):
        lr.append(mp.fsum(mp.log1p(i / A) + mp.log1p(i / C) - mp.log(B + i) - mp.log(D + i) + mp.log(D)
                          for i in range(j)) + j * mp.log(B))
    tau = h.targets(lr, n)
    X = h.scaled_config(n, tau[0], A, B, C, D)
    return tau, X


def test_contraction_holds_on_a_planted_near_point_and_refuses_a_far_one():
    # tau_3 and lambda_3 cancel about 50 digits at n = 1e12
    with mp.workdps(120):
        n = mpf(10) ** 12
        ok = []
        for dX in ((mpf("0.01"), mpf("-0.01"), mpf("0.02"), mpf("0.005")),     # inside
                   (mpf("0.01"), mpf("-0.01"), mpf("0.30"), mpf("0.005"))):    # planted far
            tau, X = _planted(n, dX)
            c = h.contraction(n, tau)
            dist = max(abs(X[i] - h.fr_mpf(h.X_STAR[i])) / h.fr_mpf(h.WEIGHTS[i]) for i in range(4))
            assert max(abs(v) for v in h.phi_exact(X, n, tau)) < mpf(10) ** -40
            ok.append(bool(c["closes"] and dist <= c["radius"]))
        assert ok == [True, False]


# ---------------------------------------------------------------------------
# Lemma T: the measured targets against their first order
# ---------------------------------------------------------------------------


def _approach(vals, limit):
    gaps = [abs(float(v) - float(limit)) for v in vals]
    return gaps == sorted(gaps, reverse=True), gaps[-1]


def test_targets_approach_their_first_order_values():
    """L t_j -> H_j (j = 1..3) and (tau_j L/2 - 1) L -> H_j - 1 (j = 0..4; j = 4 is
    the sixth difference, H3 on the real axis), monotonically over 1e4..1e20."""
    rows = _rows_B()
    for j in (1, 2, 3):
        mono, last = _approach([r["t_times_L"][j - 1] for r in rows], HARM[j])
        assert mono and last < 0.06, j
    for j in range(5):
        mono, last = _approach([r["tau_over_2_over_L_minus_1_times_L"][j] for r in rows], HARM[j] - 1)
        assert mono and last < 0.07, j
    # planted: a leading constant -6 for h^(5) halves tau_3, and L t_3 runs away
    bad = [(mpf(r["tau"][3]) / 2 / mpf(r["tau"][0]) - 1) * mpf(r["L_n"]) for r in rows]
    mono, last = _approach(bad, HARM[3])
    assert not mono and last > 20


def test_route_B_agrees_with_route_A_on_every_target():
    rows = REC["route_B_vs_A_targets"]
    assert [r["n"] for r in rows] == [n for n in p0.SUBGRID if n >= 400]
    for r in rows:
        assert float(r["max_rel_dev_A_B"]) < 1e-17, r["n"]
        assert float(r["max_rel_dev_A_B"]) < 10 * float(r["B_spread_M5_M6"]), r["n"]


def test_live_route_B_at_1e10_reproduces_the_record():
    n = mpf(10) ** 10
    with mp.workdps(h.route_B_dps(n)):
        lr = p1.lr_route_B_direct(n, p0.M_ROUTE_B)
        r, sol = h.row(n, lr, p0.script_L(n))
    rec = {float(x["n"]): x for x in _rows_B()}[1e10]
    for a, b in zip(r["tau"], rec["tau"]):
        assert abs(mpf(a) / mpf(b) - 1) < mpf(10) ** -13
    assert r["contraction"]["closes"] and r["contraction"]["measured_X_within_radius"]
    assert r["contraction"]["q"] == rec["contraction"]["q"]


# ---------------------------------------------------------------------------
# Lemma C on the measured inputs, and the first-order configuration
# ---------------------------------------------------------------------------


def test_inequality_holds_from_1e7_and_the_measured_point_is_inside_its_radius():
    for r in REC["subgrid_route_A"]:
        assert r["contraction"]["closes"] is False, r["n"]
        assert r["all_positive_and_U_gt_V"] and float(r["phi_exact_residual_at_X"]) < 1e-59, r["n"]
    for r in _rows_B():
        n = float(r["n"])
        c = r["contraction"]
        assert c["closes"] is (n >= 1e7), n
        if c["closes"]:
            assert c["measured_X_within_radius"] is True, n
            assert float(r["dX_w_norm"]) <= float(c["radius"]), n
        assert r["all_positive_and_U_gt_V"] and float(r["phi_exact_residual_at_X"]) < 1e-67, n
    c20 = _rows_B()[-1]["contraction"]
    assert abs(float(c20["q"]) - 0.4081) < 1e-4 and abs(float(c20["radius"]) - 0.01279) < 1e-5


def test_first_order_configuration_and_parameters():
    rows = _rows_B()
    for i, lim in enumerate((Fr(-2, 9), Fr(-2, 9), Fr(4, 9), Fr(1, 4))):
        mono, last = _approach([r["dX_times_L"][i] for r in rows], lim)
        assert mono and last < 0.03, i
    for key in ("A_over_nL", "D_minus_n_L_over_n"):
        gaps = [abs(float(r["params"][key]) - float(r["first_order"][key])) for r in rows]
        assert gaps == sorted(gaps, reverse=True) and gaps[-1] < 0.002, key
    for key, lim in (("B_minus_2n_L_over_n", 5 / 3), ("C_minus_2n_L_over_n", -11 / 3)):
        mono, last = _approach([r["params"][key] for r in rows], lim)
        assert mono and last < 0.35, key
    # planted: a limit of -3 for (C - 2n) L/n is passed and then left behind
    mono, _ = _approach([r["params"]["C_minus_2n_L_over_n"] for r in rows], -3)
    assert not mono


@pytest.fixture(scope="module")
def live_400():
    n = 400
    I, _ = p0.moments_trapezoid(n - 1, n + h.J_TOP, DPS)
    with mp.workdps(DPS + p0.GUARD):
        lr = h.lr_route_A(I, n, DPS)
        r, sol = h.row(n, lr, p0.script_L(n))
        return {"n": n, "lr": lr, "row": r, "sol": sol}


def test_live_reformulation_vanishes_and_sees_a_planted_target(live_400):
    with mp.workdps(DPS + p0.GUARD):
        n, sol = mpf(400), live_400["sol"]
        tau = sol["tau"]
        X = h.scaled_config(n, tau[0], sol["A"], sol["B"], sol["C"], sol["D"])
        assert max(abs(v) for v in h.phi_exact(X, n, tau)) < mpf(10) ** -55
        bad = list(tau)
        bad[3] *= 1 + mpf(10) ** -12
        assert max(abs(v) for v in h.phi_exact(X, n, bad)) > mpf(10) ** -14
    rec = {r["n"]: r for r in REC["subgrid_route_A"]}[400]
    for a, b in zip(live_400["row"]["tau"], rec["tau"]):
        assert abs(mpf(a) / mpf(b) - 1) < mpf(10) ** -13


# ---------------------------------------------------------------------------
# H3 and Lemma S
# ---------------------------------------------------------------------------


def test_G0_identity_and_derivative_asymptotics():
    rows = REC["G0"]
    assert all(float(r["G0_prime_identity_defect"]) < 1e-55 for r in rows)
    real = [r for r in rows if r["angle"] == "0"]
    for k in range(2, 7):
        mono, last = _approach([r["ratio_minus_1_times_L"][str(k)] for r in real], HARM[k - 2] - 1)
        assert mono and last < 0.03, k
    r6 = [float(r["ratio_to_leading"]["6"]) for r in real]
    assert r6 == sorted(r6, reverse=True) and abs(r6[0] - 1.1268) < 1e-4 and abs(r6[-1] - 1.00972) < 1e-5
    # complex rays: the modulus of the ratio agrees with the real one
    by = {(r["N_abs"], r["angle"]): r for r in rows}
    for N, tol in (("1e3", 2e-3), ("1e20", 5e-6), ("1e50", 3e-7)):
        for ang in ("0.25", "0.5"):
            for k in range(2, 7):
                a = float(by[(N, ang)]["ratio_to_leading"][str(k)])
                b = float(by[(N, "0")]["ratio_to_leading"][str(k)])
                assert abs(a / b - 1) < tol, (N, ang, k)


def test_live_G0_sixth_derivative_and_a_planted_constant():
    with mp.workdps(60):
        N = mpf(10) ** 20
        der, L = h.G0_derivatives(N)
        ratio = der[6] / (24 / (N ** 5 * L))
        assert abs(ratio - mpf("1.0249009")) < 1e-6
        planted = der[6] / (12 / (N ** 5 * L))  # (29') with half the constant
        assert abs(planted - 1) > mpf("0.9")


def test_h_on_a_complex_circle_record():
    for r, sup in zip(REC["h_circle"], (1.5219971, 1.5444705)):
        assert float(r["trapezoid_coarse_fine"]) < 1e-40 and float(r["center_value_vs_mean_of_circle"]) < 1e-40
        assert all(float(v) < 1e-16 for v in r["cauchy_vs_route_B_rel"].values()), r["n"]
        assert abs(float(r["sup_h6_inner_circle_over_leading"]) - sup) < 1e-6
        assert float(r["max_R_variation_on_circle_times_n"]) < 0.04
        lead = {k: float(v) for k, v in r["h_k_over_leading_route_B"].items()}
        assert all(0.4 < v < 1.2 for v in lead.values())
    assert REC["h_circle"][0]["unwrap_moves"] == 0 and REC["h_circle"][1]["unwrap_moves"] > 0


def test_live_h_circle_and_a_dropped_branch_correction():
    """Live at n = 400 (32 points); at n = 3200 the same computation without the
    branch correction must disagree with route B, which it does at k = 2 and 6."""
    good = h.h_circle(400, m=32)
    assert all(float(v) < 1e-16 for v in good["cauchy_vs_route_B_rel"].values())
    assert abs(float(good["sup_h6_inner_circle_over_leading"]) - 1.5219971) < 1e-6
    bad = h.h_circle(3200, m=32, unwrap=False)
    assert max(float(v) for v in bad["cauchy_vs_route_B_rel"].values()) > 0.1


def test_psi5_bound_and_a_planted_constant():
    rec = REC["psi5_defect_samples"]
    assert all(float(v) <= 1 for v in rec.values()) and abs(float(rec["1"]) - 0.81734306) < 1e-7
    with mp.workdps(30):
        for y in (mpf(1), mpf(100), mp.mpc(10, 30), mp.mpc(1000, 500)):
            assert h.psi5_defect(y) <= 1
        # planted: 50 in place of 120 fails on the real axis
        assert h.psi5_defect(mpf(100)) * 120 / 50 > 1


def test_psi5_sum_against_the_gap_integral(live_400):
    rec = REC["psi5_sum_vs_gap_integral_n3200"]
    assert rec["within_bound"] is True and float(rec["abs_diff_n6"]) < 30 < 599 < float(rec["bound_n6"])
    sol = live_400["sol"]
    with mp.workdps(DPS):
        live = h.psi5_sum_vs_gap_integral(400, sol["A"], sol["B"], sol["C"], sol["D"])
        assert live["within_bound"] is True
        # planted: the b-gap with the wrong sign is far outside the bound
        n = mpf(400)
        b = n + mpf(1) / 2
        A, B, C, D = sol["A"], sol["B"], sol["C"], sol["D"]
        exact = (mp.polygamma(5, B) + mp.polygamma(5, D) - mp.polygamma(5, A)
                 - mp.polygamma(5, C) - mp.polygamma(5, b))
        wrong = -24 / n ** 5 * (n ** 5 / A ** 5 + n ** 5 / C ** 5 - n ** 5 / B ** 5
                               - (n / b) ** 5 - n ** 5 / D ** 5)
        assert abs(exact - wrong) > 600 / min(A, B, C, D, b) ** 6


# ---------------------------------------------------------------------------
# the record
# ---------------------------------------------------------------------------


def test_record_exact_constants_match_recomputation():
    ex = REC["exact"]
    assert [[Fr(v) for v in r] for r in ex["J"]] == h.J_exact()
    assert [[Fr(v) for v in r] for r in ex["J_inv"]] == h.J_inv_exact()
    assert Fr(ex["kappa_bar"]) == h.kappa_bar() and Fr(ex["nu_w"]) == h.nu_w()
    assert [Fr(v) for v in ex["weights"]] == list(h.WEIGHTS) and Fr(ex["r_box"]) == h.R_BOX
    for e, v in ex["sigma_bar_at_eps"].items():
        assert Fr(v) == h.sigma_bar(Fr(e)), e
    assert ex["box_admissible_at_eps"] == {"1/8": True, "1/4": True, "1/2": True}


def test_route_A_record():
    v50, v30 = REC["validation_vs_li"]
    assert float(v50["max_abs_dlog_gamma"]) < 1e-45 and float(v30["max_abs_dlog_gamma"]) < 1e-25
    a = REC["route_A"]
    assert a["k_range"] == [49, 3206] and a["moments_computed"] == 3158
    assert float(a["max_coarse_fine_deviation"]) < 1e-60
    assert [r["n"] for r in REC["subgrid_route_A"]] == list(p0.SUBGRID)
    assert [r["n"] for r in _rows_B()] == list(h.LARGE_NS)
