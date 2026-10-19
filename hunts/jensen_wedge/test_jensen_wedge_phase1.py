"""Pins for hunt #135 phase 1 (`hunts/jensen_wedge/probe_phase1.py`).

Instrument tests first: each solver recovers a planted coefficient sequence, the
leading-order model reproduces the statements RESULTS.md derives from it, and the
derivative-ratio bound (Lemma A of RESULTS.md section 12) is checked on polynomials
whose roots are known, with a planted near-collision that it must see. Then a live
recomputation at n = 400 against `results_phase1.json` and phase 0's crossing, so a
stale JSON cannot pass on its own. Then the record. Nothing here assigns
evidentiary status.

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/jensen_wedge
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import pytest
from mpmath import mp, mpf

from hunts.jensen_wedge import probe as p0
from hunts.jensen_wedge import probe_phase1 as p1

HERE = Path(__file__).resolve().parent
RESULTS = json.loads((HERE / "results_phase1.json").read_text())
PHASE0 = json.loads((HERE / "results.json").read_text())
DPS = 60


def _log_R_jacobi(U, V, S, jmax=7):
    out = []
    for j in range(jmax + 1):
        v = j * mp.log(S) - mp.fsum(mp.log(V + i) for i in range(j))
        if U is not None:
            v += mp.fsum(mp.log1p(i / U) for i in range(j))
        out.append(v)
    return out


def _product(*factors, S=mpf("2.5"), jmax=7):
    """log R_j of S^j prod_i (U_i)_j/(U_i^j (V_i)_j) with every V_i^j scale folded
    into S (scales never touch the quotients q_k)."""
    lr = [mpf(0)] * (jmax + 1)
    for U, V in factors:
        for j, v in enumerate(_log_R_jacobi(U, V, mpf(1), jmax)):
            lr[j] += v
    return [v + j * mp.log(S) for j, v in enumerate(lr)]


# ---------------------------------------------------------------------------
# the solvers, on sequences whose answer is known
# ---------------------------------------------------------------------------


def test_log_qq_w_agrees_with_log_qq_and_is_laguerre_at_w_zero():
    with mp.workdps(DPS):
        n, U, V = 3200, mpf(41000), mpf(3500)
        for k in range(5):
            assert abs(p1.log_qq_w(k, n / U, V, n) - p0.log_qq(k, U, V)) < mpf(10) ** -55
            assert abs(p1.log_qq_w(k, 0, V, n) - p0.log_qq(k, None, V)) < mpf(10) ** -55


def test_pade_solve_recovers_a_planted_two_factor_sequence():
    with mp.workdps(DPS + p0.GUARD):
        n = 3200
        A, B, C, D = mpf(80000), mpf(7900), mpf(5100), mpf(3350)
        lq = p0.log_q_from_log_R(_product((A, B), (C, D)))
        sol = p1.pade_solve(lq, n, (n / A * mpf("1.2"), mp.log(B * mpf("0.97")),
                                     mp.log(C * mpf("1.02")), mp.log(D * mpf("0.99"))))
        for got, want in ((sol["A"], A), (sol["B"], B), (sol["C"], C), (sol["D"], D)):
            assert abs(got / want - 1) < mpf(10) ** -40
        assert abs(sol["E_S6"]) < mpf(10) ** -50


def test_pade_solve_reads_the_sign_of_a_planted_third_factor():
    """A third Jacobi factor shifts R_6 off the two-factor fit; its sign follows the
    planted factor's orientation, so the E_S6 detector reads both signs."""
    with mp.workdps(DPS + p0.GUARD):
        n = 3200
        base = ((mpf(80000), mpf(7900)), (mpf(5100), mpf(3350)))
        signs = []
        for third in ((mpf(4400), mpf(4300)), (mpf(4300), mpf(4400))):
            lq = p0.log_q_from_log_R(_product(*base, third))
            sol = p1.pade_solve(lq, n, (n / mpf(80000), mp.log(mpf(7900)),
                                        mp.log(mpf(5100)), mp.log(mpf(3350))))
            signs.append(sol["E_S6"] > 0)
        assert signs[0] != signs[1]


def test_family_solve_recovers_a_planted_sequence_through_A_infinity():
    """The theta-family solver in (w_A, log B, log(C - D)) recovers a planted model,
    including one with A = infinity (a Laguerre first factor), where phase 0's
    solver in log A could not go."""
    with mp.workdps(DPS + p0.GUARD):
        n = 3200
        for A in (mpf(60000), None):
            B, C, D = mpf(5000), mpf(3600), mpf(3300)
            lq = p0.log_q_from_log_R(_product((A, B), (C, D)))
            BJ = p0.jacobi(lq)["B_J"]
            f = p1.family_solve(lq, n, BJ, D / BJ, (mpf("0.01"), mp.log(B * mpf("1.05")),
                                                    mp.log((C - D) * mpf("0.9"))))
            w_true = 0 if A is None else n / A
            assert abs(f["w_A"] - w_true) < mpf(10) ** -40
            assert abs(f["B"] / B - 1) < mpf(10) ** -40
            assert abs(f["E_F5"]) < mpf(10) ** -50


# ---------------------------------------------------------------------------
# the leading-order model (RESULTS.md section 11)
# ---------------------------------------------------------------------------


def test_the_two_factor_pade_point_matches_four_moments_and_not_the_fifth():
    with mp.workdps(40):
        for e in ("0.342", "0.01"):
            eps = mpf(e)
            a, b = p1.lo_pade22(eps)
            for s in range(1, 5):
                assert abs(sum(x ** s for x in b) - sum(x ** s for x in a) - (1 - eps)) < mpf(10) ** -30
            br5 = sum(x ** 5 for x in b) - sum(x ** 5 for x in a) - (1 - eps)
            assert br5 < 0  # the R_6 defect sign, section 11.4
            # interlacing 0 < a1 < b1 < a2 < b2 < 1: both factors positive-root
            assert 0 < a[0] < b[0] < a[1] < b[1] < 1


def test_the_pade_point_tends_to_the_lobatto_simpson_configuration():
    """Gaps eps/6 at 0, 2 eps/3 at 1/2, eps/6 at 1; theta_star -> 1 - 2/(3L)."""
    with mp.workdps(40):
        eps = mpf("0.001")
        a, b = p1.lo_pade22(eps)
        assert abs(a[0] / (eps / 6) - 1) < 0.01
        assert abs((a[1] - b[0]) / (2 * eps / 3) - 1) < 0.01
        assert abs((1 - b[1]) / (eps / 6) - 1) < 0.01
        theta = (1 - eps / 2) / b[1]
        assert abs((1 - theta) * 2 / eps - mpf(2) / 3) < 0.001


def test_lobatto_jacobian_is_nonsingular():
    """The scaled limiting matching system (gap weights at 0, x, 1 and the node x,
    moments 0..3) has Jacobian determinant -1/24 at Simpson's rule, exactly."""
    x, w1 = Fraction(1, 2), Fraction(2, 3)
    cols = [[1, 0, 0, 0], [1, x, x ** 2, x ** 3], [1, 1, 1, 1],
            [0, w1, 2 * w1 * x, 3 * w1 * x ** 2]]
    M = [[cols[c][r] for c in range(4)] for r in range(4)]

    def det(m):
        if len(m) == 1:
            return m[0][0]
        return sum((-1) ** c * m[0][c] * det([row[:c] + row[c + 1:] for row in m[1:]])
                   for c in range(len(m)))

    assert det(M) == Fraction(-1, 24)


def test_first_order_near_identity_matching_forces_a_hole():
    """One main factor plus one auxiliary factor, all deviations O(eps): the
    first-order equations sum g w^k - b = -1/(k+1), k = 1, 2, 3, have the single
    solution b = 1/6, w = 1/2, g = -2/3 < 0, i.e. C < D in that pairing."""
    b = Fraction(1, 6)
    w = (b - Fraction(1, 3)) / (b - Fraction(1, 2))
    g = (b - Fraction(1, 2)) / w
    assert (w, g) == (Fraction(1, 2), Fraction(-2, 3))
    for k in (1, 2, 3):
        assert g * w ** k - b == Fraction(-1, k + 1)
    # and positive weights are impossible: m1 > 0 needs b > 1/2, Cauchy-Schwarz b <= 1/6
    for bb in (Fraction(1, 2), Fraction(3, 5), Fraction(2)):
        m1, m2, m3 = bb - Fraction(1, 2), bb - Fraction(1, 3), bb - Fraction(1, 4)
        assert m1 * m3 < m2 * m2


def test_first_order_family_reproduces_hollands_limits():
    """D = theta B_J at leading order: theta = 1/2 gives Holland's (6/5, 1/3, 1/24)
    and the R_5 coefficient -12/(n^4 L) (RESULTS.md section 11.2)."""
    with mp.workdps(40):
        eps = mpf("1e-6")
        f = p1.lo_family(eps, "0.5")
        L = 2 / eps
        assert abs((1 / f["w_A"]) / ((mpf(6) / 5) * L) - 1) < 1e-4          # A/(nL) -> 6/5
        assert abs(((1 / f["b1"]) - 1 / (1 - eps / 2)) * L - mpf(1) / 3) < 1e-4
        assert abs((1 / f["w_C"] - 1 / f["w_D"]) * L - mpf(1) / 24) < 1e-4
        assert abs(24 * f["E5"] * L - (-12)) < 1e-3


def test_first_order_family_formulas_hold_at_every_omega():
    """gamma = eps/(6 w (w-1)), beta = eps/2 + eps/(6 (w-1)), alpha = eps (3w-1)/(6w),
    beta_4 = eps (2w-1)/3 (RESULTS.md section 11.2), to relative O(eps)."""
    with mp.workdps(40):
        eps = mpf("1e-7")
        for om in (mpf(2), mpf("1.5"), mpf(4)):
            f = p1.lo_family(eps, (1 - eps / 2) / om)
            assert abs((f["w_D"] - f["w_C"]) / (eps / (6 * om * (om - 1))) - 1) < 1e-5
            assert abs((1 - f["b1"]) / (eps / 2 + eps / (6 * (om - 1))) - 1) < 1e-5
            assert abs(f["w_A"] / (eps * (3 * om - 1) / (6 * om)) - 1) < 1e-5
            assert abs(-4 * f["E5"] / (eps * (2 * om - 1) / 3) - 1) < 1e-5


def test_leading_order_theta_inf_is_where_A_reaches_infinity():
    """Past theta_star the numerator node w_A crosses 0 (A = infinity) at
    theta_inf -> 1 - 1/(2L), and is negative beyond: the family leaves the class."""
    with mp.workdps(40):
        eps = mpf("0.001")
        t_inf = p1.lo_bisect(eps, lambda f: f["w_A"] > 0)
        assert abs((1 - t_inf) * 2 / eps - mpf(1) / 2) < 1e-3
        assert p1.lo_family(eps, t_inf - mpf(10) ** -6)["w_A"] > 0
        assert p1.lo_family(eps, t_inf + mpf(10) ** -6)["w_A"] < 0


# ---------------------------------------------------------------------------
# Lemma A and the root-gap route (RESULTS.md section 12)
# ---------------------------------------------------------------------------


def _poly_from_roots(roots):
    c = [mpf(1)]
    for r in roots:
        c = [-r * c[0]] + [c[i - 1] - r * c[i] for i in range(1, len(c))] + [c[-1]]
    return c


def test_lemma_A_bounds_every_derivative_ratio_at_every_critical_point():
    with mp.workdps(50):
        roots = [mpf(100) + 3 * k + (k % 3) for k in range(12)]
        c = _poly_from_roots(roots)
        crits = p1.critical_points(c, roots)
        st = p1.ratio_stats(roots, crits)
        assert st["r_needed"] <= st["r_lemma_A"]
        g = min(b - a for a, b in zip(roots[:-1], roots[1:]))
        assert st["r_lemma_A"] <= roots[-1] * (4 + 3 * mp.harmonic(12)) / g


def test_lemma_A_sees_a_planted_near_collision():
    """Squeeze two roots together: the needed r grows like 1/gap, and the bound
    follows it; a bound that ignored the gap would stay flat."""
    with mp.workdps(50):
        out = []
        for gap in (mpf(1), mpf("0.01")):
            roots = [mpf(100) + 3 * k for k in range(10)]
            roots[5] = roots[4] + gap
            crits = p1.critical_points(_poly_from_roots(roots), roots)
            out.append(p1.ratio_stats(roots, crits))
        assert out[1]["r_needed"] > 20 * out[0]["r_needed"]
        assert out[1]["r_lemma_A"] >= out[1]["r_needed"]


def test_real_roots_finds_every_root_of_a_known_polynomial():
    with mp.workdps(50):
        roots = [mpf(10) + k + mpf(k * k) / 50 for k in range(9)]
        got = p1.real_roots(_poly_from_roots(roots), mpf(5), mpf(25), mpf("0.05"))
        assert len(got) == 9
        assert max(abs(a - b) for a, b in zip(got, roots)) < mpf(10) ** -30


# ---------------------------------------------------------------------------
# live recomputation at n = 400 (route A), against the record and phase 0
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def live_400():
    n = 400
    I, dev = p0.moments_trapezoid(n - 1, n + p1.J6, DPS)
    with mp.workdps(DPS + p0.GUARD):
        ell = {m: p0.log_gamma_from_moments(I, m, DPS) for m in range(n, n + p1.J6 + 1)}
        lr = [mpf(0)] + [ell[n + j] - ell[n] for j in range(1, p1.J6 + 1)]
        lq = p0.log_q_from_log_R(lr)
        Ln = p0.script_L(n)
        sol = p1.pade_solve(lq, n, p1.pade_guess(n, Ln))
        return {"n": n, "dev": dev, "lr": lr, "lq": lq, "Ln": Ln, "sol": sol,
                "BJ": p0.jacobi(lq)["B_J"], "d0": p0.defects(lr, n, Ln)}


def test_the_pade_solve_lands_on_phase_0s_crossing(live_400):
    """Two different solvers, one bisecting theta from Holland's solution (phase 0)
    and one solving (A, B, C, D) directly from the leading-order Pade guess, find
    the same point."""
    theta = live_400["sol"]["D"] / live_400["BJ"]
    phase0 = {r["n"]: r for r in PHASE0["theta_sensitivity"]}[400]["crossing"]["theta"]
    assert abs(theta - mpf(phase0)) < mpf(10) ** -11


def test_live_pade_model_reproduces_the_record(live_400):
    sol = live_400["sol"]
    row = RESULTS["pade_dense_route_A"]["rows"]["400"]
    with mp.workdps(DPS):
        assert abs(sol["E_S6"] / mpf(row["E_S6"]) - 1) < mpf(10) ** -10
        assert sol["E_S6"] < 0
        assert sol["A"] > sol["B"] > 0 and sol["C"] > sol["D"] > 0
        assert sol["res"] < mpf(10) ** -60


def test_live_theta_map_reproduces_theta_star_and_theta_inf(live_400):
    d0 = live_400["d0"]
    with mp.workdps(DPS + p0.GUARD):
        half = p1.family_from_holland(live_400["lq"], 400, live_400["BJ"], d0["ff"])
        m = p1.family_map(live_400["lq"], 400, live_400["BJ"], half,
                          ("0.85", "0.86", "0.87", "0.88", "0.89", "0.9"))
    row = {r["n"]: r for r in RESULTS["theta_map_route_A"]}[400]
    assert abs(m["theta_star"] - mpf(row["theta_star"])) < mpf(10) ** -10
    assert abs(m["theta_inf"] - mpf(row["theta_inf"])) < mpf(10) ** -10


# ---------------------------------------------------------------------------
# the record
# ---------------------------------------------------------------------------


def test_route_A_table_and_its_check_route():
    a = RESULTS["route_A"]
    assert a["k_range"] == [49, 3296] and a["moments_computed"] == 3248
    assert float(a["max_coarse_fine_deviation"]) < 1e-65
    assert float(a["max_rel_dev_vs_check_route"]) < 1e-60
    v50, v30 = RESULTS["validation_vs_li"]
    assert float(v50["max_abs_dlog_gamma"]) < 1e-45 and float(v30["max_abs_dlog_gamma"]) < 1e-25


def test_theta_star_and_theta_inf_bracket_the_positive_window_at_every_n():
    rows = RESULTS["theta_map_route_A"]
    assert [r["n"] for r in rows] == list(p0.SUBGRID)
    for r in rows:
        ts, ti = float(r["theta_star"]), float(r["theta_inf"])
        assert 0.79 < ts < ti < 0.93, r["n"]
        assert r["failed"] == {}, r["n"]
        for th, g in r["grid"].items():
            t = float(th)
            if t < ts:
                assert float(g["E_F5"]) < 0 and g["A_positive"], (r["n"], th)
            elif t > ti:
                assert not g["A_positive"], (r["n"], th)
    stars = [float(r["theta_star"]) for r in rows]
    assert stars == sorted(stars)


def test_theta_star_matches_phase_0_at_its_four_rows():
    ours = {r["n"]: float(r["theta_star"]) for r in RESULTS["theta_map_route_A"]}
    for r in PHASE0["theta_sensitivity"]:
        assert abs(ours[r["n"]] - float(r["crossing"]["theta"])) < 1e-10


def test_the_R6_defect_of_the_pade_model_is_negative_at_every_n():
    d = RESULTS["pade_dense_route_A"]
    assert d["n_count"] == 3151
    assert (d["E_S6_negative"], d["E_S6_positive"], d["E_S6_sign_changes_at_n"]) == (3151, 0, [])
    assert d["all_positive_and_U_gt_V"] is True
    assert float(d["max_match_residual"]) < 1e-60


def test_route_B_agrees_with_route_A_on_the_R6_defect():
    for r in RESULTS["route_B_subgrid"]:
        assert r["signs_agree"] and r["B_resolves_sign"], r["n"]
        assert float(r["rel_dev_A_B"]) < 1e-8, r["n"]


def test_large_n_constants_approach_their_leading_order_values():
    """n^5 L E_S6 -> -2; (1 - theta_star) L -> 2/3; (1 - theta_inf) L -> 1/2; the
    gap total times L -> 2; n^4 L E_F5 at theta = 1/2 -> -12 (section 11)."""
    rows = RESULTS["large_n_route_B"]
    assert rows[-1]["n"] == "1e20"
    e6 = [float(r["n5L_E_S6"]) for r in rows]
    assert all(v < 0 for v in e6) and e6 == sorted(e6, reverse=True)
    assert -2 < e6[-1] < -1.8
    ts = [float(r["one_minus_theta_star_times_L"]) for r in rows]
    assert all(abs(v - 2 / 3) < 0.1 for v in ts) and abs(ts[-1] - 2 / 3) < 0.01
    ti = [float(r["one_minus_theta_inf_times_L"]) for r in rows]
    assert abs(ti[-1] - 0.5) < 0.02
    half = [float(r["family"]["0.5"]["n4L_E_F5"]) for r in rows]
    assert half == sorted(half, reverse=True) and -12 < half[-1] < -10


def test_pade_parameters_the_leading_order_model_predicts_approach_their_limits():
    """A/(nL) -> 3, (D - n) L/n -> 1/3, (B - C) L/n -> 16/3, gap total x L -> 2,
    rho_CD -> 1/2, each monotonically over n = 1e4..1e20 (section 11.3). B and C
    separately are not predicted and are not pinned to a limit."""
    rows = RESULTS["large_n_route_B"]
    cols = {
        "A": ([float(r["A_over_nL"]) for r in rows], 3.0),
        "D": ([float(r["D_minus_n_L_over_n"]) for r in rows], 1 / 3),
        "BC": ([float(r["B_minus_2n_L_over_n"]) - float(r["C_minus_2n_L_over_n"]) for r in rows],
               16 / 3),
        "gap": ([float(r["gap_total_times_L"]) for r in rows], 2.0),
        "rho": ([float(r["rho_CD"]) for r in rows], 0.5),
    }
    for key, (vals, limit) in cols.items():
        gaps = [abs(v - limit) for v in vals]
        assert gaps == sorted(gaps, reverse=True), key
        assert gaps[-1] < 0.2 * gaps[0] + 0.3, key
    for r in rows:
        assert r["all_positive_and_U_gt_V"] is True, r["n"]
        assert abs(float(r["B_minus_2n_L_over_n"])) < 4 and abs(float(r["C_minus_2n_L_over_n"])) < 4


def test_the_root_geometry_record():
    geo = RESULTS["root_geometry_n3200"]
    assert float(geo["high_precision_block"]["max_abs_dlog_gamma_vs_dps60_table"]) < 1e-65
    for name, through in (("holland_theta_half", 4), ("pade", 5)):
        for r in geo[name]["by_d"]:
            d = r["d"]
            assert r["model_real_roots"] == d and r["jensen_real_roots"] == d, (name, d)
            assert r["first_factor_real_roots"] == d, (name, d)
            assert r["lemma_A_bounds_r_needed"] and r["lmesh_transfer_holds"], (name, d)
            assert float(r["first_factor_min_gap_over_sturm_bound"]) > 1, (name, d)
            assert r["c_minus_1_vanishes_through_j"] == through, (name, d)
            assert r["count_discrepancy"] <= 1, (name, d)
            assert 0.5 < float(r["r_needed_over_sqrt_Bd"]) < 2.5, (name, d)
    # the sixth-order model's residual multiplier is smaller than Holland's at every d
    for rh, rp in zip(geo["holland_theta_half"]["by_d"], geo["pade"]["by_d"]):
        assert float(rp["max_abs_c_minus_1"]) < float(rh["max_abs_c_minus_1"])


def test_the_three_factor_scan_record():
    rows = RESULTS["leading_order"]["three_factor_scan"]
    assert [r["eps"] for r in rows] == list(p1.SCAN_EPS)
    for r in rows:
        assert r["admissible_found"] and r["moment_residual_s1_to_s4"] < 1e-9
    X = [r["X3"] for r in rows]
    assert X[-1] < 0.06 and X[1:] == sorted(X[1:], reverse=True)
