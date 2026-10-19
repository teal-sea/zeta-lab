"""Tests for the phase 1 review of hunt #135 (REVIEW_PHASE1.md).

Each test checks one step of RESULTS.md sections 11 and 12 with code written for
the review (`wedge_review.py`), never with `probe.py` or `probe_phase1.py`. Every
cross-check here has a planted fault next to it that turns it red. Measured
throughout; nothing here bears on RH.
"""

from __future__ import annotations

import random
import sys
from fractions import Fraction
from pathlib import Path

import pytest
from mpmath import mp, mpf

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
for p in (str(_HERE), str(_ROOT)):
    if p not in sys.path:
        sys.path.insert(0, p)

import wedge_review as W  # noqa: E402


@pytest.fixture(autouse=True)
def _precision():
    with mp.workdps(60):
        yield


# ---------------------------------------------------------------------------
# The independent target route
# ---------------------------------------------------------------------------


def _ratio_gap(lg, ref, n0):
    return max(abs((lg[j + 1] - lg[j]) - mp.log(ref[n0 + j + 1] / ref[n0 + j])) for j in range(len(lg) - 1))


def test_kernel_route_matches_zeta_li_and_a_planted_error_is_seen():
    """phi(u) u^(2x) panels against zeta.li's theta-moment table, gamma(20..31)."""
    from zeta.li import xi_taylor_coefficients

    ref = xi_taylor_coefficients(40, dps=50)
    lg, tail = W.log_gamma_window(20, 12, dps=60)
    assert tail < mpf(10) ** -100
    assert _ratio_gap(lg, ref, 20) < mpf(10) ** -45
    planted = list(lg)
    planted[5] += mpf(10) ** -30
    assert _ratio_gap(planted, ref, 20) > mpf(10) ** -31


def test_solver_recovers_a_planted_two_factor_model_and_its_sixth_defect():
    n = 1000
    true = {"A": mpf(30000), "B": mpf("2100.5"), "C": mpf("1950.25"), "D": mpf("1010.75")}
    for delta in (mpf("1e-17"), mpf("-1e-17")):
        lq = [W.log_qq(k, true["A"], true["B"]) + W.log_qq(k, true["C"], true["D"]) for k in range(5)]
        lq[4] += delta
        guess = {s: v * (1 + mpf("0.01") * (i + 1)) for i, (s, v) in enumerate(true.items())}
        p, res = W.newton_factors(lq, guess, "ABCD", n=n)
        assert res < mpf(10) ** -50
        assert max(abs(p[s] / true[s] - 1) for s in true) < mpf(10) ** -40
        assert abs(W.defect(lq, p, 4) + delta) < mpf(10) ** -40


@pytest.mark.parametrize("n, theta, es6, ef5", [
    (200, "0.840604630", "-0.614", "-1.878"),
    (3200, "0.895770429", "-1.112", "-4.207"),
])
def test_phase1_numbers_reproduce_on_the_independent_route(n, theta, es6, ef5):
    """RESULTS 11.3 table: D/B_J at the Pade point, n^5 L E_S(6); section 4: n^4 L E_F(5)."""
    lg, _ = W.log_gamma_window(n, 8, dps=60)
    lq = W.log_q(lg)
    L = W.script_L(n)
    AJ, BJ = W.jacobi_fit(lq)
    p, res = W.solve_pade(n, lq)
    ph, resh = W.solve_holland(n, lq, BJ / 2)
    assert res < mpf(10) ** -55 and resh < mpf(10) ** -55
    assert abs(p["D"] / BJ - mpf(theta)) < mpf("5e-10")
    assert abs(n ** 5 * L * W.defect(lq, p, 4) - mpf(es6)) < mpf("5e-4")
    assert abs(n ** 4 * L * W.defect(lq, ph, 3) - mpf(ef5)) < mpf("5e-4")
    A, B, C, D = p["A"], p["B"], p["C"], p["D"]
    assert A > B > 0 and C > D > 0 and n / A < n / B < n / C < n / D < 1


# ---------------------------------------------------------------------------
# 11.1 to 11.3: the leading-order reduction and the Pade point
# ---------------------------------------------------------------------------


def test_h_derivative_leading_constants_through_k6():
    """11.1 uses h^(k) ~ (-1)^k (k-2)! (2/L)/x^(k-1) for k = 5, 6, which Holland
    does not state ((29) is an O-bound). Measured from Delta^k log M_x."""
    for n, band in ((3200, 0.12), (10 ** 6, 0.10)):
        lm, _ = W.log_moments([n + j for j in range(7)], dps=70)
        for k in range(2, 7):
            dk = mp.fsum((-1) ** (k - i) * mp.binomial(k, i) * lm[i] for i in range(k + 1))
            x = n + mpf(k) / 2
            pred = (-1) ** k * mp.factorial(k - 2) * (2 / W.script_L(x)) / x ** (k - 1)
            assert abs(dk / pred - 1) < 0.15, (n, k)
            if k >= 5:
                assert abs(dk / pred - 1) < band


def test_holland_constants_and_the_first_order_family():
    eps = mpf("1e-8")
    lag = W.betas(eps, [(0, 1 - eps)], 3)
    assert abs(lag[0]) < mpf(10) ** -50 and abs(lag[1] / eps + 1) < 1e-7
    for om in (Fraction(2), Fraction(3, 2), Fraction(5)):
        g, b, a, b4 = W.first_order_family(om)
        assert g == Fraction(1, 6) / (om * (om - 1))
        assert b == Fraction(1, 2) + Fraction(1, 6) / (om - 1)
        assert a == (3 * om - 1) / (6 * om)
        assert b4 == (2 * om - 1) / 3
    assert W.first_order_family(Fraction(2))[:3] == (Fraction(1, 12), Fraction(2, 3), Fraction(5, 12))


@pytest.mark.parametrize("eps", ["0.9", "0.342", "0.1", "1e-4"])
def test_pade22_interlaces_matches_and_is_reflection_symmetric(eps):
    eps = mpf(eps)
    a1, b1, a2, b2 = [mp.re(v) for v in W.pade22(eps)]
    assert 0 < a1 < b1 < a2 < b2 < 1
    bs = W.betas(eps, [(a1, b1), (a2, b2)], 5)
    assert max(abs(v) for v in bs[:4]) < mpf(10) ** -45
    assert bs[4] < 0
    # the reflection t -> 1 - t maps the configuration to a solution of the same
    # moment problem; Pade uniqueness then forces a1 + b2 = b1 + a2 = 1
    refl = [(1 - b2, 1 - a2), (1 - b1, 1 - a1)]
    assert max(abs(v) for v in W.betas(eps, refl, 4)) < mpf(10) ** -45
    assert abs(a1 + b2 - 1) < mpf(10) ** -40 and abs(b1 + a2 - 1) < mpf(10) ** -40


def test_lobatto_limit_and_simpson_residual():
    eps = mpf("1e-10")
    a1, b1, a2, b2 = [mp.re(v) for v in W.pade22(eps)]
    assert abs(a1 / eps - mpf(1) / 6) < 1e-8 and abs((a2 - b1) / eps - mpf(2) / 3) < 1e-8
    assert abs(W.betas(eps, [(a1, b1), (a2, b2)], 5)[4] / eps + mpf(1) / 24) < 1e-8


def test_limiting_jacobian_is_nonsingular_in_two_coordinate_systems():
    assert W.lobatto_jacobian_det() == 1
    assert W.lobatto_jacobian_det(Fraction(1, 3), Fraction(2, 3)) != 0


# ---------------------------------------------------------------------------
# 11.5: the restricted-class obstruction and the mesoscopic configurations
# ---------------------------------------------------------------------------


def test_first_order_obstruction_and_its_negative_control():
    omegas = [k / 40 for k in range(1, 401)]
    bgrid = [k / 200 for k in range(-400, 401)]
    assert W.obstruction_lp(omegas, bgrid) > 1e-3
    # drop the sign constraint and the system is solvable: the hole of 11.5
    b, om, g = Fraction(1, 6), Fraction(1, 2), Fraction(-2, 3)
    assert all(g * om ** k == b - Fraction(1, k + 1) for k in (1, 2, 3))


def test_cauchy_schwarz_bound_is_the_binding_step():
    """m1 > 0 needs b > 1/2; m2^2 <= m1 m3 needs b <= 1/6, exactly."""
    def cs_gap(b):
        return (b - Fraction(1, 2)) * (b - Fraction(1, 4)) - (b - Fraction(1, 3)) ** 2
    assert cs_gap(Fraction(1, 6)) == 0
    assert cs_gap(Fraction(1, 6) - Fraction(1, 1000)) > 0 > cs_gap(Fraction(1, 6) + Fraction(1, 1000))


def test_mesoscopic_three_factor_configuration_exists_at_leading_order():
    """eps = 0.01: auxiliary relative gaps 0.110 and 0.115, both below the 0.145
    RESULTS reports at eps = 0.03, with every factor positive-root."""
    sol, ok = W.three_factor_config(0.01, 0.110, 0.115, [0.0022, 0.78, 0.97, 0.94])
    assert ok
    a1, b1, b2, b3 = sol
    a2, a3 = b2 * (1 - 0.110), b3 * (1 - 0.115)
    assert 0 < a1 < b1 and 0 < a2 < b2 and 0 < a3 < b3 and max(b2, b3) <= 3


# ---------------------------------------------------------------------------
# 12.1 to 12.3: Proposition 2.2_m and Lemmas A, B, C
# ---------------------------------------------------------------------------


def test_derivative_ratios_agree_with_direct_differentiation():
    rs = [mpf(v) for v in (1, 2.5, 4, 7, 7.5, 11)]
    y = mpf("5.3")
    T = W.derivative_ratios(rs, y)
    dk = W.poly_from_roots(rs)
    pv = mp.polyval(list(reversed(dk)), y)
    for k in range(len(rs) + 1):
        direct = abs(y ** k * mp.polyval(list(reversed(dk)), y) / pv)
        assert abs(T[k] - direct) <= mpf(10) ** -40 * max(1, direct)
        dk = [i * dk[i] for i in range(1, len(dk))]
    # planted: a ratio from the wrong point disagrees
    assert abs(W.derivative_ratios(rs, y + mpf("0.01"))[2] - T[2]) > mpf(10) ** -6


@pytest.mark.parametrize("name", ["equal", "geometric", "collision", "clusters", "random"])
def test_lemma_a_holds_on_adversarial_root_sets(name):
    random.seed(5)
    sets = {
        "equal": [mpf(k) for k in range(1, 31)],
        "geometric": [mpf("1.05") ** k for k in range(30)],
        "collision": [mpf(k) for k in range(1, 21)] + [mpf("10.000001")],
        "clusters": [mpf(k) / 100 for k in range(10)] + [100 + mpf(k) / 100 for k in range(10)],
        "random": sorted(mpf(random.uniform(0.1, 50)) for _ in range(25)),
    }
    r = W.lemma_a_check(sets[name])
    assert r["r_needed"] <= r["lemma_a"] <= r["explicit"]
    assert r["min_slack"] > 0


@pytest.mark.parametrize("d", [2, 3, 5, 8, 12])
def test_lemma_b_at_the_edge_of_its_hypotheses(d):
    """A = 8B, B = 256 d, exact rational coefficients."""
    B = Fraction(256 * d)
    rts, im = W.real_roots_mp(W.jacobi_factor_coeffs(d, 8 * B, B, 1 / (8 * B)), dps=60)
    Bm = mpf(256 * d)
    assert im < mpf(10) ** -40
    assert all(Bm / 2 <= r <= 3 * Bm / 2 for r in rts)
    assert all(abs(r - Bm) <= 8 * mp.sqrt(Bm * d) for r in rts)  # Holland (79)
    gap = min(b - a for a, b in zip(rts, rts[1:]))
    assert gap >= W.lemma_b_gap(d, Bm) * mpf("1.5")


def test_lemma_b_hypothesis_a_ge_8b_is_load_bearing():
    """Planted: A = B + d, B = 32 d. The Sturm bound then fails by a factor of 6 or more."""
    d = 4
    B = Fraction(32 * d)
    rts, _ = W.real_roots_mp(W.jacobi_factor_coeffs(d, B + d, B, 1 / (B + d)), dps=60)
    gap = min(b - a for a, b in zip(rts, rts[1:]))
    assert gap < W.lemma_b_gap(d, mpf(32 * d)) / 6


def test_lemma_c_lmesh_never_decreases_on_random_cases():
    random.seed(9)
    worst = mpf("inf")
    for _ in range(60):
        d = random.randint(2, 6)
        pr = sorted({Fraction(random.randint(1, 300), random.randint(1, 30)) for _ in range(d)})
        qr = sorted({Fraction(random.randint(1, 300), random.randint(1, 30)) for _ in range(d)})
        if len(pr) < d or len(qr) < d:
            continue

        def asc(roots):
            c = [Fraction(1)]
            for r in roots:
                new = [Fraction(0)] * (len(c) + 1)
                for i, ci in enumerate(c):
                    new[i] += -r * ci
                    new[i + 1] += ci
                c = new
            return [x / c[0] for x in c]

        rts, im = W.real_roots_mp(W.holland_box(asc(pr), asc(qr)), dps=60)
        assert im < mpf(10) ** -40 and min(rts) > 0
        lm_p = W.lmesh([mpf(x.numerator) / x.denominator for x in pr])
        lm_q = W.lmesh([mpf(x.numerator) / x.denominator for x in qr])
        worst = min(worst, W.lmesh(rts) / max(lm_p, lm_q))
    assert worst >= 1


def test_proposition_22_six_point_on_a_planted_multiplier():
    """c(z) = 1 + kappa z(z-1)...(z-5), kappa set so sup over Omega_r |c - 1| = 31,
    above Holland's eps < 16 and inside 2.2_6's eps < 32."""
    from zeta.li import is_hyperbolic

    random.seed(11)
    d = 10
    roots = sorted(mpf(random.uniform(1, 30)) for _ in range(d))
    r = W.lemma_a_check(roots)["r_needed"]

    def base(z):
        return mp.fprod(z - j for j in range(6))

    R, sup = 2 * r, mpf(0)
    for i in range(800):
        t = mpf(i) / 800
        for z in (d * t + 1j * R, d * t - 1j * R, d + R * mp.expj(mp.pi * (t - mpf(1) / 2)),
                  R * mp.expj(mp.pi * (t + mpf(1) / 2))):
            sup = max(sup, abs(base(z)))
    kappa = 31 / sup
    worst, P = W.prop22m_margin(roots, lambda j: 1 + kappa * base(j), 6)
    assert worst < mpf(31) / 32
    hyp = is_hyperbolic([mp.re(x) for x in P], dps=60, method="sturm")
    assert hyp["n_real_exact"] == d


def test_chain_bounds_at_the_pade_model_n3200_d6():
    """12.3 combined: gap >= (1 - eta) g_1/3 and r_needed <= Lemma A <= explicit,
    at the route's own Pade parameters; RESULTS 12.6 columns reproduce."""
    n, d = 3200, 6
    lg, _ = W.log_gamma_window(n, 8, dps=60)
    p, _ = W.solve_pade(n, W.log_q(lg))
    A, B, C, D = p["A"], p["B"], p["C"], p["D"]
    with mp.workdps(120):
        p1 = W.jacobi_factor_coeffs(d, A, B, 1 / A)
        p2 = W.jacobi_factor_coeffs(d, C, D, D / C)
        r1, _ = W.real_roots_mp(p1, dps=120)
        rf, im = W.real_roots_mp(W.holland_box(p1, p2), dps=120)
        assert im < mpf(10) ** -60
        chk = W.lemma_a_check(rf)
        s = mp.sqrt(B * d)
        eta = 8 * mp.sqrt(d / D)
        assert chk["gap"] >= (1 - eta) * W.lemma_b_gap(d, B) / 3
        assert W.lmesh(rf) >= W.lmesh(r1)
        assert mp.nstr(chk["gap"] * mp.sqrt(d / B), 4) == "3.905"
        assert mp.nstr(chk["r_needed"] / s, 3) == "0.837"
        assert mp.nstr(chk["lemma_a"] / s, 3) == "1.55"
