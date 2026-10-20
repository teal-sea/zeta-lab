"""Hunt #135 phase 2 (EFFECTIVE.md): the explicit constants, their checks, and the
planted faults those checks must catch.

Two kinds of plant. A weakened *claim* (a constant moved past its own recomputation)
must turn `effectivity_check` red: that is the MISSION's kill condition. A wrong
*formula* cannot be seen by a recomputation that uses the same formula, so the
measurements of `effective.py` section H (independent routes) must catch it, as far
as their slack allows.

Phase 3 (2026-10-19) adds the last section: `REVIEW_PHASE2.md` item P planted four
formula faults and three passed this whole suite, because a measurement with slack 785
cannot see a constant five times too small. Those steps are now checked against their
own derivation (a defining integral, a disk geometry, a Sturm bound on an actual
polynomial), and each of the reviewer's plants is replayed here as a source edit that
those checks must reject.

Run: .venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/test_effective.py
"""

from __future__ import annotations

import functools
import json
import math
import sys
import types
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
for p in (str(ROOT), str(HERE)):
    if p not in sys.path:
        sys.path.insert(0, p)

import effective as E  # noqa: E402
from flint import arb  # noqa: E402
from zeta import rigor  # noqa: E402


@functools.lru_cache(maxsize=None)
def _data_models(n):
    return E.measure_data_and_models(n)


@functools.lru_cache(maxsize=None)
def _polys():
    return E.measure_polynomials(10**12, ds=(10,))


# ---------------------------------------------------------------------------
# the backend and the exact pieces
# ---------------------------------------------------------------------------


def test_backend_is_arb():
    assert rigor.BACKEND == "python-flint", rigor.BACKEND_REASON


def test_first_order_coefficients_are_harmonic_numbers_minus_one():
    for k in range(2, 8):
        H = sum(Fraction(1, i) for i in range(1, k - 1))
        assert E.first_order_coefficient(k) == H - 1


def test_F2_at_m_zero_is_one_over_one_plus_e():
    with rigor._flint_prec(E.PREC):
        for e in ("0.01", "0.1", "0.3"):
            x = E.ab(Fraction(e))
            assert (E.F_plain(2, x, arb(0)) - 1 / (1 + x)).abs_upper() < arb(10) ** -60


def test_representation_matches_the_exact_gamma_table():
    """h(z) = const - (2z+1) log 4 + log I(2z): second differences against route A
    (the tree's moment table), n = 100."""
    import probe

    n, dps = 100, 30
    with mp.workdps(dps + 10):
        a = mp.mpf(9) / 4

        def alpha(v):
            return mp.fsum((k**4 - 3 / (2 * mp.pi) * k**2 * mp.exp(-v)) * mp.exp(-mp.pi * (k * k - 1) * mp.exp(v))
                           for k in range(1, 6))

        def I(s):
            v0 = mp.findroot(lambda v: s / v + a - mp.pi * mp.exp(v), mp.log(s / mp.pi) - 1)
            w = 1 / mp.sqrt(s / v0**2 + mp.pi * mp.exp(v0))
            pts = [mp.mpf(0)] + [v0 + c * w for c in (-40, -10, -3, 0, 3, 10, 40) if v0 + c * w > 0] + [v0 + 3]
            return mp.quad(lambda v: mp.exp(s * mp.log(v) + a * v - mp.pi * mp.exp(v)) * alpha(v), pts)

        mom = probe.moments(range(n - 3, n + 6), dps)[0]

        def logM(m):
            return probe.log_gamma_from_moments(mom, m, dps) - mp.loggamma(m + 1) + mp.loggamma(2 * m + 1)

        def h(m):
            return -(2 * m + 1) * mp.log(4) + mp.log(I(2 * m))

        d_table = logM(n + 2) - 2 * logM(n + 1) + logM(n)
        d_here = h(n + 2) - 2 * h(n + 1) + h(n)
        assert abs(d_here / d_table - 1) < mp.mpf(10) ** -25


# ---------------------------------------------------------------------------
# Lemma D: the derivative enclosures against route B, and a planted formula fault
# ---------------------------------------------------------------------------


def _route_b_H(n, k, v1):
    import probe

    dps = int(5 * math.log10(n)) + 50
    with mp.workdps(dps):
        g = probe.saddle_expansion(n, dps, order=7)
        hk = mp.factorial(k) * g[k] + mp.polygamma(k - 1, n + mp.mpf(1) / 2)
        return (-1) ** k * hk * mp.mpf(n) ** (k - 1) / (2 * mp.factorial(k - 2)) * v1


@pytest.mark.parametrize("n", [10**8, 10**20])
def test_derivative_enclosures_contain_route_B(n):
    with rigor._flint_prec(E.PREC):
        lb = E.laplace_bound(Fraction(n) / 2)
        sub = E.sub_around(n)
        v1 = E.v_of_s_real(E.ab(2 * Fraction(n))).mid().str(60, radius=False)
        for k in range(2, 7):
            Hk = E.deriv_ball(k, sub, lb, arb(0), lb.q)
            with mp.workdps(60):
                assert Hk.contains(arb(mp.nstr(_route_b_H(n, k, mp.mpf(v1)), 50))), (n, k, Hk)


def test_planted_F5_fault_is_caught_by_route_B(monkeypatch):
    """Remove the first-order term 5/6 e from F_5: route B must fall outside."""
    n = 10**8
    orig = E.F_ball

    def planted(k, e, m):
        out = orig(k, e, m)
        return out - E.ab(Fraction(5, 6)) * e if k == 5 else out

    monkeypatch.setattr(E, "F_ball", planted)
    with rigor._flint_prec(E.PREC):
        lb = E.laplace_bound(Fraction(n) / 2)
        sub = E.sub_around(n)
        v1 = E.v_of_s_real(E.ab(2 * Fraction(n))).mid().str(60, radius=False)
        H5 = E.deriv_ball(5, sub, lb, arb(0), lb.q)
        with mp.workdps(60):
            assert not H5.contains(arb(mp.nstr(_route_b_H(n, 5, mp.mpf(v1)), 50)))


# ---------------------------------------------------------------------------
# Lemmas V, L, R: conditions, the measured remainder, and a planted fault
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("x0", [789702, 14237025, 10**34])
def test_laplace_conditions_hold(x0):
    lb = E.laplace_bound(x0)
    assert all(lb.conditions.values()), lb.conditions


def test_laplace_bound_covers_the_measured_remainder_at_complex_s():
    m = E.measure_laplace(10**6, 0.2)
    assert m["measured"] < m["lambda"]
    assert m["slack"] > 100


def test_planted_laplace_fault_is_caught():
    """C_rho divided by 1e4 gives a lambda below the measured |log I e^{-G}|."""
    m = E.measure_laplace(10**6, 0.2)
    with rigor._flint_prec(E.PREC):
        lb = E.laplace_bound(10**6)
        lam_planted = E.up(-(1 - lb.C_rho / 10**4 / lb.p_min.sqrt()).log())
    assert lam_planted < m["measured"]


# ---------------------------------------------------------------------------
# Lemmas M5, M6: Krawczyk boxes against Newton solves
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("n", [10**8, 10**12])
def test_boxes_contain_newton_solutions_and_targets_contain_route_B(n):
    m = _data_models(n)
    assert all(m["T_contains_route_B"]), m["T_contains_route_B"]
    assert all(m["model5_box_contains_newton"])
    assert all(m["model6_box_contains_newton"])


def test_five_coefficient_limit_is_X_star():
    """At e -> 0 the box tends to (5/12, 2/3, 1/12), Holland's 6/5, 1/3, 1/24."""
    with rigor._flint_prec(E.PREC):
        lb = E.laplace_bound(10**30)
        D = E.make_data(E.Sub(Fraction(0), Fraction(1, 10**4)), lb, 2)
        M = E.model5(D)
        assert M.ok
        for x, q in zip(M.X, E.X5_STAR):
            assert abs(x - E.ab(q)).upper() < arb("0.002")


def test_lemma_G_second_bound_fails_without_its_case():
    with mp.workdps(40):
        d, V = 5, mp.mpf(400)
        U = V + d + 5000
        J = _jacobi(d, U, V)
        H = U - d - 1
        assert max(J[k, k] - V for k in range(d)) > V * (d - 1) / H


def test_planted_data_shift_is_caught_by_newton(monkeypatch):
    n = 10**12
    newton = _data_models(n)["m5"]["X"]
    orig = E.make_data

    def planted(sub, lb, jmax):
        D = orig(sub, lb, jmax)
        D.t[1] = D.t[1] + E.ab(Fraction(1, 1000))
        return D

    monkeypatch.setattr(E, "make_data", planted)
    with rigor._flint_prec(E.PREC):
        lb = E.laplace_bound(Fraction(n) / 2)
        M = E.model5(E.make_data(E.sub_around(n), lb, 2))
        assert not all(M.X[i].contains(arb(mp.nstr(newton[i], 40))) for i in range(3))


# ---------------------------------------------------------------------------
# Holland's identities (75), (76), (86), (90), V_m, and Lemma G's sharper rows
# ---------------------------------------------------------------------------


def _jacobi(d, U, V):
    H, al, be = U - d - 1, V - 1, U - V - d
    M = mp.zeros(d, d)
    for k in range(d):
        M[k, k] = U * (H * (V + 2 * k) + 2 * k * (k + 1)) / ((H + 2 * k) * (H + 2 * k + 2))
    for k in range(1, d):
        M[k - 1, k] = M[k, k - 1] = U / (2 * k + H) * mp.sqrt(
            k * (k + al) * (k + be) * (k + H) / ((2 * k + H - 1) * (2 * k + H + 1)))
    return M


@pytest.mark.parametrize("d,V,extra", [(3, 200, 50), (5, 400, 5000), (8, 600, 9), (6, 300, 280)])
def test_jacobi_matrix_and_sharper_gershgorin_rows(d, V, extra):
    """Lemma G's rows; the second diagonal bound only for U < 2V (it fails beyond, which
    is how a first draft stating it for every U was caught)."""
    with mp.workdps(60):
        V = mp.mpf(V)
        U = V + d + extra
        c = [mp.rf(-d, j) * mp.rf(U, j) / (mp.rf(V, j) * mp.factorial(j) * U**j) for j in range(d + 1)]
        roots = sorted(mp.re(x) for x in mp.polyroots(list(reversed(c)), maxsteps=200, extraprec=200))
        J = _jacobi(d, U, V)
        ev = sorted(mp.re(x) for x in mp.eig(J)[0])
        assert max(abs(a - b) / a for a, b in zip(roots, ev)) < mp.mpf(10) ** -40
        H = U - d - 1
        for k in range(d):
            a_k = J[k, k] - V
            if U >= 2 * V:
                assert 0 <= a_k + mp.mpf(10) ** -40 and a_k <= (d - 1) * (2 * U + V) / H
            else:
                assert -2 * (d - 1) * abs(U - 2 * V) / H - mp.mpf(10) ** -40 <= a_k <= V * (d - 1) / H + mp.mpf(10) ** -40
        for k in range(1, d):
            assert J[k - 1, k] <= (U / H) * mp.sqrt(d * (d + V) * (U - V) / H)
            if U >= 2 * V:
                assert J[k - 1, k] <= (U / H) * mp.sqrt((d - 1) * (d + V - 2))


def _J_coeffs(c, d, A, B):
    """Coefficients of J p = y(1 - y/A) p'' + (B - y + (d-1) y/A) p' + d p:
    (J p)_k = (k+1)(k+B) c_{k+1} + (d-k)(1 + k/A) c_k."""
    c = list(c) + [0]
    return [(k + 1) * (k + B) * c[k + 1] + (d - k) * (1 + Fraction(k) / A if isinstance(A, Fraction) else 1 + k / A) * c[k]
            for k in range(len(c) - 1)]


def test_holland_86_factorisation_exactly_and_a_planted_sign():
    """(E + D) J p_F = -(eps_p/A) E(E - d)(E + A) p_F, coefficient by coefficient in
    exact rationals, p_F = 3F2(-d, A, C; B, D; D y/(A C))."""
    d = 7
    A, B, C, D = Fraction(371, 3), Fraction(23), Fraction(59, 2), Fraction(17)
    x = D / (A * C)
    c, term = [], Fraction(1)
    for j in range(d + 1):
        c.append(term)
        term = term * (j - d) * (A + j) * (C + j) / ((B + j) * (D + j) * (j + 1)) * x
    W = _J_coeffs(c, d, A, B)
    lhs = [(k + D) * W[k] for k in range(d + 1)]
    eps_p = (C - D) / C
    rhs = [-(eps_p / A) * k * (k - d) * (k + A) * c[k] for k in range(d + 1)]
    assert lhs == rhs
    assert lhs != [-v for v in rhs]  # the wrong sign of eps_p is caught


def test_identity_90_and_V_m_expansion():
    """(90) and A V_m = T_{m+3} + (A-d+3+3m) T_{m+2} + beta_m T_{m+1} + gamma_m T_m,
    for a polynomial of degree d at a point (both are identities, not only at
    critical points), in exact rational arithmetic."""
    d, A, B = 7, Fraction(41), Fraction(13)
    c = [Fraction(v) for v in (3, -2, 5, 1, -4, 2, 1)] + [Fraction(1, 3)]
    y = Fraction(137, 100)

    def der(cc, k):
        for _ in range(k):
            cc = [j * cc[j] for j in range(1, len(cc))]
        return cc

    def ev(cc, t):
        return sum((cj * t**j for j, cj in enumerate(cc)), Fraction(0))

    pv = ev(c, y)
    T = [y**k * ev(der(c, k), y) / pv for k in range(d + 4)]
    W = _J_coeffs(c, d, A, B)
    f3 = [cj * j * (j - d) * (j + A) for j, cj in enumerate(c)]  # E(E - d)(E + A) p
    for m in range(0, d - 1):
        Um = y**m * ev(der(W, m), y) / pv
        rhs = (1 - y / A) * T[m + 2] + (B + m - y + (d - 1 - 2 * m) * y / A) * T[m + 1] \
            + (d - m) * (1 + Fraction(m) / A) * y * T[m]
        assert y * Um == rhs
        AVm = y**m * ev(der(f3, m), y) / pv
        beta = A * (2 * m + 1 - d) - d * (2 * m + 1) + 3 * m * m + 3 * m + 1
        gamma = m * (m - d) * (m + A)
        assert AVm == T[m + 3] + (A - d + 3 + 3 * m) * T[m + 2] + beta * T[m + 1] + gamma * T[m]


# ---------------------------------------------------------------------------
# the polynomial level, n = 1e12: Lemma G, Lemma 9.1-E, Lemma 8.1-E, and plants
# ---------------------------------------------------------------------------


def test_polynomials_respect_the_bounds_and_planted_faults_are_caught():
    row = _polys()["five"][0]
    assert row["real_roots"] == row["d"]
    assert row["C_loc_measured"] <= row["C_loc_bound"]
    assert row["r_needed_over_sqrt_Bd"] <= row["K6"]
    assert row["E_F_measured_over_bound"] <= 1
    # plants: C_loc halved, K6 = 1, Theta_5 halved
    assert row["C_loc_measured"] > row["C_loc_bound"] / 2
    assert row["r_needed_over_sqrt_Bd"] > 1
    assert row["E_F_measured_over_bound"] * 2 > 1
    six = _polys()["six"][0]
    assert six["r_needed_over_sqrt_Bd"] <= six["r_12_3_over_sqrt_Bd"]


# ---------------------------------------------------------------------------
# the effectivity check (the MISSION's kill condition)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("name", list(E.SPECS))
def test_effectivity_check_is_green_at_the_claims(name):
    chk = E.effectivity_check(name)
    assert all(chk.values()), {k: v for k, v in chk.items() if not v}


@pytest.mark.parametrize("name", list(E.SPECS))
def test_every_planted_weakening_turns_the_check_red(name):
    pw = E.planted_weakenings(name)
    assert all(pw.values()), {k: v for k, v in pw.items() if not v}
    assert set(E.CLAIMS[name]) <= set(pw)


def test_claimed_K_values():
    assert E.CLAIMS["five_assisted"]["K"] == 17900
    assert E.CLAIMS["five_standalone"]["K"] == Fraction("9.10e19")
    assert E.CLAIMS["six_assisted"]["K"] == Fraction("7.21e9")
    assert E.CLAIMS["six_standalone"]["K"] == Fraction("3.61e30")


def test_gorttw_threshold_and_c_equals_one_remark():
    K = E.CLAIMS["five_assisted"]["K"]
    n_min = E.n_threshold_gorttw(K)
    assert n_min > E.ab(10**35) and n_min < E.ab(2 * 10**35)
    # NOVELTY.md 2.3: K <= e^{1e21} suffices for c = 1; at d = 9.36e20 the margin is vast
    d = 936 * 10**18
    assert math.log(K) < 1.5 * d + 2 * math.log(d / 2) - 5 * math.log(d)


def test_lemma_W_monotonicity_samples():
    with rigor._flint_prec(E.PREC):
        prev = None
        for n in (10**3, 10**4, 10**6, 10**10, 10**20, 10**40):
            v = E.v_of_s_real(E.ab(2 * n))
            f = (E.ab(n + 2).log() / v)
            if prev is not None:
                assert f < prev
            prev = f


def test_results_json_pins():
    r = json.loads((HERE / "results_effective.json").read_text())
    for name, v in r["variants"].items():
        assert v["verdict"] == "green", name
        assert v["kill_condition_met"] is False, name
        assert all(v["planted_weakenings_turn_red"].values()), name
    assert r["backend"] == "python-flint"
    assert r["first_order_coefficients_F_k"]["6"] == "13/12"


# ---------------------------------------------------------------------------
# REVIEW_PHASE2.md item P: formula faults the measurements above cannot see
# ---------------------------------------------------------------------------
#
# Each check below takes a module (the real `effective`, or a planted copy) and
# compares one formula step with its derivation, written out here independently of
# the module's code path for that step. The reviewer's plants are the same source
# edits `review_p2/plant_formula_faults.py` applies; that script is not imported.


def _lemma_L_cubic_ok(mod) -> bool:
    """Lemma L's cubic Taylor piece. EFFECTIVE.md section 3: on |t| <= T the error is
    at most (M_3/6) int |t|^3 e^{-Re Psi t^2/4} dt, normalised by sqrt(|Psi|/(2 pi)),
    with M_3 >= p e^T, Re Psi <= p cos b and |Psi| >= p. So
    C_rho >= k3 e^T/(sqrt(2 pi) cos^2 b), k3 = (1/6) int |t|^3 e^{-t^2/4} dt, which
    the test takes from quadrature rather than from the module's 8/3."""
    with mp.workdps(40):
        k3 = mp.quad(lambda t: abs(t) ** 3 * mp.exp(-t * t / 4), [-mp.inf, 0, mp.inf]) / 6
        assert abs(k3 - mp.mpf(8) / 3) < mp.mpf(10) ** -30
        k3 = arb(mp.nstr(k3, 35))
    with rigor._flint_prec(mod.PREC):
        for x0 in (789702, 14237025, 9910 * 10**30, 565 * 10**33):
            lb = mod.laplace_bound(x0)
            floor_ = k3 * mod.ab(mod.T_STEP).exp() / ((2 * arb.pi()).sqrt() * lb.b.cos().upper() ** 2)
            if not bool(lb.C_rho >= floor_):
                return False
    return True


def _lemma_D_cauchy_ok(mod) -> bool:
    """Lemma D(ii)'s Cauchy part: with F_k set to 0 the ball deriv_ball returns is the
    remainder bound alone, and it must be at least k! lambda/(r n)^k normalised, with
    r = RHO - RHO_D the radius left about a point of the derivative disk inside the
    Lemma R disk (EFFECTIVE.md section 3)."""
    r_avail = mod.ab(mod.RHO - mod.RHO_D)
    orig = mod.F_ball
    mod.F_ball = lambda k, e, m: arb(0)
    try:
        with rigor._flint_prec(mod.PREC):
            for n in (10**8, 10**20):
                lb = mod.laplace_bound(Fraction(n) / 2)
                sub = mod.sub_around(n)
                for k in range(2, 8):
                    H = mod.deriv_ball(k, sub, lb, arb(0), lb.q)
                    need = (mod.ab(k * (k - 1)) * lb.lam
                            / (2 * r_avail**k * sub.n_lo * mod.ab(sub.e_hi))).lower()
                    if not bool(arb(H.rad()) >= need):
                        return False
    finally:
        mod.F_ball = orig
    return True


def _lemma_B_sturm_factor(mod):
    """The Sturm factor sqrt(c1 + c2/d_min) that chain6 actually used, read back from
    its bracket (d + 2r)/(n sqrt(delta) log(d+2)) on a narrow subinterval at n = 2e7,
    together with the model's A, B there."""
    spec = mod.SPECS["six_standalone"]
    K, d, dw = mod.CLAIMS["six_standalone"]["K"], spec["d_min"], spec["d_wedge_min"]
    with rigor._flint_prec(mod.PREC):
        lb = mod.laplace_bound(14237025)
        sub = mod.sub_around(2 * 10**7)
        row = mod.chain6(sub, lb, K, d, dw)
        M = mod.model6(mod.make_data(sub, lb, 3))
        delta = mod.wedge_delta(sub, K, 6, 2, logd_lo=(mod.ab(dw) + 2).log().lower())
        eta8 = 8 * mod.sqrt_nn(delta * M.w_D)
        rho_r = (mod.ab(9) / (2 * arb.pi()) * (1 + eta8) / (1 - eta8)
                 * mod.ab(mod.harmonic_log_constant(d))).mid()
        first = (mod.sqrt_nn(delta) / (mod.ab(d) + 2).log().lower()).mid()
        s = (row["bracket"].mid() - first) * M.w_B.mid().sqrt() / (2 * rho_r)
        n = sub.n_lo.mid()
        return d, s, n / M.w_A.mid(), n / M.w_B.mid()


def _lemma_B_sturm_ok(mod) -> bool:
    """Lemma B (RESULTS.md 12.3): on [B/2, 3B/2] with A >= 8B, R >= (B/2)(13/16),
    |P| <= 0.501 B, |R'|, |P'| <= 1, R <= 3B/2, so Q B <= (32/13) d + 2.001 (32/13)^2/2.
    Two checks: the factor the chain used is at least that, and the actual smallest
    gap of 2F1(-d, A; B; y/A) at the chain's own A, B is at least the gap bound
    pi sqrt(B/d)/s that the factor implies (measured slack about 1.75)."""
    d, s, A, B = _lemma_B_sturm_factor(mod)
    c1 = 1 / (Fraction(1, 2) * Fraction(13, 16))
    c2 = (Fraction(501, 1000) + Fraction(3, 2)) / (2 * (Fraction(1, 2) * Fraction(13, 16)) ** 2)
    if not bool(s * s >= mod.ab(c1 + c2 / d)):
        return False
    with mp.workdps(50):
        A_, B_ = (mp.mpf(x.str(45, radius=False)) for x in (A, B))
        assert A_ >= 8 * B_ and B_ >= 256 * d  # Lemma B's hypotheses hold at this instance
        roots = sorted(mp.eigsy(_jacobi(d, A_, B_))[0])
        gap = min(b - a for a, b in zip(roots, roots[1:]))
        return bool(gap >= mp.pi * mp.sqrt(B_ / d) / mp.mpf(s.str(45, radius=False)))


#: (source edit in effective.py, the check that must reject it); review item P's four plants
FORMULA_PLANTS = {
    "Lemma L: 8/3 -> 8/15": ("r3 = (1 + a1) * (ab(8) / 3) * m3", "r3 = (1 + a1) * (ab(8) / 15) * m3",
                             _lemma_L_cubic_ok),
    "Lemma L: 8/3 -> 8/30": ("r3 = (1 + a1) * (ab(8) / 3) * m3", "r3 = (1 + a1) * (ab(8) / 30) * m3",
                             _lemma_L_cubic_ok),
    "Lemma D(ii): radius n/4": ("(2 * ab(RHO - RHO_D) ** k * sub.n_lo",
                                "(2 * ab(Fraction(1, 4)) ** k * sub.n_lo", _lemma_D_cauchy_ok),
    "Lemma B: 2.47, 6.07 -> 0.247, 0.607": (
        "s247 = (ab(Fraction(247, 100)) + ab(Fraction(607, 100)) / ab(d_min)).sqrt()",
        "s247 = (ab(Fraction(247, 1000)) + ab(Fraction(607, 1000)) / ab(d_min)).sqrt()",
        _lemma_B_sturm_ok),
}


def _planted_effective(old: str, new: str):
    """A fresh copy of effective.py with one source edit, as its own module."""
    path = HERE / "effective.py"
    src = path.read_text()
    if src.count(old) != 1:
        pytest.fail(f"plant site not found exactly once in effective.py: {old!r}")
    name = "effective_planted"
    mod = types.ModuleType(name)
    mod.__file__ = str(path)
    sys.modules[name] = mod  # dataclasses resolve their annotations through sys.modules
    try:
        exec(compile(src.replace(old, new), str(path), "exec"), mod.__dict__)
    finally:
        sys.modules.pop(name, None)
    mod.derive_F = E.derive_F  # untouched by every plant; reuse the cached sympy derivation
    return mod


def test_lemma_L_cubic_constant_matches_its_defining_integral():
    assert _lemma_L_cubic_ok(E)


def test_lemma_D_cauchy_part_uses_the_radius_the_geometry_leaves():
    assert _lemma_D_cauchy_ok(E)
    # the radius RHO (n/4) is not available: from z = n(1 + i RHO_D) the circle of
    # radius RHO n reaches outside the sector |arg| <= asin(RHO), which contains every
    # Lemma R disk |zeta - x| <= RHO x
    far = 1 + 1j * float(E.RHO_D + E.RHO)
    assert math.atan2(far.imag, far.real) > math.asin(float(E.RHO))


def test_lemma_B_sturm_constants_match_the_derivation_and_an_actual_gap():
    assert _lemma_B_sturm_ok(E)


@pytest.mark.parametrize("label", list(FORMULA_PLANTS))
def test_review_formula_plants_are_rejected(label):
    old, new, check = FORMULA_PLANTS[label]
    assert not check(_planted_effective(old, new)), label
