"""Tests for hunt #149 (`plocal_rivals`): every number in the hunt's documents
that a computation produces is pinned here, and every check that could hide a
fault is shown to fail on a planted one.

Run from the repo root:  .venv/bin/python -m pytest -q -n0 hunts/plocal_rivals
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for _p in (REPO, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import rivals as R  # noqa: E402

#: k = tan(theta/2) from the linear solve at dps 40 (pinned to 40 digits).
K17 = "0.4879283649264853247148290699651012206776"
K73 = "0.3126334205272301997186929661823790657452"
THETA17 = "0.90788749496088039"
THETA73 = "0.6060128282621622"
COS17 = "0.89872471018733976"
COS73 = "0.95444371692510638"


def _close(x, ref: str, tol: float) -> bool:
    with mp.workdps(60):
        return abs(mp.mpf(x) - mp.mpf(ref)) < tol


# ---------------------------------------------------------------------------
# the character table and the P-local condition
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("q,P,n", [(17, 2, 3), (73, 4, 5), (5, 1, 2)])
def test_P_is_one_below_the_least_nonresidue(q, P, n):
    assert R.least_nonresidue(q) == n
    assert R.p_local(q) == P
    assert all(R.is_residue(p, q) for p in R.primes_upto(P))
    assert not R.is_residue(n, q)


def test_the_character_values_the_documents_quote():
    assert R.chi_value(2, 17) == (-1, 0) and R.chi_value(3, 17) == (0, 1)
    assert R.chi_value(2, 73) == (1, 0) and R.chi_value(3, 73) == (-1, 0)
    assert R.chi_value(5, 73) == (0, 1)
    assert R.parity(17) == 0 and R.parity(73) == 0 and R.parity(5) == 1


@pytest.mark.parametrize("q", [5, 17, 73])
def test_character_is_order_four_and_squares_to_legendre(q):
    chi = R.character(q)
    for a in range(1, q):
        x, y = chi[a]
        sq = (x * x - y * y, 2 * x * y)
        leg = 1 if R.is_residue(a, q) else -1
        assert sq == (leg, 0)
    assert chi[R.primitive_root(q)] == (0, 1)


@pytest.mark.parametrize("q", [17, 73])
def test_character_table_matches_flint(q):
    """Route B's character comes from flint's Conrey table: same values."""
    import arb_route as B

    rv = B.ArbRival(q)
    for a in range(1, q):
        v = rv.char(a)
        x, y = R.chi_value(a, q)
        assert abs(v.real - x) < 1e-30 and abs(v.imag - y) < 1e-30


# ---------------------------------------------------------------------------
# step 1: the linear solve, the Gauss sum, PARI, and cos(theta/2) != 0
# ---------------------------------------------------------------------------


def test_q5_reproduces_davenport_heilbronn_kappa():
    from zeta.epstein import KAPPA_REF

    assert _close(R.k_linear_solve(5, 40), KAPPA_REF, 1e-39)


@pytest.mark.parametrize("q,ref", [(17, K17), (73, K73)])
def test_k_linear_solve_is_real_and_pinned(q, ref):
    k = R.k_linear_solve(q, 40)
    k_re, k_im, rel = R._k_cached(q, 40)
    assert abs(k_im) < 1e-50 and rel < 1e-50
    assert _close(k, ref, 1e-39)


@pytest.mark.parametrize("q", [5, 17, 73])
def test_gauss_sum_route_agrees_with_linear_solve(q):
    assert abs(R.k_from_gauss(q, 40) - R.k_linear_solve(q, 40)) < 1e-40


@pytest.mark.parametrize("q,theta,cos_half", [(17, THETA17, COS17), (73, THETA73, COS73)])
def test_cos_half_theta_is_nonzero_by_the_jacobi_sum(q, theta, cos_half):
    r = R.jacobi_check(q, 40)
    jre, jim = r["J"]
    assert r["norm_J"] == q and jim != 0  # eps^2 not real, so theta != pi
    assert r["eps_squared_identity_residual"] < 1e-40
    assert _close(r["theta"], theta, 1e-15)
    assert _close(r["cos_half_theta"], cos_half, 1e-15)


def test_jacobi_sums_are_the_quoted_gaussian_integers():
    assert R.jacobi_sum(17) == (-1, 4)
    assert R.jacobi_sum(73) == (3, 8)
    assert R.jacobi_sum(5) == (-1, -2)


def _pari_setup(pari, q):
    pari(f"G = znstar({q}, 1); g = lift(znprimroot({q}))")
    pari("C = 0; forvec(v = vector(#G.cyc, j, [0, G.cyc[j] - 1]), "
         "if(chareval(G, v~, g) == 1/4 && charorder(G, v~) == 4, C = v~; break))")
    # the conjugate's exponent vector must be reduced mod G.cyc: lfuncreate([G, -C])
    # is not L(s, chi-bar), although chareval reads -C correctly (measured)
    pari("Cb = vector(#C, j, (G.cyc[j] - C[j]) % G.cyc[j])~")
    pari("L = lfuncreate([G, C]); Lb = lfuncreate([G, Cb]); k = tan(arg(lfunrootres(L)[3])/2)")
    pari("bn(n) = my(x = chareval(G, C, n, [I, 4])); if(x == 0, 0, real(x) + k*imag(x))")


@pytest.mark.parametrize("q", [17, 73])
def test_pari_L_functions_are_chi_and_chi_bar(q):
    cypari2 = pytest.importorskip("cypari2")
    pari = cypari2.Pari()
    pari.set_real_precision(40)
    _pari_setup(pari, q)
    s = mp.mpc(0.75, 3.5)
    for name, conj in (("L", False), ("Lb", True)):
        v = pari(f"lfun({name}, 3/4 + 7/2*I)")
        ours = R.L_mp(s, q, conj=conj, dps=35)
        theirs = mp.mpc(str(pari(f"real({v})")).replace(" E", "e"),
                        str(pari(f"imag({v})")).replace(" E", "e"))
        assert abs(ours - theirs) < 1e-30


@pytest.mark.parametrize("q,ref", [(17, K17), (73, K73)])
def test_pari_root_number_gives_the_same_k(q, ref):
    cypari2 = pytest.importorskip("cypari2")
    pari = cypari2.Pari()
    pari.set_real_precision(45)
    _pari_setup(pari, q)
    assert _close(str(pari("k")).replace(" E", "e"), ref, 1e-38)


@pytest.mark.parametrize("q", [17, 73])
def test_pari_checks_the_self_dual_functional_equation_and_its_faults(q):
    """A third, code-disjoint FE check: PARI's lfuncheckfeq on F's own series.

    Pinned at real precision 40: F passes below 2^-140; a 1e-10 change in one
    coefficient, a 1e-12 change in k, and the wrong root number all fail it.
    """
    cypari2 = pytest.importorskip("cypari2")
    pari = cypari2.Pari()
    pari.set_real_precision(40)
    _pari_setup(pari, q)
    good = int(pari(f"lfuncheckfeq(lfuncreate([n -> vector(n, j, bn(j)), 0, [0], 1, {q}, 1]))"))
    coef = int(pari(f"lfuncheckfeq(lfuncreate([n -> vector(n, j, bn(j) + if(j == 7, 1/10^10, 0)), "
                    f"0, [0], 1, {q}, 1]))"))
    sign = int(pari(f"lfuncheckfeq(lfuncreate([n -> vector(n, j, bn(j)), 0, [0], 1, {q}, -1]))"))
    assert good < -140
    assert coef > -50 and sign > -5
    assert good < coef - 90


# ---------------------------------------------------------------------------
# step 1: the functional-equation defect, its precision response, planted faults
# ---------------------------------------------------------------------------


def test_fe_defect_at_dps_40_for_q17_and_its_precision_response():
    d20, _ = R.fe_defect_table(17, 20)
    d40, _ = R.fe_defect_table(17, 40)
    assert d40 < 1e-40
    assert d20 < 1e-20
    assert d40 < d20 * 1e-15  # the defect is precision, not structure


def test_fe_defect_at_dps_40_for_q73():
    pts = [mp.mpc(3, 4), mp.mpc(0.8, 21)]
    assert max(R.fe_defect(s, 73, dps=40) for s in pts) < 1e-40


#: MATCH.md's defect table: max over FE_POINTS, (lower, upper) brackets.
FE_TABLE = {
    17: {20: (3.0e-22, 3.2e-22), 30: (1.6e-32, 1.8e-32), 40: (1.2e-42, 1.4e-42)},
    73: {20: (2.9e-22, 3.1e-22), 30: (1.0e-32, 1.1e-32), 40: (2.8e-42, 3.0e-42)},
}


@pytest.mark.parametrize("q", [17, pytest.param(73, marks=pytest.mark.slow)])
def test_fe_defect_table_quoted_in_match(q):
    for dps, (lo, hi) in FE_TABLE[q].items():
        d, _ = R.fe_defect_table(q, dps)
        assert lo < d < hi, (q, dps, d)


def test_theta_and_cos_half_theta_for_davenport_heilbronn():
    r = R.jacobi_check(5, 40)
    assert _close(r["theta"], "0.55357435889704525", 1e-15)
    assert _close(r["cos_half_theta"], "0.96193835778391744", 1e-15)


def test_fe_defect_at_dps_60_for_q17():
    pts = [mp.mpc(3, 4), mp.mpc(-0.25, 10.5), mp.mpc(0.8, 21)]
    assert max(R.fe_defect(s, 17, dps=60) for s in pts) < 1e-60


@pytest.mark.parametrize("fault", ["class", "single", "k"])
def test_a_planted_fault_fails_the_defect_test(fault):
    """Perturb one residue class, one coefficient, or k: the defect test fails."""
    s = mp.mpc(0.8, 21)
    if fault == "class":
        d = R.fe_defect(s, 17, dps=40, perturb={3: mp.mpf("1e-10")})
    elif fault == "single":
        d = R.fe_defect(s, 17, dps=40, perturb_n={7: mp.mpf("1e-10")})
    else:
        k = R.k_linear_solve(17, 40) + mp.mpf("1e-12")
        d = R.fe_defect(s, 17, dps=40, k=k)
    assert d > 1e-14  # against below 1e-40 unperturbed


# ---------------------------------------------------------------------------
# step 2: the P-smooth identities, exactly, and the full agreement set
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("q,first,n_smooth,n_dis", [(17, 3, 14, 2138), (73, 5, 67, 1535), (5, 2, 1, 3497)])
def test_exact_identities_to_ten_thousand(q, first, n_smooth, n_dis):
    r = R.exact_identity_report(q, 10 ** 4)
    assert r["smooth_coefficient_failures"] == []
    assert r["smooth_log_derivative_failures"] == []
    assert r["n_smooth"] == n_smooth
    assert r["first_disagreement"] == first == R.least_nonresidue(q)
    assert r["disagreement_set_equals_nr_composed"]
    assert r["accidental_agreements"] == []
    assert r["n_disagreements"] == n_dis
    assert r["min_numeric_gap_on_disagreements"] > 1e-6


def test_the_first_log_derivative_coefficients_of_F17():
    lam = R.exact_lambda_F(12, 17)
    assert lam[2] == {(2, 0): -1}          # Lambda(2) chi(2) = -log 2
    assert lam[3] == {(3, 1): 1}           # k log 3, against i log 3 for L
    assert lam[6] == {}                    # mixed n: 0 on both sides
    assert lam[9] == {(3, 0): -2, (3, 2): -1}   # -(2 + k^2) log 3: non-unitary at 9


def test_the_identity_check_has_power_on_a_wrong_character():
    """Lesion: flip chi(2) for the comparison side; the P-smooth check must fail."""
    lam = R.exact_lambda_F(64, 17)
    bad = {}
    for n in (2, 4, 8, 16, 32, 64):
        lc = R.exact_lambda_chi(n, 17)
        flipped = {p: (-re, im) for p, (re, im) in lc.items()} if n in (2, 8, 32) else lc
        bad[n] = R.exact_agrees(lam[n], flipped)
    assert not bad[2] and not bad[8] and not bad[32]
    assert bad[4] and bad[16] and bad[64]


# ---------------------------------------------------------------------------
# step 3: the window forms
# ---------------------------------------------------------------------------


def test_window_form_reproduces_galerkin_dh_at_q5():
    g = R._galerkin()
    with mp.workdps(40):
        c = mp.mpf("13.5")
        W = R.window_form_F(c, 6, 5, dps=40)
        T = g.Truncation(c, 6, "dh")
        d = max(abs(W.entry(n, m) - T.entry(n, m)) for n in range(-6, 7) for m in range(-6, 7))
    assert d < 1e-38


def test_window_form_archimedean_block_reproduces_galerkin_zeta():
    g = R._galerkin()
    with mp.workdps(40):
        c = mp.mpf(11)
        coeffs = [(qq, mp.log(p)) for (qq, p) in g.prime_powers_upto(float(c))]
        W = R.CharacterTruncation(c, 6, 1, 0, coeffs)
        T = g.Truncation(c, 6, "zeta")
        d = max(abs(W.entry(n, m) + T.w02(n, m) - T.entry(n, m))
                for n in range(-6, 7) for m in range(-6, 7))
    assert d < 1e-38


@pytest.mark.parametrize("args", [(7, 2, -3, None), (7, 3, 3, None), (5.5, -1, 4, 0.9)])
def test_parity_odd_kernel_against_quadrature(args):
    r = R.odd_kernel_check(*args)
    assert r["q_closed_minus_quad"] < 1e-25 and r["qo_closed_minus_quad"] < 1e-25
    assert r["g_symmetric"] < 1e-25


@pytest.mark.parametrize("q,cs", [(17, ("2.5", "3")), (73, ("3.5", "5"))])
def test_window_forms_agree_up_to_P_plus_one(q, cs):
    for c in cs:
        r = R.window_comparison(mp.mpf(c), 8, q, dps=40)
        assert r["max_abs_entry_diff"] < 1e-38
        assert r["max_eig_diff"] < 1e-36


@pytest.mark.parametrize("q,c,lo,hi", [(17, "3.001", 1e-5, 1e-3), (17, "3.5", 0.1, 1.0),
                                       (73, "5.001", 1e-5, 1e-3), (73, "5.5", 0.05, 1.0)])
def test_window_forms_differ_once_c_passes_the_first_nonsquare(q, c, lo, hi):
    r = R.window_comparison(mp.mpf(c), 6, q, dps=40)
    assert lo < r["max_abs_entry_diff"] < hi
    assert r["L_parity_coupled"]


#: MATCH.md's N = 8 table: (q, c) -> (entry diff bracket, eig diff bracket, lambda_min(F)).
WINDOW_TABLE = [
    (17, "2.5", (0, 1e-40), (0, 1e-38), "1.360618"),
    (17, "3", (1e-42, 1e-40), (1e-41, 1e-38), "1.267932"),
    (17, "3.001", (1.8e-4, 2.0e-4), (1.0e-3, 1.2e-3), "1.267757"),
    (17, "3.01", (2.3e-3, 2.5e-3), (1.0e-2, 1.2e-2), "1.266187"),
    (17, "3.5", (0.16, 0.18), (0.17, 0.19), "1.177847"),
    (73, "3.5", (1e-43, 1e-40), (1e-41, 1e-38), "1.963318"),
    (73, "5", (1e-42, 1e-40), (1e-41, 1e-38), "1.661545"),
    (73, "5.001", (5.6e-5, 5.8e-5), (5.1e-4, 5.3e-4), "1.661346"),
    (73, "5.01", (6.6e-4, 6.8e-4), (5.1e-3, 5.3e-3), "1.659553"),
    (73, "5.5", (8.3e-2, 8.5e-2), (9.2e-2, 9.4e-2), "1.565040"),
]


@pytest.mark.parametrize("q,c,ed,eg,lmin", WINDOW_TABLE)
def test_window_table_quoted_in_match(q, c, ed, eg, lmin):
    r = R.window_comparison(mp.mpf(c), 8, q, dps=40)
    assert ed[0] <= r["max_abs_entry_diff"] < ed[1]
    assert eg[0] <= r["max_eig_diff"] < eg[1]
    assert abs(r["lambda_min_F"] - float(lmin)) < 1e-6


def test_window_comparison_has_power_below_P_on_a_wrong_local_factor():
    """Lesion: an L-form with chi(2) flipped differs from F already at c = 2.5."""
    with mp.workdps(40):
        c = mp.mpf("2.5")
        WF = R.window_form_F(c, 6, 17, dps=40)
        coeffs = [(2, -R.lambda_chi_numeric(2, 17))]
        WX = R.CharacterTruncation(c, 6, 17, 0, coeffs)
        d = R.matrix_max_abs_diff(WF.full_matrix(), WX.full_matrix())
    assert d > 0.1


# ---------------------------------------------------------------------------
# step 4: the abscissa bounds
# ---------------------------------------------------------------------------


def test_phase_abscissa_reproduces_strip2_at_q5():
    import abscissa as A

    ps = A.PhaseStrip(5, P=10 ** 5)
    lo, hi, _ = ps.bisect(Fraction("1.10"), Fraction("1.15"), Fraction(1, 10 ** 20))
    # strip2_results.json's flint enclosure of the same root
    assert Fraction("1.1203624981833869487276") <= lo
    assert hi <= Fraction("1.1203624981833869487332")
    assert ps.excludes(Fraction("1.12036249819"))


@pytest.mark.parametrize("q,star,below", [(17, "1.09896904163", "1.0989690416"),
                                          (73, "1.0445906373", "1.0445906372")])
def test_phase_abscissa_for_the_rivals(q, star, below):
    import abscissa as A

    ps = A.PhaseStrip(q, P=10 ** 5)
    assert ps.excludes(Fraction(star))
    lo_b, _ = ps.theta_bounds(Fraction(below))
    assert lo_b > ps.tau  # below the root the obstruction is not available


@pytest.mark.parametrize("q,lo,hi", [(17, "1.5842597817", "1.5842597818"),
                                     (73, "1.6148802929", "1.6148802930")])
def test_domination_abscissa_sits_below_the_census_right_edge(q, lo, hi):
    import abscissa as A

    a, b = A.domination_bracket(q, Fraction("1.3"), Fraction("2.0"), Fraction(1, 10 ** 11))
    assert Fraction(lo) <= a and b <= Fraction(hi)
    assert b < Fraction(17, 10)


# ---------------------------------------------------------------------------
# step 4: the first off-line zero of F_17 on three routes
# ---------------------------------------------------------------------------

Z17_RE = "0.6670253335339771563145982207134238324630"
Z17_IM = "25.69077157780038556074134204260582393293"


def test_first_offline_zero_of_F17_route_A():
    rv = R.FpRival(17)
    z = R.newton_fp(rv, complex(0.667, 25.69))
    assert abs(z.real - float(Z17_RE)) < 1e-11 and abs(z.imag - float(Z17_IM)) < 1e-11
    assert abs(rv.F(z)) < 1e-12


def test_first_offline_zero_of_F17_route_B_decided_box():
    import arb_route as B

    rv = B.ArbRival(17)
    r = rv.tiny_box(0.667025, 25.690771, log2_half=30)
    assert r["status"] == "decided" and r["N"] == 1
    x0, x1, y0, y1 = (Fraction(v) for v in r["box"])
    assert x0 > Fraction(1, 2)
    assert x0 < Fraction(Z17_RE) < x1 and y0 < Fraction(Z17_IM) < y1


def test_first_offline_zero_of_F17_pari_third_route():
    cypari2 = pytest.importorskip("cypari2")
    pari = cypari2.Pari()
    pari.set_real_precision(45)
    _pari_setup(pari, 17)
    pari("A = (1 - I*k)/2")
    # a GP definition swallows the rest of its line, so one per call
    pari("Fp(s) = A*lfun(L, s) + conj(A)*lfun(Lb, s)")
    pari("dFp(s) = A*lfun(L, s, 1) + conj(A)*lfun(Lb, s, 1)")
    pari("z = 0.667 + 25.69*I; for(i = 1, 10, z = z - Fp(z)/dFp(z))")
    zr = str(pari("real(z)")).replace(" E", "e")
    zi = str(pari("imag(z)")).replace(" E", "e")
    assert _close(zr, Z17_RE, 1e-38) and _close(zi, Z17_IM, 1e-38)
    assert float(pari("abs(Fp(z))")) < 1e-40


def test_the_offline_zero_is_not_a_zero_of_L():
    """F and L share every window form with c <= 3 and still not this zero.

    At a zero of F, A L(chi) = -conj(A) L(chi-bar), so the two moduli are equal
    there and neither vanishes: the zero is a phase coincidence of two
    non-vanishing L-values (measured, |L| = 0.3396 here).
    """
    with mp.workdps(40):
        s = mp.mpc(Z17_RE, Z17_IM)
        a = abs(R.L_mp(s, 17, dps=40))
        b = abs(R.L_mp(s, 17, conj=True, dps=40))
        assert a > 0.3 and abs(a - b) < 1e-35
        assert _close(a, "0.3396173662371325", 1e-14)


def test_route_B_guards_for_the_cited_bound():
    import arb_route as B

    rv = B.ArbRival(73)
    g = rv.rademacher_guard([(0.5, 25), (0.3, 100.5), (1.2, 500.25), (0.0, 999.5), (-0.4, 40.0)])
    assert g["passed"] and g["max_ratio"] < 0.9
    m = rv.m2_guard(Fraction(1, 2) + Fraction(1, 64), Fraction(990), Fraction(1, 64))
    assert m["passed"] and m["ratio"] < 0.5


def test_route_B_m2_guard_catches_a_deflated_bound():
    """Lesion: deflate the tube radius 10^6-fold and the measured guard fails."""
    import arb_route as B

    rv = B.ArbRival(17)
    orig = rv.tube_radius
    rv.tube_radius = lambda mx, my, h: orig(mx, my, h) * 1e-6
    m = rv.m2_guard(Fraction(1, 2) + Fraction(1, 64), Fraction(25), Fraction(1, 64))
    assert not m["passed"]


def test_folded_count_detects_a_broken_functional_equation():
    """Lesion: with k off by 1e-3 the folded count stops being an integer."""
    good = R.psi_fp(R.FpRival(17), 30.2, 1.7)
    bad = R.psi_fp(R.FpRival(17, k=float(R.k_linear_solve(17, 30)) + 1e-3), 30.2, 1.7)
    assert good["defect"] < 1e-9 and good["N"] == 16
    assert bad["defect"] > 1e-5


# ---------------------------------------------------------------------------
# OBSTRUCTION.md: how large P can be
# ---------------------------------------------------------------------------

#: least prime q = 1 (mod 4) whose least quadratic non-residue is n (exact search)
LEAST_Q = {2: 5, 3: 17, 5: 73, 7: 241, 11: 1009, 13: 2689, 17: 8089, 19: 33049, 23: 53881}


def test_least_conductor_for_each_P():
    best = {}
    q = 5
    while len(best) < len(LEAST_Q):
        if R.is_prime(q):
            n = R.least_nonresidue(q)
            best.setdefault(n, q)
        q += 4
    assert best == LEAST_Q
    assert all(R.is_prime(n) for n in best)


# ---------------------------------------------------------------------------
# CORE_CANDIDATE.md: the battery's blind spot, and the prototype interface
# ---------------------------------------------------------------------------


def test_battery_reports_a_false_positive_that_the_plocal_rival_corrects():
    r = R.battery_with_plocal(R.claim_unitary_euler_factor_at_2)
    assert r["riemann_zeta"] is True
    assert r["distinguishes_without_plocal"] is True    # every current rival fails it
    assert r["plocal_17"] is True and r["shared_with"] == ("plocal_17",)
    assert r["distinguishes"] is False


def test_prototype_interface_meets_the_battery_contract():
    from zeta.epstein import claim_functional_equation, claim_multiplicativity

    iface = R.plocal_interface(17)
    assert set(iface) == {"name", "coefficient", "completed", "fe_defect", "Z",
                          "zeros_on_line", "count_zeros_box"}
    assert claim_functional_equation(iface) is True
    assert claim_multiplicativity(iface) is False
    # the off-line zero of F_17 at height 25.69, seen by the interface's own box count
    assert iface["count_zeros_box"](mp.mpc(0.6, 25.5), mp.mpc(0.75, 26)) == 1
    assert iface["zeros_on_line"](25, 26.5) == 0


def test_plocal_rival_fails_the_claims_the_old_rivals_already_refute():
    """CORE_CANDIDATE.md's scope line: it adds nothing where the battery already says no."""
    from zeta.epstein import claim_euler_product_positivity

    iface = R.plocal_interface(17)
    b = iface["coefficient"]
    assert abs(b(21) - b(3) * b(7)) > 0.1        # multiplicativity fails at (3, 7)
    assert abs(b(6) - b(2) * b(3)) < 1e-12       # and holds at (2, 3), a residue prime
    assert claim_euler_product_positivity(iface, n_max=50) is False   # Lambda_F(2) = -log 2


def test_fe_defect_at_dps_60_for_q73():
    assert R.fe_defect(mp.mpc(0.8, 21), 73, dps=60) < 1e-60


def test_precision_response_of_the_offline_zero():
    """The standing rule: a real quantity holds still as precision improves.

    Route B's Arb polish at 160 and 256 bits, and route A's mpmath polish at
    dps 30, against PARI's 45-digit value Z17_RE + i Z17_IM.
    """
    import arb_route as B

    rv = B.ArbRival(17)
    x1, y1, _ = rv.polish(0.667025, 25.690771, prec=160)
    x2, y2, _ = rv.polish(0.667025, 25.690771, prec=256)
    assert abs(Fraction(_frac_str(x1)) - Fraction(_frac_str(x2))) < Fraction(1, 10 ** 40)
    assert abs(Fraction(_frac_str(y1)) - Fraction(_frac_str(y2))) < Fraction(1, 10 ** 40)
    assert abs(Fraction(_frac_str(x2)) - Fraction(Z17_RE)) < Fraction(1, 10 ** 38)
    s, res = R.polish_mp(17, mp.mpc(0.667025, 25.690771), dps=30)
    assert res < 1e-28
    assert _close(mp.re(s), Z17_RE, 1e-27) and _close(mp.im(s), Z17_IM, 1e-27)


def _frac_str(x) -> str:
    """An exact decimal-free rational string for an Arb midpoint."""
    m, e = x.mid().man_exp()
    v = Fraction(int(m)) * Fraction(2) ** int(e)
    return f"{v.numerator}/{v.denominator}"
