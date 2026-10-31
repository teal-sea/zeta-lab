"""Hunt #148 (`ff_probe`): the tests.

Run with ``.venv/bin/python -m pytest -q -n0 hunts/ff_probe/test_ffprobe.py``.

Three kinds of test, as in hunt #120:

* **live** tests recompute the cheap facts on every run (small-degree brute
  force, the local identity at a few primes, one nonzero probe value in three
  representations, the rival's zeros);
* **second-implementation** tests recompute exact numbers in PARI/GP
  (``ffprobe_pari.py``, which imports nothing from ``ffprobe.py``) and compare
  them with ``ffprobe`` as exact elements of Q(zeta_N);
* **pinned** tests read the ``results_*.json`` files written by the full run
  (``ffprobe.py --part ...``) and check that the documents quote them.

Planted faults (a wrong Gauss-sum sign, a wrong residue symbol in either route)
must turn the equality checks red; the tests below make sure they do.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import ffprobe as F  # noqa: E402

CACHE = Path(os.environ.get("ZETA_LAB_CACHE", os.path.expanduser("~/.cache/zeta-lab")))
PAPER = CACHE / "openai-math-adc7f124/paper.tex"
PAPER_SHA = "42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3"
P2007 = CACHE / "ffprobe-sources-patterson2007/patterson2007.pdf"
P2007_SHA = "789082e8b99dbf97612bbc2e494ee37f237cc54a2a5ff70b5084e33f7cb04824"
P2014 = CACHE / "ffprobe-sources-patterson2014/JHPaper.tex"
P2014_SHA = "d39e92ef8da150fd063db0fdd01013e62668bc2e37bfe3219fe0f3cf3212403c"


def _results(name: str) -> dict:
    path = HERE / f"results_{name}.json"
    if not path.is_file():
        pytest.skip(f"{path.name} not present (run ffprobe.py --part {name})")
    return json.loads(path.read_text())


@pytest.fixture(scope="module")
def S3():
    return F.Setup(7, 3)


@pytest.fixture(scope="module")
def S6():
    return F.Setup(7, 6)


@pytest.fixture(scope="module")
def S4():
    return F.Setup(13, 4)


@pytest.fixture(scope="module")
def Pr(S6):
    return F.Probe(S6)


# ---------------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------------


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_the_template_source_is_the_pinned_paper():
    if not PAPER.is_file():
        pytest.skip("paper.tex cache absent")
    assert _sha(PAPER) == PAPER_SHA
    lines = PAPER.read_text().splitlines()
    assert lines[3722].startswith(r"\section{The Poisson representation and its Euler factors}")
    assert r"\begin{lemma}[The complete local identity]\label{lem:local-euler}" in lines[4009]
    assert lines[4066] == r"\end{lemma}"
    # the J_j table and the pairing the cubic case relies on
    assert "5&-a_p^2Q^{3-6x}." in lines[4030]
    assert r"=-\alpha(p)\overline{\chi_p(4)}\gamma_3," in lines[4117]


def test_the_function_field_sources_are_the_ones_cited():
    if not (P2007.is_file() and P2014.is_file()):
        pytest.skip("source cache absent")
    assert _sha(P2007) == P2007_SHA
    assert _sha(P2014) == P2014_SHA
    text = P2014.read_text(encoding="latin-1")
    # Davenport-Hasse in the 2014 form, and the definition of rho_0
    assert r"\rho_0(r,\varepsilon,i)=\Psi(r,\varepsilon,i,q^{-n-1})" in text
    assert r"(-\tau(\varepsilon\chi))^{\deg(c)}" in text
    assert r"e(f)= e_o(\sum_v \mathrm{Res}_v(f  d x)) = e_o(-\mathrm{Res}_\infty(f \mathrm d x))" in text


# ---------------------------------------------------------------------------
# Step 1: the function-field formulas
# ---------------------------------------------------------------------------


def test_sqrt_q_is_the_positive_root(S6, S4):
    assert S6.sqrtq * S6.sqrtq == 7 and S6.sqrtq.to_complex().real > 0
    assert S4.sqrtq * S4.sqrtq == 13 and S4.sqrtq.to_complex().real > 0


def test_two_residue_symbol_routes_agree(S3, S4):
    for S, dmax in ((S3, 2), (S4, 2)):
        for d in range(1, dmax + 1):
            for c in S.monic(d):
                assert (F.symbol_table_res(S, c) == F.symbol_table_crt(S, c)).all()


def test_davenport_hasse_in_the_2014_form(S6, S4):
    """g(r, eps, c) = mu(c) eps((r/c)^-1 (c'/c)) (-tau(eps chi))^deg c, e = e_o(a_-1)."""
    for S in (S6, S4):
        for d in (1, 2):
            for c in S.monic(d):
                if not F.is_squarefree(S, c):
                    continue
                tab = F.symbol_table_res(S, c)
                for r in [S.P([1]), S.P([2]), S.P([3, 1])]:
                    if r.gcd(c).degree() > 0:
                        continue
                    for j in range(1, S.n):
                        assert F.gauss_brute(S, r, j, c, table=tab) == F.gauss_dh(S, r, j, c, "2014")


def test_the_2007_form_holds_for_its_own_additive_character(S6):
    """Patterson 2007's ((-r)/c)^-1 is the same theorem for e = e_o(-a_-1), i.e. g at -r;
    with the 2014 character it fails exactly where eps(chi(-1)) = -1 and deg c is odd."""
    S = S6
    assert S.eps_chi_minus1() == 3  # eps(chi(-1)) = -1 for q = 7, n = 6
    c = S.P([1, 1])  # T + 1
    r = S.P([1])
    tab = F.symbol_table_res(S, c)
    assert F.gauss_brute(S, -r, 1, c, table=tab) == F.gauss_dh(S, r, 1, c, "2007")
    assert not F.gauss_brute(S, r, 1, c, table=tab) == F.gauss_dh(S, r, 1, c, "2007")


def test_structural_gauss_sums_match_brute_force(S3):
    for d in (1, 2):
        for c in S3.monic(d):
            tab = F.symbol_table_res(S3, c)
            for rd in (0, 1, 2):
                for r in S3.monic(rd):
                    for j in (1, 2):
                        assert F.gauss_brute(S3, r, j, c, table=tab) == F.gauss_struct(S3, r, j, c)


def test_non_squarefree_moduli_give_zero(S3):
    T = S3.P([0, 1])
    for c in [T * T, S3.P([1, 1]) ** 2 * T]:
        for r in [S3.P([1]), S3.P([2, 1])]:
            if r.gcd(c).degree() == 0:
                assert F.gauss_brute(S3, r, 1, c).is_zero()


def test_three_routes_to_C(S3):
    T = S3.P([0, 1])
    for r in [S3.P([1]), T, T * F.lin_poly(S3, 1), T * T]:
        for j in (1, 2):
            for i in range(0, 3):
                cb = F.C_sum(S3, r, j, i, "brute")
                assert cb == F.C_sum(S3, r, j, i, "struct") == F.C_fast(S3, r, j, i)


def test_theta_base_values_n3(S3):
    one = S3.P([1])
    for j in (1, 2):
        assert F.rho0(S3, one, j, 0)[0] == 1
        assert F.rho0(S3, one, j, 1)[0] == S3.tau(j) * 7
        assert F.rho0(S3, one, j, 2)[0].is_zero()


def test_psi_is_a_polynomial_of_degree_at_most_R(S3):
    T = S3.P([0, 1])
    for r in [S3.P([1]), T, T * F.lin_poly(S3, 1)]:
        for j in (1, 2):
            for i in range(3):
                _, D = F.rho0(S3, r, j, i, extra=1)
                R = F.R_index(S3, r.degree(), i)
                assert all(x.is_zero() for x in D[max(R, -1) + 1:])


def test_patterson_2014_R2_evaluation_has_a_typo():
    """Psi(q^(-n-1)) for R = 2 is C_0 q^-2 + C_1 q^(-n-2) + C_2 q^(-2n-2); the 2014
    text prints q^(-n-2) on C_2.  Pure algebra on the T-coefficients, with symbols."""
    import sympy as sp
    q, n, T = sp.symbols("q n T", positive=True)
    C0, C1, C2 = sp.symbols("C0 C1 C2")
    # D_l = C_l - (q-1) sum_{m<l} q^(n(l-m)) C_m
    D0 = C0
    D1 = C1 - (q - 1) * q ** n * C0
    D2 = C2 - (q - 1) * (q ** n * C1 + q ** (2 * n) * C0)
    val = sp.expand(D0 + D1 * q ** (-n - 1) + D2 * q ** (-2 * n - 2))
    assert sp.simplify(val - (C0 * q ** -2 + C1 * q ** (-n - 2) + C2 * q ** (-2 * n - 2))) == 0
    assert sp.simplify(val - (C0 * q ** -2 + C1 * q ** (-n - 2) + C2 * q ** (-n - 2))) != 0


def _rho_cache(S):
    cache = {}

    def rho(r, j, i):
        key = (S.key(r), j, i % S.n)
        if key not in cache:
            cache[key] = F.rho0(S, r, j, i % S.n)[0]
        return cache[key]

    return rho


def test_hecke_at_infinity_corrected_holds_and_printed_forms_fail(S3):
    rho = _rho_cache(S3)
    T = S3.P([0, 1])
    printed_2014_fail = printed_2007_fail = 0
    for r in [S3.P([1]), T, T * F.lin_poly(S3, 1), S3.P([1, 1, 0, 1])]:
        for j in (1, 2):
            rr = {i: rho(r, j, i) for i in range(3)}
            assert all(x[2] for x in F.hecke_infinity_corrected(S3, r, j, rr))
            printed_2014_fail += sum(1 for x in F.hecke_infinity(S3, r, j, rr) if not x[2])
            printed_2007_fail += sum(1 for x in F.hecke_infinity_2007(S3, r, j, rr) if not x[2])
    assert printed_2014_fail > 0
    # the 2007 form as printed fails only once R >= 1 (deg r = 3 here)
    assert printed_2007_fail == 4


def test_finite_hecke_relation_and_vanishing(S3):
    rho = _rho_cache(S3)
    T = S3.P([0, 1])
    for ro, P in [(S3.P([1]), T), (F.lin_poly(S3, 1), T), (S3.P([1]), S3.P([1, 0, 1]))]:
        for jj in (0, 1):
            for j in (1, 2):
                for i in range(3):
                    lhs = rho(ro * P ** jj, j, i)
                    assert lhs == F.finite_hecke_rhs(S3, ro, P, jj, j, i, lambda a, b, j=j: rho(a, j, b))
        assert all(rho(ro * P ** 2, j, i).is_zero() for j in (1, 2) for i in range(3))


def test_periodicity_and_affine_invariance(S3):
    rho = _rho_cache(S3)
    T = S3.P([0, 1])
    for r, b in [(T, F.lin_poly(S3, 1)), (F.lin_poly(S3, 2), T)]:
        assert all(rho(r * b ** 3, j, i) == rho(r, j, i) for j in (1, 2) for i in range(3))
    for r in [T, T * F.lin_poly(S3, 1)]:
        k = r.degree()
        for a, b in [(2, 0), (3, 1)]:
            rt = F.affine_transform(S3, r, a, b)
            for j in (1, 2):
                for i in range(3):
                    pred = rho(r, j, i) * S3.zeta_n(j * i * (k + 1 - i) * S3.chi_exp(a))
                    assert rho(rt, j, i) == pred


def test_cubic_theta_coefficients_are_gauss_sums_times_a_degree_factor(S3, S6, Pr):
    """rho_0(c, eps^2, (b - deg c) mod 3) / gamma_2(c) depends on deg c only (b = 0, 1);
    the family b = 2 vanishes."""
    for b in (0, 1, 2):
        for d in (1, 2):
            ratios = set()
            for c in S3.monic(d):
                if F.mobius(S3, c) == 0:
                    continue
                r0 = F.rho0(S3, c, 2, (b - d) % 3)[0]
                ratios.add(str((r0 / Pr.gamma(S6.P([int(x) for x in c.coeffs()]), 2)).p))
            assert len(ratios) == 1
            if b == 2:
                assert ratios == {"0"}


# ---------------------------------------------------------------------------
# Step 2: the F_7[T] probe, its representations and Lemma 7.1
# ---------------------------------------------------------------------------


def test_phase_identities_hold_in_F7T(S6, Pr):
    S = S6
    for c in list(S.monic(1)) + list(S.monic(2)):
        m = F.mobius(S, c)
        if m == 0:
            continue
        g1, g2, g3 = Pr.gamma(c, 1), Pr.gamma(c, 2), Pr.gamma(c, 3)
        assert g2 ** 3 == Pr.alpha(c) * m
        assert g1 * g2 == Pr.alpha(c) * Pr.G(c) * m
        assert Pr.G(c) == Pr.chi_val(c, S.P([4])).conj() * g3
    for c in list(S.monic(1)) + list(S.monic(2)):
        assert Pr.Gamma(c, "brute") == Pr.Gamma(c, "closed")
    for v in list(S.monic(1)):
        for w in list(S.monic(1)) + [S.P([1])]:
            assert Pr.G(v * w, "brute") == Pr.G(v, "brute") * Pr.G(w, "brute") * Pr.R(v, w)


def test_three_routes_to_F(S6, Pr):
    S = S6
    for s in F.monic_coprime_T(S, 1):
        for A in F.monic_coprime_T(S, 1)[:3]:
            for H in [S.P([1]), S.P([3]), S.P([2, 1])]:
                fb = Pr.F_brute(s, A, H)
                assert fb == Pr.F_def(s, A, H) == Pr.F_local(s, A, H)


def test_local_scalar_values(Pr, S6):
    for key in [(1, 1), (1, 0, 1)]:
        P = S6.P(list(key))
        for t in range(0, 5):
            for k in (0, 1):
                for jp in range(0, 6):
                    assert Pr.C_p_def(P, t, k, jp) == Pr.C_p_closed(P, t, k, jp)


def test_coefficient_separates_into_local_summands(S6, Pr):
    S = S6
    for u in [S.P([1]), S.P([1, 1]), S.P([2, 1]) ** 2]:
        for D in (0, 1, 2):
            for (c, n_) in F.theta_indices(S, D):
                for s in F.monic_coprime_T(S, 1)[:3] + [S.P([1])]:
                    for a in [S.P([1]), S.P([1, 1])]:
                        assert Pr.K_def(c, n_, s, a, u) == F.K_product(Pr, c, n_, s, a, u)


@pytest.mark.parametrize("j", range(6))
def test_lemma_7_1_local_factor(S6, Pr, j):
    S = S6
    P = S.P([1, 1])
    B = F.Bound(13, 2, 1)
    for w in [S.P([1]), S.P([3, 1])]:
        u = P ** j * w
        assert Pr.P_local_def(P, u, B).equals(Pr.P_local_closed(P, u, B))


def test_probe_three_representations_nonzero_case(Pr):
    d = F.probe_direct(Pr, 0, 2, 1)
    assert not d.is_zero()
    assert d == F.probe_poisson(Pr, 0, 2, 1) == F.probe_euler(Pr, 0, 2, 1)


@pytest.mark.parametrize("xi_j,DX,DA", [(3, 2, 3), (4, 1, 2), (5, 0, 1)])
def test_vectorized_s1_routes_match_the_slow_routes(S6, xi_j, DX, DA):
    """The D_s = 0 routes of step 2b (one character histogram per A on the Poisson side; a
    Moebius sum times the local factors at w = v = 0 on the Euler side) against all three
    slow representations, at small nonzero triples of other auxiliary characters."""
    P = F.Probe(S6, xi_j=xi_j)
    d = F.probe_direct(P, DX, 0, DA)
    assert not d.is_zero()
    assert d == F.probe_poisson(P, DX, 0, DA) == F.probe_euler(P, DX, 0, DA)
    assert d == F.probe_poisson_s1(P, DX, DA) == F.probe_euler_s1(P, DX, DA)


def test_selection_census_of_small_triples():
    c = F.selection_census()
    assert {k: len(v) for k, v in c.items()} == {"off_class": 70, "on_class_empty_box": 9, "on_class_nonempty_box": 5}
    assert sorted(map(tuple, c["on_class_nonempty_box"])) == [(0, 0, 5), (0, 2, 1), (0, 3, 2), (1, 0, 5), (1, 3, 2)]
    assert sorted(map(tuple, c["on_class_empty_box"])) == sorted(F.PROBE_TRIPLES_EMPTY)


def test_probe_selection_rule(Pr):
    """The constants in m force deg s = deg A + xi_j (mod 6): (0,1,1) and (0,1,2) vanish."""
    assert F.probe_direct(Pr, 0, 1, 1).is_zero()
    assert F.probe_direct(Pr, 0, 1, 2).is_zero()


# ---------------------------------------------------------------------------
# Planted faults
# ---------------------------------------------------------------------------


def test_planted_gauss_sign_fault_turns_checks_red(S6, Pr):
    """A sign error in G_1 at the primes of degree 2 breaks the brute-force comparison and,
    through the pairing gamma_1 gamma_2 = -alpha conj(chi(4)) gamma_3, the j = 3 row of
    Lemma 7.1 (the J_3 term)."""
    S = S6
    P2 = S.P([1, 0, 1])  # T^2 + 1, degree 2
    u = P2 ** 3
    B = F.Bound(4, 1, 0)
    with F.planted("gauss_sign"):
        assert not F.gauss_brute(S, S.P([1]), 1, P2) == F.gauss_struct(S, S.P([1]), 1, P2)
        loc_d, loc_c = Pr.P_local_def(P2, u, B), Pr.P_local_closed(P2, u, B)
        # the second J_3 term, b_p^2 rho^-4 Q^(2-4x): (e0, l, k) = (1, 1, 0) carries gamma_1^-1
        assert loc_d.diff_keys(loc_c) == [(4, 0, 0)]
    assert F.gauss_brute(S, S.P([1]), 1, P2) == F.gauss_struct(S, S.P([1]), 1, P2)
    assert Pr.P_local_def(P2, u, B).equals(Pr.P_local_closed(P2, u, B))


def test_planted_symbol_faults_turn_checks_red(S6, Pr):
    S = S6
    P = S.P([1, 1])  # T + 1
    u = S.P([1])
    B = F.Bound(4, 1, 0)
    one = S.P([1])
    with F.planted("symbol"):
        assert not (F.symbol_table_res(S, P) == F.symbol_table_crt(S, P)).all()
        assert Pr.P_local_def(P, u, B).diff_keys(Pr.P_local_closed(P, u, B)) == [(0, 1, 0)]
        assert not Pr.K_def(P, one, one, one, one) == F.K_product(Pr, P, one, one, one, one)
    with F.planted("symbol_res"):
        assert not (F.symbol_table_res(S, P) == F.symbol_table_crt(S, P)).all()
        assert Pr.P_local_def(P, P, B).diff_keys(Pr.P_local_closed(P, P, B)) == [(1, 1, 0)]
    assert (F.symbol_table_res(S, P) == F.symbol_table_crt(S, P)).all()
    assert Pr.P_local_def(P, u, B).equals(Pr.P_local_closed(P, u, B))


PLANTS = ["gauss_sign", "gauss_brute_sign", "dh_sign", "prime_gauss_all", "tau_sign", "symbol", "symbol_res", "dlog"]


def _lesion_checks(PC) -> dict:
    """The quick equality checks every plant must be able to turn red, on fresh objects (a
    Probe caches g_xi(T, 1), tau and lambda when it is built)."""
    S = F.Setup(7, 6)
    Pr = F.Probe(S)
    one = S.P([1])
    mods = [S.P([1, 1]), S.P([2, 1]), S.P([1, 0, 1]), S.P([1, 1]) * S.P([3, 1]), S.P([1, 1]) ** 2]
    res = {"symbol_routes": all((F.symbol_table_res(S, c) == F.symbol_table_crt(S, c)).all() for c in mods)}
    dh = st = True
    for c in mods:
        for r in (one, S.P([3, 1])):
            for j in range(1, 6):
                g = F.gauss_brute(S, r, j, c)
                st &= g == F.gauss_struct(S, r, j, c)
                if F.is_squarefree(S, c) and r.gcd(c).degree() == 0:
                    dh &= g == F.gauss_dh(S, r, j, c)
    res["davenport_hasse"], res["structural"] = dh, st
    B = F.Bound(7, 1, 1)
    loc = True
    for P, js in ((S.P([1, 1]), range(6)), (S.P([1, 0, 1]), (0, 3))):
        for j in js:
            u = P ** j * S.P([3, 1])
            loc &= Pr.P_local_def(P, u, B).equals(Pr.P_local_closed(P, u, B))
    res["lemma_7_1"] = loc
    res["probe_direct_eq_euler"] = F.probe_direct(Pr, 0, 2, 1) == F.probe_euler(Pr, 0, 2, 1)
    pari_ok = True
    for c in mods[:4]:
        cc = [int(x) for x in c.coeffs()]
        pari_ok &= bool((PC.symbol_vector(cc, c.degree(), 7, 6) == F.symbol_table_res(S, c)).all())
        for j in (1, 2, 3):
            pari_ok &= PC.equal(PC.gauss([1], cc, 7, 6, j, 84), PC.to_pari(F.gauss_struct(S, one, j, c)))
            pari_ok &= PC.equal(PC.gauss([1], cc, 7, 6, j, 84), PC.to_pari(F.gauss_brute(S, one, j, c)))
    for j in range(1, 6):
        pari_ok &= PC.equal(PC.tau(7, 6, j, 84), PC.to_pari(S.tau(j)))
    res["pari_second_implementation"] = pari_ok
    return res


def test_the_lesion_checks_pass_without_a_plant(PC):
    res = _lesion_checks(PC)
    assert all(res.values()), res


#: which checks each plant turns red (measured, then pinned so that a change is noticed).
#: The Davenport-Hasse closed form of ``gauss_dh`` feeds nothing else (the structural route
#: has its own prime formula), so its sign is caught by that check alone.
_ALL6 = {"symbol_routes", "davenport_hasse", "structural", "lemma_7_1", "probe_direct_eq_euler",
         "pari_second_implementation"}
LESION_MATRIX = {
    "gauss_sign": {"structural", "lemma_7_1", "probe_direct_eq_euler", "pari_second_implementation"},
    "gauss_brute_sign": {"davenport_hasse", "structural", "probe_direct_eq_euler", "pari_second_implementation"},
    "dh_sign": {"davenport_hasse"},
    "prime_gauss_all": {"structural", "lemma_7_1", "probe_direct_eq_euler", "pari_second_implementation"},
    "tau_sign": _ALL6 - {"symbol_routes"},
    "symbol": _ALL6 - {"davenport_hasse"},
    "symbol_res": _ALL6,
    "dlog": _ALL6,
}


@pytest.mark.parametrize("plant", PLANTS)
def test_every_plant_turns_a_check_red(PC, plant):
    with F.planted(plant):
        res = _lesion_checks(PC)
    red = {k for k, v in res.items() if not v}
    assert red, f"{plant} left every check green"
    assert red == LESION_MATRIX[plant], (plant, sorted(red))


def test_planted_faults_break_the_probe_identity(Pr):
    with F.planted("symbol_res"):
        d = F.probe_direct(Pr, 0, 2, 1)
        e = F.probe_euler(Pr, 0, 2, 1)
        assert not d == e
    with F.planted("gauss_sign"):
        # a probe value whose sums meet a degree-2 prime: s of degree 2 includes T^2 + 1
        d = F.probe_direct(Pr, 0, 2, 1)
        e = F.probe_euler(Pr, 0, 2, 1)
        assert not d == e


# ---------------------------------------------------------------------------
# Step 3: the biquadratic theta over F_13[T]
# ---------------------------------------------------------------------------


def test_n4_base_values(S4):
    rho = _rho_cache(S4)
    one = S4.P([1])
    assert rho(one, 1, 0) == 1 and rho(one, 1, 1) == S4.tau(1) * 13
    assert rho(one, 1, 2).is_zero() and rho(one, 1, 3).is_zero()
    P = F.lin_poly(S4, 1)
    assert rho(P, 1, 0) == 1 and rho(P, 1, 2) == S4.tau(2) * 13 * 13
    assert rho(P, 1, 1).is_zero() and rho(P, 1, 3).is_zero()


def test_n4_unit_rule_and_both_additive_characters(S4):
    """rho_0(-r, i) = eps(chi(-1))^(-i) rho_0(r, i), and the Hecke relation at infinity holds
    in each additive character with its own sign (eps(chi(-1)) = -1 at q = 13, n = 4)."""
    rho = _rho_cache(S4)
    assert S4.eps_chi_minus1() == 2
    one = S4.P([1])
    assert rho(-one, 1, 1) == -rho(one, 1, 1)
    for r in [one, F.lin_poly(S4, 1), F.lin_poly(S4, 1) * F.lin_poly(S4, 2)]:
        rr = {i: rho(r, 1, i) for i in range(4)}
        rm = {i: rho(-r, 1, i) for i in range(4)}
        res = F.hecke_infinity_both(S4, r, 1, rr, rm)
        assert res["2007_character"][0] == res["2007_character"][1] == 4
        assert res["2014_character"][0] == res["2014_character"][1] == 4


def test_n4_degree_four_relation_has_q_not_q2(S4):
    """Patterson 2007, page 252, as extracted: C(r,3) = tau(eps) q^2 C(r,2) at degree 4; the
    Hecke relation at infinity gives q, and q is what holds."""
    L = lambda a: F.lin_poly(S4, a)
    r = L(1) * L(2) * L(3) * L(4)
    C2, C3 = F.C_fast(S4, r, 1, 2), F.C_fast(S4, r, 1, 3)
    assert not C2.is_zero()
    assert C3 == S4.tau(1) * 13 * C2
    assert not C3 == S4.tau(1) * 169 * C2


def test_n4_every_family_has_a_forced_zero_class(S4):
    """For n = 4 the family i = (b - deg r) mod 4 must vanish on deg r = 2b + 1 mod 4, an
    odd class, by R < 0 or by the Hecke relation at infinity (i = i')."""
    for b in range(4):
        for d in range(12):
            reason = F.zero_reason(S4, d, (b - d) % 4)
            if d % 4 == (2 * b + 1) % 4:
                assert reason is not None
            elif d % 2 == 0:
                assert reason != "i=i'"
    # n = 3: families 0 and 1 have none, family 2 is forced to vanish everywhere
    S = F.Setup(7, 3)
    assert [d for d in range(6) if F.zero_reason(S, d, (0 - d) % 3) == "i=i'"] == []
    assert [d for d in range(6) if F.zero_reason(S, d, (1 - d) % 3) == "i=i'"] == []
    assert all(F.zero_reason(S, d, (2 - d) % 3) is not None for d in range(6))
    # n = 2: both families vanish on odd degrees, the classical theta's support on squares
    S2 = F.Setup(7, 2)
    for b in (0, 1):
        assert all((F.zero_reason(S2, d, (b - d) % 2) is not None) == (d % 2 == 1) for d in range(1, 10))


def test_n4_degree_three_coefficient_is_hypergeometric_and_varies(S4):
    rho = _rho_cache(S4)
    vals = {}
    for lam in (3, 4, 5, 6):
        r = F.lin_poly(S4, 1) * F.lin_poly(S4, 2) * F.lin_poly(S4, lam)
        H = F.hypergeometric_sum(S4, r, 1)
        # with e = e_o(a_-1) the degree-one Gauss sums are tau(eps chi) conj(eps(chi(r(a))))
        assert rho(r, 1, 1) == F.C_fast(S4, r, 1, 1) == S4.tau(1) * H
        vals[lam] = str((H * H.conj()).p)
    assert len(set(vals.values())) > 1


# ---------------------------------------------------------------------------
# Step 5: the rival
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def rival(S6):
    return F.Rival(S6, F.CharModT3(S6, 2, 2, 2))


def test_rival_functional_equation_and_zeros_off_the_circle(S6, rival):
    c = rival.L
    assert c[1] == rival.eps * c[1].conj() and rival.eps * rival.eps.conj() == 1
    d = rival.poly()
    assert d[2] == d[0] * 7
    roots = F._roots_quadratic_arb(d)
    import flint
    sq = flint.arb(7).sqrt()
    mods = [abs(r) * sq for r in roots]
    assert any(m > 1 for m in mods) and any(m < 1 for m in mods)
    sig = sorted(float((-(abs(r).log()) / flint.arb(7).log()).mid()) for r in roots)
    assert abs(sig[1] - 1.0068553516) < 1e-8 and abs(sig[0] + sig[1] - 1) < 1e-9


def test_rival_local_identity_fails_at_the_degree_two_term(S6, rival):
    B = F.Bound(2, 0, 0)
    u = S6.P([1])
    Pr_r = F.Probe(S6, eta_fun=rival)
    lhs = F.high_series_def(Pr_r, u, B)
    rhs = F.euler_product(Pr_r, u, B, closed=True)
    assert lhs.diff_keys(rhs) == [(2, 0, 0)]
    Pr_c = F.Probe(S6, eta_fun=rival.chi)
    assert F.high_series_def(Pr_c, u, B).equals(F.euler_product(Pr_c, u, B, closed=True))


# ---------------------------------------------------------------------------
# Second implementation: PARI/GP
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def PC():
    import ffprobe_pari
    return ffprobe_pari


def test_pari_symbols_and_gauss_sums(PC, S6, S4):
    for S in (S6, S4):
        for c in [S.P([1, 0, 1]), S.P([1, 1]) * S.P([2, 1])]:
            for a in [S.P([3, 1]), S.P([2, 0, 1]), S.P([5])]:
                k = S.symbol_res(a, c)
                assert PC.symbol(a.coeffs(), c.coeffs(), S.q, S.n) == (-1 if k is None else k)
        P = S.P([1, 0, 1]) if S.q == 7 else S.P([2, 0, 1])
        assert F.mobius(S, P) == -1
        assert PC.symbol_frob([3, 1], P.coeffs(), S.q, S.n) == S.symbol_frob(S.P([3, 1]), P)
        for j in range(1, S.n):
            g = F.gauss_struct(S, S.P([1]), j, P)
            assert PC.equal(PC.gauss([1], P.coeffs(), S.q, S.n, j, S.N), PC.to_pari(g))
            assert PC.equal(PC.tau(S.q, S.n, j, S.N), PC.to_pari(S.tau(j)))


def test_pari_poisson_coefficient(PC, S6, Pr):
    """F(s, A, H) of eq. (local-F) recomputed in GP by its definition (both sums enumerated)."""
    S = S6
    for s_, A_, H_ in [([1], [1, 1], [3]), ([2, 1], [1, 1], [1]), ([1, 1], [3, 1], [2, 1]),
                       ([1, 0, 1], [2, 1], [5]), ([3, 1], [3, 1], [1, 1])]:
        s, A, H = S.P(s_), S.P(A_), S.P(H_)
        mine = Pr.F_def(s, A, H)
        assert PC.equal(PC.F_poisson(s.coeffs(), A.coeffs(), H.coeffs(), 7, 6, 84), PC.to_pari(mine))


def test_pari_local_coefficients_and_K(PC, S6, Pr):
    """Coefficients of P_p by their definition in GP against the closed form, and K by its
    definition in GP against ffprobe's product of local summands."""
    PP = PC.PariProbe()
    P = S6.P([1, 1])
    for j in (0, 2, 3, 5):
        u = P ** j * S6.P([3, 1])
        closed = Pr.P_local_closed(P, u, F.Bound(7, 1, 1))
        for (e0, l, k, m) in [(0, 0, 0, 1), (1, 0, 1, 0), (0, 1, 0, 0), (1, 1, 1, 1), (0, 2, 0, 1)]:
            v = PC.local_coefficient(PP, [1, 1], [int(x) for x in u.coeffs()], e0, l, k, m)
            assert PC.equal(v, PC.to_pari(closed.coeff((e0 + 3 * l, k, m)))), (j, e0, l, k, m)
    for c, n_, s, a, u in [([1, 1], [1], [1], [1], [1]), ([3, 0, 1], [1], [2, 1], [1], [3]),
                           ([1], [2, 1], [1], [1, 1], [1, 1]), ([1, 1], [2, 1], [3, 1], [1], [2, 1])]:
        mine = F.K_product(Pr, S6.P(c), S6.P(n_), S6.P(s), S6.P(a), S6.P(u))
        assert PC.equal(PP.K_def(c, n_, s, a, u), PC.to_pari(mine))


def test_pari_probe_direct_sum(PC, Pr):
    PP = PC.PariProbe()
    for trip in [(0, 2, 1), (0, 1, 1)]:
        assert PC.equal(PC.probe_direct(PP, *trip), PC.to_pari(F.probe_direct(Pr, *trip)))


def test_pari_theta_coefficients(PC, S3):
    T = S3.P([0, 1])
    for r in [S3.P([1]), T, T * F.lin_poly(S3, 1)]:
        for j in (1, 2):
            for i in range(3):
                mine = F.rho0(S3, r, j, i)[0]
                assert PC.equal(PC.rho0(r.coeffs(), 7, 3, j, i, 84), PC.to_pari(mine))


def test_pari_three_body_n4(PC, S4):
    for lam in (3, 4):
        r = F.lin_poly(S4, 1) * F.lin_poly(S4, 2) * F.lin_poly(S4, lam)
        assert PC.equal(PC.C(r.coeffs(), 13, 4, 1, 1, 52), PC.to_pari(F.C_fast(S4, r, 1, 1)))


def test_pari_rival_polynomial_and_roots(PC, S6, rival):
    """The rival's L-coefficients recomputed in GP from the character formula, and its roots."""
    pari = PC.pari
    gp = r"""
    chiT3(a, q, ee, al, be, N) = {
      my(a0 = lift(polcoef(a, 0)), a1 = lift(polcoef(a, 1)), a2 = lift(polcoef(a, 2)), xx, yy, g, k);
      if (a0 % q == 0, return(0));
      xx = a1 * lift(Mod(a0, q)^-1); yy = a2 * lift(Mod(a0, q)^-1);
      g = znprimroot(q); k = znlog(Mod(a0, q), g);
      Mod('z, polcyclo(N, 'z))^((N/6)*ee*k + (N/q)*lift(Mod(al*xx + be*(yy - xx^2/2), q)));
    }
    """
    PC._load(gp)
    f = pari("chiT3")
    q = 7
    Lc = []
    for d in range(3):
        acc = pari("Mod(0, polcyclo(84, 'z))")
        for coeffs in __import__("itertools").product(range(q), repeat=d):
            a = PC.poly(list(coeffs) + [1], q)
            acc = acc + f(a, q, 2, 2, 2, 84)
        Lc.append(acc)
    for d in range(3):
        assert PC.equal(Lc[d], PC.to_pari(rival.L[d]))
    # roots of the rival polynomial with PARI's own root finder, against the Arb enclosures
    d = rival.poly()
    num = pari("(P) -> subst(lift(P), 'z, exp(2*Pi*I/84))")
    coeffs = [num(PC.to_pari(x)) for x in d]  # PARI's own complex values, at its precision
    roots = pari.polroots(pari.Pol([coeffs[2], coeffs[1], coeffs[0]]))
    mods = sorted(abs(complex(r)) * math.sqrt(7) for r in roots)
    arb = sorted(float((abs(r) * __import__("flint").arb(7).sqrt()).mid()) for r in F._roots_quadratic_arb(d))
    assert all(abs(a - b) < 1e-9 for a, b in zip(mods, arb))


# ---------------------------------------------------------------------------
# The record: lexical rules and the pinned numbers in the documents
# ---------------------------------------------------------------------------

DOCS = ["MISSION.md", "SOURCES.md", "LOCAL_IDENTITY.md", "S4.md", "RIVAL.md", "RUNS.md"]


def test_lexical_rules_hold_in_this_hunt():
    banned = "cer" + "tif"  # spelled in two pieces so this file carries no such byte run
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".py", ".md", ".json"}:
            continue
        text = path.read_text(encoding="utf-8")
        assert banned not in text.lower(), path.name
        if path.suffix == ".md":
            assert chr(0x2014) not in text, f"em dash in {path.name}"


def test_documents_exist():
    for name in DOCS:
        assert (HERE / name).is_file(), name


# ---------------------------------------------------------------------------
# Pinned: the documents quote the results files
# ---------------------------------------------------------------------------


def _doc(name: str) -> str:
    return (HERE / name).read_text(encoding="utf-8")


def test_sources_page_quotes_results_step1():
    r = _results("step1")
    text = _doc("SOURCES.md")
    assert r["symbol_routes"] == {"disagree": 0, "max_deg": 3, "moduli": 399, "n": 3, "q": 7}
    assert "all 399 monic moduli of degree at most 3" in text
    dh = r["davenport_hasse"]
    for key, n_checked, mm07 in (("q7_n3", 34202, 0), ("q7_n6", 85505, 45129), ("q13_n4", 85683, 4394)):
        assert dh[key]["checked"] == n_checked
        assert dh[key]["mismatches"] == {"2014": 0, "2007_own_character": 0, "2007_with_2014_character": mm07}
    assert "34,202 at (q, n) = (7, 3), 85,505 at (7, 6), 85,683 at (13, 4)" in text
    for piece in ("45,129 of 85,505 at (7, 6)", "15,043 pairs (c, r) with deg c odd", "4,394 of 85,683 at (13, 4)",
                  "2,197 pairs), none at (7, 3)"):
        assert piece in text
    assert 45129 == 3 * 15043 and 4394 == 2 * 2197 and 2197 == 13 * 169  # odd j, and the pair counts
    assert 15043 == 7 * 49 + 35 * 36 + 147 * 48 + 112 * 57  # deg c = 1, then the three cubic types
    assert [dh[k]["nonsquarefree_checked"] for k in ("q7_n3", "q7_n6", "q13_n4")] == [350, 350, 169]
    assert all(dh[k]["nonsquarefree_zero"] == dh[k]["nonsquarefree_checked"] for k in dh)
    assert "350 cases at (7, 3), 350 at (7, 6), 169 at (13, 4)" in text
    assert r["structural_vs_brute"] == {"checked": 319200, "max_deg_c": 3, "max_deg_r": 3, "mismatches": 0}
    assert "319,200 cases" in text
    assert r["C_routes"] == {"checked": 56, "max_i": 3, "mismatches": 0} and "i at most 3: 56 cases" in text
    assert r["psi_polynomial"] == {"checked": 36, "vanish_above_R": 36} and "all 36 checked cases" in text
    hi = r["hecke_infinity"]
    assert hi["printed_2014"] == {"checked": 40, "hold": 20} and "40 checks at (7, 3)" in text and "20 of the 40" in text
    assert hi["printed_2007"] == {"checked": 60, "hold": 40} and "40 of 60 hold" in text
    assert hi["corrected"] == {"checked": 60, "hold": 60} and "60 checks at (7, 3)" in text
    hb = r["hecke_infinity_both"]
    assert all(v == {"checked": 30, "hold": 30} for k in hb for v in hb[k].values())
    assert "30 at (7, 3) and 30 at (7, 6) in each additive character" in text
    assert r["finite_hecke"] == {"checked": 72, "hold": 72, "vanish_at_r_o_P^(n-1)": [36, 36]}
    assert "72 cases and 36 vanishing cases" in text
    assert r["periodicity"] == {"checked": 24, "hold": 24} and "exact, 24 cases" in text
    assert r["affine_invariance"] == {"checked": 144, "hold": 144} and "all 144 checked cases" in text
    assert all(all(v.values()) for v in r["theta_base"].values())
    fam = r["cubic_theta_vs_gamma2"]
    assert all(rec["distinct_ratios"] == 1 for b in fam.values() for rec in b.values())
    assert all(rec["ratio"]["poly"] == "0" for rec in fam["b2"].values())


def test_local_identity_page_quotes_results_step2():
    r = _results("step2")
    text = _doc("LOCAL_IDENTITY.md")
    ph = r["phase_identities"]
    assert ph["reciprocity"] == {"checked": 2688, "mismatches": 0} and "2,688 pairs, no mismatch" in text
    assert ph["Gamma_closed_form"] == {"checked": 400, "mismatches": 0} and "400 moduli, no mismatch" in text
    assert ph["signal"] == {"checked": 343, "mismatches": {"G_squarefree": 0, "gamma1_gamma2": 0, "gamma2_cubed": 0}}
    assert "343 moduli, no mismatch in any of the three" in text
    assert ph["G_refinement_all_pairs"] == {"checked": 3249, "mismatches": 0} and "3,249 pairs, no mismatch" in text
    assert ph["prime_phases"] == {"checked": 27, "mismatches": 0} and "27 primes, no mismatch" in text
    assert r["F_routes"] == {"checked": 30576, "mismatches_vs_brute": {"def": 0, "local": 0}}
    assert "30,576 cases, no mismatch in either comparison" in text
    assert r["C_p_values"] == {"checked": 720, "mismatches": 0} and "720 values, no mismatch" in text
    k1, k2 = r["K_multiplicative"]
    assert (k1["checked"], k1["nonzero"], k1["mismatches"], k1["max_deg_A"], k1["max_deg_s"]) == (120344, 72319, 0, 3, 1)
    assert (k2["checked"], k2["nonzero"], k2["mismatches"], k2["max_deg_A"], k2["max_deg_s"]) == (44247, 29134, 0, 2, 2)
    assert len(k1["rows"]) == 8 and k2["rows"] == ["1", "3", "x + 1"]
    assert "120,344 and 44,247 tuples (72,319 and 29,134 of them nonzero), no mismatch" in text
    assert r["lemma_7_1_local"] == {"bound_deg1": [13, 3, 2], "bound_deg2": [13, 2, 2], "checked": 72, "mismatches": 0}
    assert "72 (prime, row) cases, every coefficient equal" in text
    probes = {tuple(x["triple"]): x for x in r["probe_representations"]}
    assert len(probes) == 16 and all(x["direct_eq_poisson"] and x["poisson_eq_euler"] for x in probes.values())
    nonzero = sorted(t for t, x in probes.items() if not x["zero"])
    assert nonzero == [(0, 2, 1), (0, 3, 2), (1, 3, 2), (3, 0, 5), (4, 0, 5)]
    assert all((t[1] - t[2] - 1) % 6 == 0 for t in nonzero)
    assert all((t[1] - t[2] - 1) % 6 != 0 for t, x in probes.items() if x["zero"])


def test_rival_page_quotes_results_rival():
    r = _results("rival")
    text = _doc("RIVAL.md")
    c = r["counts"]
    assert c["characters"] == 210 and c["functional_equation_holds"] == 210 and c["degenerate"] == 0
    assert c["with_zeros_off_circle"] == 66 and c["off_iff_disc_positive"]
    assert "210" in text and "66 of the 210" in text
    ex = r["example"]
    assert (ex["e"], ex["alpha"], ex["beta"]) == (2, 2, 2)
    assert all(ex["off_circle_by_enclosure"])
    s_hi, s_lo = sorted(ex["sigma"], reverse=True)
    assert f"{s_hi:.8f}" == "1.00685535" and "1.00685535" in text
    assert f"{-s_lo:.8f}" == "0.00685535" and "-0.00685535" in text
    assert abs(s_hi + s_lo - 1) < 1e-9
    m = sorted(ex["root_abs_times_sqrtq"])
    assert f"{m[0]:.5f}" == "0.37296" and f"{m[1]:.5f}" == "2.68128"
    # the distribution of the larger abscissa
    from collections import Counter
    cnt = Counter(round(max(x["sigma"]), 4) for x in r["scan"] if any(x.get("off_circle_by_enclosure", [])))
    table = dict(re.findall(r"^\| (\d\.\d{4}) \| (\d+) \|$", text, flags=re.M))
    assert {float(k): int(v) for k, v in table.items()} == dict(cnt)
    assert sum(v for k, v in cnt.items() if k > 1) == 50 and "50 of the 66" in text
    assert r["largest_sigma_not_above_1"] < 0.8696 and "0.8695" in text
    li = r["local_identity"]
    assert li["chi"]["mismatched_monomials"] == [] and li["chi"]["bound"] == [3, 1, 0]
    assert li["rival"]["first_mismatch"] == [2, 0, 0]
    assert li["rival"]["mismatched_monomials"] == [[2, 0, 0], [2, 1, 0], [3, 0, 0], [3, 1, 0]]
    assert f"{li['rival']['lhs_at_first']['abs']:.4f}" == "3.7170" and "3.7170" in text
    assert f"{li['rival']['rhs_at_first']['abs']:.4f}" == "20.5502" and "20.5502" in text
    nm = r["non_multiplicative_at"]
    assert f"{nm['d_P1P2']['abs']:.4f}" == "2.4661" and f"{nm['d_P1_d_P2']['abs']:.4f}" == "0.1702"


def test_s4_page_quotes_results_step3():
    r = _results("step3")
    text = _doc("S4.md")
    bv = r["base_values"]
    assert all(bv.values())
    assert r["relations"]["finite_hecke"] == {"checked": 36, "hold": 36} and "all 36" in text
    hb = r["hecke_infinity_both"]
    assert hb["2007_character"] == {"checked": 20, "hold": 20} == hb["2014_character"]
    assert "all 20 checked cases in each" in text
    rel = r["patterson_n4_relations"]["e_o(a_-1)"]
    assert all(rel["deg2_C2_eq_tau_q_C1_epschi(-1)"]) and all(rel["deg2_C3_eq_tau3_q3"])
    assert all(rel["deg3_C3_eq_tau2_q2_C1"]) and not any(rel["deg4_C3_eq_tau_q2_C2"])
    census = r["degree3_census"]
    assert census["squarefree_monic_degree_3"] == 2028 and "2028" in text
    cc = census["abs2_H_counts_by_factorization_type"]
    assert cc == {"1+1+1: 0": 234, "1+1+1: 52": 52, "1+2: 0": 546, "1+2: 26": 468, "3: 13": 728}
    for row in ("| three linear primes (286) | 234 | 52 | 52 |",
                "| linear times irreducible quadratic (1014) | 546 | 468 | 26 |",
                "| irreducible cubic (728) | 0 | 728 | 13 |"):
        assert row in text
    mb = r["moduli_by_lambda"]
    assert mb["single"] == {"0": ["1"], "1": ["0"], "2": [str(13 ** 5)], "3": ["0"]}
    assert mb["pair"] == {"0": ["1"], "1": [str(13 ** 2)], "2": [str(13 ** 5)], "3": [str(13 ** 7)]}
    nonzero = sorted(int(l) for l, v in mb["triple"]["1"].items() if v != "0")
    assert nonzero == [5, 11] and mb["triple"]["1"]["5"] == "676"
    hyp = {h["lambda"]: h for h in r["hypergeometric"]}
    assert all(h["C1_equals_tau_times_H"] and h["rho0_i1_equals_C1"] for h in hyp.values())
    assert hyp[5]["abs2_exact"] == "52" and hyp[11]["abs2_exact"] == "52"
    ct = r["component_table"]
    assert ct["3,0"]["forced"] == "i=i'" and ct["3,2"]["forced"] == "i=i'" and ct["1,1"]["forced"] == "i=i'"
    assert ct["3,1"]["abs"] == [0.0, 26.0, 18.384776]
    assert "| 3 | 0 (i = i') | 0, 26, 18.38 | 0 (i = i') | 0, 15842.79, 11202.55 |" in text


def test_ledger_numbers_quoted():
    r = _results("ledger")
    text = _doc("LOCAL_IDENTITY.md")
    assert r["F_abs2_generic"] == {"checked": 417, "equal_q_times_qA": 417} and "417" in text
    fr = r["F_vs_elementary_bound"]
    assert abs(fr["max_ratio"] - 7 ** -0.5) < 1e-12 and fr["nonzero_cases"] == 63870 and "63,870" in text
    circ = r["principal_correction"]["circles"]
    assert r["principal_correction"]["prime_degree_cutoff"] == 6
    for key, shown in (("7/8", "0.199"), ("5/6", "0.210"), ("3/4", "0.246"), ("17/24", "0.277")):
        assert f"{circ[key]['max_abs_H_minus_1']:.3f}" == shown and shown in text
    assert r["target_L"]["abs2_c1_equals_q"] and r["target_L"]["degree_one"]
    bal = r["balanced_probe"]
    assert all(b["direct_eq_euler"] for b in bal)
    assert f"{bal[0]['abs_I_paper_normalization']:.3f}" == "1.529" and "1.529" in text
    assert f"{bal[1]['abs_I_paper_normalization']:.3f}" == "0.609" and "0.609" in text
    walls = r["template_walls"]
    assert walls["6"] == {"balanced": "11/12", "corner": "7/8", "floor": "13/15"}
    assert walls["4"] == {"balanced": "7/8", "corner": "13/16", "floor": "4/5"}
    assert F.template_walls(6)["corner"] == Fraction(7, 8) and F.template_walls(4)["corner"] == Fraction(13, 16)


def test_leading_terms_of_the_correction(S6, Pr):
    """H_p - 1 at p = T + 1, u = 1, from the closed form: the five leading monomials of
    LOCAL_IDENTITY.md section 3, item 4, with their exact squared moduli."""
    S, K = S6, S6.K
    P, u = S.P([1, 1]), S.P([1])
    B = F.Bound(6, 1, 1)
    j, rho, om, eta_p, a_p, b_p = Pr.local_params(P, u)
    one = F.Series.const(K, 3, B, K.one)
    V = F.Series.mono(K, 3, B, (0, 0, 1), K.one)
    W = F.Series.mono(K, 3, B, (0, 1, 0), Pr.chi_val(P, u))
    D = F.Series.mono(K, 3, B, (1, 0, 0), eta_p * Pr.chi_val(P, u).conj())
    H = Pr.P_local_closed(P, u, B) * (one - V) * (one - W) * D.geometric()
    t = (H - one).terms
    abs2 = {e: (c * c.conj()).rational() for e, c in t.items()}
    assert abs2[(0, 1, 1)] == abs2[(1, 0, 1)] == abs2[(1, 1, 0)] == 1  # Q^(-w-6z), Q^(-x-6z), Q^(-x-w)
    assert abs2[(1, 1, 1)] == 64                                       # (Q + 1)^2: the Q^(1-x-w-6z) term
    assert abs2[(6, 0, 1)] == 4233649                                  # about Q^8: the Q^(4-6x-6z) term
    lowest = min(sum(e) for e in t)
    assert {e for e in t if sum(e) == lowest} == {(0, 1, 1), (1, 0, 1), (1, 1, 0)}


def test_norm2_of_zero():
    """crosscheck.norm2 at an exact zero: PARI's poldegree(0) is -oo, which crashed the s4
    item of the 2026-10-26 run (RUNS.md) before this guard."""
    import crosscheck as CC

    assert CC.norm2(CC.pari("Mod(0, polcyclo(12, z))"), 12) == 0
    assert CC.norm2(CC.pari("Mod(z, polcyclo(12, z))"), 12) == 1


def test_second_implementation_reproduces_the_primary_numbers():
    """results_second.json (crosscheck.py, PARI) against the primary results files: the
    counts each side records must be equal, and the only rows short of their checked count
    are the four source errata of SOURCES.md rows 2, 8 and 9, reproduced exactly."""
    import render_verification as RV

    sec = _results("second")
    s1, s2, s3 = _results("step1"), _results("step2"), _results("step3")
    led, rv = _results("ledger"), _results("rival")
    for key in ("q7_n3", "q7_n6", "q13_n4"):
        a, b = sec["davenport_hasse"][key], s1["davenport_hasse"][key]
        assert a["mismatches"] == b["mismatches"]
        if a["max_deg"] == b["max_deg"]:
            assert a["checked"] == b["checked"]
    assert sec["rho0_relations"]["hecke_infinity"] == s1["hecke_infinity"]
    assert sec["structural"]["checked"] == sec["structural"]["agree"] == s1["structural_vs_brute"]["checked"] == 319200
    assert sec["F_routes"]["checked"] == s2["F_routes"]["checked"] == 30576
    assert sec["C_p"]["checked"] == sec["C_p"]["agree"] == s2["C_p_values"]["checked"] == 720
    for a, b in zip(sec["K"]["specs"], s2["K_multiplicative"]):
        assert a["checked"] == a["agree"] == b["checked"] and a["nonzero"] == b["nonzero"]
    assert sec["lemma"]["cases"] == s2["lemma_7_1_local"]["checked"] == 72
    assert sec["lemma"]["agree"] == sec["lemma"]["coefficients"]
    triples = {k: v for k, v in sec["probe"].items() if k[0].isdigit()}
    assert all(v.get("equal_to_stored", v.get("frequency_box_empty")) for v in triples.values())
    assert all(b["abs_I_paper_normalization"] == pytest.approx(b["stored"], rel=1e-12)
               for b in sec["probe"]["balanced"])
    assert sec["ledger"]["F_abs2_generic"] == led["F_abs2_generic"]
    assert sec["ledger"]["F_vs_elementary_bound"]["nonzero_cases"] == led["F_vs_elementary_bound"]["nonzero_cases"]
    assert sec["ledger"]["F_vs_elementary_bound"]["max_ratio"] == pytest.approx(7 ** -0.5, rel=1e-12)
    for k in ("characters", "functional_equation_holds", "with_zeros_off_circle", "off_iff_disc_positive"):
        assert sec["rival"][k] == rv["counts"][k]
    assert sec["rival"]["beyond_one"] == 50
    assert sec["rival"]["local_identity"]["rival"]["mismatched"] == rv["local_identity"]["rival"]["mismatched_monomials"]
    assert sec["rival"]["local_identity"]["chi"]["mismatched"] == []
    assert sec["s4"]["degree3_census"] == s3["degree3_census"]
    assert sec["s4"]["moduli_by_lambda"] == s3["moduli_by_lambda"]
    assert sec["s4"]["relations"] == s3["relations"]
    for k, v in s3["three_body"].items():
        w = sec["s4"]["three_body"][k]
        assert (w["defect"], w["all_equal_one"]) == (v["defect"], v["all_equal_one"])
    # three_body "not all one" is S4.md's defect itself, a finding; the s4 Hecke row at
    # infinity is the n = 3 sign fit tried at n = 4 (step3's relations_note), 10 of 20 there too
    short = {(item, ".".join(p)) for item in sec for p, _, _, ok in RV.rows(sec[item])
             if not ok and not (item == "s4" and p[0] == "three_body")}
    assert short == {
        ("s4", "relations.hecke_infinity_corrected.hold"),
        ("davenport_hasse", "q13_n4.mismatches.2007_with_2014_character"),
        ("davenport_hasse", "q7_n6.mismatches.2007_with_2014_character"),
        ("rho0_relations", "hecke_infinity.printed_2007.hold"),
        ("rho0_relations", "hecke_infinity.printed_2014.hold"),
    }
    assert RV.main(["--check"]) == 0
