"""Referee lane of hunt #136: tests for `local_identity_pari.py`.

Every number REFEREE_W1.md quotes is pinned here.  All equalities are exact, in
cyclotomic fields held by PARI/GP through cypari2.  The two planted faults required by
the task (a wrong Gauss-sum sign, a wrong local factor) have tests that assert the
checks go red, alongside the tests that assert the true objects pass.

Run from the worktree root:
    .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/referee
The `slow` tier extends boxes and adds norm 31 (the verifier's prime).
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import local_identity_pari as L  # noqa: E402

NORMS = {7: (7, 0), 13: (13, 0), 19: (19, 0), 25: (5, 0)}
BOX = L.Box(13, 2, 4)

_LD: dict = {}


def local_data(norm: int, **kw) -> L.LocalData:
    key = (norm, tuple(sorted(kw.items())))
    if key not in _LD:
        _LD[key] = L.LocalData(L.FPrime(*NORMS[norm]), **kw)
    return _LD[key]


# ---------------------------------------------------------------------------
# the source
# ---------------------------------------------------------------------------

def test_paper_is_the_pinned_source():
    if not L.PAPER_PATH.is_file():
        pytest.skip("paper.tex cache not present on this machine")
    assert L.paper_sha256() == L.PAPER_SHA256


@pytest.mark.parametrize("line, label", [
    (766, r"\label{lem:prime-gauss-identities}"),
    (965, r"\label{eq:signal}"),
    (3892, r"\label{eq:local-scalar-definition}"),
    (3900, r"\label{eq:local-scalar-values}"),
    (3997, r"\label{eq:local-P}"),
    (4010, r"\label{lem:local-euler}"),
    (4013, r"\label{old-eq:5.13a}"),
    (4043, r"\label{eq:probe-high}"),
    (4139, r"\label{eq:local-H-defect}"),
    (591, "finite set $S$ of prime ideals containing the primes above $6$"),
    (6725, r"$\mathfrak a\mapsto\chi(N\mathfrak a)$"),
    (580, "images are the six units"),
    (953, r"$G(v^2)=\chi_v(4)$"),
    (3349, "Let $b_*$ generate the squarefree product of the primes in $S$."),
    (3367, r"gives $|\tau|=1$."),
    (3742, r"\label{eq:local-F}"),
    (3755, "At the primes of $b_*$ the primitive Gauss sum vanishes unless"),
    (3815, r"\label{eq:local-full-coefficient}"),
    (3878, r"g_{\chi_p^r}(p^t,p^{j'})="),
    (3886, r"$G_1G_{-1}=\omega_pQ$."),
    (3953, "Cancellation of the remaining pair phases."),
    (3994, r"The coefficient in Equation~\eqref{eq:local-full-coefficient}"),
    (4055, r"\label{eq:local-region-one}"),
    (4057, r"\label{eq:local-region-two}"),
    (4079, r"$\gamma_3^2=\omega_p$"),
    (4086, r"\label{eq:local-family-table}"),
    (4117, r"\gamma_1\gamma_2"),
    (4120, r"\frac{\gamma_4}{\gamma_1}"),
    (4124, r"$\gamma_2\gamma_4=1$"),
    (3416, r"\overline{G(A)}=\sum_{\theta\in\widehat T}a_\theta\theta(A)"),
    (4002, r"\omega_p^{tk-e_0l-l(l-1)/2}"),
    (4148, r"For $p\nmid u$ and $\vartheta=(-w_r)_+$"),
    (4185, r"the asserted $O(P_0^{-4/5})$ estimate"),
    (841, r"\label{lem:quadratic-four-term}"),
    (954, r"\label{eq:fixed-gauss-phases}"),
])
def test_cited_lines_say_what_the_report_says(line, label):
    if not L.PAPER_PATH.is_file():
        pytest.skip("paper.tex cache not present on this machine")
    window = "\n".join(L.paper_lines(line - 1, line + 1))
    assert label in window


def test_gamma_2_gamma_4_is_cited_at_line_4124():
    """Corrected citation: gamma_2 gamma_4 = 1 is stated on line 4124; line 4122 closes the display."""
    if not L.PAPER_PATH.is_file():
        pytest.skip("paper.tex cache not present on this machine")
    assert r"$\gamma_2\gamma_4=1$" in L.paper_lines(4124, 4124)[0]
    assert L.paper_lines(4122, 4122)[0].strip() == r"\]"
    assert "gamma_2 gamma_4 = 1 (line 4124)" in L.lemma_4_2_checks(L.FPrime(7))


def test_lemma_numbers_follow_the_environment_order():
    """Lemmas 4.1-4.4 open section 4 in order; lem:local-euler is section 7's only one (inferred numbering)."""
    if not L.PAPER_PATH.is_file():
        pytest.skip("paper.tex cache not present on this machine")
    lines = L.paper_lines(1, 16677)
    envs = ("\\begin{lemma}", "\\begin{proposition}", "\\begin{theorem}", "\\begin{corollary}", "\\begin{definition}")
    sec4 = [i + 1 for i in range(556, 1647) if lines[i].lstrip().startswith(envs)]
    assert sec4[:4] == [646, 766, 841, 934]
    sec7 = [i + 1 for i in range(3722, 4200) if lines[i].lstrip().startswith(envs)]
    assert sec7 == [4010]


# ---------------------------------------------------------------------------
# infrastructure: the residue symbol and the field arithmetic
# ---------------------------------------------------------------------------

def test_primary_generators_and_symbols():
    p7, p13, p19, p25, p31 = (L.FPrime(7), L.FPrime(13), L.FPrime(19), L.FPrime(5), L.FPrime(31))
    assert (p7.pi, p13.pi, p19.pi, p25.pi, p31.pi) == ((1, 3), (4, 3), (-2, 3), (-5, 0), (1, 6))
    assert L.FPrime(7, 1).pi == (-2, -3) and L.omul((1, 3), (-2, -3)) == (7, 0)
    assert [p.omega_p() for p in (p7, p13, p19, p25, p31)] == [-1, 1, -1, 1, -1]
    assert [p.sym((4, 0)) for p in (p7, p13, p19, p25, p31)] == [4, 2, 2, 0, 0]
    # the symbol is a character: chi(xy) = chi(x) chi(y) on all residues mod p
    for p in (p7, p25):
        res = [x for x in p.residues if p.sym(x) is not None]
        for x in res:
            for y in res:
                assert p.sym(L.omul(x, y)) == (p.sym(x) + p.sym(y)) % 6


def test_python_trace_and_product_agree_with_pari():
    for x, y in [((3, 5), (-2, 7)), ((10, -4), (1, 3)), ((-5, 0), (2, 4))]:
        prod = L.omul(x, y)
        assert L.pari.nfeltmul(L.NF, L.pari_elt(x), L.pari_elt(y)) == L.pari_elt(prod)
        assert int(L.pari.nfelttrace(L.NF, L.pari_elt(x))) == L.otrace(x)
        assert int(L.pari.nfeltnorm(L.NF, L.pari_elt(x))) == L.onorm(x)


def test_conjugation_and_embedding():
    c = L.Cyc(84)
    x = c.root(5, 84) + 3 * c.root(1, 7) - c.root(1, 6) / 2
    assert c.conj(x) == L.pari.Mod(L.pari.subst(L.pari.lift(x), L.ZV, L.ZV ** 83), c.Phi)
    big = L.Cyc(420)
    assert c.embed(x, big) == L.pari.Mod(L.pari.subst(L.pari.lift(x), L.ZV, L.ZV ** 5), big.Phi)


# ---------------------------------------------------------------------------
# (1) the Gauss-sum inputs: Lemma 4.2 and Equation (4.7)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("ell", [7, 13, 19, 5])
def test_lemma_4_2(ell):
    res = L.lemma_4_2_checks(L.FPrime(ell))
    assert len(res) == 21
    assert all(res.values()), [k for k, v in res.items() if not v]


@pytest.mark.parametrize("prime_args", [
    [(7, 0)], [(7, 0), (7, 1)], [(7, 0), (13, 0)], [(13, 0), (5, 0)], [(19, 0), (19, 1)], [(7, 0), (5, 0)],
])
def test_equation_4_7(prime_args):
    res = L.equation_4_7_checks([L.FPrime(*a) for a in prime_args])
    assert all(res.values()), [k for k, v in res.items() if not v]


@pytest.mark.slow
def test_equation_4_7_three_primes():
    res = L.equation_4_7_checks([L.FPrime(7), L.FPrime(13), L.FPrime(19)])
    assert all(res.values())


@pytest.mark.parametrize("ell, t_max", [(7, 3), (13, 2), (19, 2), (5, 2)])
def test_lift_against_direct_summation(ell, t_max):
    res = L.lift_checks(L.FPrime(ell), t_max)
    assert len(res) == sum(6 * (t + 2) for t in range(1, t_max + 1))
    assert all(res.values())


@pytest.mark.slow
@pytest.mark.parametrize("ell, t_max", [(7, 4), (13, 3), (5, 3)])
def test_lift_against_direct_summation_deeper(ell, t_max):
    assert all(L.lift_checks(L.FPrime(ell), t_max).values())


@pytest.mark.parametrize("ell, t_max", [(7, 3), (13, 2), (19, 2), (5, 3)])
def test_four_term_formula_and_equation_4_6(ell, t_max):
    res = L.four_term_checks(L.FPrime(ell), t_max)
    assert all(res.values()), [k for k, v in res.items() if not v]


# ---------------------------------------------------------------------------
# (1) the local scalar and Lemma 7.1's closed form
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("ell, T, K, J, D", [
    (7, 13, 3, 29, 2), (13, 13, 2, 29, 1), (19, 13, 2, 29, 1), (5, 13, 2, 29, 1),
])
def test_local_scalar_table(ell, T, K, J, D):
    """C_p by definition (local-scalar-definition) equals the paper's table, every key."""
    res = L.scalar_table_checks(L.FPrime(ell), T, K, J, direct_t_max=D)
    assert len(res) == (T + 1) * (K + 1) * (J + 1)
    assert all(res.values())


@pytest.mark.parametrize("norm", [7, 13, 19, 25])
def test_lemma_7_1_closed_form(norm):
    """(local-P) = old-eq:5.13a through t <= 13, k <= 2, m <= 4, all six rows, all six rho."""
    ld = local_data(norm)
    checked = 0
    for j in range(6):
        for rk in range(6):
            assert L.lemma_7_1_identity(ld, j, rk, BOX) == [], (norm, j, rk)
            checked += 1
    assert checked == 36


def test_identity_is_not_vacuous():
    ld = local_data(7)
    sizes = [len(L.series_local_P(ld, j, 2, BOX)) for j in range(6)]
    assert sizes == [28, 24, 26, 28, 26, 26]
    num, _ = L.closed_form_numerator(ld, 0, 1)
    assert len(num) == 11


def test_lemma_7_1_is_homogeneous_in_eta():
    """Every monomial X^t carries eta^t, so eta = 1 suffices; eta = zeta_12^5 and 2 agree."""
    p = L.FPrime(7)
    for eta in (L.Cyc(84).root(5, 12), 2 * L.Cyc(84).one):
        ld = L.LocalData(p, eta=eta)
        assert all(L.lemma_7_1_identity(ld, j, 3, BOX) == [] for j in range(6))


@pytest.mark.parametrize("norm", [7, 13, 19, 25])
def test_raw_coefficient_matches_the_phase_bookkeeping(norm):
    """gamma_2^e0 conj(alpha)^t conj(G(p^t)) R(p^t,p^k) rho^(k-t) C_p equals (local-P)'s summand."""
    ld = local_data(norm)
    for j in range(6):
        for rk in (0, 1, 2, 5):
            assert L.raw_vs_series(ld, j, rk, L.Box(13, 2, 3)) == [], (norm, j, rk)


@pytest.mark.parametrize("norm", [7, 13, 19, 25])
def test_hp_defect_formula_and_the_minus_D_cancellation(norm):
    ld = local_data(norm)
    for j in range(6):
        for rk in range(6):
            h = L.hp_checks(ld, j, rk, BOX)
            assert h["defect formula (local-H-defect)"]
            assert h["no X^1 term in H_p - 1 (the -D cancellation)"]


def test_analytic_bookkeeping():
    for eps0 in (Fraction(1, 1000), Fraction(1, 50), Fraction(1, 10)):
        r = L.analytic_claims(eps0)
        for j in range(6):
            assert r[j]["region one ok"] and r[j]["region two ok"], (eps0, j)
    r10 = L.analytic_claims(Fraction(1, 10))
    assert [r10[j]["region one max"] for j in range(6)] == [
        Fraction(-11, 10), Fraction(-11, 10), Fraction(-3, 100), Fraction(-1, 25), Fraction(-1, 10), Fraction(-3, 50)]
    r = L.analytic_claims(Fraction(1, 1000))
    assert r[0]["region one max"] == Fraction(-1001, 1000)
    assert r[1]["region one max"] == Fraction(-1001, 1000)
    assert r[0]["region two max"] == Fraction(-363, 200) and r[0]["region two closest"] == (2, 1, 1, 1)
    for j in (2, 3, 4, 5):
        assert r[j]["region two max"] == Fraction(-33, 40) and r[j]["region two closest"] == (2, 1, 1, 0)
        assert r[j]["region one max"] == Fraction(-1, 1000)
    assert r["tail exponent 1 - 363/200"] == Fraction(-163, 200)
    assert r["tail implies c_H = 4/5"]


# ---------------------------------------------------------------------------
# (1) the global coefficient: separation into prime factors and its local factor
# ---------------------------------------------------------------------------

def test_s_prime_claims():
    for extra in ((), (5,)):
        res = L.s_prime_claims(L.GlobalData(extra))
        assert all(res.values()), [k for k, v in res.items() if not v]


@pytest.mark.parametrize("j", [0, 1, 2])
def test_global_coefficient_matches_local_summand(j):
    cases = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1),
             (3, 0, 0), (3, 0, 1), (3, 1, 1), (0, 2, 0)]
    for u0 in (0, 1):
        res = L.global_vs_local(L.FPrime(7), u0, j, cases)
        assert all(ok for ok, _ in res.values()), (j, u0, res)
        assert sum(nz for _, nz in res.values()) == {0: 6, 1: 4, 2: 5}[j]


def test_global_coefficient_matches_local_summand_other_primes():
    cases = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 1, 1)]
    for ell in (13, 5):
        for j in (0, 1):
            res = L.global_vs_local(L.FPrime(ell), 1, j, cases)
            assert all(ok for ok, _ in res.values()), (ell, j, res)


@pytest.mark.slow
@pytest.mark.parametrize("j", [3, 4])
def test_global_coefficient_rows_three_and_four(j):
    cases = [(3, 1, 0), (4, 0, 0), (4, 1, 0)]
    res = L.global_vs_local(L.FPrime(7), 0, j, cases)
    assert all(ok for ok, _ in res.values()), res


@pytest.mark.parametrize("a, b", [((7, 0), (7, 1)), ((7, 0), (13, 0)), ((7, 0), (5, 0))])
def test_separation_into_prime_factors(a, b):
    p, q = L.FPrime(*a), L.FPrime(*b)
    chi4 = lambda n, cyc: (1 if n % 4 == 1 else -1) * cyc.one  # noqa: E731
    for u in (L.ONE, L.UNITS6[1], p.pi):
        for eta in (None, chi4):
            out, _ = L.separation_checks(p, q, u, [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0)], eta_dirichlet=eta)
            assert all(K == prod for K, prod in out.values())
            assert sum(1 for K, _ in out.values() if K != 0) >= 6


# ---------------------------------------------------------------------------
# planted faults: each must turn checks red
# ---------------------------------------------------------------------------

def test_planted_fault_wrong_gauss_sum_sign():
    """G_1 -> -G_1: Lemma 4.2 and the raw check go red at every row; the closed-form
    identity goes red at rows 3 and 4 only, where gamma_1 meets a Gauss sum other than G_1."""
    p = L.FPrime(7)
    res = L.lemma_4_2_checks(p, fault="gauss_sign")
    assert sorted(k for k, v in res.items() if not v) == sorted([
        "gamma_1 gamma_2 = conj(H(4)) gamma_3 gamma_2^3",
        "tau(H^1) tau(conj H^1) = H^1(-1) P",
        "tau(H^5) tau(conj H^5) = H^5(-1) P",
        "G_1 G_{-1} = omega_p Q (line 3886)",
        "gamma_1 gamma_2 = -alpha(p) conj(chi_p(4)) gamma_3 (line 4117)",
        "gamma_4/gamma_1 = -conj(alpha(p))/G(p) (line 4120)",
    ])
    ldf = L.LocalData(p, gauss_fault="gauss_sign")
    assert [j for j in range(6) if L.lemma_7_1_identity(ldf, j, 1, BOX)] == [3, 4]
    assert all(L.raw_vs_series(ldf, j, 1, L.Box(7, 1, 2)) for j in range(6))
    assert not all(L.lift_checks(p, 1).values()) is False  # the lift check itself uses true sums


def test_planted_fault_gauss_sign_reaches_the_lift_comparison():
    p = L.FPrime(7)
    G = L.gauss_sums(p, p.small_field(), fault="gauss_sign")
    res = L.scalar_table_checks(p, 4, 1, 6, G=G, direct_t_max=2)
    # the table uses the faulty G_1 on its k = 1 line; definition-by-direct-sum does not
    assert not all(res.values())


def test_planted_fault_wrong_local_factor():
    """R built from a_p instead of a_p^2: every row fails, first at (6,0,1) and (6,1,1)."""
    ld = local_data(7)
    for j in range(6):
        diff = L.lemma_7_1_identity(ld, j, 1, BOX, fault="local_factor")
        assert diff[:2] == [(6, 0, 1), (6, 1, 1)], (j, diff[:4])


def test_other_local_factor_faults_fire():
    ld = local_data(7)
    assert [j for j in range(6) if L.lemma_7_1_identity(ld, j, 1, BOX, fault="J2_rho")] == [2]
    assert all(L.lemma_7_1_identity(ld, j, 1, BOX, fault="one_minus_Qinv") for j in range(6))


def test_planted_fault_unconjugated_euler_factor():
    ld = local_data(7)
    caught = [rk for rk in range(6)
              if not L.hp_checks(ld, 0, rk, BOX, fault="D_unconjugated")["no X^1 term in H_p - 1 (the -D cancellation)"]]
    assert caught == [1, 2, 4, 5]  # invisible exactly when rho = conj(rho)
    r = L.analytic_claims(Fraction(1, 1000), fault="D_unconjugated")
    assert not r[0]["region one ok"] and r[0]["region one max"] == Fraction(-51, 100)


# ---------------------------------------------------------------------------
# (2) rivals
# ---------------------------------------------------------------------------

def test_rival_values():
    cyc = L.Cyc(420)
    k = L.dh_kappa(cyc)
    assert abs(cyc.number(k) - 0.2840790438404123) < 1e-15
    assert L.dh_coefficient(7, cyc) == k and L.dh_coefficient(343, cyc) == -k
    assert L.dh_coefficient(49, cyc) == -cyc.one and L.dh_coefficient(7 ** 6, cyc) == -cyc.one
    assert L.dh_coefficient(13 ** 6, cyc) == -cyc.one
    ns = [1, 4, 6, 7, 49, 343, 2401, 19, 361, 6859, 5, 2, 91, 133, 589, 16807, 117649]
    assert len(ns) == 17
    for n in ns:
        assert L.epstein_count(n) == 2 * L.epstein_coefficient(n), n
    assert [L.epstein_coefficient(7 ** t) for t in range(7)] == [1, 0, 1, 0, 1, 0, 1]
    assert [L.epstein_coefficient(19 ** t) for t in range(7)] == [1, 2, 3, 4, 5, 6, 7]
    assert L.epstein_coefficient(13 ** 6) == 1 and L.epstein_coefficient(31 ** 6) == 7
    assert abs(cyc.number(k) ** 2 - 0.0807009) < 1e-7
    # (19, 31): the coefficients themselves are multiplicative there, for both rivals
    c60 = L.Cyc(60)
    for name in ("DH", "Epstein-15"):
        f = L.rival_coefficient(name)
        assert f(19 * 31, c60) == f(19, c60) * f(31, c60)


@pytest.mark.parametrize("name, ell, multiplicative", [
    ("DH", 7, False), ("DH", 13, False), ("DH", 19, True), ("DH", 31, True),
    ("Epstein-15", 7, False), ("Epstein-15", 13, False), ("Epstein-15", 19, False), ("Epstein-15", 31, False),
])
def test_rival_prime_powers(name, ell, multiplicative):
    rows = L.rival_prime_powers(name, ell, 13)
    assert all(eq for (_, _, eq) in rows.values()) == multiplicative


FIRST_DH = [(6, 0, 1), (6, 0, 1), (3, 0, 0), (3, 1, 0), (4, 1, 0), (6, 0, 0)]
FIRST_E7 = [(6, 0, 1), (6, 0, 1), (6, 0, 1), (4, 0, 0), (4, 1, 0), (6, 0, 0)]


@pytest.mark.parametrize("name, ell, firsts", [
    ("DH", 7, FIRST_DH), ("DH", 13, FIRST_DH), ("DH", 19, [None] * 6),
    ("Epstein-15", 7, FIRST_E7), ("Epstein-15", 13, FIRST_E7), ("Epstein-15", 19, FIRST_DH),
    pytest.param("DH", 31, [None] * 6, marks=pytest.mark.slow),
    pytest.param("Epstein-15", 31, FIRST_DH, marks=pytest.mark.slow),
])
def test_rival_local_first_failure(name, ell, firsts):
    r = L.rival_local(name, L.FPrime(ell), BOX)
    assert [r[(j, 0)]["first"] for j in range(6)] == firsts
    if firsts[0] is not None:
        assert r[(0, 0)]["entry"].startswith("R(1-Q^-1)")


def test_first_difference_shortcut_matches_the_series():
    """The multiplier (1-R)(1-V)(1-W) has constant term 1, so both comparisons first differ at one key."""
    ld = L.LocalData(L.FPrime(7), extra_N=20)
    f = L.rival_coefficient("DH")
    coef = lambda t: f(7 ** t, ld.cyc)  # noqa: E731
    S = L.series_local_P(ld, 0, 0, BOX, coef=coef)
    Cf = L.closed_form_series(ld, 0, 0, BOX, eta=coef(1))
    assert L.peq(S, Cf, BOX)[0] == L.lemma_7_1_identity(ld, 0, 0, BOX, coef=coef, eta=coef(1))[0] == (6, 0, 1)


@pytest.mark.parametrize("name, a, b, separates, fpq, fpfq", [
    ("DH", (7, 0), (7, 1), False, -1.0, 0.0807009),
    ("DH", (7, 0), (13, 0), False, 1.0, -0.0807009),
    ("DH", (19, 0), (19, 1), True, 1.0, 1.0),
    ("Epstein-15", (7, 0), (7, 1), False, 1.0, 0.0),
    ("Epstein-15", (19, 0), (19, 1), False, 3.0, 4.0),
    ("Epstein-15", (7, 0), (13, 0), True, 0.0, 0.0),
    pytest.param("DH", (7, 0), (19, 0), True, -0.2840790, -0.2840790, marks=pytest.mark.slow),
    pytest.param("Epstein-15", (7, 0), (19, 0), True, 0.0, 0.0, marks=pytest.mark.slow),
])
def test_rival_cross_term(name, a, b, separates, fpq, fpfq):
    r = L.rival_cross_term(name, L.FPrime(*a), L.FPrime(*b))
    assert r["trivial character separates"]
    assert r["separates"] == separates
    assert abs(r["f(pq)"] - fpq) < 1e-6 and abs(r["f(p)f(q)"] - fpfq) < 1e-6
    assert r["K(pq) = f(pq) K_1(pq)"]


def test_row_zero_reads_only_t_0_1_below_six():
    """The u = 1 row has monomials only at t in {0, 1, 6, 7, 12, 13} in the box, and X^6 V is
    one of them: so that row fails at X^6 V exactly when f(p^6) != f(p)^6."""
    for norm in (7, 13, 19, 25):
        ld = local_data(norm)
        for rk in (0, 1):
            keys = L.series_local_P(ld, 0, rk, BOX)
            assert sorted({t for (t, _, _) in keys}) == [0, 1, 6, 7, 12, 13], norm
            assert (6, 0, 1) in keys and (6, 0, 0) not in keys
    for ell in (7, 13, 19, 5):
        p = L.FPrime(ell)
        small = p.small_field()
        assert L.C_p(p, L.gauss_sums(p, small), 6, 0, 6, small) == (p.Q ** 6 - p.Q ** 5) * small.one


def test_dh_both_steps_fail_on_the_same_primes():
    """Exhaustive over N p mod 5: DH is locally the character chi o N exactly where chi(N p)
    is real, and f(pq) = f(p) f(q) fails exactly when both chi(N p) and chi(N q) are not real.
    So every pair that fails separation is made of two primes that fail the single-prime step."""
    d = L.dh_residue_structure()
    assert d["chi_real"] == {1: True, 2: False, 3: False, 4: True}
    assert d["local"] == d["sixth"] == d["chi_real"]
    for (x, y), ok in d["pairs"].items():
        assert ok == (d["chi_real"][x] or d["chi_real"][y]), (x, y)
    failing = sorted(k for k, ok in d["pairs"].items() if not ok)
    assert failing == [(2, 2), (2, 3), (3, 2), (3, 3)]
    assert all(not d["local"][x] and not d["local"][y] for (x, y) in failing)
    assert d["inert norms"] == [1, 4]  # an inert prime has square norm: chi(N p) is real there
    # the residues of the computed primes: 7, 13 non-real; 19, 31 real
    assert [d["chi_real"][n % 5] for n in (7, 13, 19, 31)] == [False, False, True, True]


def test_epstein_single_prime_fails_everywhere_and_separation_only_at_conjugates():
    """At every split ell < 200: f(p^6) != f(p)^6 and f(ell^2) != f(ell)^2 (the conjugate pair);
    across distinct rational primes the coefficient is multiplicative (210 pairs)."""
    e = L.epstein_split_structure(200)
    assert len(e["ells"]) == 21 and e["ells"][:4] == [7, 13, 19, 31]
    assert e["f(p^t) = sum chi_5(ell)^i"]
    assert not any(e["sixth"].values())
    assert not any(e["conjugate pair separates"].values())
    assert len(e["distinct pairs separate"]) == 210 and all(e["distinct pairs separate"].values())


# ---------------------------------------------------------------------------
# (3) the lower-order probes, one prime each
# ---------------------------------------------------------------------------

def test_twist_products_at_norm_7():
    tp = L.twist_products(L.FPrime(7))
    assert tp[("gamma_2", 1)]["equals_-alphaG"]           # the paper: gamma_1 gamma_2 = -alpha G
    assert tp[("gamma_2", 4)]["equals_1"]                 # S1: gamma_2 gamma_4 = 1
    assert tp[("gamma_2", 3)]["alpha_exponent"] == Fraction(1, 3)  # S2: not scalar
    assert not tp[("gamma_2", 3)]["scalar"]
    assert tp[("gamma_4", 3)]["alpha_exponent"] == Fraction(-1, 3)  # S2 with the conjugate theta
    assert tp[("gamma_4", 2)]["equals_1"]
    assert tp[("gamma_4", 5)]["scalar"] and tp[("gamma_4", 5)]["alpha_exponent"] == -1


def test_S1_and_S2_at_norm_7():
    r = L.probe_S1_S2(L.FPrime(7))
    assert r["alpha(p) is a root of unity"] is False
    for rk in (0, 1):
        assert r[("paper (sextic twist)", "paper row normalization")][rk]["r = -1"]
        assert r[("paper (sextic twist)", "bare row")][rk]["r = -alpha G"]
        assert r[("S1 (conjugate cubic twist)", "paper row normalization")][rk]["r = conj(alpha G)"]
        assert r[("S1 (conjugate cubic twist)", "bare row")][rk]["r = +1"]
        s2p = r[("S2 (quadratic twist)", "paper row normalization")][rk]
        s2b = r[("S2 (quadratic twist)", "bare row")][rk]
        assert s2p["alpha exponent of r"] == Fraction(-2, 3) and not s2p["scalar"]
        assert s2b["alpha exponent of r"] == Fraction(1, 3) and not s2b["scalar"]
    assert L.s1_two_prime_product(L.FPrime(7), L.FPrime(13))
    assert L.s1_two_prime_product(L.FPrime(7), L.FPrime(7, 1))


@pytest.mark.parametrize("ell", [7, 13])
def test_S1_scalar_factorization_with_the_target_in_the_numerator(ell):
    """P = (1-V)^-1 (1-W)^-1 (1 - eta^2 X^2)/(1 - eta X) H with no pure X or X^2 in H - 1."""
    r = L.s1_factorization(L.FPrime(ell))
    assert r["psi = +eta"]
    assert r["pure X and X^2 absent from H - 1"]
    assert r["largest size exponent of H - 1, region one corners (measured at this prime)"][0] < -1
    assert r["largest size exponent of H - 1, region two (measured at this prime)"][0] < -1.6


@pytest.mark.parametrize("a, b, R", [
    ((7, 0), (13, 0), -1), ((7, 0), (19, 0), -1), ((13, 0), (19, 0), -1), ((7, 0), (31, 0), -1),
    ((7, 0), (7, 1), 1), ((13, 0), (13, 1), 1), ((19, 0), (19, 1), 1),
])
def test_S1_does_not_separate_in_the_paper_row_normalization(a, b, R):
    """With the conj(alpha) conj(G) insertion, the paper's probe gives mu(c) and separates, while
    S1 gives conj(alpha(c) G(c)), which carries the pair phase: X_4(pq) = conj(R(p,q)) X_4(p) X_4(q)."""
    r = L.s1_pair_phase(L.FPrime(*a), L.FPrime(*b))
    assert r["gamma_2 gamma_4 = 1 at p, q, pq"]
    assert r["R agrees with the four-term formula"]
    assert r["paper's probe: X_1 = mu at p, q, pq"] and r["paper's probe separates"]
    assert r["S1: X_4(pq) = conj(R) X_4(p) X_4(q)"]
    assert r["R = -1"] == (R == -1) and r["R = +1"] == (R == 1)
    assert r["S1 separates"] == (R == 1)


def test_S1_pair_phase_lesion_without_the_G_insertion():
    """Planted lesion: dropping conj(G(c)) flips both verdicts at (7, 13), where R = -1."""
    r = L.s1_pair_phase(L.FPrime(7), L.FPrime(13), insert_G=False)
    assert not r["paper's probe separates"]
    assert r["S1 separates"]


def test_S3_at_norm_13():
    r = L.probe_S3(13)
    assert r["prime"].endswith("pi = 3+2i")
    assert r["theta coefficient #{x: x^2 = p^t}, t=0..4"] == {0: 2, 1: 0, 2: 2, 3: 0, 4: 2}
    assert r["alpha exponent of gamma_3"] == Fraction(-1, 2)
    assert r["no theta coefficient at A = p"]
    assert r["quadratic Gauss sum scalar: G_2^2 = chi^2(-1) Q"]
    assert r["alpha(p) a root of unity"] is False
    assert r["alpha exponent of gamma_1 (quartic)"] == Fraction(1, 2)
    assert r["alpha exponent of gamma_2 (quadratic)"] == 0
    assert r["lift at p^2 = direct summation"]
    assert r["smallest x-power in the u = 1 row"] == 4


@pytest.mark.slow
def test_S3_direct_at_norm_5():
    r = L.probe_S3_direct(5, 4)
    assert r["prime"].endswith("pi = -1+2i")
    dead = {v["alpha exponent"] for row in r["rows"].values() for v in row.values() if not v["survives theta"]}
    assert dead == {Fraction(1, 2), Fraction(-1, 2)}
    assert not r["X^1 term possible"]
    assert r["every surviving coefficient scalar"]
    assert r["some non-surviving coefficient non-scalar"]
    assert r["smallest surviving x-power, u = 1"] == 4


# ---------------------------------------------------------------------------
# the verifier's prime (norm 31)
# ---------------------------------------------------------------------------

def test_lemma_4_2_at_norm_31():
    assert all(L.lemma_4_2_checks(L.FPrime(31)).values())


@pytest.mark.slow
def test_lemma_7_1_at_norm_31():
    ld = L.LocalData(L.FPrime(31))
    for j in range(6):
        for rk in (0, 1):
            assert L.lemma_7_1_identity(ld, j, rk, BOX) == []
        assert L.raw_vs_series(ld, j, 1, L.Box(7, 1, 2)) == []
    ldf = L.LocalData(L.FPrime(31), gauss_fault="gauss_sign")
    assert all(L.raw_vs_series(ldf, j, 1, L.Box(7, 1, 2)) for j in range(6))
    assert all(L.lemma_7_1_identity(ld, j, 1, BOX, fault="local_factor") for j in range(6))


def test_disagreements_file_is_consistent_with_the_report():
    import json
    with open(os.path.join(HERE, "disagreements.json"), encoding="utf-8") as fh:
        d = json.load(fh)
    assert d["source"]["sha256"] == L.PAPER_SHA256
    assert [x["id"] for x in d["disagreements"]] == ["D1"]
    assert d["paper"]["defects_found"] == []
    assert "0.0807009" in d["rivals"]["failing_term"]
    with open(os.path.join(HERE, "REFEREE_W1.md"), encoding="utf-8") as fh:
        md = fh.read()
    assert "disagreement D1" in md
    assert ("Not performed" in md) == (d["comparison_with_lane_files"]["performed"] is False)
    # the repaired rival verdict: both steps fail, on the same primes; the old reading is withdrawn
    assert "both steps" in d["rivals"]["verdict"] and "withdrawn" in d["rivals"]
    assert set(d["rivals"]["where_each_step_fails"]) == {"DH", "Epstein-15"}
    assert "both, on the same primes" in md and "reading is withdrawn" in md
    assert "line 6725" in d["rivals"]["placement"] and "extended by this lane" in d["rivals"]["placement"]
    # D1 carries the three post-review items; the paper-normalization pair phase is pinned
    assert [x["item"] for x in d["disagreements"][0]["after_adversarial_review"]] == ["a", "b", "c"]
    assert "test_S1_does_not_separate_in_the_paper_row_normalization" in d["disagreements"][0]["evidence"]
    # corrected citation and versions
    assert "4117-4121 and 4124" in md and "4117-4122)" not in md
    assert "cypari2 package version 2.2.4" in md
    # every test the report names exists in this module (file names such as test_x.py excluded)
    import re
    pat = r"(test_[A-Za-z0-9_]+)(?!\.py|[A-Za-z0-9_])"
    names = set(re.findall(pat, md)) | set(re.findall(pat, json.dumps(d)))
    assert len(names) >= 10 and all(n in globals() for n in names), sorted(n for n in names if n not in globals())
