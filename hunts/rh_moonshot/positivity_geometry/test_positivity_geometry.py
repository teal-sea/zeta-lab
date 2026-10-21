"""Tests for hunts/rh_moonshot/positivity_geometry (hunt #150, mechanism 4).

Run from the worktree root:
    .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/positivity_geometry

Every number stated in NOTES.md is asserted here. All sign and equality decisions are
exact integer arithmetic; mpmath appears only for eigenvalue moduli and residues. The
tests write nothing to disk.
"""

from __future__ import annotations

import random
import re
import sys
from pathlib import Path

import numpy as np
import pytest
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for _p in (str(HERE), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import frobenius_span as fs  # noqa: E402
from zeta import finitefield as ff  # noqa: E402

# (f, p, N_1..N_4 by brute force, Weil polynomial, full inertia at window 5)
CURVES = [
    ((1, 0, 1, 1), 5, [9, 27, 108, 675], [1, 3, 5], (1, 3, 3)),
    ((1, 0, 2, 3), 7, [6, 60, 378, 2400], [1, -2, 7], (1, 3, 3)),
    ((1, 0, -1, 0), 11, [12, 144, 1332, 14400], [1, 0, 11], (1, 3, 3)),
    ((1, 0, 1, 6), 13, [13, 195, 2236, 28275], [1, -1, 13], (1, 3, 3)),
    ((1, 0, 0, 0, -1, 1), 5, [11, 31, 101, 651], [1, 5, 15, 25, 25], (1, 5, 1)),
    ((1, 0, 0, 0, 1, 3), 7, [11, 55, 371, 2419], [1, 3, 7, 21, 49], (1, 5, 1)),
    ((1, 0, 2, 0, 1, 3), 11, [9, 133, 1296, 14809], [1, -3, 10, -33, 121], (1, 5, 1)),
    ((1, 0, 0, 1, 0, 2), 13, [12, 178, 2148, 29038], [1, -2, 6, -26, 169], (1, 5, 1)),
]

GENUS1_FAKES = [(5, 5), (5, -5), (7, 6), (7, 7), (11, 7), (11, 10), (13, 8), (13, 13)]


@pytest.fixture(scope="module")
def brute_counts():
    return {(f, p): fs.point_counts(f, p, 4) for f, p, *_ in CURVES}


# ---------------------------------------------------------------------------
# 1. the instruments: exact inertia and the finite fields
# ---------------------------------------------------------------------------


def test_inertia_routes_agree_with_each_other_and_with_floats():
    rng = random.Random(150)
    for trial in range(60):
        n = rng.randint(1, 8)
        r = rng.randint(0, n)
        B = [[rng.randint(-4, 4) for _ in range(r)] for _ in range(n)]
        D = [rng.choice([-3, -1, 1, 2]) for _ in range(r)]
        M = [[sum(B[i][k] * D[k] * B[j][k] for k in range(r)) for j in range(n)] for i in range(n)]
        a = fs.inertia_charpoly(M)
        b = fs.inertia_ldl(M)
        assert a == b
        ev = np.linalg.eigvalsh(np.array(M, dtype=float)) if n else np.array([])
        scale = max(1.0, float(np.abs(ev).max()) if n else 1.0)
        tol = 1e-9 * scale
        assert a == (int((ev > tol).sum()), int((ev < -tol).sum()), int((abs(ev) <= tol).sum()))


@pytest.mark.parametrize("p,n", [(5, 2), (5, 3), (7, 2), (7, 3), (11, 2), (13, 2)])
def test_extension_fields_are_fields(p, n):
    assert fs.PrimePowerField(p, n).is_field()


def test_the_field_check_can_fail():
    F = fs.PrimePowerField(5, 2)
    F.low = np.array([4, 0], dtype=np.int64)  # t^2 + 4 = (t - 1)(t + 1) over F_5
    assert not F.is_field()


@pytest.mark.parametrize("a,b,p", [(1, 1, 5), (2, 3, 7), (-1, 0, 11), (1, 6, 13), (3, 5, 101)])
def test_brute_force_counts_match_zeta_finitefield(a, b, p):
    f = (1, 0, a, b)
    assert fs.count_points(f, p, 1) == ff.count_points(a, b, p)
    if p <= 13:
        assert fs.count_points(f, p, 2) == ff.count_points_fp2(a, b, p)
        lef = ff.point_counts_over_extensions(a, b, p, 4)
        assert [fs.count_points(f, p, n) for n in (3, 4)] == lef[2:4]


def test_brute_force_counts_are_the_pinned_ones_and_rational(brute_counts):
    for f, p, N, P, _ in CURVES:
        got = brute_counts[(f, p)]
        assert [got[n] for n in range(1, 5)] == N
        g = fs._check_curve_poly(f, p)
        assert fs.weil_polynomial(p, got, g) == P
        # rationality: N_1..N_g determine all the others (Weil), checked on the brute counts
        assert fs.counts_from_weil_polynomial(p, P, 4) == got


# ---------------------------------------------------------------------------
# 2. the shadow: Hodge index on the Frobenius span, exactly, from point counts
# ---------------------------------------------------------------------------


def test_hodge_index_holds_on_the_frobenius_span_of_real_curves(brute_counts):
    for f, p, N, P, full in CURVES:
        g = fs._check_curve_poly(f, p)
        counts = brute_counts[(f, p)]
        rep = fs.hodge_index_report(p, counts, g, window=5)
        assert rep["full_inertia"] == full
        assert rep["hodge_index_holds"]
        assert rep["projected_inertia"][0] == 0  # the projected form is <= 0
        assert rep["projected_rank"] == 2 * g  # the Frobenius span has rank 2 + 2g


def test_transposes_obey_the_second_intersection_formula(brute_counts):
    """G_{-2..2} (transposes use G_a^t.G_b = N_{a+b}) must have the inertia of the
    one-sided window G_0..G_4 (which uses only q^min N_|a-b|): two formulas, one form."""
    for f, p, *_ in CURVES:
        g = fs._check_curve_poly(f, p)
        counts = brute_counts[(f, p)]
        sym = fs.hodge_index_report(p, counts, g, window=2, symmetric=True)
        one = fs.hodge_index_report(p, counts, g, window=5)
        assert sym["full_inertia"] == one["full_inertia"]
        assert sym["projected_inertia"] == one["projected_inertia"]


def test_castelnuovo_severi_minors(brute_counts):
    margins = {}
    for f, p, *_ in CURVES:
        g = fs._check_curve_poly(f, p)
        m = fs.castelnuovo_severi_margins(p, brute_counts[(f, p)], g, 4)
        assert min(m) >= 0
        margins[(f, p)] = m
    assert margins[((1, 0, 1, 1), 5)] == [11, 99, 176, 99]
    # y^2 = x^3 - x is supersingular at 11: the bound is attained at even n
    assert margins[((1, 0, -1, 0), 11)] == [44, 0, 5324, 0]


def test_the_eigenvalue_route_agrees(brute_counts):
    for f, p, N, P, _ in CURVES:
        for r in fs.eigenvalue_moduli_ratio(p, P, dps=30):
            assert abs(r - 1) < mp.mpf(10) ** -25


def test_the_toeplitz_symbols_are_the_normalized_traces(brute_counts):
    f, p = (1, 0, 1, 1), 5
    t = fs.weil_toeplitz_symbols(p, brute_counts[(f, p)], 1, 4, dps=30)
    with mp.workdps(30):
        alpha = mp.mpc(-3, mp.sqrt(11)) / 2  # roots of x^2 + 3x + 5
        for k in range(1, 5):
            want = 2 * mp.re((alpha / mp.sqrt(5)) ** k)
            assert abs(t[k] - want) < mp.mpf(10) ** -25


# ---------------------------------------------------------------------------
# 3. planted violations: fakes with every arithmetic hypothesis, refused
# ---------------------------------------------------------------------------


def test_the_golden_fake():
    q, a = 5, 5
    P = [1, -a, q]
    assert fs.is_self_reciprocal(q, P)
    with mp.workdps(30):
        phi = (1 + mp.sqrt(5)) / 2
        r = fs.eigenvalue_moduli_ratio(q, P, dps=30)
        assert abs(r[0] - 1 / phi) < mp.mpf(10) ** -25
        assert abs(r[1] - phi) < mp.mpf(10) ** -25
    N = fs.fake_genus1_counts(q, a, 60)
    b = fs.closed_point_counts(N, 60)
    assert b[:6] == [1, 5, 25, 110, 500, 2215]
    assert min(b) >= 1
    assert fs.fake_genus1_threshold(q, a) == 2  # so b_d > 0 for every d >= 2 (NOTES s4)
    assert fs.hodge_index_report(q, N, 1, window=2)["full_inertia"] == (2, 2, 0)
    assert fs.hodge_index_report(q, N, 1, window=5)["full_inertia"] == (2, 2, 3)
    assert fs.castelnuovo_severi_margins(q, N, 1, 1) == [-5]


@pytest.mark.parametrize("q,a", GENUS1_FAKES)
def test_every_genus1_fake_has_a_counting_euler_product_and_is_refused(q, a):
    P = [1, -a, q]
    assert a * a > 4 * q and abs(a) <= q and fs.is_self_reciprocal(q, P)
    N = fs.fake_genus1_counts(q, a, 60)
    b = fs.closed_point_counts(N, 60)
    D0 = fs.fake_genus1_threshold(q, a)
    assert D0 <= 3 and min(b[: D0 + 1]) >= 0 and min(b) >= 0
    assert fs.hodge_index_report(q, N, 1, window=2)["full_inertia"][0] == 2


def _random_weil_type_polynomials(q, g, rng, n):
    """Self-reciprocal integer P of degree 2g, P(0) = 1, as products of quadratic and
    quartic Weil-type factors with random middle coefficients (on or off the circle)."""
    out = []
    while len(out) < n:
        P = [1]
        deg = 0
        while deg < 2 * g:
            if 2 * g - deg >= 4 and rng.random() < 0.4:
                b1 = rng.randint(-3 * q, 3 * q)
                b2 = rng.randint(-4 * q, 4 * q)
                P = fs.poly_mul(P, [1, b1, b2, q * b1, q * q])
                deg += 4
            else:
                a = rng.randint(-(q + 1), q + 1)
                P = fs.poly_mul(P, [1, -a, q])
                deg += 2
        out.append(P)
    return out


@pytest.mark.parametrize("q,g", [(5, 2), (7, 2), (5, 3), (7, 3)])
def test_window_2g_decides_rh_for_weil_type_polynomials(q, g):
    """NOTES section 2.4 derives: the Frobenius-span form is positive on the first 2g
    Frobenius powers iff every |alpha| = sqrt(q). Checked on a seeded random family,
    with on/off-circle classification by mpmath roots at 40 digits (ambiguous cases
    skipped) and the verdicts by exact inertia."""
    rng = random.Random(1000 * q + g)
    checked = {"on": 0, "off": 0, "off_hidden_below_2g": 0}
    for P in _random_weil_type_polynomials(q, g, rng, 40):
        assert fs.is_self_reciprocal(q, P)
        dev = max(abs(r - 1) for r in fs.eigenvalue_moduli_ratio(q, P, dps=40))
        if mp.mpf(10) ** -25 < dev < mp.mpf(10) ** -6:
            continue
        N = fs.counts_from_polynomial(q, P, 2 * g + 2)
        holds = [fs.hodge_index_report(q, N, g, window=w)["hodge_index_holds"] for w in range(2, 2 * g + 3)]
        if dev <= mp.mpf(10) ** -25:
            assert all(holds), (P, holds)
            checked["on"] += 1
        else:
            assert not holds[2 * g - 2], (P, holds)  # refused at window 2g
            assert not any(holds[2 * g - 2 :]), (P, holds)
            checked["off"] += 1
            if holds[2 * g - 3]:
                checked["off_hidden_below_2g"] += 1
    assert checked["on"] >= 3 and checked["off"] >= 10
    # sharpness: some off-circle polynomial is positive on every window below 2g
    assert checked["off_hidden_below_2g"] >= 1


def test_window_2g_is_sharp_in_genus_2():
    """The genus-2 fake (-3, golden) is positive on windows 2 and 3 = 2g - 1."""
    q = 5
    N = fs.counts_from_polynomial(q, [1, -2, -5, -10, 25], 6)
    assert fs.hodge_index_report(q, N, 2, window=3)["hodge_index_holds"]
    assert not fs.hodge_index_report(q, N, 2, window=4)["hodge_index_holds"]


def test_b2_of_the_negative_golden_fake_is_zero():
    b = fs.closed_point_counts(fs.fake_genus1_counts(5, -5, 12), 12)
    assert b[:6] == [11, 0, 55, 110, 748, 2200]


def test_a_genus2_fake_passes_small_windows_and_is_refused_at_window_4():
    q = 5
    P = fs.poly_mul([1, 3, 5], [1, -5, 5])  # honest factor a = -3, golden factor a = 5
    assert P == [1, -2, -5, -10, 25] and fs.is_self_reciprocal(q, P)
    N = fs.counts_from_polynomial(q, P, 60)
    b = fs.closed_point_counts(N, 60)
    assert min(b) == 4 and fs.fake_threshold_general(q, P) == 5
    verdicts = [fs.hodge_index_report(q, N, 2, window=w)["hodge_index_holds"] for w in range(2, 6)]
    assert verdicts == [True, True, False, False]
    m = fs.castelnuovo_severi_margins(q, N, 2, 4)
    assert m == [76, 204, -2624, -5876]


# ---------------------------------------------------------------------------
# 4. the base-field Euler product: quadratic-character local factors over F_q(t)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("f,p", [((1, 0, 1, 1), 5), ((1, 0, 2, 3), 7), ((1, 0, -1, 0), 11), ((1, 0, 1, 6), 13)])
def test_honest_curves_have_their_quadratic_euler_product(f, p):
    ram = fs.curve_ramification(f, p)
    N1 = fs.count_points(f, p, 1)
    res = fs.quadratic_euler_decomposition([1, -(p + 1 - N1), p], p, ram, 40)
    assert res["failure"] is None and res["conductor_ok"]


@pytest.mark.parametrize("f,p", [((1, 0, 1, 1), 5), ((1, 0, 2, 3), 7), ((1, 0, 1, 6), 13)])
def test_the_recursion_counts_actual_split_and_inert_places(f, p):
    """Control: the per-degree counts the recursion produces are the geometric ones."""
    ram = fs.curve_ramification(f, p)
    N1 = fs.count_points(f, p, 1)
    res = fs.quadratic_euler_decomposition([1, -(p + 1 - N1), p], p, ram, 3)
    for d in (1, 2, 3):
        split, inert, ram_fin = fs.split_inert_bruteforce(f, p, d)
        assert (split, inert) == (res["split"][d], res["inert"][d])
        assert ram_fin == ram.get(d, 0) - (1 if d == 1 else 0)


def test_the_golden_fake_has_a_quadratic_character_euler_product():
    q, P = 5, [1, -5, 5]
    verdicts = {
        tuple(sorted(conf.items())): fs.quadratic_euler_decomposition(P, q, conf, 40)["failure"]
        for conf in fs.ramification_configurations(4)
    }
    assert verdicts[((1, 1), (3, 1))] is None
    assert all(v == (1, "parity") for k, v in verdicts.items() if k != ((1, 1), (3, 1)))
    res = fs.quadratic_euler_decomposition(P, q, {1: 1, 3: 1}, 40)
    assert res["conductor_ok"]
    assert [res["split"][d] for d in range(1, 5)] == [0, 0, 12, 50]
    assert [res["inert"][d] for d in range(1, 5)] == [5, 10, 27, 100]
    assert [fs.places_of_degree(q, d) for d in range(1, 5)] == [6, 10, 40, 150]
    # all degrees: integrality from the mod-2 congruence with an honest curve of the
    # same ramification, nonnegativity past the tail threshold (NOTES section 5)
    ref = fs.mod2_reference_curve(P, q, {1: 1, 3: 1})
    assert ref == ((1, 0, 1, 1), [1, 3, 5])
    assert fs.quadratic_tail_threshold(q, P) == 4


@pytest.mark.parametrize("q,a", GENUS1_FAKES)
def test_every_genus1_fake_admits_some_quadratic_euler_product_to_degree_40(q, a):
    P = [1, -a, q]
    ok = [
        conf
        for conf in fs.ramification_configurations(4)
        if fs.quadratic_euler_decomposition(P, q, conf, 40)["failure"] is None
    ]
    # at least one admissible configuration has an honest cubic reference curve, so
    # integrality holds in every degree; nonnegativity past the tail threshold <= 8
    assert any(fs.mod2_reference_curve(P, q, conf) is not None for conf in ok)
    assert fs.quadratic_tail_threshold(q, P) <= 8


# ---------------------------------------------------------------------------
# 5. the number-field rival table: G1 (proper intersections are counts), G2 (one pole)
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def rival_table():
    return fs.nf_rival_table(n_max=60, dps=30)


def test_zeta_meets_both_preconditions(rival_table):
    z = rival_table["zeta"]
    assert z["G1_nonnegative_to_n_max"] and z["G1_prime_power_support_to_n_max"]
    assert z["poles_right_of_half"] == 1 and abs(z["residues"][0][1] - 1) < 1e-12


def test_davenport_heilbronn_fails_both(rival_table):
    d = rival_table["davenport_heilbronn"]
    assert (d["first_negative"], d["first_off_prime_power"]) == (3, 6)
    assert d["poles_right_of_half"] == 0 and not d["G2_one_hyperbolic_plane"]
    lam = fs.nf_log_derivative_profile(n_max=6, dps=30)["davenport_heilbronn"]["lam"]
    k = float(__import__("zeta.epstein", fromlist=["kappa"]).kappa(30))
    assert abs(lam[2] - k * np.log(2)) < 1e-12
    assert abs(lam[3] + k * np.log(3)) < 1e-12
    assert abs(lam[6] - (1 + k * k) * np.log(6)) < 1e-12


def test_epstein_116_fails_g1_and_meets_g2(rival_table):
    e = rival_table["epstein_1_1_6"]
    assert (e["first_negative"], e["first_off_prime_power"]) == (48, 6)
    assert e["poles_right_of_half"] == 1
    assert abs(e["residues"][0][1] - 2 * np.pi / np.sqrt(23)) < 1e-12


def test_w_half_is_the_zeta_function_of_the_projective_line_over_z():
    """W_{1/2}(s - 1/2) = zeta(s) zeta(s - 1) = Z(P^1_Z, s): coefficients sigma(n)."""
    from sympy import divisor_sigma

    from zeta.epstein import shifted_coefficient

    with mp.workdps(30):
        for n in range(1, 31):
            c = shifted_coefficient(n, shift=mp.mpf(1) / 2, dps=30) * mp.sqrt(n)
            assert abs(c - int(divisor_sigma(n))) < mp.mpf(10) ** -20


def test_shifted_product_meets_g1_and_fails_g2(rival_table):
    w = rival_table["shifted_product_quarter"]
    assert w["G1_nonnegative_to_n_max"] and w["G1_prime_power_support_to_n_max"]
    assert w["poles_right_of_half"] == 2
    with mp.workdps(30):
        want = {1.25: float(mp.zeta(1.5)), 0.75: float(mp.zeta(0.5))}
    for s0, r in w["residues"]:
        assert abs(r - want[s0]) < 1e-12


# ---------------------------------------------------------------------------
# 6. house rules for this directory
# ---------------------------------------------------------------------------

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)


def test_lexical_rules_of_this_directory():
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".py", ".md", ".json"}:
            continue
        text = path.read_text(encoding="utf-8")
        assert _RESERVED not in text.lower(), path.name
        assert _EM_DASH not in text, path.name


def test_run_manifests_validate():
    sys.path.insert(0, str(ROOT / "tests"))
    try:
        import test_huntspec as hs
    finally:
        sys.path.remove(str(ROOT / "tests"))
    text = (HERE / "RUNS.md").read_text(encoding="utf-8")
    blocks = re.findall(r"```runmanifest\n(.*?)```", text, re.DOTALL)
    assert blocks
    for block in blocks:
        assert hs.validate_runmanifest(hs.parse_huntspec(block)) == ()
