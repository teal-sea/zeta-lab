"""Tests for zeta.finitefield — the blueprint universe, where RH is a theorem.

Every number asserted here was computed and cross-checked in this environment
first.  The structure follows the module's story:

1. **The field.**  ``legendre_symbol`` against sympy's independent
   implementation for every residue of eight primes; the squaring table
   ``_chi_table`` against Euler's criterion for every residue of six primes;
   F_{p^2} = F_p[t]/(t^2-n) checked to actually *be* a field (commutative,
   associative, distributive, Fermat's little theorem in the form
   ``u^{p^2-1} = 1``).
2. **The counting.**  ``count_points`` against a literal enumeration of all
   ``p^2`` pairs (x, y) — exhaustively, for every nonsingular curve over every
   prime up to 43 (7 968 curves in the fast tier; 19 968 up to 61 once the
   slow tier is included).  Plus a genuinely independent oracle: Gauss's two-squares theorem for
   ``y^2 = x^3 - x`` (:func:`zeta.finitefield.gauss_trace`), agreeing over all
   301 primes below 2000 and at p = 10009.  The pinned value from
   ``docs/09-new-ontologies.md`` section 1.1 — p = 1009, N = 1040, a_p = -30 —
   is reproduced.
3. **RH, form one (Hasse).**  Zero violations of ``|a_p| <= 2 sqrt p`` over
   1 279 678 curves (every curve over p = 101, 503 and 1009), checked in exact
   integer arithmetic, plus a seeded 862-curve survey over 18 primes up to
   10007.  It is a theorem; a violation would be a bug in this module.
4. **RH, form two (critical line).**  ``T = p^{-s}`` sends every numerator root
   to ``Re(s) = 1/2``.  Demanded to 1e-12; *measured* at 1.2e-41 worst case at
   dps = 30 over the whole survey, so the tolerance is not doing the work.
5. **Lefschetz.**  ``N_2`` from the eigenvalue formula
   ``p^2 + 1 - (alpha^2 + alphabar^2)`` against a brute-force enumeration over
   an explicitly constructed F_{p^2} — exhaustively for p = 5, 7, 11 by the
   literal ``p^4``-pair double loop, and up to p = 199 by tabulated
   enumeration.  Because both of the module's methods share one presentation of
   F_{p^2}, the same count is done again in a *second* presentation
   ``F_p[t]/(t^2 - c t - d)`` built and enumerated by code local to this file
   (p = 5, 7, 11, 13, all 328 curves), and a third time through
   ``N_2 = N_1 * N_1(twist)`` with the twist counted rather than deduced.  This
   is the test that shows the operator is real.
6. **Statistics.**  The vertical Sato-Tate semicircle, the exact identities
   ``#{nonsingular (a,b)} = p^2 - p``, ``sum a_p = 0``,
   ``sum a_p^2 = (p-1)^2 (p+1)``, and Deuring's theorem that every trace in the
   Hasse interval is attained.  The FFT sweep behind those statistics recovers
   integers from float64, so its exact row identities are re-derived here in
   pure Python and its guard is shown to *fire* on a one-unit corruption —
   rounding residuals alone would not catch a mis-rounding, and the test says
   so explicitly.
"""

from __future__ import annotations

import math
import random
from fractions import Fraction

import mpmath
import numpy as np
import pytest
import sympy
from mpmath import mp

from zeta.finitefield import (
    count_points,
    count_points_bruteforce,
    count_points_fp2,
    critical_line_check,
    curve_survey,
    discriminant,
    fp2_mul,
    frobenius_eigenvalues,
    frobenius_power_traces,
    gauss_trace,
    hasse_check,
    is_singular,
    legendre_symbol,
    point_counts_over_extensions,
    quadratic_nonresidue,
    random_curve,
    sato_tate_histogram,
    survey_summary,
    trace_of_frobenius,
    traces_mod_p,
    weil_conjecture_facts,
    zeta_function_values,
    zeta_functional_equation_defect,
    zeta_log_series_defect,
    zeta_numerator,
)

SMALL_PRIMES = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
SURVEY_PRIMES = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 101, 211, 503, 1009,
                 2003, 4001, 7919, 10007)


def nonsingular_pairs(p: int) -> list[tuple[int, int]]:
    """All ``(a, b)`` in F_p^2 defining an elliptic curve, in row-major order."""
    return [
        (a, b)
        for a in range(p)
        for b in range(p)
        if (4 * a ** 3 + 27 * b ** 2) % p != 0
    ]


# ---------------------------------------------------------------------------
# 1. the finite field
# ---------------------------------------------------------------------------

def test_legendre_symbol_matches_sympy_for_every_residue():
    """Euler's criterion here vs sympy's independent implementation."""
    for p in (5, 7, 11, 13, 101, 211, 1009, 10007):
        assert legendre_symbol(0, p) == 0
        for a in range(1, p):
            assert legendre_symbol(a, p) == sympy.legendre_symbol(a, p), (a, p)


def test_legendre_symbol_is_a_character_and_counts_residues():
    for p in (11, 13, 101, 1009):
        # exactly (p-1)/2 nonzero residues are squares
        assert sum(1 for a in range(1, p) if legendre_symbol(a, p) == 1) == (p - 1) // 2
        # completely multiplicative
        rng = random.Random(p)
        for _ in range(50):
            u, v = rng.randrange(1, p), rng.randrange(1, p)
            assert legendre_symbol(u * v, p) == legendre_symbol(u, p) * legendre_symbol(v, p)
        # periodic mod p, and (a|p) = 1 iff a is a square
        squares = {x * x % p for x in range(1, p)}
        for a in range(1, p):
            assert (legendre_symbol(a, p) == 1) == (a in squares)
            assert legendre_symbol(a + p, p) == legendre_symbol(a, p)


def test_legendre_symbol_rejects_bad_characteristic():
    for bad in (2, 3, 4, 9, 15, 1, 0, -7):
        with pytest.raises(ValueError):
            legendre_symbol(1, bad)


def test_chi_table_matches_the_euler_criterion():
    """The O(p) squaring table used by ``count_points`` vs Euler's criterion.

    ``_chi_table`` is built by squaring every residue; ``legendre_symbol``
    computes ``a^{(p-1)/2} mod p``.  Two different routes, asserted equal for
    *every* residue of six primes — the table is the hot path of every point
    count in the module, so it gets its own direct check rather than being
    tested only through its consequences.
    """
    import zeta.finitefield as ff

    for p in (5, 7, 13, 101, 1009, 10007):
        table = ff._chi_table(p)
        assert len(table) == p
        assert table[0] == 0
        for a in range(p):
            assert table[a] == legendre_symbol(a, p), (a, p)


def test_quadratic_nonresidue_is_least_and_is_a_nonresidue():
    for p in (5, 7, 11, 13, 17, 101, 1009):
        n = quadratic_nonresidue(p)
        assert legendre_symbol(n, p) == -1
        assert all(legendre_symbol(m, p) == 1 for m in range(1, n))


def test_fp2_is_a_field():
    """F_p[t]/(t^2 - n) really is F_{p^2}: axioms plus Fermat's little theorem."""
    for p in (5, 7, 11, 13):
        n = quadratic_nonresidue(p)
        els = [(u, v) for u in range(p) for v in range(p)]
        one, zero = (1, 0), (0, 0)
        rng = random.Random(p)
        # t^2 = n
        assert fp2_mul((0, 1), (0, 1), p, n) == (n % p, 0)
        for _ in range(200):
            x, y, z = (rng.choice(els) for _ in range(3))
            assert fp2_mul(x, y, p, n) == fp2_mul(y, x, p, n)
            assert fp2_mul(fp2_mul(x, y, p, n), z, p, n) == fp2_mul(x, fp2_mul(y, z, p, n), p, n)
            assert fp2_mul(x, one, p, n) == x
            assert fp2_mul(x, zero, p, n) == zero
            lhs = fp2_mul(x, ((y[0] + z[0]) % p, (y[1] + z[1]) % p), p, n)
            xy, xz = fp2_mul(x, y, p, n), fp2_mul(x, z, p, n)
            assert lhs == ((xy[0] + xz[0]) % p, (xy[1] + xz[1]) % p)
        # every nonzero element satisfies u^{p^2 - 1} = 1  (=> no zero divisors)
        for u in els:
            if u == zero:
                continue
            acc, base, e = one, u, p * p - 1
            while e:
                if e & 1:
                    acc = fp2_mul(acc, base, p, n)
                base = fp2_mul(base, base, p, n)
                e >>= 1
            assert acc == one, (p, u)


# ---------------------------------------------------------------------------
# 2. the curve: singularity is refused, not silently mishandled
# ---------------------------------------------------------------------------

def test_discriminant_matches_the_4a3_27b2_condition():
    for p in (5, 7, 11, 13, 101):
        for a in range(p):
            for b in range(p):
                assert (discriminant(a, b, p) == 0) == ((4 * a ** 3 + 27 * b ** 2) % p == 0)
                assert is_singular(a, b, p) == (discriminant(a, b, p) == 0)


def test_singular_curve_raises_everywhere():
    """A singular cubic is not an elliptic curve: every entry point refuses it."""
    # y^2 = x^3 (a cusp) is singular over every p; y^2 = x^3 - 3x + 2 has a node.
    singular = [(0, 0, 7), (0, 0, 101), (-3, 2, 11), (-3, 2, 1009)]
    for a, b, p in singular:
        assert is_singular(a, b, p)
        for fn in (count_points, count_points_bruteforce, trace_of_frobenius,
                   zeta_numerator, frobenius_eigenvalues, critical_line_check,
                   hasse_check, count_points_fp2):
            with pytest.raises(ValueError, match="singular"):
                fn(a, b, p)
        with pytest.raises(ValueError, match="singular"):
            point_counts_over_extensions(a, b, p, 3)
        with pytest.raises(ValueError, match="singular"):
            zeta_function_values(a, b, p, 0.01)


def test_a_node_really_is_singular_by_hand():
    """y^2 = x^3 - 3x + 2 = (x-1)^2 (x+2): a double root, hence a node at x = 1."""
    for p in (11, 101, 1009):
        assert (4 * (-3) ** 3 + 27 * 2 ** 2) % p == 0
        # the double root x = 1 gives f(1) = f'(1) = 0
        assert (1 - 3 + 2) % p == 0 and (3 - 3) % p == 0


def test_bad_characteristic_raises():
    for bad in (2, 3, 4, 9, 21, 1001):
        with pytest.raises(ValueError):
            count_points(1, 1, bad)


def test_internal_primality_test_matches_sympy():
    """The gatekeeper is a deterministic Miller-Rabin; check it against sympy.

    Every n from 0 to 3000, plus the Carmichael numbers (which fool naive
    Fermat tests) and a few large primes/near-primes.
    """
    import zeta.finitefield as ff

    for n in range(0, 3000):
        assert ff._is_prime(n) == sympy.isprime(n), n
    for n in (561, 1105, 1729, 2465, 2821, 6601, 8911, 41041, 825265,
              104729, 104730, 1000003, 1000001, 2 ** 31 - 1, 2 ** 31 - 3,
              99999999977, 99999999979):
        assert ff._is_prime(n) == sympy.isprime(n), n


def test_number_of_nonsingular_curves_is_p_squared_minus_p():
    """An exact identity, used by curve_survey and sato_tate_histogram."""
    for p in (5, 7, 11, 13, 17, 19, 23, 101, 211, 503):
        assert len(nonsingular_pairs(p)) == p * p - p


# ---------------------------------------------------------------------------
# 3. point counting against a brute-force independent count
# ---------------------------------------------------------------------------

def test_count_points_equals_brute_force_exhaustively():
    """The headline oracle: character sum vs enumerating all p^2 pairs (x, y).

    Every nonsingular curve over every prime up to 43 — 7 968 curves.
    """
    n = 0
    for p in SMALL_PRIMES:
        for a, b in nonsingular_pairs(p):
            assert count_points(a, b, p) == count_points_bruteforce(a, b, p), (a, b, p)
            n += 1
    assert n == 7968


@pytest.mark.slow
def test_count_points_equals_brute_force_up_to_61():
    n = 0
    for p in (47, 53, 59, 61):
        for a, b in nonsingular_pairs(p):
            assert count_points(a, b, p) == count_points_bruteforce(a, b, p), (a, b, p)
            n += 1
    assert n == 12000  # 7968 + 12000 = 19968 curves across the two tiers


def test_docs_09_pinned_value():
    """p = 1009, y^2 = x^3 - x: N = 1040, a_p = -30 (docs/09 section 1.1)."""
    assert count_points(-1, 0, 1009) == 1040
    assert trace_of_frobenius(-1, 0, 1009) == -30
    assert 2 * math.sqrt(1009) == pytest.approx(63.5295206970, abs=1e-9)


def test_gauss_two_squares_oracle():
    """a_p for y^2 = x^3 - x from Gauss's theorem — no point counting at all.

    p = A^2 + B^2 with A odd and A + B = 1 mod 4 gives a_p = 2A (and a_p = 0
    for p = 3 mod 4).  Agreement over all 301 primes below 2000.
    """
    primes = list(sympy.primerange(5, 2000))
    assert len(primes) == 301
    for p in primes:
        assert gauss_trace(p) == trace_of_frobenius(-1, 0, p), p
        if p % 4 == 3:
            assert gauss_trace(p) == 0
        else:
            A = gauss_trace(p) // 2
            B2 = p - A * A
            B = math.isqrt(B2)
            assert B * B == B2 and A % 2 != 0 and (A + B) % 4 == 1
    assert gauss_trace(10009) == trace_of_frobenius(-1, 0, 10009) == -6
    assert gauss_trace(1009) == -30


def test_supersingular_families():
    """Two classical CM families where a_p vanishes for structural reasons."""
    for p in sympy.primerange(5, 500):
        if p % 4 == 3:  # y^2 = x^3 - x is supersingular
            assert trace_of_frobenius(-1, 0, p) == 0
            assert count_points(-1, 0, p) == p + 1
        if p % 3 == 2:  # y^2 = x^3 + b is supersingular for every b != 0
            for b in (1, 2, 3):
                assert trace_of_frobenius(0, b, p) == 0


def test_quadratic_twist_negates_the_trace():
    """(a,b) -> (d^2 a, d^3 b) multiplies a_p by (d|p): the twisting symmetry."""
    for p in (11, 13, 17, 101, 1009):
        rng = random.Random(p)
        for _ in range(12):
            a, b = random_curve(p, rng)
            ap = trace_of_frobenius(a, b, p)
            for d in range(1, p):
                at, bt = d * d % p * a % p, d ** 3 % p * b % p
                assert trace_of_frobenius(at, bt, p) == legendre_symbol(d, p) * ap


# ---------------------------------------------------------------------------
# 4. the zeta function of the curve
# ---------------------------------------------------------------------------

def test_zeta_numerator_and_eigenvalues_are_consistent():
    for p in (11, 101, 1009, 10007):
        rng = random.Random(p)
        for _ in range(6):
            a, b = random_curve(p, rng)
            c0, c1, c2 = zeta_numerator(a, b, p)
            ap = trace_of_frobenius(a, b, p)
            assert [c0, c1, c2] == [1, -ap, p]
            with mp.workdps(40):
                alpha, alphabar = frobenius_eigenvalues(a, b, p, dps=40)
                # alpha + alphabar is EXACTLY a_p: alpha = mpf(a_p)/2 + i(...),
                # and mpf(int)/2 is exact in binary, so the pair sums with no
                # round-off at all.  Asserted as equality, not as a tolerance.
                assert alpha + alphabar - ap == 0
                # measured worst case over these 24 curves: 1.88e-37
                assert abs(alpha * alphabar - p) < mp.mpf(10) ** -36
                assert mp.im(alpha) > 0 and mp.conj(alpha) == alphabar
                # T = 1/alpha is a root of the numerator (measured 2.31e-41)
                for al in (alpha, alphabar):
                    t = 1 / al
                    assert abs(c0 + c1 * t + c2 * t ** 2) < mp.mpf(10) ** -40


def test_zeta_function_values_against_hand_evaluation():
    a, b, p = -1, 0, 1009
    ap = -30
    with mp.workdps(30):
        for T in (mp.mpf("0.01"), mp.mpf("-0.5"), mp.mpc("0.2", "0.3")):
            expect = (1 - ap * T + p * T ** 2) / ((1 - T) * (1 - p * T))
            # measured worst case over these three T: 1.02e-31
            assert abs(zeta_function_values(a, b, p, T, dps=30) - expect) < mp.mpf(10) ** -30
    # the H^0 and H^2 poles are refused -- exactly, via rational arithmetic
    for T in (1, 1.0, Fraction(1), Fraction(1, 1009)):
        with pytest.raises(ValueError, match="pole"):
            zeta_function_values(a, b, p, T)
    # ...while the float 1/1009, a different rational, is evaluated honestly:
    # a large finite value, not an exception and not an infinity.
    near = zeta_function_values(a, b, p, 1.0 / 1009, dps=30)
    assert mpmath.isfinite(near) and abs(near) > 1e13


def test_zeta_equals_exp_of_the_counting_series():
    """Z(T) = exp(sum_n N_n T^n / n): the *definition* vs Weil's rational form.

    Measured exactly 0.0 at dps = 30 and dps = 50 with n_max = 60, for six
    curves spanning p = 7 to 10007.  With n_max = 40 at dps = 50 the truncation
    tail 10^-41/41 = 2.4e-43 becomes visible — asserted, so the test would
    notice if the series were being silently over-truncated.
    """
    curves = [(1, 1, 101), (-1, 0, 1009), (0, 1, 997), (3, 5, 53), (2, 3, 7), (0, 2, 10007)]
    worst15 = 0.0
    for a, b, p in curves:
        assert zeta_log_series_defect(a, b, p, 60, dps=30) == 0
        assert zeta_log_series_defect(a, b, p, 60, dps=50) == 0
        d = zeta_log_series_defect(a, b, p, 40, dps=50)
        assert 1e-44 < float(d) < 1e-41
        worst15 = max(worst15, float(zeta_log_series_defect(a, b, p, 60, dps=15)))
    # at dps = 15 the truncation is invisible and what is left is round-off:
    # measured 2.22e-16, i.e. one ulp of Z(T) ~ 1.  Pinned two-sided.
    assert 1e-17 < worst15 < 1e-15, worst15


def test_curve_functional_equation_Z_of_one_over_pT():
    """Z(1/(pT)) = Z(T) — under T = p^{-s} this is exactly s <-> 1-s.

    The identity is algebraic (the numerator is self-reciprocal), so the defect
    is pure round-off at the requested precision.  Measured worst case over six
    curves and five T values: 2.487e-14 at dps = 15, 9.466e-30 at dps = 30,
    3.421e-49 at dps = 50.  Pinned two-sided within a factor of three: an upper
    bound alone would be passed just as happily by a function that returned
    zero, and a lower bound alone by one that lost precision.
    """
    curves = [(1, 1, 101), (-1, 0, 1009), (0, 1, 997), (3, 5, 53), (2, 3, 7), (0, 2, 10007)]
    for dps, pinned in ((15, 2.487e-14), (30, 9.466e-30), (50, 3.421e-49)):
        worst = 0.0
        for a, b, p in curves:
            with mp.workdps(dps):
                Ts = [mp.mpf("0.31"), mp.mpf(-3), mp.mpf("0.02"), mp.mpf("2.5"),
                      mp.mpc("0.2", "0.7")]
            for T in Ts:
                worst = max(worst, float(zeta_functional_equation_defect(a, b, p, T, dps=dps)))
        assert pinned / 3 < worst < pinned * 3, (dps, worst)
    with pytest.raises(ValueError):
        zeta_functional_equation_defect(1, 1, 101, 0)


# ---------------------------------------------------------------------------
# 5. RH form one: the Hasse bound, with zero violations
# ---------------------------------------------------------------------------

def test_hasse_check_shape_and_pinned_values():
    h = hasse_check(-1, 0, 1009)
    assert set(h) >= {"a_p", "bound", "satisfied", "ratio"}
    assert h["a_p"] == -30 and h["N_1"] == 1040
    assert h["bound"] == pytest.approx(63.52952069707436, rel=1e-14)
    assert h["satisfied"] is True
    assert h["ratio"] == pytest.approx(30 / 63.52952069707436, rel=1e-14)
    # supersingular: a_p = 0, ratio 0
    h0 = hasse_check(-1, 0, 103)  # 103 = 3 mod 4
    assert h0["a_p"] == 0 and h0["ratio"] == 0.0 and h0["satisfied"] is True


def test_hasse_holds_for_every_curve_over_the_small_primes():
    """Exhaustive, in exact integers: 7 968 curves, zero violations."""
    violations = []
    for p in SMALL_PRIMES:
        for a, b in nonsingular_pairs(p):
            ap = trace_of_frobenius(a, b, p)
            if ap * ap > 4 * p:
                violations.append((a, b, p, ap))
    assert violations == []


def test_hasse_holds_for_over_a_million_curves():
    """Every curve over p = 101, 503, 1009: 1 279 678 of them, zero violations.

    This is RH for those 1 279 678 curves, checked by counting.  It cannot fail
    — Hasse's theorem — so a failure here means a bug in this module.
    """
    total = 0
    for p in (101, 503, 1009):
        ap = traces_mod_p(p)
        assert ap.size == p * p - p
        assert int((ap.astype(np.int64) ** 2 > 4 * p).sum()) == 0
        total += int(ap.size)
    assert total == 1_279_678


def test_large_seeded_survey_has_zero_violations():
    """862 curves over 18 primes from 5 to 10007."""
    rows = curve_survey(SURVEY_PRIMES, 50, seed=20260801, dps=30)
    s = survey_summary(rows)
    assert s["n_curves"] == 862
    assert s["violations"] == 0
    assert all(r["satisfied"] for r in rows)
    assert all(abs(r["a_p"]) <= r["bound"] for r in rows)
    # exact integer restatement of the same bound
    assert all(r["a_p"] ** 2 <= 4 * r["p"] for r in rows)
    # the bound is nearly attained somewhere, so it is not vacuous
    assert 0.99 < s["max_ratio"] < 1.0
    assert s["primes"] == sorted(SURVEY_PRIMES)


def test_survey_is_reproducible_and_deduplicated():
    r1 = curve_survey((101, 1009), 20, seed=7)
    r2 = curve_survey((101, 1009), 20, seed=7)
    r3 = curve_survey((101, 1009), 20, seed=8)
    assert [(r["p"], r["a"], r["b"]) for r in r1] == [(r["p"], r["a"], r["b"]) for r in r2]
    assert [(r["p"], r["a"], r["b"]) for r in r1] != [(r["p"], r["a"], r["b"]) for r in r3]
    for rows in (r1, r3):
        keys = [(r["p"], r["a"], r["b"]) for r in rows]
        assert len(keys) == len(set(keys))
    # asking for more curves than exist mod p yields all of them, exactly once
    full = curve_survey((5,), 10 ** 6)
    assert len(full) == 5 * 5 - 5
    assert {(r["a"], r["b"]) for r in full} == set(nonsingular_pairs(5))


def test_survey_summary_rejects_empty():
    with pytest.raises(ValueError):
        survey_summary([])


# ---------------------------------------------------------------------------
# 6. RH form two: Re(s) = 1/2 on the nose
# ---------------------------------------------------------------------------

def test_critical_line_for_every_surveyed_curve():
    """T = p^{-s} puts every numerator root at Re(s) = 1/2.

    Demanded: 1e-12.  Measured at dps = 30 over these 862 curves: worst case
    1.148e-41, so the loose tolerance is not what makes the test pass.
    """
    rows = curve_survey(SURVEY_PRIMES, 50, seed=20260801, dps=30)
    assert len(rows) == 862
    worst = 0.0
    for r in rows:
        assert r["max_deviation_from_half"] < 1e-12
        worst = max(worst, r["max_deviation_from_half"])
        for re in r["re_s"]:
            assert abs(re - 0.5) < 1e-12
    assert worst < 1e-38          # the honest, tight bound
    assert survey_summary(rows)["max_deviation_from_half"] == worst


def test_critical_line_check_internals():
    for p in (7, 101, 1009, 10007):
        rng = random.Random(p + 1)
        for _ in range(5):
            a, b = random_curve(p, rng)
            c = critical_line_check(a, b, p, dps=30)
            assert set(c) >= {"re_s", "max_deviation_from_half"}
            with mp.workdps(30):
                # the returned Re(s), at the returned precision, IS one half
                assert all(r == mp.mpf(1) / 2 for r in c["re_s"])
                # |alpha| = sqrt p.  Measured worst case over these 20 curves:
                # 4.59e-41 at dps = 30, so the bound below is 20x, not 1e13x.
                assert c["abs_alpha_defect"] < 1e-39
                # roots_T are the numerator's roots, and p^{-s} = T
                # (measured 1.97e-31 and 8.89e-32 respectively)
                c0, c1, c2 = zeta_numerator(a, b, p)
                for t, s in zip(c["roots_T"], [mp.mpc(r, i) for r, i in
                                               zip(c["re_s"], c["im_s"])]):
                    assert abs(c0 + c1 * t + c2 * t ** 2) < mp.mpf(10) ** -30
                    assert abs(mp.power(p, -s) - t) < mp.mpf(10) ** -30
            # the two roots are complex conjugates, never real: 4p - a_p^2 > 0
            assert c["a_p"] ** 2 < 4 * p
            assert c["im_s"][0] > 0 > c["im_s"][1]
            # exact: alphabar is mp.conj(alpha), and mpmath's integer powers and
            # log preserve conjugation bit for bit, so the sum is exactly zero.
            assert c["im_s"][0] + c["im_s"][1] == 0


@pytest.mark.slow
def test_critical_line_deviation_tracks_the_requested_precision():
    """The reported deviation is a real measurement, not hard-wired to zero.

    Over the 862-curve survey the worst ``|Re s - 1/2|`` is 8.47e-22 at
    dps = 10, 9.86e-32 at dps = 20, 1.15e-41 at dps = 30 and 7.78e-62 at
    dps = 50 — i.e. it falls by ten orders of magnitude for every ten digits
    requested, which is what a genuine round-off measurement does.  (Most
    individual curves give exactly 0.0; only the maximum over a large sample
    exposes the scale, which is why this test needs the whole survey.)
    """
    devs = {}
    for dps in (10, 20, 30, 50):
        rows = curve_survey(SURVEY_PRIMES, 50, seed=20260801, dps=dps)
        devs[dps] = max(r["max_deviation_from_half"] for r in rows)
    assert devs[10] > devs[20] > devs[30] > devs[50] > 0
    for dps, d in devs.items():
        assert d < 10.0 ** -(dps + 8)      # about 10^{-(dps+11)} in practice
        assert d < 1e-12
    for dps, pinned in ((10, 8.470e-22), (20, 9.861e-32),
                        (30, 1.148e-41), (50, 7.779e-62)):
        assert devs[dps] == pytest.approx(pinned, rel=0.01), (dps, devs[dps])


# ---------------------------------------------------------------------------
# 7. Lefschetz: solution counts are traces of powers of Frobenius
# ---------------------------------------------------------------------------

def test_power_traces_match_the_complex_eigenvalues():
    """The exact integer recursion t_n = a_p t_{n-1} - p t_{n-2} vs alpha^n + alphabar^n."""
    for p in (7, 101, 1009):
        rng = random.Random(p + 2)
        for _ in range(5):
            a, b = random_curve(p, rng)
            t = frobenius_power_traces(a, b, p, 8)
            with mp.workdps(50):
                alpha, alphabar = frobenius_eigenvalues(a, b, p, dps=50)
                for n in range(1, 9):
                    want = alpha ** n + alphabar ** n
                    # exactly real: alphabar = conj(alpha) bit for bit, so
                    # alphabar^n = conj(alpha^n) and the imaginary parts cancel
                    assert mp.im(want) == 0
                    rel = abs(want - t[n - 1]) / max(1, abs(t[n - 1]))
                    # measured worst case over these 15 curves: 4.54e-50
                    assert rel < mp.mpf(10) ** -48, (p, a, b, n)
            assert all(isinstance(x, int) for x in t)
    with pytest.raises(ValueError):
        frobenius_power_traces(1, 1, 101, 0)


def test_N1_from_the_extension_list_matches_brute_force():
    for p in (5, 7, 11, 13, 17, 19):
        for a, b in nonsingular_pairs(p):
            assert point_counts_over_extensions(a, b, p, 4)[0] == count_points_bruteforce(a, b, p)


def test_lefschetz_N2_against_brute_force_over_Fp2_literal_double_loop():
    """THE test: N_2 = p^2 + 1 - (alpha^2 + alphabar^2) vs counting in F_{p^2}.

    ``method="pairs"`` is the literal double loop over all p^4 pairs (x, y) in
    F_{p^2} x F_{p^2}, using only the explicit field arithmetic of
    ``fp2_mul`` — no zeta function, no eigenvalues, no Weil theory.  Run
    exhaustively over every nonsingular curve for p = 5, 7, 11 (172 curves).
    """
    n = 0
    for p in (5, 7, 11):
        for a, b in nonsingular_pairs(p):
            predicted = point_counts_over_extensions(a, b, p, 2)[1]
            assert count_points_fp2(a, b, p, method="pairs") == predicted, (a, b, p)
            assert count_points_fp2(a, b, p, method="table") == predicted, (a, b, p)
            n += 1
    assert n == 172


def test_lefschetz_N2_at_larger_primes():
    """Same check to p = 199, via the O(p^2) tabulated enumeration."""
    for p in (13, 17, 31, 53, 101, 127, 199):
        rng = random.Random(p + 3)
        for _ in range(4):
            a, b = random_curve(p, rng)
            assert count_points_fp2(a, b, p) == point_counts_over_extensions(a, b, p, 2)[1]
    # spot values computed here and pinned
    assert count_points_fp2(1, 1, 5) == 27
    assert count_points_fp2(0, 1, 7) == 48
    assert count_points_fp2(-1, 0, 13) == 160


def _irreducible_quadratic(p: int, rng: random.Random) -> tuple[int, int]:
    """Random ``(c, d)`` with ``t^2 - c t - d`` irreducible over F_p.

    Irreducible iff the discriminant ``c^2 + 4d`` is a quadratic non-residue.
    Deliberately *not* of the module's shape ``t^2 - n`` (which is the case
    c = 0): a genuinely different presentation of F_{p^2}.
    """
    while True:
        c, d = rng.randrange(p), rng.randrange(p)
        disc = (c * c + 4 * d) % p
        if disc != 0 and pow(disc, (p - 1) // 2, p) == p - 1:
            return c, d


def _mul_ct_d(u, v, p, c, d):
    """Multiply in ``F_p[t]/(t^2 - c t - d)``, i.e. with ``t^2 = c t + d``."""
    hi = u[1] * v[1]
    return ((u[0] * v[0] + hi * d) % p, (u[0] * v[1] + u[1] * v[0] + hi * c) % p)


def _count_fp2_general(a, b, p, c, d):
    """``#E(F_{p^2})`` in the ``t^2 = ct + d`` model — no module code at all."""
    squares: dict[tuple[int, int], int] = {}
    for y0 in range(p):
        for y1 in range(p):
            s = _mul_ct_d((y0, y1), (y0, y1), p, c, d)
            squares[s] = squares.get(s, 0) + 1
    total = 1
    for x0 in range(p):
        for x1 in range(p):
            x = (x0, x1)
            x3 = _mul_ct_d(_mul_ct_d(x, x, p, c, d), x, p, c, d)
            r = ((x3[0] + a * x0 + b) % p, (x3[1] + a * x1) % p)
            total += squares.get(r, 0)
    return total


def test_lefschetz_N2_in_a_second_model_of_Fp2():
    """N_2 again, in a *different* presentation of F_{p^2}.

    ``count_points_fp2`` builds F_{p^2} as ``F_p[t]/(t^2 - n)``.  If that one
    construction were subtly wrong (wrong non-residue, wrong reduction rule)
    both of its methods would be wrong together and the Lefschetz test would
    confirm nothing.  Here F_{p^2} is built as ``F_p[t]/(t^2 - c t - d)`` with
    a random irreducible quadratic (``c != 0`` in general), the counting is
    done by code local to this test, and the answer must still be
    ``p^2 + 1 - (alpha^2 + alphabar^2)`` — exhaustively for p = 5, 7, 11, 13.
    """
    n = 0
    cs = []
    for p in (5, 7, 11, 13):
        rng = random.Random(p * 97 + 5)
        c, d = _irreducible_quadratic(p, rng)
        cs.append(c)
        for a, b in nonsingular_pairs(p):
            predicted = point_counts_over_extensions(a, b, p, 2)[1]
            assert _count_fp2_general(a, b, p, c, d) == predicted, (a, b, p, c, d)
            assert count_points_fp2(a, b, p) == predicted
            n += 1
    assert n == 20 + 42 + 110 + 156
    # the second model really is a different one: some c is nonzero, i.e. the
    # defining polynomial is not of the module's t^2 - n shape.
    assert any(c != 0 for c in cs), cs


def test_N2_equals_N1_times_the_quadratic_twist_count():
    """A third, purely arithmetic route to N_2: ``N_2 = N_1 * N_1(twist)``.

    ``#E(F_{p^2}) = (p+1)^2 - a_p^2 = (p+1-a_p)(p+1+a_p)``, and ``p+1+a_p`` is
    the point count of the quadratic twist over F_p — which this test obtains
    by *counting the twist*, not by negating a_p.  So the identity is checked
    against two genuine F_p point counts.
    """
    for p in (5, 7, 11, 13, 17, 31, 101, 199):
        rng = random.Random(p + 11)
        nr = quadratic_nonresidue(p)
        for _ in range(4):
            a, b = random_curve(p, rng)
            n1 = count_points(a, b, p)
            twist = count_points(nr * nr % p * a % p, nr ** 3 % p * b % p, p)
            assert point_counts_over_extensions(a, b, p, 2)[1] == n1 * twist


def test_count_points_fp2_rejects_unknown_method():
    with pytest.raises(ValueError, match="method"):
        count_points_fp2(1, 1, 11, method="magic")


def test_extension_counts_obey_the_weil_bound_and_group_divisibility():
    """|N_n - (p^n + 1)| <= 2 p^{n/2} (RH over every extension), and N_1 | N_n.

    The divisibility is a group-theoretic fact independent of everything above:
    E(F_p) is a subgroup of E(F_{p^n}).
    """
    for p in (5, 11, 101, 1009):
        rng = random.Random(p + 4)
        for _ in range(6):
            a, b = random_curve(p, rng)
            Ns = point_counts_over_extensions(a, b, p, 10)
            for n, N in enumerate(Ns, start=1):
                assert N > 0
                assert (N - (p ** n + 1)) ** 2 <= 4 * p ** n   # exact integer form
                assert N % Ns[0] == 0
            assert Ns[0] == count_points(a, b, p)


# ---------------------------------------------------------------------------
# 8. the vertical Sato-Tate law
# ---------------------------------------------------------------------------

def test_traces_mod_p_agrees_with_trace_of_frobenius():
    """The FFT sweep vs the per-curve routine, exhaustively at p = 53."""
    p = 53
    got = traces_mod_p(p)
    want = [trace_of_frobenius(a, b, p) for a, b in nonsingular_pairs(p)]
    assert got.tolist() == want
    # and on a random sample at a bigger prime
    p = 1009
    got = traces_mod_p(p)
    pairs = nonsingular_pairs(p)
    rng = random.Random(0)
    for _ in range(40):
        i = rng.randrange(len(pairs))
        a, b = pairs[i]
        assert int(got[i]) == trace_of_frobenius(a, b, p)


def test_traces_mod_p_against_a_direct_integer_matmul():
    """Second method, no FFT: chi table times the multiplicity vector, in int64."""
    for p in (23, 101):
        x = np.arange(p, dtype=np.int64)
        chi = np.array([legendre_symbol(int(v), p) for v in x], dtype=np.int64)
        cube = (x * x % p * x) % p
        v = np.arange(p).reshape(-1, 1)
        bb = np.arange(p).reshape(1, -1)
        C = chi[(v + bb) % p]
        direct = np.empty((p, p), dtype=np.int64)
        for a in range(p):
            direct[a, :] = -(np.bincount((cube + a * x) % p, minlength=p) @ C)
        aa = np.arange(p, dtype=np.int64).reshape(-1, 1)
        mask = (4 * aa ** 3 + 27 * bb ** 2) % p != 0
        assert traces_mod_p(p).tolist() == direct[mask].tolist()


def test_row_invariants_match_a_straight_integer_computation():
    """The exact identities that make the float64 FFT safe, re-derived by hand.

    For each ``a``: ``sum_b a_p(a,b) = 0`` and
    ``sum_b a_p(a,b)^2 = p * sum_v c_v^2 - p^2``, with
    ``c_v = #{x : x^3 + a x = v}``.  Here both sides are recomputed in pure
    Python integers — the character sums ``sum_x chi(x^3+ax+b)`` are formed
    term by term, with no FFT and no numpy — and compared with
    ``_row_invariants``.
    """
    import zeta.finitefield as ff

    for p in (5, 7, 11, 13, 23, 53):
        chi = [legendre_symbol(v, p) for v in range(p)]
        for a in range(p):
            c = [0] * p
            for x in range(p):
                c[(x ** 3 + a * x) % p] += 1
            ap_row = [-sum(c[v] * chi[(v + b) % p] for v in range(p)) for b in range(p)]
            want_sum, want_sq = ff._row_invariants(
                np.array([c], dtype=np.int64), p
            )
            assert sum(ap_row) == int(want_sum[0]) == 0
            assert sum(v * v for v in ap_row) == int(want_sq[0])
            assert int(want_sq[0]) == p * sum(v * v for v in c) - p * p
            # and the row really is the trace row of traces_mod_p
            for b in range(p):
                if (4 * a ** 3 + 27 * b ** 2) % p != 0:
                    assert ap_row[b] == trace_of_frobenius(a, b, p)


def test_fft_integer_recovery_guard_actually_fires():
    """The guard in ``traces_mod_p`` is a real check, not decoration.

    ``np.rint`` alone proves nothing: an FFT error of 0.9 rounds to the *wrong*
    integer while leaving a residual of only 0.1, well under the 0.25 slack
    threshold.  So the recovery is verified against the exact row identities
    instead — corrupt a single entry by 1 and ``_verify_trace_rows`` must raise.
    """
    import zeta.finitefield as ff

    # the rounding-residual test is genuinely unsound, by construction:
    conv = np.array([[3.0 + 0.9]])
    assert np.rint(conv)[0, 0] == 4.0
    assert float(np.abs(conv - np.rint(conv)).max()) < 0.25

    p = 23
    x = np.arange(p, dtype=np.int64)
    counts = np.empty((p, p), dtype=np.int64)
    for a in range(p):
        counts[a] = np.bincount((x ** 3 + a * x) % p, minlength=p)
    rows = np.empty((p, p), dtype=np.int64)
    chi = [legendre_symbol(int(v), p) for v in range(p)]
    for a in range(p):
        for b in range(p):
            rows[a, b] = -sum(int(counts[a, v]) * chi[(v + b) % p] for v in range(p))
    # clean rows pass
    assert ff._verify_trace_rows(rows, counts, p) == p
    # every single-entry +/-1 corruption is caught
    for (a, b) in ((0, 0), (3, 7), (11, 22), (22, 5)):
        for delta in (+1, -1):
            bad = rows.copy()
            bad[a, b] += delta
            with pytest.raises(RuntimeError, match="integer recovery failed"):
                ff._verify_trace_rows(bad, counts, p)
    # a sign flip on a nonzero entry is caught too
    a, b = next((a, b) for a in range(p) for b in range(p) if rows[a, b] != 0)
    bad = rows.copy()
    bad[a, b] = -bad[a, b]
    with pytest.raises(RuntimeError, match="integer recovery failed"):
        ff._verify_trace_rows(bad, counts, p)


def test_exact_identities_of_the_trace_multiset():
    """sum a_p = 0, sum a_p^2 = (p-1)^2 (p+1), and Deuring's full coverage."""
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 101, 211, 503):
        ap = traces_mod_p(p).astype(object)
        assert int(sum(ap)) == 0                       # quadratic-twist symmetry
        assert int(sum(v * v for v in ap)) == (p - 1) ** 2 * (p + 1)
        # Deuring 1941: every integer in the Hasse interval is attained
        attained = {int(v) for v in ap}
        assert attained == {t for t in range(-math.isqrt(4 * p), math.isqrt(4 * p) + 1)}
        # the multiset is exactly symmetric under a_p -> -a_p
        counts: dict[int, int] = {}
        for v in ap:
            counts[int(v)] = counts.get(int(v), 0) + 1
        assert all(counts[t] == counts[-t] for t in counts)


def test_sato_tate_histogram_structure_and_exact_moments():
    st = sato_tate_histogram(503, n_bins=20, cache=False)
    assert st["p"] == 503
    assert st["n_curves"] == 503 * 503 - 503 == 252506
    assert st["hasse_violations"] == 0
    assert st["sum_a_p"] == 0
    assert st["max_abs_a_p"] == 44 < 2 * math.sqrt(503)
    assert st["second_moment_exact"] == st["second_moment_closed_form"] == 127010016
    assert st["distinct_traces"] == st["hasse_interval_size"] == 89
    assert st["counts"].sum() == st["n_curves"]
    assert st["density"].shape == st["semicircle"].shape == (20,)
    # a probability density: integrates to 1
    assert float(st["density"].sum() * 2 / 20) == pytest.approx(1.0, abs=1e-12)
    # normalised traces live in [-1, 1] -- that containment *is* RH here
    assert st["bin_edges"][0] == -1.0 and st["bin_edges"][-1] == 1.0
    with pytest.raises(ValueError):
        sato_tate_histogram(503, n_bins=0, cache=False)


def test_sato_tate_moments_approach_the_semicircle():
    """mean((a_p/2 sqrt p)^{2k}) -> C_k/4^k = 1/4, 1/8, 5/64 (Catalan/4^k).

    The second moment is *exactly* ``(p^2-1)/(4p^2)``, from the closed form
    ``sum a_p^2 = (p-1)^2 (p+1)`` — so its deviation from 1/4 is exactly
    ``1/(4p^2)``.  Measured here: all three deviations scale the same way,

        p = 101:  2.45e-5, 1.84e-5, 1.39e-5    (1/(4p^2) = 2.451e-5)
        p = 503:  9.88e-7, 7.42e-7, 5.56e-7    (1/(4p^2) = 9.881e-7)
        p = 1009: 2.46e-7, 1.84e-7, 1.38e-7
        p = 2003: 6.23e-8, 4.67e-8, 3.51e-8    (1/(4p^2) = 6.231e-8)

    so the bound below is tight to 1% for k = 1 and is a real constraint on
    the fourth and sixth moments, not a formality.  (The ratios 1 : 0.75 :
    0.5625 are an observation only; nothing here depends on them.)
    """
    prev = None
    for p in (101, 503, 1009, 2003):
        st = sato_tate_histogram(p, cache=False)
        m = st["moments"]
        assert m[0] == pytest.approx((p * p - 1) / (4.0 * p * p), rel=1e-12)
        assert abs(m[0] - 0.25) == pytest.approx(1.0 / (4.0 * p * p), rel=1e-9)
        for got, want in zip(m, (0.25, 0.125, 5 / 64)):
            assert abs(got - want) <= 1.01 / (4.0 * p * p), (p, got, want)
        if prev is not None:  # monotone improvement with p, all three moments
            assert all(abs(g - w) < abs(q - w)
                       for g, q, w in zip(m, prev, (0.25, 0.125, 5 / 64)))
        prev = m
        if p == 101:  # the exact triple quoted in the module docstring
            for got, want, pinned in zip(m, (0.25, 0.125, 5 / 64),
                                         (2.451e-5, 1.844e-5, 1.386e-5)):
                assert abs(got - want) == pytest.approx(pinned, rel=0.01)
        if p == 2003:
            for got, want, pinned in zip(m, (0.25, 0.125, 5 / 64),
                                         (6.231e-8, 4.674e-8, 3.506e-8)):
                assert abs(got - want) == pytest.approx(pinned, rel=0.01)


@pytest.mark.slow
def test_sato_tate_histogram_converges_to_the_semicircle():
    """Measured sup deviation of the density from (2/pi) sqrt(1-x^2), 20 bins.

    0.218 (p=503) -> 0.122 (p=1009) -> 0.140 (p=2003) -> 0.054 (p=4001).  It is
    NOT monotone bin-by-bin, which is why only the endpoints are asserted.
    """
    sups = {p: sato_tate_histogram(p, n_bins=20, cache=False)["sup_deviation"]
            for p in (503, 1009, 2003, 4001)}
    for p, pinned in ((503, 0.2183), (1009, 0.1224), (2003, 0.1404), (4001, 0.0540)):
        assert sups[p] == pytest.approx(pinned, abs=5e-4), (p, sups[p])
    assert sups[4001] < sups[503] / 3
    l1 = {p: sato_tate_histogram(p, n_bins=20, cache=False)["l1_deviation"]
          for p in (503, 4001)}
    assert l1[503] == pytest.approx(0.1669, abs=5e-4)
    assert l1[4001] == pytest.approx(0.0409, abs=5e-4)


def test_shipped_cache_agrees_with_a_fresh_computation():
    """Guards against a stale ``data/finitefield_ap_counts_p*.json``.

    If the cache files shipped in ``data/`` were computed by different code
    they would silently make the statistics tests pass on old numbers.
    """
    import json

    import zeta.finitefield as ff

    for p in (503, 1009, 2003):
        path = ff._sato_tate_cache_path(p)
        assert path.exists(), path.name
        shipped = {int(k): int(v)
                   for k, v in json.loads(path.read_text())["counts"].items()}
        # the shipped file passes the integrity check, so it really is the file
        # being used -- otherwise the comparison below would be vacuous
        assert ff._trace_counts_are_consistent(shipped, p), p
        vals, cnts = np.unique(traces_mod_p(p), return_counts=True)
        assert shipped == {int(v): int(c) for v, c in zip(vals, cnts)}, p

        cached = sato_tate_histogram(p, cache=True)
        fresh = sato_tate_histogram(p, cache=False)
        assert cached["counts"].tolist() == fresh["counts"].tolist()
        assert cached["second_moment_exact"] == fresh["second_moment_exact"]
        assert cached["n_curves"] == fresh["n_curves"] == p * p - p
        assert cached["distinct_traces"] == fresh["distinct_traces"]
        assert cached["second_moment_exact"] == (p - 1) ** 2 * (p + 1)


@pytest.mark.slow
def test_shipped_cache_agrees_with_a_fresh_computation_p4001():
    """Same stale-cache guard for the largest shipped cache (p = 4001)."""
    import json

    import zeta.finitefield as ff

    path = ff._sato_tate_cache_path(4001)
    assert path.exists()
    shipped = {int(k): int(v) for k, v in json.loads(path.read_text())["counts"].items()}
    assert ff._trace_counts_are_consistent(shipped, 4001)
    vals, cnts = np.unique(traces_mod_p(4001), return_counts=True)
    assert shipped == {int(v): int(c) for v, c in zip(vals, cnts)}

    cached = sato_tate_histogram(4001, cache=True)
    fresh = sato_tate_histogram(4001, cache=False)
    assert cached["counts"].tolist() == fresh["counts"].tolist()
    assert cached["second_moment_exact"] == fresh["second_moment_exact"] == 4000 ** 2 * 4002
    assert cached["n_curves"] == fresh["n_curves"] == 4001 ** 2 - 4001


def test_a_stale_cache_is_rejected_not_trusted(tmp_path, monkeypatch):
    """CLAUDE.md: "stale numbers will pass".  Here they must not.

    The cache is keyed on p alone, so a table written by earlier code would be
    trusted forever unless something checks it.  A damaged table — one curve
    moved from trace t to trace t+2, which keeps the total count and the
    (already zero) sum but breaks ``sum a_p^2 = (p-1)^2 (p+1)`` — must be
    detected and recomputed, not returned.
    """
    import json

    import zeta.finitefield as ff

    monkeypatch.setattr(ff, "_DATA_DIR", tmp_path)
    good = ff.sato_tate_histogram(101, cache=True)
    path = tmp_path / "finitefield_ap_counts_p101.json"
    raw = json.loads(path.read_text())
    counts = {int(k): int(v) for k, v in raw["counts"].items()}
    assert ff._trace_counts_are_consistent(counts, 101)

    # move one curve from a_p = 2 to a_p = 4: count and sum-of-traces survive
    # the edit only if we also move one from -2 to -4, so do both.
    for t, u in ((2, 4), (-2, -4)):
        counts[t] -= 1
        counts[u] += 1
    assert sum(counts.values()) == 101 * 101 - 101
    assert sum(t * c for t, c in counts.items()) == 0
    assert not ff._trace_counts_are_consistent(counts, 101)   # caught by sum a_p^2

    path.write_text(json.dumps({"p": 101, "counts": {str(k): v for k, v in counts.items()}}))
    recovered = ff.sato_tate_histogram(101, cache=True)
    assert recovered["counts"].tolist() == good["counts"].tolist()
    assert recovered["second_moment_exact"] == 100 ** 2 * 102

    # other failure modes of the integrity check
    assert not ff._trace_counts_are_consistent({}, 101)
    assert not ff._trace_counts_are_consistent({0: 101 * 100}, 101)   # sum a_p^2
    bad = dict(counts)
    bad[10 ** 6] = 1                                                  # Hasse
    assert not ff._trace_counts_are_consistent(bad, 101)
    assert not ff._trace_counts_are_consistent({0: -1}, 101)          # negative


def test_sato_tate_cache_round_trip(tmp_path, monkeypatch):
    import zeta.finitefield as ff

    monkeypatch.setattr(ff, "_DATA_DIR", tmp_path)
    fresh = ff.sato_tate_histogram(101, cache=True)
    assert (tmp_path / "finitefield_ap_counts_p101.json").exists()
    cached = ff.sato_tate_histogram(101, cache=True)
    assert cached["n_curves"] == fresh["n_curves"]
    assert cached["second_moment_exact"] == fresh["second_moment_exact"]
    assert cached["counts"].tolist() == fresh["counts"].tolist()


# ---------------------------------------------------------------------------
# 9. the prose, and the honest-scope rule
# ---------------------------------------------------------------------------

def test_weil_conjecture_facts_are_labelled_theorems_and_point_at_the_gap():
    f = weil_conjecture_facts()
    assert f["status"].startswith("THEOREM")
    assert {"space", "operator", "positivity"} == set(f["ingredients"])
    assert "docs/09-new-ontologies.md" in f["what_is_missing_over_Z"]
    assert "docs/11-f1-and-the-missing-geometry.md" in f["what_is_missing_over_Z"]
    assert "is evidence for RH over the integers" in f["honest_scope"]
    assert f["honest_scope"].startswith("Nothing in zeta.finitefield")
    who = " ".join(h["who"] for h in f["history"])
    for name in ("Hasse", "Weil", "Deligne", "Grothendieck", "Dwork", "Birch", "Deuring"):
        assert name in who
    assert all({"result", "who", "where"} <= set(h) for h in f["history"])


def test_module_contains_no_absolute_user_paths():
    """House rule: paths are derived from __file__, never hardcoded.

    Checked for the module, for this test file, and for the shipped ``data/``
    caches (a committed file must not carry anyone's home directory).
    """
    import zeta.finitefield as ff

    # assembled, not written out, so that this file does not trip its own check
    needles = ("/" + "Users" + "/", "/" + "home" + "/")
    for path in (ff.__file__, __file__):
        src = open(path, encoding="utf-8").read()
        assert not any(nd in src for nd in needles), path
    assert ff._DATA_DIR.name == "data"
    assert ff._DATA_DIR.parent.name == ff._REPO_ROOT.name
    caches = sorted(ff._REPO_ROOT.glob("data/finitefield_*.json"))
    assert caches, "no shipped caches found to check"
    for cache in caches:
        text = cache.read_text(encoding="utf-8")
        assert not any(nd in text for nd in needles), cache.name
