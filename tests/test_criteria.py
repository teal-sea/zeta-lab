"""Tests for zeta.criteria — four equivalence faces of RH, made executable.

Every literal quoted below was computed and cross-checked in this environment
before it was asserted:

* mu and sigma against sympy (every n <= 2000, plus random n up to 10^7);
* M(x) against a direct sum of mu, against the published table
  M(10^6) = 212, M(10^7) = 1037, and against the Mobius-inversion identity
  sum_{n <= N} M(N // n) = 1, which never mentions mu at all;
* the Baez-Duarte Gram matrix against four independent routes -- the closed
  form <A_2, A_2> = (log 2)/4, an mp.nsum of the same series that never calls
  mp.psi, a Mellin-Parseval integral of |zeta(1/2+it)|^2 over the critical
  line, and a 2*10^6-sample Monte-Carlo of the raw definition
  A_k(x) = {1/(kx)} - (1/k){1/x};
* d_2^2 = 1 - log 2 exactly; d_N^2 independent of dps (25 / 40 / 60 / 90);
  and the whole least-squares solve reproduced in float64 by a Jacobi-scaled
  Cholesky and by numpy's lstsq, out to N = 50;
* Robin's 26 exceptional n <= 20000 against docs/07 *and* against a dps = 30
  re-run of all 19 998 verdicts, sigma(5040) = 19344, and the colossally
  abundant chain against OEIS A004490;
* the two lowest zeros of zeta' against the values in docs/07 (Spira), the
  argument-principle box counts against a refinement of the contour step, and
  the region Re >= 30 against a Dirichlet-series domination bound.

**What is *not* certified.**  The zeta' zero counts are floating-point
argument-principle evaluations, not interval enclosures; see the note in
``zeta_prime_zeros``.  Every test below that depends on them says so.

**Framing.**  Every range-limited assertion below is phrased as "no violation
found in the range scanned".  None of it is evidence for RH; the Mertens face
is in this module precisely because it is the standing counterexample to
reading numerics as evidence (the strong Mertens conjecture survived a century
of confirming computation and is false).
"""

from __future__ import annotations

import math

import numpy as np
import pytest
import sympy
from mpmath import mp

from zeta.criteria import (
    BD_CONSTANT,
    MERTENS_PINNED,
    ROBIN_EXCEPTIONS,
    ROBIN_THRESHOLD,
    ZETA_PRIME_ZEROS_PINNED,
    baez_duarte_basis,
    baez_duarte_d2,
    baez_duarte_gram,
    baez_duarte_rhs,
    baez_duarte_table,
    colossally_abundant,
    criteria_report,
    divisor_sigma,
    harmonic_number,
    lagarias_ratio,
    lagarias_ratio_from_log,
    lagarias_violations,
    mertens_M,
    mertens_array,
    mertens_facts,
    mertens_ratio,
    mertens_ratio_extremes,
    mobius,
    mobius_sieve,
    robin_ratio,
    robin_ratio_from_log,
    robin_search,
    robin_violations,
    sigma_sieve,
    speiser_scan,
    superabundant_candidates,
    zeta_prime,
    zeta_prime_zeros,
)


# ===========================================================================
# 1.  MERTENS / MOBIUS
# ===========================================================================

def test_mobius_agrees_with_sympy_up_to_2000():
    """mu(n) against an independent oracle for every n <= 2000."""
    for n in range(1, 2001):
        assert mobius(n) == sympy.mobius(n), f"mu({n})"


def test_mobius_agrees_with_sympy_on_random_large_n():
    """mu(n) for 200 pseudo-random n up to 10^7 (fixed seed: reproducible)."""
    rng = np.random.default_rng(20240811)
    for n in rng.integers(2, 10**7, size=200):
        n = int(n)
        assert mobius(n) == sympy.mobius(n), f"mu({n})"


def test_mobius_small_values_and_domain():
    assert mobius(1) == 1
    assert [mobius(n) for n in range(1, 13)] == [1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0]
    assert mobius(2 * 3 * 5 * 7) == 1          # four primes, squarefree
    assert mobius(2 * 3 * 5) == -1             # three primes
    assert mobius(4 * 9) == 0                  # not squarefree
    with pytest.raises(ValueError):
        mobius(0)


def test_mobius_sieve_outer_loop_length_is_pi_of_sqrt_limit():
    """The sieve's outer loop runs over the 446 primes below sqrt(10^7).

    That is the number quoted in ``mobius_sieve``'s docstring, and the reason
    the sieve is cheap: 446 iterations rather than one per prime below 10^7.
    The prime list itself is checked against sympy so the 446 is not just this
    module agreeing with itself.
    """
    from zeta.criteria import _primes_upto

    assert math.isqrt(10**7) == 3162
    assert len(_primes_upto(3162)) == 446
    assert _primes_upto(3162) == tuple(sympy.primerange(2, 3163))
    assert sympy.primepi(10**7) == 664579, "the loop it replaces would be 664579 long"


def test_mobius_sieve_matches_pointwise_mobius():
    """The vectorised sieve and the trial-division mu agree everywhere <= 20000."""
    mu = mobius_sieve(20000, use_cache=False)
    assert mu.dtype == np.int8
    assert mu[0] == 0 and mu[1] == 1
    for n in range(1, 20001):
        assert int(mu[n]) == mobius(n), f"sieve mu({n})"


def test_mertens_M_matches_direct_sum():
    """M(x) from the sieve is literally sum_{n <= x} mu(n) -- checked directly."""
    running = 0
    for n in range(1, 6000):
        running += mobius(n)
        assert mertens_M(n) == running, f"M({n})"
    # and the array route agrees with the pointwise route
    M = mertens_array(6000, use_cache=False)
    assert int(M[5999]) == running


def test_mertens_M_pinned_values_up_to_1e5():
    for x, want in MERTENS_PINNED.items():
        if x <= 10**5:
            assert mertens_M(x) == want, f"M({x})"


@pytest.mark.slow
def test_mertens_M_pinned_values_1e6_and_1e7():
    """M(10^6) = 212 and M(10^7) = 1037 -- the published table values."""
    assert mertens_M(10**6) == 212
    assert mertens_M(10**7) == 1037


def test_mertens_ratio_stays_bounded_in_range():
    """|M(x)|/sqrt(x) < 1 for every 2 <= x <= 10^5 scanned here.

    NOT evidence.  The bound |M(x)| < sqrt(x) is the strong Mertens
    conjecture, which is FALSE (Odlyzko-te Riele 1985); the disproof is
    non-constructive and the first counterexample is believed astronomical.
    The assertion records what the finite range shows, and the range shows
    nothing either way about RH.
    """
    ext = mertens_ratio_extremes(10**5, x_min=2, use_cache=False)
    assert ext["max_abs_ratio"] < 1.0
    # the extremum in this range is M(5) = -2 against sqrt(5)
    assert ext["argmin"] == 5
    assert ext["min_ratio"] == pytest.approx(-2.0 / math.sqrt(5), rel=1e-12)


def test_mertens_ratio_extremes_degenerate_x_equals_one():
    """With x_min = 1 the maximum is the degenerate M(1)/sqrt(1) = 1."""
    ext = mertens_ratio_extremes(10**5, x_min=1, use_cache=False)
    assert ext["argmax"] == 1
    assert ext["max_ratio"] == pytest.approx(1.0, abs=1e-15)
    assert ext["max_abs_ratio"] == pytest.approx(1.0, abs=1e-15)


def test_mertens_ratio_extremes_away_from_the_origin():
    """From x = 100 up to 10^5 the largest |M(x)|/sqrt(x) is 0.5671 at x = 199."""
    ext = mertens_ratio_extremes(10**5, x_min=100, use_cache=False)
    assert ext["argmax_abs"] == 199
    assert ext["max_abs_ratio"] == pytest.approx(0.5671049640066687, rel=1e-9)
    assert ext["strong_mertens_conjecture"].startswith("FALSE")


@pytest.mark.slow
def test_mertens_ratio_extremes_to_1e7():
    """Out to 10^7: still 0.5671 at x = 199 once the tiny x are excluded."""
    ext = mertens_ratio_extremes(10**7, x_min=100)
    assert ext["M_at_limit"] == 1037
    assert ext["argmax_abs"] == 199
    assert ext["max_abs_ratio"] < 0.6


@pytest.mark.slow
def test_mertens_largest_excursion_below_1e7():
    """int32 is ample: max |M(x)| for x <= 10^7 is 1143, at x = 9993034.

    The number quoted in ``mertens_array``'s docstring to justify the dtype.
    """
    M = mertens_array(10**7)
    assert M.dtype == np.int32
    assert int(np.abs(M).max()) == 1143
    assert int(np.argmax(np.abs(M))) == 9993034


def test_mertens_matches_the_mobius_inversion_identity():
    """sum_{n <= N} M(N // n) = 1 -- an oracle that never mentions mu.

    Mobius inversion of ``sum_{n<=N} 1 = N``: it constrains the whole table of
    M at once, so a single wrong mu(k) anywhere below N would break it.
    Checked at N = 10^4 and 10^5, with a hyperbola-style grouping of the
    divisor blocks.
    """
    for N in (10**4, 10**5):
        M = mertens_array(N, use_cache=False)
        total, n = 0, 1
        while n <= N:
            q = N // n
            nxt = N // q
            total += (nxt - n + 1) * int(M[q])
            n = nxt + 1
        assert total == 1, f"Mobius inversion failed at N = {N}"


def test_mertens_ratio_function():
    assert mertens_ratio(5) == pytest.approx(-2.0 / math.sqrt(5), rel=1e-12)
    assert mertens_ratio(0.5) == 0.0


def test_mertens_facts_label_the_disproof():
    facts = mertens_facts()
    assert facts["criterion_status"] == "THEOREM"
    assert facts["strong_mertens_status"].startswith("FALSE")
    assert "Odlyzko" in facts["strong_mertens_status"]
    assert "non-constructive" in facts["strong_mertens_status"].lower()


# ===========================================================================
# 2.  NYMAN-BEURLING / BAEZ-DUARTE
# ===========================================================================

def test_baez_duarte_basis_k1_is_identically_zero():
    """A_1 = {1/x} - {1/x} = 0: the k = 1 basis vector carries no information."""
    for x in ("0.1", "0.37", "0.9"):
        assert abs(baez_duarte_basis(1, x, dps=30)) < mp.mpf("1e-28")


def test_baez_duarte_basis_matches_its_step_form():
    """A_k(x) = {n/k} on (1/(n+1), 1/n) -- the identity the Gram formula rests on.

    It comes from rho_theta(x) = theta*floor(1/x) - floor(theta/x); if it were
    wrong every Gram entry would be wrong, so it is checked directly.
    """
    with mp.workdps(30):
        for k in (2, 3, 4, 5, 7, 12, 30):
            for n in range(1, 80):
                x = (mp.mpf(1) / (n + 1) + mp.mpf(1) / n) / 2
                assert abs(
                    baez_duarte_basis(k, x, dps=30) - mp.frac(mp.mpf(n) / k)
                ) < mp.mpf("1e-25"), f"A_{k} at n={n}"


def test_baez_duarte_rhs_is_log_k_over_k():
    """<1, A_k> = -theta log theta = (log k)/k, the Mellin value at s = 1.

    Derived from int_0^1 {theta/x} x^{s-1} dx = theta/(s-1) - theta^s zeta(s)/s,
    whose theta = 1 case is the classical int_0^1 {1/x} dx = 1 - gamma.  The
    series form sum_n {n/k}/(n(n+1)) is checked against it here.
    """
    with mp.workdps(30):
        b = baez_duarte_rhs(12, dps=30)
        for i, k in enumerate(range(2, 13)):
            assert abs(b[i] - mp.log(k) / k) < mp.mpf("1e-28")
            # independent: the digamma-summed series for the same quantity
            L = k
            series = sum(
                (mp.mpf(r) / k) * (mp.psi(0, mp.mpf(r + 1) / L) - mp.psi(0, mp.mpf(r) / L))
                for r in range(1, L)
            ) / L
            assert abs(series - mp.log(k) / k) < mp.mpf("1e-28")


def test_fractional_part_integral_is_one_minus_gamma():
    """int_0^1 {1/x} dx = 1 - gamma: the calibration of the whole convention.

    On (1/(n+1), 1/n) the integrand is 1/x - n, so the integral is
    sum_n [log((n+1)/n) - 1/(n+1)], whose partial sum to N-1 is
    log N - (H_N - 1) -> 1 - gamma.  Truncating at N = 200000 leaves a tail of
    about 1/(2N) = 2.5e-6, so the assertion below is at 1e-5 -- the accuracy the
    truncation permits, not more.  (The module's Mellin identity
    int_0^1 rho_theta = -theta log theta is pinned to 28 digits separately, in
    test_baez_duarte_rhs_is_log_k_over_k; this test exists to check the
    theta = 1 endpoint that fixes the convention.)
    """
    with mp.workdps(30):
        N = 200000
        total = mp.fsum(
            mp.log(mp.mpf(n + 1) / n) - mp.mpf(1) / (n + 1) for n in range(1, N)
        )
        assert abs(total - (1 - mp.euler)) < mp.mpf("1e-5")
        assert abs(total - (1 - mp.euler)) > mp.mpf("1e-7"), (
            "the truncation error should be visible at ~2.5e-6; if it is not, "
            "the tail estimate in this docstring is wrong"
        )


def test_baez_duarte_gram_diagonal_closed_form():
    """<A_2, A_2> = (log 2)/4 exactly -- an independent closed form.

    {n/2} is 1/2 on odd n and 0 on even n, so the series
    sum_n {n/2}^2/(n(n+1)) is (1/4) * sum_{n odd} (1/n - 1/(n+1)) = (log 2)/4.
    """
    with mp.workdps(40):
        G, index = baez_duarte_gram(4, dps=40, use_cache=False)
        assert index == [2, 3, 4]
        assert abs(G[0, 0] - mp.log(2) / 4) < mp.mpf("1e-36")


def test_baez_duarte_gram_is_symmetric_and_positive_definite():
    """Symmetry is *recomputed*, not read back off the mirrored assignment.

    ``baez_duarte_gram`` fills G[a,b] and G[b,a] from one value, so comparing
    them tests nothing.  Instead the (j,k) entry is rebuilt from the closed
    form with the arguments swapped -- <A_k, A_j> computed independently -- and
    must reproduce it.
    """
    from zeta.criteria import _bd_gram_block

    with mp.workdps(40):
        G, index = baez_duarte_gram(10, dps=40, use_cache=False)
        for (j, k) in ((2, 7), (3, 4), (5, 9), (6, 10)):
            L = j * k // math.gcd(j, k)
            fwd = _bd_gram_block(L, [(0, 0, j, k)])[0][2]
            rev = _bd_gram_block(L, [(0, 0, k, j)])[0][2]
            # both sides are computed at the ambient dps = 40, so the floor is
            # the 1e-41-ish rounding of a value of size 1e-1, not zero
            assert abs(fwd - rev) < mp.mpf("1e-38"), f"<A_{j},A_{k}> not symmetric"
            assert abs(G[index.index(j), index.index(k)] - rev) < mp.mpf("1e-38")
        eig = mp.eigsy(G, eigvals_only=True)
        assert min(eig) > 0, "a Gram matrix of independent vectors is SPD"


def test_baez_duarte_gram_matches_an_nsum_of_the_same_series():
    """A third route to the Gram entries that never calls ``mp.psi``.

    The module sums ``sum_{m>=0} 1/((mL+r)(mL+r+1))`` in closed form with a
    digamma difference.  Here the same inner sums are evaluated by
    ``mp.nsum``'s Richardson acceleration instead -- a completely different
    numerical path to the same number -- so a wrong digamma identity (an easy
    off-by-one in ``psi(r/L)`` vs ``psi((r+1)/L)``) could not survive.
    Measured agreement: better than 1e-25 at dps 30.
    """
    G, index = baez_duarte_gram(8, dps=30, use_cache=False)
    with mp.workdps(30):
        for (j, k) in ((2, 3), (4, 6), (5, 7), (8, 8)):
            L = j * k // math.gcd(j, k)
            tot = mp.mpf(0)
            for r in range(1, L):
                fj, fk = mp.mpf(r % j) / j, mp.mpf(r % k) / k
                if fj == 0 or fk == 0:
                    continue
                tot += fj * fk * mp.nsum(
                    lambda m, r=r, L=L: 1 / ((m * L + r) * (m * L + r + 1)),
                    [0, mp.inf],
                )
            assert abs(tot - G[index.index(j), index.index(k)]) < mp.mpf("1e-25"), (j, k)


def test_baez_duarte_d2_agrees_with_a_float64_cholesky_solve():
    """A different conditioning strategy entirely: Jacobi scaling + Cholesky.

    The module solves ``G c = b`` by ``mp.lu_solve`` at dps 50.  Here the same
    system is scaled to unit diagonal, factored by float64 Cholesky, and also
    solved by ``numpy.linalg.lstsq`` -- three routes, two of them in double
    precision.  They agree to 12 digits out to N = 50, which is the concrete
    content of the claim that this problem is *not* severely ill-conditioned.
    """
    for N in (5, 10, 20, 50):
        rec = baez_duarte_d2(N, dps=50, with_condition=False)
        G, index = baez_duarte_gram(N, dps=50)
        b = baez_duarte_rhs(N, dps=50)
        n = len(index)
        Gf = np.array([[float(G[a, c]) for c in range(n)] for a in range(n)])
        bf = np.array([float(b[i]) for i in range(n)])
        scale = 1.0 / np.sqrt(np.diag(Gf))
        Gs, bs = Gf * np.outer(scale, scale), bf * scale
        L = np.linalg.cholesky(Gs)
        cs = np.linalg.solve(L.T, np.linalg.solve(L, bs))
        d2_chol = 1.0 - float(bs @ cs)
        d2_lstsq = 1.0 - float(bf @ np.linalg.lstsq(Gf, bf, rcond=None)[0])
        assert d2_chol == pytest.approx(float(rec["d2"]), rel=1e-12), N
        assert d2_lstsq == pytest.approx(float(rec["d2"]), rel=1e-10), N
        # numpy's 2-norm condition number must match the module's mpmath one
        full = baez_duarte_d2(N, dps=50)
        assert float(np.linalg.cond(Gf)) == pytest.approx(
            float(full["condition_number"]), rel=1e-8
        ), N


def test_baez_duarte_gram_matches_a_monte_carlo_of_the_raw_definition():
    """Independent check: Monte-Carlo <A_j, A_k> from A_k(x) = {1/(kx)} - {1/x}/k.

    The Gram entries come from an exact digamma closed form; this route uses
    nothing but the definition and float64 sampling, so it catches a wrong
    formula (though only to Monte-Carlo accuracy, ~1e-4 here).
    """
    G, index = baez_duarte_gram(6, dps=30, use_cache=False)
    rng = np.random.default_rng(4242)
    x = rng.random(2_000_000)
    inv = 1.0 / x
    frac1 = inv - np.floor(inv)
    cols = {}
    for k in index:
        y = inv / k
        cols[k] = (y - np.floor(y)) - frac1 / k
    for a, j in enumerate(index):
        for b in range(a, len(index)):
            k = index[b]
            mc = float(np.mean(cols[j] * cols[k]))
            assert mc == pytest.approx(float(G[a, b]), abs=3e-4), f"<A_{j},A_{k}>"


@pytest.mark.slow
def test_baez_duarte_gram_matches_a_mellin_parseval_integral():
    """The strongest independent oracle: the Gram entry as a zeta integral.

    The Mellin transform of ``rho_theta`` on ``0 < Re(s) < 1`` is
    ``(zeta(s)/s)(theta - theta^s)``, so Mellin--Plancherel on ``Re(s) = 1/2``
    gives

        <A_j, A_k> = (1/2 pi) int_R |zeta(1/2+it)|^2 / (1/4 + t^2)
                             * (a - a^s)(b - conj(b^s)) dt,   a = 1/j, b = 1/k.

    Nothing in that route touches the digamma closed form used by the module --
    it goes through zeta on the critical line instead.  The integral is
    truncated at |t| = 200; the integrand decays like ``log t / t^2``, so the
    residual truncation error is a few times 1e-5, which is the tolerance used.
    Measured: |difference| = 1.4e-5 at (j,k) = (2,3) and 3.9e-6 at (3,5).
    """
    G, index = baez_duarte_gram(6, dps=30, use_cache=False)
    with mp.workdps(15):
        T = mp.mpf(200)
        grid = [-T, -100, -50, -20, -10, -5, 0, 5, 10, 20, 50, 100, T]
        for (j, k) in ((2, 3), (3, 5)):
            a, b = mp.mpf(1) / j, mp.mpf(1) / k

            def integrand(t, a=a, b=b):
                s = mp.mpc(mp.mpf(1) / 2, t)
                z = mp.zeta(s)
                return mp.re(
                    z * mp.conj(z) / (mp.mpf(1) / 4 + t**2)
                    * (a - a**s) * (b - mp.conj(b**s))
                )

            got = mp.quad(integrand, grid, maxdegree=6) / (2 * mp.pi)
            want = G[index.index(j), index.index(k)]
            assert abs(got - want) < mp.mpf("5e-5"), f"<A_{j},A_{k}>"


def test_baez_duarte_d2_at_N_equals_2_is_one_minus_log2():
    """d_2^2 = 1 - b^2/G = 1 - (log2/2)^2/(log2/4) = 1 - log 2, exactly."""
    with mp.workdps(40):
        rec = baez_duarte_d2(2, dps=40, use_cache=False)
        assert abs(rec["d2"] - (1 - mp.log(2))) < mp.mpf("1e-36")
        assert rec["condition_number"] == 1


def test_baez_duarte_d2_decreases_with_N():
    """d_N is non-increasing in N -- extra basis vectors can only help.

    A property of the criterion (Baez-Duarte 2003) and therefore a test of the
    implementation, not of RH.
    """
    with mp.workdps(40):
        prev = None
        for N in range(2, 15):
            rec = baez_duarte_d2(N, dps=40, use_cache=False, with_condition=False)
            d2 = rec["d2"]
            assert 0 < d2 < 1
            if prev is not None:
                assert d2 <= prev + mp.mpf("1e-35"), f"d_{N}^2 rose above d_{N-1}^2"
            prev = d2


def test_baez_duarte_residual_check_matches_the_shortcut():
    """1 - b.c and 1 - 2 b.c + c^T G c agree: the linear solve is consistent."""
    with mp.workdps(40):
        for N in (5, 10, 14):
            rec = baez_duarte_d2(N, dps=40, use_cache=False, with_condition=False)
            assert abs(rec["d2"] - rec["residual_check"]) < mp.mpf("1e-30")


def test_baez_duarte_d2_is_independent_of_working_precision():
    """dps 25 / 40 / 60 / 90 at N = 12 -- rounding is not the story.

    Measured deviations from the dps = 90 value: 1.28e-28 at dps 25, 1.67e-43
    at dps 40, 6.73e-64 at dps 60.  Each is a little better than the ambient
    rounding of the corresponding working precision, so the assertions below
    are two-sided: an upper bound that pins the docstring claim of 25-digit
    agreement, and a lower bound that would fire if the numbers had somehow
    become bit-identical (which would mean the dps argument was being ignored).
    """
    values = {d: baez_duarte_d2(12, dps=d, use_cache=False, with_condition=False)["d2"]
              for d in (25, 40, 60, 90)}
    with mp.workdps(110):
        ref = values[90]
        assert abs(values[25] - ref) < mp.mpf("1e-25")
        assert abs(values[25] - ref) > mp.mpf("1e-31"), "dps is being ignored?"
        assert abs(values[40] - ref) < mp.mpf("1e-40")
        assert abs(values[60] - ref) < mp.mpf("1e-60")


def test_baez_duarte_conditioning_is_reported_and_measured():
    """Report the conditioning honestly: it is mild at these N, not severe.

    docs/07 repeats the folklore that the least-squares problem is severely
    ill-conditioned.  In this basis, with exact Gram entries, the measured
    cond(G) is about 98.7 at N = 10 and 308 at N = 16 -- a small power of N,
    well inside float64.  The obstruction to the criterion is the 1/log N
    decay, not the linear algebra.  If this test ever fails because cond has
    exploded, the docstring of baez_duarte_d2 is what must change.
    """
    c10 = baez_duarte_d2(10, dps=40, use_cache=False)["condition_number"]
    c16 = baez_duarte_d2(16, dps=40, use_cache=False)["condition_number"]
    c20 = baez_duarte_d2(20, dps=50)["condition_number"]
    assert float(c10) == pytest.approx(98.6989, rel=1e-4)
    assert float(c16) == pytest.approx(308.33, rel=1e-4)
    assert float(c20) == pytest.approx(534.5547, rel=1e-6)
    assert c16 > c10 and c20 > c16, "conditioning worsens with N, but slowly"
    assert float(c20) < 1e4


def test_baez_duarte_matches_the_conjectured_asymptotic_within_a_factor():
    """d_N^2 * log N / C is near 1 for N = 10, 16 -- consistent with BBLS.

    CONJECTURE (Baez-Duarte, Balazard, Landreau, Saias): d_N^2 ~ C/log N with
    C = 2 + gamma - log(4 pi) = 0.0461914...  This asserts only that the
    computed residual is within 30% of that shape at these N; no finite N can
    test an asymptotic, and the ratio is *not* required to be monotone.
    """
    with mp.workdps(50):
        C = mp.mpf(BD_CONSTANT)
        # the pinned string is the closed form to every digit it carries
        assert abs(C - (2 + mp.euler - mp.log(4 * mp.pi))) < mp.mpf("1e-30")
        for row in baez_duarte_table([10, 16], dps=40, use_cache=False):
            ratio = float(row["d2_times_logN_over_C"])
            assert 0.7 < ratio < 1.3, f"N={row['N']} ratio {ratio}"


def test_baez_duarte_table_ratios_are_pinned():
    """The four ratios quoted in ``baez_duarte_table``'s docstring, exactly.

    Not a test of the BBLS conjecture -- these are four numbers from a finite
    computation.  Note the ratio is *not* monotone: N = 20 gives 1.0725840 and
    N = 30 gives 1.0718511, a fall of 7e-4 where a clean 1/log N would have
    predicted more.
    """
    want = {10: 1.1890203, 20: 1.0725840, 30: 1.0718511, 50: 1.0067260}
    rows = baez_duarte_table(sorted(want), dps=50)
    assert [r["N"] for r in rows] == sorted(want)
    for row in rows:
        assert float(row["d2_times_logN_over_C"]) == pytest.approx(
            want[row["N"]], rel=1e-6
        ), row["N"]


@pytest.mark.slow
def test_baez_duarte_d2_at_N_30_recomputed_from_scratch():
    """The generator, not the cache: N = 30 rebuilt entirely (about 9 s).

    Measured: d_30^2 = 0.014556733577, cond(G) = 1365.2137.
    """
    rec = baez_duarte_d2(30, dps=50, use_cache=False)
    assert float(rec["d2"]) == pytest.approx(0.014556733577, rel=1e-9)
    assert float(rec["condition_number"]) == pytest.approx(1365.2137, rel=1e-6)


@pytest.mark.slow
def test_baez_duarte_d2_at_N_50():
    """The honest headline of the module docstring, pinned.

    Measured: d_50^2 = 0.0118869704185326, cond(G) = 4774.5129.  Building the
    N = 50 Gram matrix from scratch takes about 60 s, so this test uses the
    committed cache; the *generator* is exercised without any cache by
    test_baez_duarte_d2_at_N_30_recomputed_from_scratch, and the cache round
    trip is checked by test_baez_duarte_gram_cache_round_trips.
    """
    rec = baez_duarte_d2(50, dps=50, use_cache=True)
    assert float(rec["d2"]) == pytest.approx(0.0118869704185326, rel=1e-11)
    assert float(rec["condition_number"]) == pytest.approx(4774.5129, rel=1e-6)


def test_baez_duarte_gram_cache_round_trips():
    """Cached entries equal freshly computed ones to the stored precision.

    The cache stores dps + 10 digits as strings and a request for N is served
    from any cached N' >= N, so this compares a 5x5 block computed from scratch
    against the same block read back out of the committed N = 50 table.
    """
    fresh, index = baez_duarte_gram(6, dps=40, use_cache=False)
    cached, index2 = baez_duarte_gram(6, dps=40, use_cache=True)
    assert index == index2
    with mp.workdps(40):
        for a in range(len(index)):
            for b in range(len(index)):
                assert abs(fresh[a, b] - cached[a, b]) < mp.mpf("1e-38")


# ===========================================================================
# 3.  ROBIN / LAGARIAS
# ===========================================================================

def test_divisor_sigma_agrees_with_sympy():
    for n in range(1, 3001):
        assert divisor_sigma(n) == sympy.divisor_sigma(n), f"sigma({n})"


def test_divisor_sigma_agrees_with_sympy_on_random_large_n():
    rng = np.random.default_rng(11071875)
    for n in rng.integers(2, 10**7, size=200):
        n = int(n)
        assert divisor_sigma(n) == sympy.divisor_sigma(n), f"sigma({n})"


def test_sigma_sieve_matches_pointwise():
    sig = sigma_sieve(5000)
    for n in range(1, 5001):
        assert int(sig[n]) == divisor_sigma(n), f"sigma({n})"


def test_harmonic_number():
    assert harmonic_number(1) == 1
    with mp.workdps(30):
        for n in (2, 10, 100, 2000):
            direct = mp.fsum(mp.mpf(1) / k for k in range(1, n + 1))
            assert abs(harmonic_number(n, dps=30) - direct) < mp.mpf("1e-27")


def test_robin_ratio_at_5040_is_the_last_exception():
    """sigma(5040) = 19344 against e^gamma*5040*loglog(5040) = 19237.06."""
    with mp.workdps(30):
        assert divisor_sigma(5040) == 19344
        r = robin_ratio(5040, dps=30)
        assert float(r) == pytest.approx(1.00555898145672 * float(mp.e**mp.euler), rel=1e-12)
        bound = mp.e**mp.euler * 5040 * mp.log(mp.log(5040))
        assert float(bound) == pytest.approx(19237.0615, rel=1e-8)
        assert r > mp.e**mp.euler, "5040 is an exception (that is the point of >5040)"


def test_robin_violations_reproduce_the_26_exceptions():
    """Exactly 26 n in [3, 20000] fail sigma(n) < e^gamma n log log n.

    All of them are <= 5040, i.e. **no violation of Robin's criterion (n > 5040)
    was found in this range**.  Matches the list in docs/07 section 6.
    """
    got = robin_violations(20000)
    assert got == list(ROBIN_EXCEPTIONS)
    assert len(got) == 26
    assert max(got) == ROBIN_THRESHOLD == 5040
    assert all(n <= ROBIN_THRESHOLD for n in got)


def test_robin_violations_are_verified_at_high_precision():
    """The float64 sieve verdict is re-checked at dps = 30 on both sides."""
    with mp.workdps(30):
        eg = mp.e**mp.euler
        for n in ROBIN_EXCEPTIONS:
            assert robin_ratio(n, dps=30) >= eg, n
        # the tightest non-exception just above the last one
        for n in (5041, 5042, 7560, 10080, 15120, 20000):
            assert robin_ratio(n, dps=30) < eg, n
        # the closest call in the whole range: n = 720 exceeds e^gamma by 0.0874%,
        # so no float64/mpmath disagreement is possible on any verdict here
        margin = (robin_ratio(720, dps=30) - eg) / eg
        assert float(margin) == pytest.approx(0.00087432421, rel=1e-6)
        assert min(
            abs(robin_ratio(n, dps=30) - eg) / eg for n in (3, 720, 5040, 5041, 10080)
        ) > mp.mpf("1e-4")


def test_every_float64_robin_verdict_is_re_checked_at_dps_30():
    """All 19 998 verdicts for 3 <= n <= 20000, redone in arbitrary precision.

    ``robin_violations`` classifies in float64.  This redoes *every* comparison
    at dps = 30 (about 0.7 s) and reports the global minimum of the relative
    margin ``|ratio - e^gamma| / e^gamma``.  Measured: 8.7432421e-4, attained
    at n = 720 (an exception); the tightest non-exception is n = 420 at
    9.874e-4.  Eleven orders of magnitude above float64 rounding, so no
    float64 verdict in this range can be wrong -- which is what makes the
    cheap sieve legitimate.
    """
    sig = sigma_sieve(20000)
    with mp.workdps(30):
        eg = mp.e**mp.euler
        exceptions, worst, worst_n = [], None, None
        for n in range(3, 20001):
            ratio = mp.mpf(int(sig[n])) / (mp.mpf(n) * mp.log(mp.log(n)))
            if ratio >= eg:
                exceptions.append(n)
            margin = abs(ratio - eg) / eg
            if worst is None or margin < worst:
                worst, worst_n = margin, n
    assert exceptions == list(ROBIN_EXCEPTIONS)
    assert exceptions == robin_violations(20000), "float64 and dps-30 verdicts differ"
    assert worst_n == 720
    assert float(worst) == pytest.approx(8.7432421e-4, rel=1e-6)
    assert float(worst) > 1e-5, "float64 could not be trusted at this margin"


@pytest.mark.slow
def test_no_robin_violation_above_5040_up_to_1e5():
    """No n with 5040 < n <= 10^5 violates Robin's inequality.

    "No violation found in the range scanned", not evidence for RH: Gronwall's
    theorem makes the ratio approach e^gamma unconditionally.
    """
    got = robin_violations(10**5)
    assert got == list(ROBIN_EXCEPTIONS)


def test_lagarias_equality_at_one_and_no_violations():
    """Lagarias: sigma(n) <= H_n + exp(H_n) log H_n, equality only at n = 1."""
    assert lagarias_ratio(1) == 1
    assert lagarias_violations(20000) == []
    with mp.workdps(30):
        for n in (2, 3, 5040, 55440):
            assert lagarias_ratio(n, dps=30) < 1, n


def test_every_float64_lagarias_verdict_is_re_checked_at_dps_30():
    """All 20 000 comparisons for 1 <= n <= 20000, redone at dps = 30.

    ``lagarias_violations`` classifies in float64.  Here H_n is accumulated
    exactly as a running arbitrary-precision sum (not via psi, so this is also
    an independent check of :func:`harmonic_number`'s digamma route), and every
    comparison is redone.  n = 1 gives exact equality; the smallest relative
    slack over 2 <= n <= 20000 is 1.1364e-2 at n = 12 -- an order of magnitude
    more room than Robin's tightest call, which is the quantitative content of
    "Lagarias' form needs no n > 5040 clause".
    """
    sig = sigma_sieve(20000)
    with mp.workdps(30):
        H, worst, worst_n = mp.mpf(0), None, None
        for n in range(1, 20001):
            H += mp.mpf(1) / n
            s = mp.mpf(int(sig[n]))
            if n == 1:
                assert H == 1 and s == 1
                assert abs(H + mp.e**H * mp.log(H) - 1) < mp.mpf("1e-28")
                continue
            rhs = H + mp.e**H * mp.log(H)
            assert s <= rhs, f"Lagarias' inequality failed at n = {n}"
            slack = (rhs - s) / rhs
            if worst is None or slack < worst:
                worst, worst_n = slack, n
            if n in (10, 100, 5040):
                assert abs(H - harmonic_number(n, dps=30)) < mp.mpf("1e-27")
    assert worst_n == 12
    assert float(worst) == pytest.approx(1.1363573e-2, rel=1e-6)
    assert lagarias_violations(20000) == [], "float64 and dps-30 verdicts differ"


def test_lagarias_pinned_right_hand_sides():
    """H_n + exp(H_n) log H_n at 5040 and 55440, against docs/07."""
    with mp.workdps(30):
        for n, sigma_n, rhs in ((5040, 19344, 19836.32), (55440, 232128, 241179.92)):
            assert divisor_sigma(n) == sigma_n
            got = mp.mpf(sigma_n) / lagarias_ratio(n, dps=30)
            assert float(got) == pytest.approx(rhs, rel=1e-7)


def test_lagarias_absorbs_every_robin_exception():
    """The 26 Robin exceptions all satisfy Lagarias' inequality.

    That is the whole content of the "no n > 5040 clause needed" remark: the
    extra H_n plus lower-order corrections supply exactly enough slack.
    """
    for n in ROBIN_EXCEPTIONS:
        assert lagarias_ratio(n, dps=30) < 1, n


def test_lagarias_ratio_from_log_agrees_with_the_exact_form():
    """The log-space evaluator, needed for n with thousands of digits.

    It replaces H_n by its asymptotic expansion through 1/(120 n^4); the first
    omitted term is 1/(252 n^6) = 2.4e-25 at n = 5040.  The agreement measured
    here is relative 2.54e-25 at n = 5040 -- the truncation, visible and of
    exactly the predicted size -- and 1.0e-31 from n = 55440 up, which is the
    dps = 30 rounding floor with no truncation left above it.  Both bounds are
    asserted, so a tolerance loose enough to hide a wrong expansion would fail
    the lower one.
    """
    with mp.workdps(30):
        rel = {}
        for n in (5040, 55440, 720720, 21621600):
            exact = lagarias_ratio(n, dps=30)
            approx = lagarias_ratio_from_log(
                mp.log(n), mp.mpf(divisor_sigma(n)) / n, dps=30
            )
            rel[n] = abs(exact - approx) / exact
        assert mp.mpf("1e-26") < rel[5040] < mp.mpf("1e-24"), (
            "the 1/(252 n^6) truncation should be visible at n = 5040"
        )
        assert float(rel[5040]) == pytest.approx(2.54e-25, rel=0.05)
        for n in (55440, 720720, 21621600):
            assert rel[n] < mp.mpf("1e-30"), n


def test_robin_ratio_from_log_agrees_with_the_exact_form():
    with mp.workdps(30):
        for n in (5040, 10080, 720720):
            exact = robin_ratio(n, dps=30)
            approx = robin_ratio_from_log(mp.log(n), mp.mpf(divisor_sigma(n)) / n, dps=30)
            assert abs(exact - approx) < mp.mpf("1e-25"), n


def test_colossally_abundant_reproduces_the_published_sequence():
    """The first 14 CA numbers, against OEIS A004490."""
    want = [2, 6, 12, 60, 120, 360, 2520, 5040, 55440, 720720,
            1441440, 4324320, 21621600, 367567200]
    chain = colossally_abundant(14)
    assert [rec["n"] for rec in chain] == want
    with mp.workdps(30):
        for rec in chain:
            if rec["n"] is not None:
                assert abs(rec["log_n"] - mp.log(rec["n"])) < mp.mpf("1e-25")
                assert abs(
                    rec["sigma_over_n"] - mp.mpf(divisor_sigma(rec["n"])) / rec["n"]
                ) < mp.mpf("1e-25")


def test_superabundant_candidates_have_non_increasing_exponents():
    """The enumerated shapes really are products of primorials."""
    seen = 0
    for pattern in superabundant_candidates(20.0):
        assert all(a >= b for a, b in zip(pattern, pattern[1:])), pattern
        assert pattern[-1] >= 1
        seen += 1
    assert seen == 1108, "1108 primorial-product shapes with log n <= 20"


def test_superabundant_enumeration_refuses_to_truncate_silently():
    """Past the primorial of all primes < 4096 the enumeration would be partial."""
    with pytest.raises(ValueError):
        next(superabundant_candidates(1e9))
    with pytest.raises(ValueError):
        robin_search(max_log_n=1e9, ca_steps=5)


def test_robin_search_finds_no_violation_above_5040():
    """Exhaustive over every superabundant shape with log n <= 40, plus 200 CA steps.

    Both nets come back empty, and the largest ratio found above 5040 is
    1.755814338925 at n = 2^5*3^2*5*7 = 10080 (2.53e-02 short of
    e^gamma = 1.7810724...).  This is "no counterexample in the range
    scanned"; Gronwall's theorem says the ratio must approach e^gamma anyway,
    so proximity is expected and means nothing.
    """
    rep = robin_search(max_log_n=40.0, ca_steps=200, dps=30)
    assert rep["exhaustive_violations"] == []
    assert rep["ca_violations"] == []
    assert rep["lagarias_violations_on_chain"] == []
    assert rep["patterns_scanned"] == 27055
    assert rep["exhaustive_argmax_n"] == 10080
    assert float(rep["exhaustive_max_ratio"]) == pytest.approx(1.755814338925, rel=1e-11)
    with mp.workdps(30):
        eg = mp.e**mp.euler
        assert rep["exhaustive_max_ratio"] < eg
        assert rep["ca_max_ratio"] < eg
        assert float(eg) == pytest.approx(1.7810724179901980, rel=1e-15)
    # the CA chain climbs above the exhaustive maximum only much further out
    assert float(rep["ca_max_ratio"]) == pytest.approx(1.773581846871, rel=1e-10)
    assert float(rep["ca_gap_to_e_gamma"]) == pytest.approx(0.00749057112, rel=1e-8)


@pytest.mark.slow
def test_robin_search_to_log_n_80_and_2000_ca_steps():
    """The headline numbers in ``robin_search``'s docstring, pinned (about 3 s).

    Exhaustive over all 2 023 242 superabundant-shaped n with log n <= 80
    (n <= 5.5e34), plus the colossally abundant chain to step 2000, where
    log n = 16674.12 -- an integer of roughly 7242 digits.  Both nets come
    back empty.  "No violation found in the range scanned"; Gronwall's theorem
    already guarantees the ratio climbs to e^gamma, so 1.19e-3 of headroom at
    step 2000 is the expected behaviour under RH *and* the expected behaviour
    if RH is false with a counterexample further out.  Nothing here is
    evidence either way.
    """
    rep = robin_search(max_log_n=80.0, ca_steps=2000, dps=30)
    assert rep["patterns_scanned"] == 2023242
    assert rep["exhaustive_violations"] == []
    assert rep["ca_violations"] == []
    assert rep["lagarias_violations_on_chain"] == []
    assert rep["exhaustive_argmax_n"] == 10080
    assert rep["exhaustive_argmax_pattern"] == (5, 2, 1, 1)
    assert float(rep["exhaustive_max_ratio"]) == pytest.approx(1.7558143389253, rel=1e-12)
    assert float(rep["exhaustive_gap_to_e_gamma"]) == pytest.approx(
        0.0252580790649012, rel=1e-10)
    assert rep["ca_argmax_step"] == 2000
    assert float(rep["ca_argmax_log_n"]) == pytest.approx(16674.1228329607, rel=1e-12)
    assert float(rep["ca_max_ratio"]) == pytest.approx(1.77988114995847, rel=1e-12)
    assert float(rep["ca_gap_to_e_gamma"]) == pytest.approx(0.00119126803172323, rel=1e-10)


def test_superabundant_pattern_count_at_log_n_80():
    """2 023 242 primorial-product shapes with log n <= 80 (about 2 s)."""
    assert sum(1 for _ in superabundant_candidates(80.0)) == 2023242


def test_colossally_abundant_float_eps_matches_mpf_eps():
    """The heap key is float64 inside an mp.workdps block -- so check it.

    ``colossally_abundant`` reduces the critical exponent eps(p, a) to float64
    before pushing it on the heap.  Only the ordering matters, but a precision
    drop inside an arbitrary-precision routine has to be justified by
    measurement rather than by assertion.  Rebuilding the chain with mpf keys
    at dps = 40 reproduces it step for step.
    """
    import heapq

    from zeta.criteria import _primes_upto

    steps, max_prime = 300, 5000
    with mp.workdps(40):
        primes = _primes_upto(max_prime)

        def eps(p, a):
            P = mp.mpf(p)
            return mp.log((P ** (a + 1) - 1) / (P * (P**a - 1))) / mp.log(P)

        heap = [(-eps(p, 1), p, 1) for p in primes]
        heapq.heapify(heap)
        ref = []
        for _ in range(steps):
            _, p, a = heapq.heappop(heap)
            ref.append((p, a))
            heapq.heappush(heap, (-eps(p, a + 1), p, a + 1))
    got = [(r["prime"], r["exponent"])
           for r in colossally_abundant(steps, dps=30, max_prime=max_prime)]
    assert got == ref, "float64 heap keys changed the colossally abundant chain"


def test_ca_robin_ratio_dips_are_exactly_where_the_docstring_says():
    """The dip list in ``robin_search``'s docstring, pinned exactly.

    Among the chain steps with log n > log 5040, the Robin ratio falls at
    steps 10, 11, 12, 13, 17, 18, 21, 28, 29, 52, 126, 129 and nowhere else in
    the first 150.  Recorded because the natural assumption -- that a chain
    converging up to e^gamma converges monotonically -- is false, and an
    earlier version of this test asserted monotonicity and failed.
    """
    chain = [r for r in colossally_abundant(150, dps=30)
             if r["robin_ratio"] is not None and r["log_n"] > math.log(5040)]
    dips = [chain[i]["step"] for i in range(1, len(chain))
            if chain[i]["robin_ratio"] < chain[i - 1]["robin_ratio"]]
    assert dips == [10, 11, 12, 13, 17, 18, 21, 28, 29, 52, 126, 129]
    assert chain[0]["step"] == 9


@pytest.mark.slow
def test_robin_search_deep_and_wide():
    """log n <= 60 exhaustively (288457 shapes) and 1000 CA steps: still empty.

    At CA step 1000, log n = 7401.27 -- an integer of about 3215 digits --
    and the ratio is 1.779131716, within 1.94e-03 of e^gamma.
    """
    rep = robin_search(max_log_n=60.0, ca_steps=1000, dps=30)
    assert rep["patterns_scanned"] == 288457
    assert rep["exhaustive_violations"] == []
    assert rep["ca_violations"] == []
    assert float(rep["ca_max_ratio"]) == pytest.approx(1.779131716, rel=1e-9)
    assert float(rep["ca_gap_to_e_gamma"]) == pytest.approx(0.001940702, rel=1e-6)


def test_robin_ratio_climbs_but_not_monotonically_along_the_ca_chain():
    """The CA Robin ratio trends up towards e^gamma -- with genuine dips.

    Measured, and worth recording because it is easy to assume otherwise:
    the ratio *decreases* at some steps (10-13, 17-18, 21, 28-29, 52, 126, 129
    of the chain), always when a new large prime is admitted.  So the running
    maximum is what climbs; the sequence itself does not.  It stays strictly
    below e^gamma everywhere, which is Robin's inequality holding in the range
    scanned -- not evidence for RH, since Gronwall's theorem makes the approach
    to e^gamma unconditional.
    """
    chain = [r for r in colossally_abundant(150, dps=30)
             if r["robin_ratio"] is not None and r["log_n"] > math.log(5040)]
    ratios = [r["robin_ratio"] for r in chain]
    assert len(ratios) > 100
    with mp.workdps(30):
        eg = mp.e**mp.euler
        assert all(r < eg for r in ratios), "Robin's inequality failed on the chain"
    assert not all(b > a for a, b in zip(ratios, ratios[1:])), (
        "the chain is expected to dip; if it is now monotone the docstring is wrong"
    )
    running = [max(ratios[: i + 1]) for i in range(len(ratios))]
    assert all(b >= a for a, b in zip(running, running[1:]))
    assert ratios[-1] > ratios[0], "the trend is upward over 140 steps"


# ===========================================================================
# 4.  SPEISER
# ===========================================================================

def test_zeta_prime_matches_mpmath_and_a_finite_difference():
    with mp.workdps(30):
        for s in (mp.mpf(2), mp.mpf(3), mp.mpc(2, 1), mp.mpc("0.75", 14)):
            assert abs(zeta_prime(s, dps=30) - mp.zeta(s, derivative=1)) < mp.mpf("1e-27")
        h = mp.mpf(10) ** -12
        fd = (mp.zeta(2 + h) - mp.zeta(2 - h)) / (2 * h)
        assert abs(fd - zeta_prime(2, dps=30)) < mp.mpf("1e-16")


def test_pinned_zeta_prime_zeros_are_zeros():
    """The two lowest zeros of zeta' quoted in docs/07, polished here."""
    with mp.workdps(35):
        for re_, im_ in ZETA_PRIME_ZEROS_PINNED:
            z = mp.mpc(mp.mpf(re_), mp.mpf(im_))
            assert abs(mp.zeta(z, derivative=1)) < mp.mpf("1e-13")
            r = mp.findroot(lambda w: mp.zeta(w, derivative=1), z, solver="secant")
            assert abs(r - z) < mp.mpf("1e-13")
            assert mp.re(r) > mp.mpf("0.5")


def test_zeta_prime_zeros_in_a_window_are_all_right_of_the_critical_line():
    """Every zero of zeta' with 0.001 < Re < 6, 1 < Im < 40 has Re > 1/2.

    Speiser's theorem (1934/35) makes "zeta' has no zero in 0 < Re(s) < 1/2"
    equivalent to RH, so this is the criterion evaluated on one finite window.
    Finding no violation is what RH predicts; it is **not** evidence for RH
    (docs/08).  The argument-principle box count and the number of located
    zeros must agree -- that equality is the certificate that nothing was
    missed, and zeta_prime_zeros raises if it fails.
    """
    found = zeta_prime_zeros(t_min=1, t_max=40, dps=25, use_cache=False)
    assert found["box_count"] == len(found["zeros"]) == 3
    with mp.workdps(25):
        for z in found["zeros"]:
            assert abs(mp.zeta(z, derivative=1)) < mp.mpf("1e-18")
            assert mp.re(z) > mp.mpf("0.5"), f"zero of zeta' left of the line: {z}"
        assert abs(found["zeros"][0] - mp.mpc("2.46316186945432", "23.2983204927629")) < mp.mpf("1e-12")
        assert abs(found["zeros"][1] - mp.mpc("1.28649682226905", "31.7082500831159")) < mp.mpf("1e-12")


def test_zeta_prime_zeros_window_to_height_60():
    """The Im <= 60 window quoted in ``zeta_prime_zeros``' docstring.

    7 zeros, box count 7, 950 distinct ``zeta'`` evaluations behind the
    memoised counter, leftmost Re = 0.964685622705686.  Served from the
    committed cache; the generator itself is exercised without a cache by
    ``test_zeta_prime_zeros_in_a_window_are_all_right_of_the_critical_line``.
    """
    found = zeta_prime_zeros(t_min=1, t_max=60, dps=25)
    assert found["box_count"] == len(found["zeros"]) == 7
    assert found["zeta_prime_evaluations"] == 950
    with mp.workdps(25):
        res = [mp.re(z) for z in found["zeros"]]
        assert float(min(res)) == pytest.approx(0.964685622705686, rel=1e-13)
        assert all(r > mp.mpf("0.5") for r in res)
        assert max(abs(mp.zeta(z, derivative=1)) for z in found["zeros"]) < mp.mpf("1e-20")


def test_zeta_prime_box_count_survives_refining_the_contour_step():
    """The winding count must not depend on the subdivision that produced it.

    ``count_zeros_box`` is ordinary floating point: it sums principal phase
    increments and accepts the total when it lands within 1e-6 of an integer.
    An undersampled edge could lose a whole turn and the integrality check
    would never notice.  The only honest defence is to refine and see whether
    the answer moves.  Halving the module's step from 0.4 to 0.2 to 0.1 leaves
    both counts fixed at 3 and 0.
    """
    from zeta.criteria import _count_zp, _zp_counter

    counts = []
    with mp.workdps(35):
        for step in ("0.4", "0.2", "0.1"):
            fn = _zp_counter()
            box = _count_zp(fn, mp.mpf("0.001"), mp.mpf(6), mp.mpf(1), mp.mpf(40),
                            15, mp.mpf(step))
            left = _count_zp(fn, mp.mpf("0.001"), mp.mpf("0.5"), mp.mpf(1), mp.mpf(40),
                             15, mp.mpf(step))
            counts.append((box, left))
    assert counts == [(3, 0), (3, 0), (3, 0)], counts


def _uniform_grid_winding(a, b, c, d, h="0.05", dps=20):
    """Winding number of zeta' round a rectangle, by a *non-adaptive* grid.

    A second implementation of the argument principle that shares no code with
    ``zeta.epstein``: a uniform grid, principal phase differences summed with
    no recursion and no refinement, and -- crucially -- the largest increment
    returned so the caller can verify it stayed below pi/2.  Under pi/2 per
    step, no full turn can hide between two samples, which is the failure mode
    that makes adaptive schemes untrustworthy.

    Returns ``(winding, max_increment)``.
    """
    with mp.workdps(dps):
        a, b, c, d = (mp.mpf(v) for v in (a, b, c, d))
        h = mp.mpf(h)
        corners = [mp.mpc(a, c), mp.mpc(b, c), mp.mpc(b, d), mp.mpc(a, d), mp.mpc(a, c)]
        total, worst = mp.mpf(0), mp.mpf(0)
        for i in range(4):
            z0, z1 = corners[i], corners[i + 1]
            n = max(1, int(mp.ceil(abs(z1 - z0) / h)))
            prev = mp.arg(mp.zeta(z0, derivative=1))
            for k in range(1, n + 1):
                z = z0 + (z1 - z0) * mp.mpf(k) / n
                cur = mp.arg(mp.zeta(z, derivative=1))
                d_phi = cur - prev
                while d_phi > mp.pi:
                    d_phi -= 2 * mp.pi
                while d_phi <= -mp.pi:
                    d_phi += 2 * mp.pi
                worst = max(worst, abs(d_phi))
                total += d_phi
                prev = cur
        return total / (2 * mp.pi), worst


def test_zeta_prime_box_count_against_an_independent_winding_implementation():
    """The Im <= 40 counts, recomputed by code that shares nothing with epstein.

    This is the check that keeps ``box_count`` from being self-confirming: the
    module's count comes from ``zeta.epstein.count_zeros_box`` (forced
    subdivision plus adaptive bisection), while this one is a flat uniform
    grid whose maximum phase increment is *verified* to stay below pi/2.
    Measured at h = 0.05: winding 3 for the full box with largest increment
    0.1031 rad, winding 0 for the Speiser strip with 0.1262 rad.  Takes ~7 s.
    """
    w_box, worst_box = _uniform_grid_winding("0.001", 6, 1, 40)
    w_left, worst_left = _uniform_grid_winding("0.001", "0.5", 1, 40)
    with mp.workdps(20):
        assert worst_box < mp.pi / 2 and worst_left < mp.pi / 2, "grid too coarse"
        assert float(worst_box) == pytest.approx(0.1031, rel=1e-3)
        assert float(worst_left) == pytest.approx(0.1262, rel=1e-3)
        assert abs(w_box - 3) < mp.mpf("1e-9")
        assert abs(w_left) < mp.mpf("1e-9")
    found = zeta_prime_zeros(t_min=1, t_max=40, dps=25)
    assert found["box_count"] == 3, "two independent windings must agree"


@pytest.mark.slow
def test_zeta_prime_box_count_to_height_100_against_the_independent_winding():
    """Same independent grid at Im <= 100: 19 in the box, 0 in the Speiser strip."""
    w_box, worst_box = _uniform_grid_winding("0.001", 6, 1, 100)
    w_left, worst_left = _uniform_grid_winding("0.001", "0.5", 1, 100)
    with mp.workdps(20):
        assert worst_box < mp.pi / 2 and worst_left < mp.pi / 2, "grid too coarse"
        assert abs(w_box - 19) < mp.mpf("1e-9")
        assert abs(w_left) < mp.mpf("1e-9")
    found = zeta_prime_zeros(t_min=1, t_max=100, dps=25)
    assert found["box_count"] == len(found["zeros"]) == 19
    assert found["zeta_prime_evaluations"] == 2543
    with mp.workdps(25):
        worst = max(abs(mp.zeta(z, derivative=1)) for z in found["zeros"])
        assert float(worst) == pytest.approx(8.2e-25, rel=0.1)


def test_zeta_prime_has_no_zero_with_re_at_least_30():
    """Beyond the scanned box no contour is needed -- the n = 2 term dominates.

    ``zeta'(s) = -sum_{n>=2} (log n) n^{-s}``.  For ``Re(s) = 30`` the first
    term has modulus ``(log 2) 2^{-30} = 6.45e-10`` while everything else sums
    to at most ``sum_{n>=3} (log n) n^{-30} = 5.3e-15``, so ``zeta'`` cannot
    vanish for ``Re(s) >= 30``.  This is what closes the gap that
    ``speiser_scan``'s ``right_tail_count`` (which only reaches Re = 30) would
    otherwise leave open.
    """
    with mp.workdps(30):
        head = mp.log(2) * mp.mpf(2) ** -30
        rest = mp.nsum(lambda n: mp.log(n) * n ** mp.mpf(-30), [3, mp.inf])
        assert float(head) == pytest.approx(6.4535e-10, rel=1e-4)
        assert float(rest) == pytest.approx(5.3399e-15, rel=1e-4)
        assert head > 10**4 * rest, "the tail bound does not close"
        # and a spot check that zeta' really is far from zero out there
        for t in (0, 7, 41, 99):
            assert abs(mp.zeta(mp.mpc(30, t), derivative=1)) > mp.mpf("6e-10")


def test_both_root_solvers_are_load_bearing_in_polish_zp():
    """Neither secant nor Muller alone finds all 19 zeros -- measured, not assumed.

    Over the 25 boxes the Im <= 100 scan bisects down to, Muller-only fails on
    5 and secant-only on 3.  One representative box of each kind is replayed
    here with a single solver; the module's own ``_polish_zp``, which tries
    secant then Muller, succeeds on both.
    """
    from zeta.criteria import _polish_zp

    def polish_with(solvers, a, b, c, d, dps=25):
        with mp.workdps(dps + 10):
            f = lambda z: mp.zeta(z, derivative=1)  # noqa: E731
            tol = mp.mpf(10) ** (-dps + 5)
            for i in (2, 1, 3):
                for j in (2, 1, 3):
                    seed = mp.mpc(a + (b - a) * i / 4, c + (d - c) * j / 4)
                    for solver in solvers:
                        try:
                            r = mp.findroot(f, seed, solver=solver)
                        except Exception:
                            continue
                        if (a <= mp.re(r) <= b and c <= mp.im(r) <= d
                                and abs(f(r)) < tol):
                            return +r
        return None

    with mp.workdps(35):
        a0, b0, c0, d0 = mp.mpf("0.001"), mp.mpf(6), mp.mpf(1), mp.mpf(100)
        w, h = b0 - a0, d0 - c0

        def box(i0, i1, j0, j1):
            return (a0 + w * i0 / 32, a0 + w * i1 / 32,
                    c0 + h * j0 / 32, c0 + h * j1 / 32)

        muller_blind = box(4, 5, 24, 25)      # holds 0.86462286 + 76.36280790i
        secant_blind = box(10, 12, 18, 20)    # holds 1.89595976 + 57.13475320i

        assert polish_with(("muller",), *muller_blind) is None
        got = polish_with(("secant",), *muller_blind)
        assert got is not None
        assert abs(got - mp.mpc("0.8646228644261133", "76.36280789646704")) < mp.mpf("1e-14")
        assert abs(mp.zeta(got, derivative=1)) < mp.mpf("1e-20")

        assert polish_with(("secant",), *secant_blind) is None
        got = polish_with(("muller",), *secant_blind)
        assert got is not None
        assert abs(got - mp.mpc("1.89595976247124", "57.1347531990195")) < mp.mpf("1e-12")
        assert abs(mp.zeta(got, derivative=1)) < mp.mpf("1e-20")

        # the shipped combination handles both
        for bx in (muller_blind, secant_blind):
            r = _polish_zp(*bx, 25)
            assert r is not None and abs(mp.zeta(r, derivative=1)) < mp.mpf("1e-20")


def test_speiser_scan_left_strip_is_empty():
    """The Speiser strip 0.001 < Re(s) < 1/2, 1 < Im < 40, counted directly.

    An argument-principle count on the strip itself, independent of the root
    finder: 0 zeros.  Also 0 in 6 < Re < 30, so the right edge of the search
    box is not hiding anything.
    """
    rep = speiser_scan(t_max=40, dps=25, use_cache=False)
    assert rep["left_strip_count"] == 0
    assert rep["right_tail_count"] == 0
    assert rep["n_zeros"] == rep["box_count"] == 3
    assert rep["all_right_of_critical_line"] is True
    assert float(rep["leftmost_re"]) == pytest.approx(1.28649682226905, rel=1e-12)
    assert "THEOREM" in rep["criterion_status"]
    assert "not evidence for RH" in rep["honest_scope"]


@pytest.mark.slow
def test_speiser_scan_to_height_100():
    """19 zeros of zeta' up to Im = 100, leftmost Re = 0.780628004725.

    Still comfortably right of 1/2, and the strip 0.001 < Re < 1/2 is empty.
    Nothing here is evidence for RH.
    """
    rep = speiser_scan(t_max=100, dps=25)
    assert rep["n_zeros"] == rep["box_count"] == 19
    assert rep["left_strip_count"] == 0
    assert rep["right_tail_count"] == 0
    assert rep["all_right_of_critical_line"] is True
    assert float(rep["leftmost_re"]) == pytest.approx(0.780628004725, rel=1e-10)
    assert float(rep["leftmost_at_t"]) == pytest.approx(95.29296827135, rel=1e-11)


def test_zeta_prime_zeros_rejects_a_contour_through_the_pole():
    with pytest.raises(ValueError):
        zeta_prime_zeros(t_min=0, t_max=10, use_cache=False)
    with pytest.raises(ValueError):
        zeta_prime_zeros(sigma_min=0, t_max=10, use_cache=False)


# ===========================================================================
# the report
# ===========================================================================

def test_criteria_report_runs_all_four_faces():
    rep = criteria_report(
        mertens_limit=10**5,
        bd_N=10,
        bd_dps=40,
        robin_max_log_n=25.0,
        robin_ca_steps=60,
        speiser_t_max=40.0,
    )
    assert set(rep) == {"mertens", "baez_duarte", "robin", "speiser", "honest_scope"}
    assert rep["mertens"]["M_at_limit"] == -48
    assert rep["mertens"]["strong_mertens_conjecture"].startswith("FALSE")
    assert 0 < float(rep["baez_duarte"]["d2"]) < 1
    assert rep["robin"]["violations"] == []
    assert rep["speiser"]["left_strip_count"] == 0
    assert "no finite range is evidence for RH" in rep["honest_scope"]
    for face in ("mertens", "baez_duarte", "robin", "speiser"):
        # each face must label its criterion's status in the criterion string
        # itself -- not merely somewhere in the repr of the whole record
        assert "THEOREM" in rep[face]["criterion"], face


def test_no_absolute_user_paths_in_committed_artefacts():
    """House rule: committed files must not contain a username-bearing path.

    Covers the module, this test file, and the JSON caches the module writes
    (the ``.npz`` sieves are gitignored).  The needles are assembled at runtime
    so this test does not flag itself.
    """
    import pathlib

    import zeta.criteria as criteria_module

    needles = ("/" + "Users" + "/", "/" + "home" + "/", "C:" + "\\Users")
    paths = [pathlib.Path(criteria_module.__file__), pathlib.Path(__file__)]
    paths += sorted(pathlib.Path(criteria_module.DATA_DIR).glob("baez_duarte_gram_*.json"))
    paths += sorted(pathlib.Path(criteria_module.DATA_DIR).glob("zeta_prime_zeros_*.json"))
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            assert needle not in text, f"{path.name} carries an absolute path"
