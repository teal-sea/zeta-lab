"""Tests for :mod:`zeta.statistics`, unfolding, spacings, GUE, Montgomery.

Everything numeric here is checked against either
  * published constants (the first ten zero ordinates, ζ special values),
  * an independent mpmath oracle (``siegeltheta``, ``siegelz``, ``zetazero``,
    ``backlunds``), or
  * an exact analytic identity (∫p = 1, ∫s·p = 1, E'(0;0) = −1,
    montgomery_prediction(k) = 1 at integers).
"""

from __future__ import annotations

import numpy as np
import pytest
from mpmath import backlunds, mp, siegeltheta, siegelz, zetazero
from scipy.special import digamma
from scipy.stats import kstest

from zeta.statistics import (
    _find_zeros_by_scan,
    _zeros_cache_path,
    compare_to_random_matrix,
    form_factor,
    gue_eigenvalues,
    gue_gap_probability,
    gue_spacing_exact,
    gue_spacing_exact_cdf,
    level_repulsion_report,
    montgomery_prediction,
    nearest_neighbour_spacings,
    pair_correlation,
    poisson_spacing,
    poisson_spacing_cdf,
    riemann_siegel_theta,
    riemann_siegel_z,
    unfold,
    unfold_gue,
    wigner_surmise_gue,
    wigner_surmise_gue_cdf,
    zero_ordinates,
)

# The first ten ordinates γₙ, to 19 significant figures (Odlyzko's tables).
FIRST_TEN = np.array(
    [
        14.134725141734693790,
        21.022039638771554993,
        25.010857580145688763,
        30.424876125859513210,
        32.935061587739189691,
        37.586178158825671257,
        40.918719012147495187,
        43.327073280914999519,
        48.005150881167159727,
        49.773832477672302182,
    ]
)

T_MAX = 10000.0  # 10142 zeros, the module default


def gammas_with_unfolded_image(u: np.ndarray) -> np.ndarray:
    """Solve θ(γ)/π = u for γ, so that ``unfold(γ) == u`` to ~1e-11.

    Needed to feed a *synthetic* level sequence (e.g. a Poisson process) through
    the module's real ``form_factor`` / ``pair_correlation`` entry points, which
    take raw ordinates and unfold internally.  Without this, a "control
    experiment" can only re-implement the estimator, which tests nothing.

    Newton on θ(t)/π − u, seeded by interpolating a coarse θ table.  θ is
    strictly increasing for t > 6.29 so the root is unique;
    θ'(t) = ½·Re ψ(¼ + it/2) − ½ log π.
    """
    u = np.asarray(u, dtype=np.float64)
    grid = np.arange(10.0, 20000.0, 0.05)
    t = np.interp(u, riemann_siegel_theta(grid) / np.pi, grid)
    for _ in range(4):
        f = riemann_siegel_theta(t) / np.pi - u
        fp = (0.5 * np.real(digamma(0.25 + 0.5j * t)) - 0.5 * np.log(np.pi)) / np.pi
        t = t - f / fp
    return t


def poisson_gammas(n: int, seed: int, start_height: float = 500.0) -> np.ndarray:
    """Ordinates whose unfolded image is an exact unit-rate Poisson process."""
    rng = np.random.default_rng(seed)
    u = np.cumsum(rng.exponential(1.0, size=n)) + float(riemann_siegel_theta(start_height) / np.pi)
    return gammas_with_unfolded_image(u)


@pytest.fixture(scope="module")
def gammas() -> np.ndarray:
    """All zero ordinates below T = 10⁴ (10142 of them).  Cached in data/."""
    return zero_ordinates(t_max=T_MAX)


@pytest.fixture(scope="module")
def spacings(gammas: np.ndarray) -> np.ndarray:
    return nearest_neighbour_spacings(gammas)


# --------------------------------------------------------------------------- #
# Riemann–Siegel machinery vs mpmath
# --------------------------------------------------------------------------- #


def test_riemann_siegel_theta_matches_mpmath() -> None:
    """θ is accurate to float64 machine precision, not merely to 1e-10.

    Measured relative error ≤ 2.6e-16 over t ∈ [1, 10⁶]; the assertion is at
    1e-14 so it still has margin but would catch any real regression.
    """
    mp.dps = 30
    for t in (1.0, 5.0, 10.0, 14.134725141734694, 100.0, 1000.0, 1e4, 1e5, 1e6):
        ref = float(siegeltheta(t))
        assert abs(float(riemann_siegel_theta(t)) - ref) <= 1e-14 * abs(ref), f"t={t}"


def test_riemann_siegel_theta_is_odd() -> None:
    """θ(−t) = −θ(t): catches a wrong branch / sign in the log Γ."""
    t = np.array([1.0, 10.0, 100.0, 1000.0])
    assert np.max(np.abs(riemann_siegel_theta(-t) + riemann_siegel_theta(t))) < 1e-12


def test_riemann_siegel_theta_asymptotic() -> None:
    """θ(t) = (t/2)log(t/2π) − t/2 − π/8 + 1/(48t) + O(1/t³).

    Asserting only |θ − asym| < 1e-4 would be 50× looser than reality and would
    not test the *shape* of the error; here the residual is pinned to the next
    term of the expansion, 1/(48t), to 1e-11.
    """
    for t in (1000.0, 10000.0, 100000.0):
        asym = 0.5 * t * np.log(t / (2 * np.pi)) - 0.5 * t - np.pi / 8
        residual = float(riemann_siegel_theta(t)) - asym
        assert abs(residual - 1.0 / (48.0 * t)) < 1e-10, f"t={t}"


@pytest.mark.parametrize(
    ("t0", "tol"),
    [(100.0, 2e-7), (1000.0, 2e-8), (10000.0, 2e-10)],
)
def test_riemann_siegel_z_matches_mpmath(t0: float, tol: float) -> None:
    """Measured max error: 4.6e-8, 4.6e-9, 2.9e-11, tolerances are ~5×, not 20×."""
    mp.dps = 25
    ts = t0 + np.linspace(0.0, 3.0, 15)
    ref = np.array([float(siegelz(t)) for t in ts])
    assert np.max(np.abs(riemann_siegel_z(ts) - ref)) < tol


def test_riemann_siegel_z_remainder_order_improves_with_each_term() -> None:
    """Each C_k must divide the error by ~a = √(t/2π); if a coefficient had the
    wrong sign or constant, adding it would make things *worse*, not better."""
    mp.dps = 25
    ts = 10000.0 + np.linspace(0.0, 3.0, 20)
    ref = np.array([float(siegelz(t)) for t in ts])
    errs = [float(np.max(np.abs(riemann_siegel_z(ts, k_terms=k) - ref))) for k in range(4)]
    assert errs[0] > errs[1] > errs[2] > errs[3], errs
    assert errs[0] / errs[3] > 1e4, errs  # measured ratio ≈ 1.7e5


def test_riemann_siegel_z_shape_follows_input() -> None:
    """Scalar in → 0-d out, exactly like ``riemann_siegel_theta``."""
    assert np.shape(riemann_siegel_z(100.0)) == np.shape(riemann_siegel_theta(100.0)) == ()
    assert riemann_siegel_z(np.linspace(100.0, 103.0, 7)).shape == (7,)
    assert riemann_siegel_z([100.0, 101.0]).shape == (2,)


def test_z_vanishes_at_the_known_zeros() -> None:
    """|Z(γₙ)| at the published ordinates.

    The worst is γ₁ (|Z| = 7.7e-5) because the asymptotic series is weakest at
    t = 14; it falls to ~1.7e-6 by γ₁₀.  Tolerance 2e-4, not 1e-3.
    """
    z = np.abs(riemann_siegel_z(FIRST_TEN))
    assert z.max() < 2e-4
    assert z[-1] < 5e-6  # already much better by γ₁₀ = 49.77


def test_z_has_no_sign_change_below_the_first_zero() -> None:
    """Guards the N = 0 regime (t < 2π), where the main sum is empty: a wrong
    remainder sign there would inject spurious 'zeros' at the bottom of the scan."""
    tt = np.linspace(5.0, 14.13, 5000)
    assert np.all(riemann_siegel_z(tt) < 0.0)


# --------------------------------------------------------------------------- #
# The zeros themselves
# --------------------------------------------------------------------------- #


def test_first_ten_zero_ordinates(gammas: np.ndarray) -> None:
    assert np.max(np.abs(gammas[:10] - FIRST_TEN)) < 1e-12


def test_twenty_nine_zeros_below_one_hundred(gammas: np.ndarray) -> None:
    assert int((gammas < 100.0).sum()) == 29


def test_zeros_are_strictly_increasing(gammas: np.ndarray) -> None:
    assert gammas.size > 10000
    assert np.all(np.diff(gammas) > 0.0)


def test_zero_count_matches_riemann_von_mangoldt(gammas: np.ndarray) -> None:
    """N(T) = θ(T)/π + 1 + S(T), exact; mpmath.backlunds supplies S(T).

    A single missed (or spurious) zero anywhere below T shows up here.  A ladder
    of 34 heights spaced 300 apart, not a handful: a miss that is compensated by
    a spurious root further up would slip through a sparse check.
    """
    mp.dps = 25
    for t in np.arange(50.0, 10000.0, 300.0):
        expected = int(round(float(siegeltheta(t) / mp.pi + 1 + backlunds(t))))
        assert int((gammas < t).sum()) == expected, f"count mismatch at T={t}"


def test_no_zero_is_missing_anywhere(gammas: np.ndarray) -> None:
    """S(γₙ) = n − 1 − θ(γₙ)/π must hover around ½ across the whole range.

    A single missed zero shifts every later value by exactly 1, so block means
    are a sensitive, oracle-free completeness check over *all* 10142 zeros,
    not just at the heights where ``backlunds`` was sampled.  (½, not 0, because
    S evaluated at a zero is the average of the two one-sided limits.)
    """
    n = np.arange(1, gammas.size + 1)
    s = (n - 1) - unfold(gammas)
    block = 250
    means = np.array([s[i : i + block].mean() for i in range(0, s.size - block, block)])
    assert np.max(np.abs(means - 0.5)) < 0.05, (means.min(), means.max())
    assert abs(s.mean() - 0.5) < 0.01
    assert -1.0 < s.min() and s.max() < 2.0  # |S| stays small below T = 10⁴


def test_adaptive_gap_refinement_actually_recovers_lost_zeros() -> None:
    """Exercise step 2 of the scan, which the default settings never trigger.

    At ``samples_per_spacing`` = 14 and T ≤ 10⁴ the coarse sign-change scan is
    already complete, so the refinement branch was dead code as far as the
    suite was concerned, disabling it entirely left all tests green.  Here the
    grid is deliberately crippled (3 samples per mean spacing) so that the
    coarse pass provably loses zeros, and the refinement must recover *every*
    one of them.

    Measured at T = 2000 (true count 1517): coarse alone finds 1509, refinement
    restores 1517.  Same story at T = 10⁴ for 6/4/3/2 samples per spacing
    (10 / 30 / 96 / 326 recovered), and at the default density at T = 10⁵ (14).
    """
    mp.dps = 25
    t = 2000.0
    true_count = int(round(float(siegeltheta(t) / mp.pi + 1 + backlunds(t))))

    coarse = _find_zeros_by_scan(t, samples_per_spacing=3, gap_threshold=99.0, t_polish=50.0)
    refined = _find_zeros_by_scan(t, samples_per_spacing=3, t_polish=50.0)

    assert coarse.size < true_count, "crippled grid was supposed to lose zeros"
    assert refined.size == true_count, f"{refined.size} != {true_count}"
    assert np.all(np.diff(refined) > 0.0)  # merge/dedup must not duplicate roots
    # the recovered roots are genuine zeros, not artefacts of the finer grid.
    # Above t = 50 (the polish cutoff used here) |Z| at every root is ≤ 8.5e-12;
    # below it the *series* is weak, |Z(γ₁)| = 7.7e-5 even though γ₁ is exact,
    # so the residual there measures the RS truncation, not the root.
    above = refined[refined > 50.0]
    assert np.max(np.abs(riemann_siegel_z(above))) < 1e-10


def test_zeros_index_match_mpmath_zetazero(gammas: np.ndarray) -> None:
    """Independent oracle, by index: γₙ must equal mpmath.zetazero(n).imag.

    Worst measured error is 5.4e-9, at n = 100 (γ ≈ 236.5, just above the
    mpmath-polish cutoff of t = 200).  n ≤ 50 are exact in float64.
    """
    mp.dps = 25
    for n in (1, 3, 29, 100, 250, 1000, 5000, 10142):
        assert abs(gammas[n - 1] - float(zetazero(n).imag)) < 2e-8, f"n={n}"
    for n in (1, 5, 10, 29, 50):
        assert gammas[n - 1] == float(zetazero(n).imag), f"n={n}"


def test_zero_cache_is_keyed_by_the_actual_t_max() -> None:
    """Regression: ``int(round(t_max))`` in the cache filename made 59.0 and
    59.4 share one file, so the second request silently returned the first
    answer, missing γ₁₃ = 59.3470.  Two different heights, two different
    answers, in either call order.
    """
    mp.dps = 25
    for t in (59.0, 59.4):
        got = zero_ordinates(t_max=t)
        expected = int(round(float(siegeltheta(t) / mp.pi + 1 + backlunds(t))))
        assert got.size == expected, f"t_max={t}: {got.size} != {expected}"
        assert np.all(got < t)
    # and again, now that both caches exist, to prove the load path is keyed too
    assert zero_ordinates(t_max=59.0).size == 12
    assert zero_ordinates(t_max=59.4).size == 13


def test_zero_cache_rejects_a_file_written_for_another_height() -> None:
    """Second line of defence: the ``t_max`` stored *inside* the .npz is checked.

    The filename fix alone would already be enough, so without this test that
    check is unreachable code.  Here a deliberately mislabelled cache is planted
    and ``zero_ordinates`` must ignore and rebuild it rather than hand back the
    three fake ordinates.
    """
    path = _zeros_cache_path(59.0)
    np.savez_compressed(
        path, gammas=np.array([1.0, 2.0, 3.0]), t_max=np.float64(1234.0)
    )
    got = zero_ordinates(t_max=59.0)
    assert got.size == 12, "a cache written for another height was reused"
    assert abs(got[0] - 14.134725141734694) < 1e-12
    # the poisoned file must have been overwritten with the correct one
    with np.load(path) as fh:
        assert float(fh["t_max"]) == 59.0
        assert fh["gammas"].size == 12


# --------------------------------------------------------------------------- #
# Unfolding
# --------------------------------------------------------------------------- #


def test_unfolded_mean_spacing_is_one_within_one_percent(spacings: np.ndarray) -> None:
    assert abs(spacings.mean() - 1.0) < 0.01


def test_unfolded_mean_spacing_is_one_far_better_than_one_percent(spacings: np.ndarray) -> None:
    """γ̃ₙ = n − 1 − S(γₙ), so the mean spacing deviates only by O(1/N)."""
    assert abs(spacings.mean() - 1.0) < 1e-4


def test_unfold_is_monotone_and_right_length(gammas: np.ndarray) -> None:
    u = unfold(gammas)
    assert u.shape == gammas.shape
    assert np.all(np.diff(u) > 0.0)
    assert nearest_neighbour_spacings(gammas).size == gammas.size - 1


def test_unfold_agrees_with_asymptotic_formula(gammas: np.ndarray) -> None:
    """θ(γ)/π  vs  (γ/2π)log(γ/2π) − γ/2π: the two differ by 1/8 + O(1/γ)."""
    g = gammas[gammas > 1000.0]
    theta_over_pi = unfold(g)
    asymptotic = (g / (2 * np.pi)) * np.log(g / (2 * np.pi)) - g / (2 * np.pi)
    assert np.max(np.abs((asymptotic - theta_over_pi) - 0.125)) < 1e-4


def test_unfold_removes_the_density_drift(gammas: np.ndarray) -> None:
    """Mean spacing in the bottom and top decile must both be ≈ 1."""
    s = nearest_neighbour_spacings(gammas)
    k = s.size // 10
    assert abs(s[:k].mean() - 1.0) < 0.02
    assert abs(s[-k:].mean() - 1.0) < 0.02


# --------------------------------------------------------------------------- #
# The spacing laws themselves
# --------------------------------------------------------------------------- #


def test_wigner_surmise_is_normalised() -> None:
    s = np.linspace(0.0, 12.0, 400001)
    p = wigner_surmise_gue(s)
    assert abs(np.trapezoid(p, s) - 1.0) < 1e-9
    assert abs(np.trapezoid(s * p, s) - 1.0) < 1e-9


def test_wigner_surmise_vanishes_quadratically_at_zero() -> None:
    assert wigner_surmise_gue(0.0) == 0.0
    # p(s) ~ (32/π²)s²  as s → 0
    assert abs(float(wigner_surmise_gue(1e-3)) / (32 / np.pi**2 * 1e-6) - 1.0) < 1e-5


def test_wigner_cdf_is_the_integral_of_the_pdf() -> None:
    s = np.linspace(0.0, 4.0, 200001)
    p = wigner_surmise_gue(s)
    cum = np.concatenate([[0.0], np.cumsum(0.5 * (p[1:] + p[:-1]) * np.diff(s))])
    assert np.max(np.abs(cum - wigner_surmise_gue_cdf(s))) < 1e-6


def test_poisson_spacing_is_exponential() -> None:
    s = np.array([0.0, 0.5, 1.0, 2.0, 5.0])
    assert np.allclose(poisson_spacing(s), np.exp(-s))
    assert np.allclose(poisson_spacing_cdf(s[1:]), 1.0 - np.exp(-s[1:]))
    assert float(poisson_spacing(0.0)) == 1.0  # maximal at s = 0: clumping


def test_gue_gap_probability_boundary_values() -> None:
    assert abs(float(gue_gap_probability(0.0)) - 1.0) < 1e-12
    assert float(gue_gap_probability(0.0)) > float(gue_gap_probability(1.0)) > 0.0
    assert float(gue_gap_probability(5.0)) < 1e-10


def test_gue_exact_spacing_is_normalised_with_unit_mean() -> None:
    """The Gaudin law p = E'' must satisfy ∫p = 1 and ∫s·p = 1."""
    s = np.linspace(1e-9, 6.0, 600001)
    p = gue_spacing_exact(s)
    assert abs(np.trapezoid(p, s) - 1.0) < 1e-6
    assert abs(np.trapezoid(s * p, s) - 1.0) < 1e-6


def test_gue_gap_matches_an_independent_fredholm_determinant() -> None:
    """E(0;s) against a second, independent evaluation of det(I − K_s).

    The module uses 60 Gauss–Legendre nodes and Π(1 − λᵢ) from ``eigvalsh``;
    here we use 200 nodes and ``det`` (LU, not eigenvalues), and no spline.
    Agreement to ≤ 1.2e-11 relative for s ≤ 3 confirms the quadrature count,
    the eigenvalue product and the spline interpolation all at once.

    (``errstate``: numpy 2.5's ``det`` raises spurious divide/overflow FP flags
    from inside LAPACK even for this well-conditioned matrix, cond = 4.6, and
    returns the right answer regardless.)
    """
    m = 200
    nodes, weights = np.polynomial.legendre.leggauss(m)
    cases = [(0.25, 1e-12), (0.5, 1e-12), (1.0, 1e-12), (1.5, 1e-11), (2.0, 1e-10), (3.0, 1e-9)]
    for s, rtol in cases:
        x = 0.5 * s * nodes
        w = 0.5 * s * weights
        a = np.sqrt(w)[:, None] * np.sinc(x[:, None] - x[None, :]) * np.sqrt(w)[None, :]
        with np.errstate(all="ignore"):
            ref = float(np.linalg.det(np.eye(m) - a))
        assert abs(float(gue_gap_probability(s)) - ref) < rtol * ref, f"s={s}"


def test_gue_cubic_repulsion_coefficient_is_pi_squared_over_nine() -> None:
    """F(s) → (π²/9)s³ as s → 0 for the exact GUE law, a closed form that the
    whole Fredholm/spline pipeline has to reproduce with nothing fitted.

    (p(s) = (π²/3)s² + O(s⁴), so F(s) = (π²/9)s³.  The 2×2 Wigner surmise gets
    32/(3π²) = 1.0808 instead, a 1.4 % different constant, so this test can
    tell the exact law from the surmise, which is the point.)

    Measured F(s)/s³ − π²/9: 1.6e-6, 2.2e-5, 8.7e-5 at s = 0.0025, 0.005, 0.01,
    the residual is the genuine O(s²) term of the expansion (it quadruples
    when s doubles), not error, which the last assertion checks.
    """
    devs = {}
    for s in (0.0025, 0.005, 0.01):
        devs[s] = float(gue_spacing_exact_cdf(s)) / s**3 - np.pi**2 / 9.0
        assert abs(devs[s]) < 2e-4, f"s={s}: {devs[s]}"
    # the residual scales like s², i.e. it is the next term, not numerical noise
    assert 3.0 < devs[0.01] / devs[0.005] < 5.0

    assert abs(float(wigner_surmise_gue_cdf(0.01)) / 0.01**3 - 32.0 / (3 * np.pi**2)) < 2e-4
    # the two constants really are different, the test above is not vacuous
    assert abs(np.pi**2 / 9.0 - 32.0 / (3 * np.pi**2)) > 0.01


def test_gue_exact_variance_matches_mehta() -> None:
    """Var(s) = 0.1800 for GUE (Mehta, Random Matrices, Table 6.x)."""
    s = np.linspace(1e-9, 6.0, 600001)
    p = gue_spacing_exact(s)
    m1 = np.trapezoid(s * p, s)
    m2 = np.trapezoid(s * s * p, s)
    assert abs((m2 - m1**2) - 0.1800) < 5e-4


def test_gue_exact_cdf_starts_at_zero_and_repels() -> None:
    assert float(gue_spacing_exact_cdf(0.0)) == 0.0
    assert float(gue_spacing_exact_cdf(1e-3)) < 1e-8  # cubic repulsion
    assert 0.99 < float(gue_spacing_exact_cdf(5.0)) <= 1.0


def test_wigner_surmise_is_close_to_the_exact_gue_law() -> None:
    """The 2×2 surmise is within ~0.2% of the N → ∞ answer in CDF."""
    s = np.linspace(0.0, 5.0, 20001)
    assert np.max(np.abs(gue_spacing_exact_cdf(s) - wigner_surmise_gue_cdf(s))) < 5e-3
    assert np.max(np.abs(gue_spacing_exact(s) - wigner_surmise_gue(s))) < 2e-2


# --------------------------------------------------------------------------- #
# Montgomery's pair correlation
# --------------------------------------------------------------------------- #


def test_montgomery_prediction_at_integers() -> None:
    """R₂(k) = 1 − (sin πk/πk)² = 1 at every non-zero integer, since sin πk = 0."""
    assert montgomery_prediction(1.0) == 1.0
    assert montgomery_prediction(2.0) == 1.0
    assert np.all(montgomery_prediction(np.arange(1.0, 11.0)) == 1.0)


def test_montgomery_prediction_correlation_hole() -> None:
    """R₂(0) = 0 exactly, and R₂(r) ~ (πr)²/3 for small r."""
    assert montgomery_prediction(0.0) == 0.0
    r = 1e-3
    assert abs(float(montgomery_prediction(r)) / ((np.pi * r) ** 2 / 3.0) - 1.0) < 1e-5
    assert np.all(montgomery_prediction(np.linspace(0.01, 0.5, 50)) < 1.0)


def test_pair_correlation_reproduces_montgomery(gammas: np.ndarray) -> None:
    r, r2 = pair_correlation(gammas, r_max=3.0, bins=30)
    pred = montgomery_prediction(r)
    sel = r > 0.15
    assert np.sqrt(np.mean((r2[sel] - pred[sel]) ** 2)) < 0.06
    assert np.max(np.abs(r2[sel] - pred[sel])) < 0.15


def test_pair_correlation_shows_the_correlation_hole(gammas: np.ndarray) -> None:
    """The empirical density of small differences must be ≪ 1 (Poisson gives 1)."""
    r, r2 = pair_correlation(gammas, r_max=3.0, bins=30)
    assert r2[r < 0.1].max() < 0.1
    assert abs(r2[r > 2.0].mean() - 1.0) < 0.05  # decorrelates to density 1


def test_pair_correlation_estimator_is_unbiased(gammas: np.ndarray) -> None:
    """Poisson control through the real ``pair_correlation``.

    Uncorrelated levels have R₂ ≡ 1 at every r, so the estimator's edge/window
    normalisation 1/(Δ·(L − r)) must return a flat 1, otherwise the dip the
    zeros show near r = 0 could be an artefact of the normalisation rather than
    the correlation hole.  Measured over 6 seeds: mean 0.996–1.046, and the
    *minimum* over all 30 bins never drops below 0.91, whereas the zeros'
    first bin is 0.005.
    """
    r, r2 = pair_correlation(poisson_gammas(9000, seed=4), r_max=3.0, bins=30)
    assert abs(r2.mean() - 1.0) < 0.08
    assert r2.min() > 0.85  # no spurious hole at small r
    assert abs(r2[r < 0.2].mean() - 1.0) < 0.15

    # and the zeros, through the identical call, are an order of magnitude down
    _, r2_zeros = pair_correlation(gammas, r_max=3.0, bins=30)
    assert r2_zeros[0] < r2.min() / 10.0


def test_pair_correlation_shapes(gammas: np.ndarray) -> None:
    r, r2 = pair_correlation(gammas[:2000], r_max=2.0, bins=25)
    assert r.shape == r2.shape == (25,)
    assert 0.0 < r[0] < r[-1] < 2.0


# --------------------------------------------------------------------------- #
# The headline: level repulsion, GUE vs Poisson
# --------------------------------------------------------------------------- #


def test_level_repulsion_report_prefers_gue_by_a_mile(gammas: np.ndarray) -> None:
    rep = level_repulsion_report(gammas)
    d_gue = rep["ks_gue_exact"]["statistic"]
    d_poi = rep["ks_poisson"]["statistic"]
    assert d_gue < 0.05
    assert d_poi > 0.25
    assert d_gue < d_poi / 5.0  # "substantially smaller"
    assert rep["verdict"].startswith("GUE")
    assert rep["ks_poisson"]["pvalue"] < 1e-100
    assert rep["ks_gue_wigner"]["statistic"] < d_poi / 5.0


def test_level_repulsion_report_fields(gammas: np.ndarray) -> None:
    rep = level_repulsion_report(gammas)
    assert rep["n_zeros"] == gammas.size
    assert rep["n_spacings"] == gammas.size - 1
    assert abs(rep["mean_spacing"] - 1.0) < 0.01
    assert 0.10 < rep["var_spacing"] < 0.25  # nowhere near Poisson's 1.0
    assert abs(rep["variance_reference"]["gue_exact"] - 0.1800) < 5e-4


def test_small_spacings_are_suppressed(gammas: np.ndarray) -> None:
    """Poisson would put ~9.5% of spacings below 0.1; GUE ~0.1%.  Zeros: ~0.05%."""
    rep = level_repulsion_report(gammas)
    frac = rep["frac_spacing_below_0.1"]
    assert frac["poisson"] > 0.09
    assert frac["gue_exact"] < 0.005
    assert frac["observed"] < 0.005
    assert frac["observed"] < frac["poisson"] / 20.0


def test_no_two_zeros_collide(spacings: np.ndarray) -> None:
    """Level repulsion at its most literal: the minimum spacing is far from 0."""
    assert spacings.min() > 0.01


# --------------------------------------------------------------------------- #
# Actual random matrices
# --------------------------------------------------------------------------- #


def test_gue_eigenvalues_follow_the_semicircle() -> None:
    n = 400
    lam = gue_eigenvalues(n, seed=3)
    assert lam.shape == (n,)
    assert np.all(np.diff(lam) >= 0.0)
    r = 2.0 * np.sqrt(n)
    assert lam.min() > -1.15 * r and lam.max() < 1.15 * r
    # semicircle second moment: E[λ²] = n  (so RMS ≈ √n)
    assert abs(np.mean(lam**2) / n - 1.0) < 0.05


def test_unfold_gue_gives_unit_mean_spacing() -> None:
    n = 600
    lam = gue_eigenvalues(n, seed=7)
    bulk = lam[n // 5 : -n // 5]
    s = np.diff(unfold_gue(bulk, n))
    assert abs(s.mean() - 1.0) < 0.02
    assert abs(s.var(ddof=1) - 0.18) < 0.05


def test_compare_to_random_matrix_is_the_headline(gammas: np.ndarray) -> None:
    res = compare_to_random_matrix(gammas.size, seed=0, matrix_size=400, gammas=gammas)

    # (a) the random matrix really does obey the exact Gaudin law
    assert res["ks_gue_matrix_vs_gaudin"]["statistic"] < 0.02
    assert res["ks_gue_matrix_vs_gaudin"]["pvalue"] > 0.01

    # (b) the zeros look like the random matrix, and nothing like Poisson
    d_gue = res["ks2_zeta_vs_gue_matrix"]["statistic"]
    d_poi = res["ks2_zeta_vs_poisson"]["statistic"]
    assert d_gue < 0.06
    assert d_poi > 0.25
    assert d_gue < d_poi / 5.0

    # (c) same for the histograms and the moments
    assert res["max_hist_abs_diff_zeta_vs_gue"] < res["max_hist_abs_diff_zeta_vs_poisson"] / 4.0
    assert abs(res["mean_spacing_zeta"] - res["mean_spacing_gue"]) < 0.01
    assert abs(res["var_spacing_zeta"] - res["var_spacing_gue"]) < 0.05


def test_compare_to_random_matrix_arrays_line_up(gammas: np.ndarray) -> None:
    res = compare_to_random_matrix(2000, seed=1, matrix_size=300, bins=40, gammas=gammas[:2000])
    for key in ("bin_centres", "hist_zeta", "hist_gue_matrix", "hist_poisson", "hist_gue_exact"):
        assert res[key].shape == (40,)
    assert res["n_spacings"] == 1999


# --------------------------------------------------------------------------- #
# Spectral form factor
# --------------------------------------------------------------------------- #


def test_form_factor_has_a_ramp_and_a_plateau(gammas: np.ndarray) -> None:
    """GUE: K(τ) ≈ min(τ,1).  Poisson: K(τ) ≡ 1.  The zeros show the ramp."""
    tau = np.linspace(0.02, 2.0, 400)
    k = form_factor(gammas, tau, smooth=12)
    ramp = k[(tau > 0.05) & (tau < 0.3)].mean()
    plateau = k[tau > 1.3].mean()
    assert ramp < 0.4  # a Poisson process would sit at 1 here
    assert 0.6 < plateau < 1.6
    assert ramp < plateau / 2.0


def test_form_factor_of_a_poisson_process_is_flat(gammas: np.ndarray) -> None:
    """Control experiment, run through ``form_factor`` itself.

    The previous version of this test re-implemented the estimator inline on
    already-unfolded points, on the grounds that building γ's with a prescribed
    unfolded image "is not possible".  It is: θ/π is strictly monotone, so
    Newton inverts it (``gammas_with_unfolded_image``, accurate to 5e-12).  So
    the control now exercises the real code path, same function, same
    unfolding, same smoothing, and the only difference is the input process.

    Measured ramp-band K: 0.98 for Poisson (theory 1, no ramp) vs 0.13 for the
    zeros.  Seed-to-seed spread over 6 seeds: 0.84–1.08.
    """
    tau = np.linspace(0.05, 1.5, 200)
    k_poisson = form_factor(poisson_gammas(8000, seed=11), tau, smooth=12)
    band = (tau > 0.05) & (tau < 0.3)
    assert abs(k_poisson[band].mean() - 1.0) < 0.35

    # the same estimator on the real zeros must be far lower in the same band
    k_zeros = form_factor(gammas, tau, smooth=12)
    assert k_zeros[band].mean() < 0.3
    assert k_zeros[band].mean() < k_poisson[band].mean() / 3.0


def test_form_factor_shape(gammas: np.ndarray) -> None:
    tau = np.linspace(0.1, 1.0, 17)
    assert form_factor(gammas[:1000], tau).shape == (17,)


# --------------------------------------------------------------------------- #
# Caching / API hygiene
# --------------------------------------------------------------------------- #


def test_zero_ordinates_slicing_and_cache(gammas: np.ndarray) -> None:
    first_20 = zero_ordinates(20, t_max=T_MAX)
    assert first_20.shape == (20,)
    assert np.array_equal(first_20, gammas[:20])
    with pytest.raises(ValueError):
        zero_ordinates(10**9, t_max=T_MAX)
    with pytest.raises(ValueError):
        zero_ordinates(10, source="nonsense")


def test_ks_statistic_shrinks_with_height(gammas: np.ndarray) -> None:
    """Montgomery–Odlyzko convergence, at *matched sample size*.

    The obvious version of this test, γ < 1000 (648 spacings) against
    γ > 2000 (8624 spacings), is worthless: the KS statistic of a *correct*
    model already falls like 1/√n, and 1/√648 = 0.039 is essentially the whole
    of the observed D_low = 0.046.  It would pass with no height dependence at
    all.  So take equally many spacings from the bottom and the top.

    Measured (k = 2000): D_low = 0.0427, D_high = 0.0280.  Robust for every
    k from 1000 to 5000 (ratio 0.60–0.88).
    """
    s = nearest_neighbour_spacings(gammas)
    for k in (1000, 2000, 3000):
        d_low = kstest(s[:k], gue_spacing_exact_cdf).statistic
        d_high = kstest(s[-k:], gue_spacing_exact_cdf).statistic
        assert d_high < d_low, f"k={k}: {d_high} !< {d_low}"


def test_spacing_variance_rises_towards_gue_with_height(gammas: np.ndarray) -> None:
    """The honest picture: at γ < 10⁴ the zeros are *more rigid* than GUE.

    Var(s) = 0.1542 over the whole range against the GUE value 0.1800: 14 %
    low, and a real finite-height effect rather than a bug.  This test pins the
    number and its direction of travel (deciles: 0.1442 → 0.1578), and is
    sample-size-free, unlike a KS statistic.
    """
    s = nearest_neighbour_spacings(gammas)
    assert 0.150 < s.var(ddof=1) < 0.160  # 0.15420, well below GUE's 0.18000
    block = s.size // 10
    first = s[:block].var(ddof=1)
    last = s[-block:].var(ddof=1)
    assert first < last < 0.1800
    assert last - first > 0.005  # measured 0.0136


def test_against_zeta_zeros_module(gammas: np.ndarray) -> None:
    """Cross-check the fast Riemann–Siegel scan against the repo's own
    mpmath ``zetazero`` driver in :mod:`zeta.zeros`."""
    pytest.importorskip("zeta.zeros")
    ref = zero_ordinates(50, source="zeta.zeros")
    assert np.max(np.abs(ref - gammas[:50])) < 1e-9
