"""Tests for the randomised Euler product null model.

Every closed form used by ``zeta.surrogate`` is checked against a sampled
estimate, and the reusable interval statistic is checked against the moment
experiment's own pipeline so the null comparison runs on the same algorithm.
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from zeta.surrogate import (
    covariance_profile,
    euler_field_variance,
    euler_intensity_moment,
    exact_intensity_moment,
    field_variance,
    intensity_moment_defect,
    interval_statistics,
    primes_up_to,
    sample_euler_intensity,
    sample_euler_log_field,
    sample_field,
    sample_intensity,
    variance_defect,
)


def test_primes_up_to_matches_known_counts():
    assert list(primes_up_to(30)) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    assert len(primes_up_to(10_000)) == 1229
    assert len(primes_up_to(100_000)) == 9592
    assert primes_up_to(1).size == 0


def test_field_variance_is_half_sum_of_reciprocal_primes():
    primes = primes_up_to(10_000)
    expected = 0.5 * sum(1.0 / float(p) for p in primes)
    assert field_variance(primes) == pytest.approx(expected, rel=1e-14)
    # (1/2) log log P is the Selberg normalisation; Mertens' constant is the gap.
    assert field_variance(primes) == pytest.approx(1.24152, abs=1e-5)


def test_sampled_variance_matches_the_closed_form():
    primes = primes_up_to(10_000)
    assert variance_defect(primes, seed=11, samples=120_000, span=4_000.0) < 0.02


def test_exact_intensity_moment_matches_a_direct_bessel_product():
    primes = primes_up_to(1_000)
    from scipy.special import i0

    for k in (1, 2, 3, 4):
        expected = float(np.prod(i0(2.0 * k / np.sqrt(primes.astype(float)))))
        assert exact_intensity_moment(k, primes) == pytest.approx(expected, rel=1e-12)


def test_exact_intensity_moment_is_reproduced_by_sampling_at_low_order():
    """The k=1 estimator converges; the k=4 one does not at any feasible size.

    This is the phenomenon the null exists to probe, so both halves are pinned:
    a small defect for the second moment, and a defect near one for the eighth,
    where a finite sample misses almost all of the true mean.
    """

    primes = primes_up_to(2_000)
    assert intensity_moment_defect(1, primes, seed=5, samples=200_000) < 0.05
    assert intensity_moment_defect(4, primes, seed=5, samples=200_000) > 0.5


def test_covariance_profile_decays_from_the_variance():
    primes = primes_up_to(10_000)
    lags = np.array([0.0, 0.05, 0.2, 1.0, 5.0])
    profile = covariance_profile(primes, lags)
    assert profile[0] == pytest.approx(field_variance(primes), rel=1e-14)
    assert np.all(np.diff(profile[:4]) < 0)
    assert abs(profile[4]) < 0.35 * profile[0]


def test_sampling_is_deterministic_in_the_seed():
    primes = primes_up_to(500)
    ts = np.linspace(0.0, 50.0, 4_001)
    first = sample_field(ts, primes, seed=7)
    second = sample_field(ts, primes, seed=7)
    other = sample_field(ts, primes, seed=8)
    assert np.array_equal(first, second)
    assert not np.allclose(first, other)


def test_intensity_is_the_exponential_of_twice_the_field():
    primes = primes_up_to(500)
    ts = np.linspace(0.0, 20.0, 1_001)
    assert np.allclose(
        sample_intensity(ts, primes, seed=3),
        np.exp(2.0 * sample_field(ts, primes, seed=3)),
        rtol=1e-14,
    )


def test_variance_normalisation_has_mutation_teeth():
    """Halving the weights must break the pinned variance, not slip through."""

    primes = primes_up_to(10_000)
    ts = np.linspace(0.0, 4_000.0, 120_000)
    honest = float(np.var(sample_field(ts, primes, seed=11)))
    assert honest == pytest.approx(field_variance(primes), rel=0.02)

    rng = np.random.default_rng(11)
    phases = rng.uniform(0.0, 2.0 * np.pi, size=len(primes))
    mutated = (
        np.cos(ts[:, None] * np.log(primes.astype(float))[None, :] + phases[None, :])
        @ (0.5 / np.sqrt(primes.astype(float)))
    )
    assert float(np.var(mutated)) != pytest.approx(field_variance(primes), rel=0.02)


def test_interval_statistics_reproduce_the_trapezoid_integral():
    values = np.linspace(1.0, 2.0, 1_001)
    spacing = 0.001
    stats = {item.k: item for item in interval_statistics(values, spacing, blocks=8)}
    assert stats[1].integral == pytest.approx(
        float(np.trapezoid(values, dx=spacing)), rel=1e-14
    )
    assert stats[2].integral == pytest.approx(
        float(np.trapezoid(values**2, dx=spacing)), rel=1e-14
    )
    # A smooth monotone ramp is not concentrated and barely disperses.
    assert stats[1].top_contribution < 0.02
    assert stats[1].block_dispersion < 0.35


def test_interval_statistics_match_the_moment_pipeline_on_real_zeta():
    """The adapter must agree with ``scripts/14_moment_experiment.py`` exactly.

    If these two disagree, the null comparison is not running the same
    algorithm as the zeta measurement and means nothing.
    """

    import importlib.util
    import sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    path = root / "scripts" / "14_moment_experiment.py"
    spec = importlib.util.spec_from_file_location("moment_experiment_for_null", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    from zeta.statistics import riemann_siegel_z

    start, length, spacing = 1e5, 5e1, 5e-3
    _, concentrations, _, _ = module.block_peak_sweep(
        start, length, spacing, blocks=8, peak_fractions=(0.01,)
    )
    reference = {item.k: item.contribution_fraction for item in concentrations}

    count = int(round(length / spacing)) + 1
    ts = start + np.arange(count) * spacing
    mine = {
        item.k: item.top_contribution
        for item in interval_statistics(
            riemann_siegel_z(ts) ** 2, spacing, blocks=8, top_fraction=0.01
        )
    }
    for k in (1, 2, 3, 4):
        assert mine[k] == pytest.approx(reference[k], rel=1e-12)


def test_interval_statistics_reject_bad_grids():
    values = np.ones(101)
    with pytest.raises(ValueError):
        interval_statistics(values, 0.0)
    with pytest.raises(ValueError):
        interval_statistics(values, 0.01, blocks=8)  # 100 intervals, 8 blocks
    with pytest.raises(ValueError):
        interval_statistics(values, 0.01, blocks=10, top_fraction=1.5)


def test_euler_moment_reproduces_the_repository_arithmetic_factor():
    """The strongest check available: a_k derived two unrelated ways.

    ``euler_intensity_moment`` is ``prod_p sum_m d_k(p^m)^2 p^{-m}``, computed
    here from the random Euler product.  Dividing out the Euler-product
    regularisation ``prod_p (1-1/p)^{-k^2}`` must return the arithmetic factor
    that ``scripts/14_moment_experiment.py`` computes independently for the
    CFKRS polynomials.  Agreement is not assumed anywhere; it is measured.
    """

    import importlib.util
    import sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    path = root / "scripts" / "14_moment_experiment.py"
    spec = importlib.util.spec_from_file_location("moment_experiment_for_ak", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    primes = primes_up_to(200_000)
    regularisation = float(np.sum(np.log1p(-1.0 / primes.astype(float))))
    for k in (1, 2, 3, 4):
        implied = math.exp(
            math.log(euler_intensity_moment(k, primes)) + k * k * regularisation
        )
        assert implied == pytest.approx(
            float(module.arithmetic_factor(k)), rel=1e-10
        )

    # Pinned so a normalisation change cannot pass silently.
    implied_four = math.exp(
        math.log(euler_intensity_moment(4, primes)) + 16 * regularisation
    )
    assert implied_four == pytest.approx(2.1468e-4, rel=1e-4)


def test_euler_variance_exceeds_the_first_order_variance():
    """The dropped prime-power terms are positive, so the Euler field is wider."""

    primes = primes_up_to(10_000)
    first = field_variance(primes)
    full = euler_field_variance(primes)
    assert full > first
    # The m=1 term of the Euler series is exactly the first-order variance.
    assert full - first == pytest.approx(
        sum(
            float(p) ** -m / (2.0 * m**2)
            for p in primes
            for m in range(2, 60)
        ),
        rel=1e-10,
    )


def test_sampled_euler_variance_matches_its_closed_form():
    primes = primes_up_to(10_000)
    ts = np.linspace(0.0, 4_000.0, 120_000)
    measured = float(np.var(sample_euler_log_field(ts, primes, seed=11)))
    assert measured == pytest.approx(euler_field_variance(primes), rel=0.03)


def test_euler_sampling_is_deterministic_and_exponentiates_consistently():
    primes = primes_up_to(500)
    ts = np.linspace(0.0, 20.0, 1_001)
    assert np.array_equal(
        sample_euler_log_field(ts, primes, seed=7),
        sample_euler_log_field(ts, primes, seed=7),
    )
    assert np.allclose(
        sample_euler_intensity(ts, primes, seed=3),
        np.exp(2.0 * sample_euler_log_field(ts, primes, seed=3)),
        rtol=1e-14,
    )


def test_euler_intensity_moment_matches_a_direct_expansion():
    """Check the series against an independent brute-force phase average."""

    primes = primes_up_to(50)
    rng = np.random.default_rng(2)
    for k in (1, 2):
        draws = 400_000
        phases = rng.uniform(0.0, 2.0 * np.pi, size=(draws, len(primes)))
        x = 1.0 / np.sqrt(primes.astype(float))
        magnitude = 1.0 + 1.0 / primes.astype(float) - 2.0 * x * np.cos(phases)
        sampled = float(np.mean(np.exp(-k * np.sum(np.log(magnitude), axis=1))))
        assert sampled == pytest.approx(
            euler_intensity_moment(k, primes), rel=0.05
        )


def test_tail_profile_separates_variance_from_the_upper_tail():
    """Pin the measured split: zeta is wider overall but shorter at the top.

    ``log|zeta|`` diverges at every zero, so its variance exceeds both zero-free
    surrogates while its upper quantiles fall below them.  High moments depend
    only on the upper tail, so this is the direction that matters and it is
    pinned here rather than described.
    """

    import importlib.util
    import sys
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    path = root / "scripts" / "15_null_control.py"
    spec = importlib.util.spec_from_file_location("null_control_for_tails", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    profile = module.tail_profile(1e4)
    assert profile["zeta"]["variance"] == pytest.approx(1.7149, abs=1e-3)
    assert profile["first-order"]["variance"] == pytest.approx(1.2592, abs=1e-3)
    assert profile["euler"]["variance"] == pytest.approx(1.2998, abs=1e-3)
    assert profile["zeta"]["p999"] == pytest.approx(2.7039, abs=1e-3)
    assert profile["first-order"]["p999"] == pytest.approx(3.6277, abs=1e-3)

    for null in ("first-order", "euler"):
        assert profile["zeta"]["variance"] > profile[null]["variance"]
        assert profile["zeta"]["p99"] < profile[null]["p99"]
        assert profile["zeta"]["p999"] < profile[null]["p999"]
        assert profile["zeta"]["max"] < profile[null]["max"]


def test_cue_moment_matches_a_direct_product_and_sampling():
    from zeta.surrogate import (
        cue_moment,
        sample_cue_eigenangles,
        sample_cue_intensity,
    )

    # Direct evaluation of the Keating-Snaith product for a small dimension.
    for k in (1, 2):
        expected = 1.0
        for j in range(6):
            expected *= math.factorial(j) * math.factorial(j + 2 * k) / (
                math.factorial(j + k) ** 2
            )
        assert cue_moment(k, 6) == pytest.approx(expected, rel=1e-10)

    # E|Lambda_N|^2 = N + 1 is the classical second-moment identity.
    for dimension in (3, 7, 12):
        assert cue_moment(1, dimension) == pytest.approx(dimension + 1.0, rel=1e-10)

    # Sampled against the closed form.  |Lambda|^2 is heavy enough that 400
    # matrices land within ~5% and 2000 within ~1%; the tolerance here is set
    # from that measured convergence, not from optimism.
    for seed in (4, 5):
        values = sample_cue_intensity(6, 2_000, 32, seed=seed)
        assert float(np.mean(values)) == pytest.approx(cue_moment(1, 6), rel=0.02)

    angles = sample_cue_eigenangles(5, 3, seed=1)
    assert angles.shape == (3, 5)
    assert np.array_equal(angles, sample_cue_eigenangles(5, 3, seed=1))


def test_arithmetic_and_matrix_factors_reconstruct_the_cfkrs_coefficient():
    """a_k from the Euler product times g_k from CUE is the leading coefficient.

    Neither factor is taken from a table: ``a_k`` comes from the random Euler
    product's exact intensity moment and ``g_k`` from the Keating-Snaith
    product divided by ``N^{k^2}``.  Their product must converge to the leading
    CFKRS coefficient that ``scripts/14_moment_experiment.py`` derives
    independently, and the residual must shrink with the matrix dimension.
    """

    import importlib.util
    import sys
    from pathlib import Path

    from zeta.surrogate import cue_moment

    root = Path(__file__).resolve().parent.parent
    path = root / "scripts" / "14_moment_experiment.py"
    spec = importlib.util.spec_from_file_location("moment_experiment_for_gk", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    primes = primes_up_to(200_000)
    regularisation = float(np.sum(np.log1p(-1.0 / primes.astype(float))))
    for k in (1, 2, 3, 4):
        a_k = math.exp(
            math.log(euler_intensity_moment(k, primes)) + k * k * regularisation
        )
        reference = float(module.leading_coefficient(k))
        ratios = []
        for dimension in (4_000, 40_000):
            g_k = math.exp(
                math.log(cue_moment(k, dimension)) - k * k * math.log(dimension)
            )
            ratios.append(a_k * g_k / reference)
        assert ratios[1] == pytest.approx(1.0, abs=2e-3)
        assert abs(ratios[1] - 1.0) < abs(ratios[0] - 1.0)


@pytest.mark.slow
def test_davenport_heilbronn_also_shows_rising_concentration():
    """The counterexample battery's gate applied to the concentration pattern.

    ``f`` violates the Riemann Hypothesis, so a property ``f`` also has cannot
    be structural evidence about zeta.  Concentration rising with moment order
    is such a property, which is exactly why the pattern distinguishes nothing.
    """

    from zeta.epstein import Z_dh, _dh_mean_spacing

    height = 200.0
    spacing = float(_dh_mean_spacing(height)) / 32.0
    ts = height + np.arange(481) * spacing
    values = np.array([float(Z_dh(float(t), dps=15)) for t in ts]) ** 2
    shares = [
        item.top_contribution
        for item in interval_statistics(values, spacing, blocks=8, top_fraction=0.05)
    ]
    assert shares == sorted(shares)
    assert shares[3] > 2.0 * shares[0]


def test_zeta_concentration_approaches_the_cue_median_with_height():
    """The eighth-moment gap to the CUE median shrinks as the height grows.

    At t=1e3 zeta is far below the CUE distribution; by t=1e6 it sits on the
    median.  The CUE side is a fixed set of seeds so the comparison is
    deterministic, and the assertion is on the shrinking gap rather than on a
    hand-chosen tolerance.
    """

    from zeta.statistics import riemann_siegel_z
    from zeta.surrogate import sample_cue_log_field

    gaps, points_per_gap, seeds = 750, 32, 40
    measured = {}
    for height in (1e3, 1e6):
        spacing = (2.0 * math.pi / math.log(height / (2.0 * math.pi))) / points_per_gap
        ts = height + np.arange(gaps * points_per_gap + 1) * spacing
        zeta_share = [
            item.top_contribution
            for item in interval_statistics(
                riemann_siegel_z(ts) ** 2, spacing, blocks=8, top_fraction=0.01
            )
        ][3]

        dimension = int(round(math.log(height / (2.0 * math.pi))))
        matrices = math.ceil(gaps / dimension)
        cue_spacing = 2.0 * math.pi / (dimension * points_per_gap)
        shares = []
        for index in range(seeds):
            values = np.exp(
                2.0
                * sample_cue_log_field(
                    dimension, matrices, points_per_gap, seed=1000 + index
                )
            )
            usable = len(values) - (len(values) - 1) % 8
            shares.append(
                [
                    item.top_contribution
                    for item in interval_statistics(
                        values[:usable], cue_spacing, blocks=8, top_fraction=0.01
                    )
                ][3]
            )
        measured[height] = zeta_share - float(np.median(shares))

    assert measured[1e3] < -0.10
    assert abs(measured[1e6]) < 0.05
    assert abs(measured[1e6]) < abs(measured[1e3])


def test_surrogate_concentration_rises_with_moment_order():
    """The null's own concentration ordering, the pattern under audit.

    Pinned loosely: the point is the ordering, which the null produces without
    any arithmetic input, so the ordering alone distinguishes nothing.
    """

    primes = primes_up_to(10_000)
    spacing = (2.0 * math.pi / math.log(1e4 / (2.0 * math.pi))) / 64.0
    ts = np.arange(24_001) * spacing
    values = sample_intensity(ts, primes, seed=20260804)
    shares = [
        item.top_contribution
        for item in interval_statistics(values, spacing, blocks=8, top_fraction=0.01)
    ]
    assert shares == sorted(shares)
    assert shares[0] > 0.2
    assert shares[3] > 0.95
