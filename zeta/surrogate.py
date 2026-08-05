"""Null-model surrogates for the critical-line value distribution.

This module builds *controls*, not models of anything claimed to be new.  The
purpose is adversarial: if a surrogate field with no arithmetic content
reproduces a statistic measured on ``|zeta(1/2+it)|``, then that statistic is
explained by the surrogate's generic structure and is not evidence of anything
specific to zeta.  A control that matches is a finding killed, not a finding
supported.  Nothing here bears on the Riemann Hypothesis in either direction.

The surrogate is the randomised Euler product, the standard random model for
``log|zeta|``::

    X(t) = sum_{p <= P} p^{-1/2} cos(t log p + theta_p),   theta_p iid U[0, 2pi)

with the surrogate intensity ``exp(2 X(t))`` standing in for
``|zeta(1/2+it)|^2``.  Two properties make it useful as a null:

* ``Var X = (1/2) sum_{p <= P} 1/p``, which is ``~ (1/2) log log P``, matching
  the Selberg central-limit-theorem variance when ``P`` is taken to be the
  height; and
* the intensity moments are available in closed form,
  ``E[exp(2k X)] = prod_{p <= P} I_0(2k p^{-1/2})``, because each phase is
  uniform.  The null therefore needs no conjectural reference value: its
  analogue of the CFKRS ratio is measured against an exact mean.

Both properties are *derived* here and then *measured* by the defect functions
below rather than assumed, following the repository's habit.

What the surrogate deliberately does not model: the arithmetic factor ``a_k``,
the functional equation, the true non-Gaussian tail of ``log|zeta|``, and the
slow variation of the field with height.  It is stationary by construction,
whereas zeta is not.  Any comparison must therefore be read as "does the
generic log-correlated structure already account for the statistic", not as a
fit.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from scipy.special import i0

__all__ = [
    "IntervalStatistics",
    "covariance_profile",
    "cue_moment",
    "euler_field_variance",
    "euler_intensity_moment",
    "exact_intensity_moment",
    "field_variance",
    "interval_statistics",
    "intensity_moment_defect",
    "primes_up_to",
    "sample_cue_eigenangles",
    "sample_cue_intensity",
    "sample_cue_log_field",
    "sample_euler_intensity",
    "sample_euler_log_field",
    "sample_field",
    "sample_intensity",
    "variance_defect",
]


def primes_up_to(limit: int) -> np.ndarray:
    """Return every prime ``p <= limit`` as an ``int64`` array."""

    if isinstance(limit, bool) or not isinstance(limit, (int, np.integer)):
        raise TypeError("limit must be an integer")
    if limit < 2:
        return np.empty(0, dtype=np.int64)
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for candidate in range(2, int(math.isqrt(limit)) + 1):
        if sieve[candidate]:
            sieve[candidate * candidate :: candidate] = False
    return np.flatnonzero(sieve).astype(np.int64)


def field_variance(primes: np.ndarray) -> float:
    """Exact variance of ``X``: ``(1/2) sum 1/p`` over the supplied primes.

    Each summand ``p^{-1/2} cos(t log p + theta_p)`` has variance ``1/(2p)``
    because ``Var cos(U) = 1/2`` for uniform ``U``, and the phases are
    independent.  Checked against a sampled estimate by :func:`variance_defect`.
    """

    if len(primes) == 0:
        return 0.0
    return float(0.5 * np.sum(1.0 / primes.astype(float)))


def exact_intensity_moment(k: int, primes: np.ndarray) -> float:
    """Exact ``E[exp(2k X)] = prod_p I_0(2k p^{-1/2})``.

    For uniform phase ``U`` and any real ``a``, ``E[exp(a cos U)] = I_0(a)``;
    independence across primes turns the expectation of the product into the
    product of the expectations.  Returned in linear scale via a log-sum so the
    product does not overflow.  Checked by :func:`intensity_moment_defect`.
    """

    if isinstance(k, bool) or not isinstance(k, (int, np.integer)) or k < 1:
        raise ValueError("k must be a positive integer")
    if len(primes) == 0:
        return 1.0
    argument = 2.0 * k / np.sqrt(primes.astype(float))
    return float(np.exp(np.sum(np.log(i0(argument)))))


def sample_field(
    ts: np.ndarray,
    primes: np.ndarray,
    *,
    seed: int,
    max_elements: int = 20_000_000,
) -> np.ndarray:
    """Sample ``X(t)`` on ``ts`` for one draw of the phases.

    ``seed`` fixes the phases and therefore the entire realisation; the same
    seed and primes always reproduce the same field.
    """

    if isinstance(seed, bool) or not isinstance(seed, (int, np.integer)):
        raise TypeError("seed must be an integer")
    ts = np.asarray(ts, dtype=float)
    if ts.ndim != 1:
        raise ValueError("ts must be one-dimensional")
    if len(primes) == 0:
        return np.zeros_like(ts)

    rng = np.random.default_rng(seed)
    phases = rng.uniform(0.0, 2.0 * np.pi, size=len(primes))
    log_primes = np.log(primes.astype(float))
    weights = 1.0 / np.sqrt(primes.astype(float))

    out = np.empty(len(ts), dtype=float)
    chunk = max(1, int(max_elements // len(primes)))
    for begin in range(0, len(ts), chunk):
        block = ts[begin : begin + chunk]
        angles = block[:, None] * log_primes[None, :] + phases[None, :]
        out[begin : begin + chunk] = np.cos(angles) @ weights
    return out


def sample_intensity(
    ts: np.ndarray,
    primes: np.ndarray,
    *,
    seed: int,
    max_elements: int = 20_000_000,
) -> np.ndarray:
    """Surrogate for ``|zeta(1/2+it)|^2``: ``exp(2 X(t))``."""

    return np.exp(
        2.0 * sample_field(ts, primes, seed=seed, max_elements=max_elements)
    )


def variance_defect(
    primes: np.ndarray, *, seed: int, samples: int = 200_000, span: float = 5_000.0
) -> float:
    """Relative defect between sampled variance of ``X`` and ``(1/2) sum 1/p``.

    Sampling over a finite span of a field with long-range correlation is a
    biased estimator, so a defect of a few percent is expected and is reported,
    not hidden.
    """

    ts = np.linspace(0.0, span, samples)
    values = sample_field(ts, primes, seed=seed)
    measured = float(np.var(values))
    target = field_variance(primes)
    return abs(measured - target) / target


def intensity_moment_defect(
    k: int,
    primes: np.ndarray,
    *,
    seed: int,
    samples: int = 200_000,
    span: float = 5_000.0,
) -> float:
    """Relative defect between a sampled mean of ``exp(2kX)`` and the exact moment.

    This estimator is itself tail-dominated for larger ``k`` — the very effect
    under study — so a large defect at ``k = 3, 4`` is a statement about sample
    size, not about the closed form.  Interpret accordingly.
    """

    ts = np.linspace(0.0, span, samples)
    values = sample_intensity(ts, primes, seed=seed)
    measured = float(np.mean(values**k))
    target = exact_intensity_moment(k, primes)
    return abs(measured - target) / target


def covariance_profile(
    primes: np.ndarray, lags: np.ndarray
) -> np.ndarray:
    """Exact ``Cov(X(t), X(t+tau)) = (1/2) sum_p cos(tau log p) / p`` per lag.

    The log-decaying shape of this profile is what makes the surrogate a
    *log-correlated* null rather than a white one; it is computed exactly here
    so a test can pin it without sampling noise.
    """

    lags = np.asarray(lags, dtype=float)
    if len(primes) == 0:
        return np.zeros_like(lags)
    log_primes = np.log(primes.astype(float))
    inverse = 1.0 / primes.astype(float)
    return np.array(
        [0.5 * float(np.sum(np.cos(lag * log_primes) * inverse)) for lag in lags]
    )


def euler_field_variance(primes: np.ndarray, *, terms: int = 200) -> float:
    """Exact ``Var log|Z|`` for the full random Euler product.

    From ``-log|1 - x e^{iU}| = sum_{m>=1} x^m cos(mU)/m`` with ``x = p^{-1/2}``
    and uniform ``U``, each prime contributes ``sum_{m>=1} p^{-m} / (2 m^2)``.
    The ``m = 1`` term alone is ``1/(2p)``, which is :func:`field_variance`; the
    remainder is the correction the first-order surrogate drops.
    """

    if len(primes) == 0:
        return 0.0
    p = primes.astype(float)[:, None]
    m = np.arange(1, terms + 1, dtype=float)[None, :]
    return float(np.sum(p ** (-m) / (2.0 * m**2)))


def euler_intensity_moment(k: int, primes: np.ndarray, *, terms: int = 200) -> float:
    """Exact ``E[|Z|^{2k}] = prod_p sum_m d_k(p^m)^2 p^{-m}`` for the Euler product.

    Expanding ``(1 - x e^{iU})^{-k}`` gives coefficients ``d_k(p^m) =
    C(m+k-1, m)``; the uniform phase kills every cross term, leaving the
    diagonal sum.  This is precisely the product whose regularisation is the
    arithmetic factor ``a_k`` — the quantity the first-order surrogate has no
    way to produce.  Returned via a log-sum so the product does not overflow.
    """

    if isinstance(k, bool) or not isinstance(k, (int, np.integer)) or k < 1:
        raise ValueError("k must be a positive integer")
    if len(primes) == 0:
        return 1.0
    m = np.arange(terms + 1)
    coefficients = np.array(
        [float(math.comb(int(order) + k - 1, int(order))) for order in m]
    )
    p = primes.astype(float)[:, None]
    series = np.sum(coefficients[None, :] ** 2 * p ** (-m[None, :].astype(float)), axis=1)
    return float(np.exp(np.sum(np.log(series))))


def sample_euler_log_field(
    ts: np.ndarray,
    primes: np.ndarray,
    *,
    seed: int,
    max_elements: int = 20_000_000,
) -> np.ndarray:
    """Sample ``log|Z(t)|`` for the full random Euler product.

    ``Z(t) = prod_p (1 - p^{-1/2} e^{i(theta_p - t log p)})^{-1}`` keeps the
    genuine ``p^{-it}`` frequency structure while randomising the phase offset,
    so it is a stationary field in ``t`` whose one-point law is exactly the
    classical random Euler product.  Its logarithm is
    ``-(1/2) sum_p log(1 - 2 p^{-1/2} cos(phi_p) + 1/p)``.
    """

    if isinstance(seed, bool) or not isinstance(seed, (int, np.integer)):
        raise TypeError("seed must be an integer")
    ts = np.asarray(ts, dtype=float)
    if ts.ndim != 1:
        raise ValueError("ts must be one-dimensional")
    if len(primes) == 0:
        return np.zeros_like(ts)

    rng = np.random.default_rng(seed)
    phases = rng.uniform(0.0, 2.0 * np.pi, size=len(primes))
    log_primes = np.log(primes.astype(float))
    x = 1.0 / np.sqrt(primes.astype(float))
    offset = 1.0 + 1.0 / primes.astype(float)

    out = np.empty(len(ts), dtype=float)
    chunk = max(1, int(max_elements // len(primes)))
    for begin in range(0, len(ts), chunk):
        block = ts[begin : begin + chunk]
        angles = phases[None, :] - block[:, None] * log_primes[None, :]
        magnitude = offset[None, :] - 2.0 * x[None, :] * np.cos(angles)
        out[begin : begin + chunk] = -0.5 * np.sum(np.log(magnitude), axis=1)
    return out


def sample_euler_intensity(
    ts: np.ndarray,
    primes: np.ndarray,
    *,
    seed: int,
    max_elements: int = 20_000_000,
) -> np.ndarray:
    """Surrogate for ``|zeta(1/2+it)|^2`` from the full random Euler product."""

    return np.exp(
        2.0
        * sample_euler_log_field(ts, primes, seed=seed, max_elements=max_elements)
    )


def cue_moment(k: int, dimension: int) -> float:
    """Exact ``E|Lambda_N(theta)|^{2k}`` for the CUE characteristic polynomial.

    The Keating-Snaith formula ``prod_{j=0}^{N-1} j! (j+2k)! / ((j+k)!)^2``.
    Its large-``N`` growth is ``g_k N^{k^2}``, so the CUE side supplies the
    random-matrix factor of the CFKRS constant exactly as the random Euler
    product supplies the arithmetic factor.  Computed by a log-sum of log-gamma
    values so the factorials do not overflow.
    """

    if isinstance(k, bool) or not isinstance(k, (int, np.integer)) or k < 1:
        raise ValueError("k must be a positive integer")
    if (
        isinstance(dimension, bool)
        or not isinstance(dimension, (int, np.integer))
        or dimension < 1
    ):
        raise ValueError("dimension must be a positive integer")
    j = np.arange(dimension, dtype=float)
    from scipy.special import gammaln

    total = np.sum(
        gammaln(j + 1.0) + gammaln(j + 2 * k + 1.0) - 2.0 * gammaln(j + k + 1.0)
    )
    return float(np.exp(total))


def sample_cue_eigenangles(
    dimension: int, matrices: int, *, seed: int
) -> np.ndarray:
    """Eigenangles of ``matrices`` independent Haar-distributed unitaries.

    Drawn by QR of a complex Ginibre matrix with the diagonal phases of ``R``
    divided out, which is the standard construction giving exactly Haar measure
    rather than a biased approximation.  Returns shape ``(matrices, dimension)``.
    """

    if isinstance(seed, bool) or not isinstance(seed, (int, np.integer)):
        raise TypeError("seed must be an integer")
    rng = np.random.default_rng(seed)
    out = np.empty((matrices, dimension), dtype=float)
    for index in range(matrices):
        ginibre = (
            rng.standard_normal((dimension, dimension))
            + 1j * rng.standard_normal((dimension, dimension))
        ) / math.sqrt(2.0)
        q, r = np.linalg.qr(ginibre)
        diagonal = np.diagonal(r)
        q = q * (diagonal / np.abs(diagonal))[None, :]
        out[index] = np.angle(np.linalg.eigvals(q))
    return out


def sample_cue_log_field(
    dimension: int,
    matrices: int,
    points_per_gap: int,
    *,
    seed: int,
) -> np.ndarray:
    """``log|Lambda_N|`` on a uniform grid spanning ``matrices`` independent draws.

    Each matrix covers ``dimension`` mean eigenvalue gaps, so concatenating
    ``matrices`` of them produces a field of ``dimension * matrices`` nominal
    gaps at ``points_per_gap`` resolution.  The concatenation is honest only
    because the field decorrelates within a couple of gaps; it cannot model
    correlation longer than one matrix, and no statistic sensitive to that
    range should be read off it.

    Unlike either Euler surrogate this field has genuine zeros on the grid's
    own circle, so ``log|Lambda_N|`` diverges exactly as ``log|zeta|`` does.
    """

    if points_per_gap < 1:
        raise ValueError("points_per_gap must be at least one")
    angles = sample_cue_eigenangles(dimension, matrices, seed=seed)
    per_matrix = dimension * points_per_gap
    theta = 2.0 * np.pi * np.arange(per_matrix) / per_matrix
    blocks = []
    for index in range(matrices):
        difference = theta[:, None] - angles[index][None, :]
        blocks.append(
            np.sum(np.log(2.0 * np.abs(np.sin(difference / 2.0))), axis=1)
        )
    return np.concatenate(blocks)


def sample_cue_intensity(
    dimension: int,
    matrices: int,
    points_per_gap: int,
    *,
    seed: int,
) -> np.ndarray:
    """``|Lambda_N|^2`` on the concatenated grid; the CUE analogue of ``|zeta|^2``."""

    return np.exp(
        2.0
        * sample_cue_log_field(dimension, matrices, points_per_gap, seed=seed)
    )


@dataclass(frozen=True)
class IntervalStatistics:
    """Concentration and block dispersion for one moment order on one grid."""

    k: int
    integral: float
    block_integrals: tuple[float, ...]
    block_dispersion: float
    top_fraction: float
    top_contribution: float


def interval_statistics(
    values: np.ndarray,
    spacing: float,
    *,
    blocks: int = 8,
    top_fraction: float = 0.01,
    orders: tuple[int, ...] = (1, 2, 3, 4),
) -> tuple[IntervalStatistics, ...]:
    """Concentration and block statistics for ``values^k`` on a uniform grid.

    This mirrors the interval algorithm of ``scripts/14_moment_experiment.py``
    exactly: composite-trapezoid contributions per grid interval, each interval
    assigned to one of ``blocks`` equal-width blocks, and the ``top_fraction``
    of interval contributions ranked by size and summed.  ``values`` are the
    ``|f|^2`` samples, so order ``k`` corresponds to the ``2k``-th moment.

    ``block_dispersion`` is the sample coefficient of variation (``ddof=1``) of
    the block integrals.  For a stationary field with a constant reference mean
    it equals the coefficient of variation of block ratios used on the zeta
    side.  It is a dispersion of deterministic disjoint blocks, not a standard
    error and not a confidence interval.
    """

    values = np.asarray(values, dtype=float)
    if values.ndim != 1 or len(values) < 3:
        raise ValueError("values must be a one-dimensional array of length at least 3")
    if not (math.isfinite(spacing) and spacing > 0):
        raise ValueError("spacing must be finite and positive")
    if isinstance(blocks, bool) or not isinstance(blocks, int) or blocks < 2:
        raise ValueError("blocks must be an integer at least 2")
    if not (math.isfinite(top_fraction) and 0 < top_fraction < 1):
        raise ValueError("top_fraction must lie strictly between 0 and 1")

    intervals = len(values) - 1
    if intervals % blocks:
        raise ValueError("interval count must be divisible by the block count")
    per_block = intervals // blocks
    interval_count = max(1, math.ceil(top_fraction * intervals))

    results = []
    for k in orders:
        powered = values**k
        contributions = spacing * (powered[:-1] + powered[1:]) / 2.0
        total = float(np.sum(contributions))
        block_integrals = tuple(
            float(np.sum(contributions[index * per_block : (index + 1) * per_block]))
            for index in range(blocks)
        )
        mean = float(np.mean(block_integrals))
        dispersion = float(np.std(block_integrals, ddof=1)) / abs(mean)
        largest = np.partition(contributions, intervals - interval_count)[
            intervals - interval_count :
        ]
        results.append(
            IntervalStatistics(
                k=k,
                integral=total,
                block_integrals=block_integrals,
                block_dispersion=dispersion,
                top_fraction=interval_count / intervals,
                top_contribution=float(np.sum(largest)) / total,
            )
        )
    return tuple(results)
