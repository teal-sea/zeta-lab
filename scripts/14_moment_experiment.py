#!/usr/bin/env python
"""Critical-line moments from locally computed values, and where they can be tested.

What this is
------------
``zeta/moments.py`` was built to consume an *external* dense table of
``|zeta(1/2+it)|`` samples, because the heights worth reaching for zero
statistics (Odlyzko's ``10^21``-``10^22`` landmarks) are far beyond anything
this laboratory computes.  The 2026-08-04 source audit in ``docs/13-moments.md``
found no such public table, and the module correctly refuses to invent one.

This script takes the other road.  It **generates its own values** at a modest
height, where the vectorised Riemann--Siegel evaluation in
``zeta.statistics.riemann_siegel_z`` is fast and is cross-checked against
mpmath's ``siegelz``, and it measures the finite moments

    M_k(A, B) = (1/(B-A)) * integral_A^B |zeta(1/2+it)|^(2k) dt

for k = 1, 2, 3, 4 -- the 2nd, 4th, 6th and 8th moments.

Why the full polynomial matters at this height
-----------------------------------------------
The instinct that moments need enormous ``t`` comes from the *leading-order*
Keating--Snaith form, ``M_k ~ c_k (log(t/2pi))^(k^2)``.  At the modest height
this script can sweep directly, lower-order terms are still numerically large.

Apply Cauchy--Schwarz to the leading terms alone.  For the true moments,
``E[X^2] >= E[X]^2`` with ``X = |zeta|^(2k)``, so a *necessary* condition for the
leading-order forms of the ``2k``-th and ``4k``-th moments to be simultaneously
in force is

    c_2k (log(t/2pi))^(4k^2) >= c_k^2 (log(t/2pi))^(2k^2).

Solving for the height gives a pairwise consistency threshold.  For example,
the threshold computed with ``k=4`` concerns the 8th *and* 16th moments
together; it is not a floor for the 8th moment alone.  Below a threshold, at
least one of the two leading forms is not dominant.  Above it, Cauchy--Schwarz
says nothing about whether either asymptotic is accurate.  The calculation is a
diagnostic for the leading-term comparison, not a computational-reach bound.

What is actually testable here, and what is not
-----------------------------------------------
Numerically checked by this script:

  * The **2nd moment**, using Ingham's two-term global theorem:
    ``integral_0^T |zeta|^2 dt = T log(T/2pi) + (2 gamma - 1) T + E(T)``.
    The script uses the difference of the displayed main term across its window
    as a numerical calibration.  This does not turn the global theorem into a
    short-interval theorem: the residual includes ``E(B)-E(A)``.

Reported as a finite-window diagnostic, not a test of the conjectures:

  * The 4th, 6th and 8th moments against the full CFKRS moment polynomial of
    degree ``k^2``.  The 4th-moment polynomial is theorem-backed; the 6th and
    8th are conjectural.  Published decimal coefficients for the latter have
    reported stable digits but no interval enclosure, so they are accurate
    inputs, not certified ones.  None of these global formulas becomes a
    short-interval theorem merely because it is evaluated on this window.

With ``--convergence``, one finest-grid evaluation is reused for prefix windows
of width ``L/4``, ``L/2`` and ``L`` and spacings ``h``, ``2h`` and ``4h``.
Grid drift diagnoses quadrature resolution; window-ratio drift exposes finite-
window variability to which rare peaks may contribute. Neither is an error
bound, confidence interval or certificate, and one nested family is not a
collection of independent samples.

With ``--blocks N``, the same one-pass principle measures ``N`` equal disjoint
blocks and ranks trapezoidal interval contributions. It reports deterministic
block-ratio dispersion and the integral shares carried by the largest 0.1% and
1% of grid intervals. Disjoint blocks are not asserted to be statistically
independent, and their dispersion is not a standard error.

With ``--replicate``, that block/peak study is repeated at ``10^4``, ``10^5``
and ``10^6``. Each window spans 6,000 local asymptotic mean zero gaps with 128
points per gap, so height changes without silently changing nominal zero count
or grid resolution. These are three deterministic windows, not repeated random
trials.

With ``--attack``, four consecutive non-overlapping whole windows are run in
each height band. Three gates are fixed in code before evaluation: 5% pooled
tolerance for the theorem controls, 15% for conjectural ratios, and strictly
rising median top-one-percent concentration for the 6th and 8th moments. The
candidate pattern is rejected if any gate fails; survival is still not proof.

Nothing here settles, supports or weakens the Riemann Hypothesis, and finite
moment measurements could not do so in principle.

Usage
-----
    .venv/bin/python scripts/14_moment_experiment.py
    .venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 2e4
    .venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 4e3 \
        --convergence
    .venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 4e3 \
        --blocks 8
    .venv/bin/python scripts/14_moment_experiment.py --replicate
    .venv/bin/python scripts/14_moment_experiment.py --attack
    .venv/bin/python scripts/14_moment_experiment.py --emit data/samples.txt.gz \
        --emit-length 100 --emit-error-estimate 1e-8

``--emit`` writes the samples as ``offset abs_zeta absolute_error`` rows, the
format ``zeta.moments.load_critical_line_samples`` documents.  Note that the
loader binds samples to an imported *external* zero window and will not accept a
locally generated file; the emitted rows are a reusable artefact and a format
reference, not a drop-in for that route.  Rows are large -- the default window
would emit tens of millions of them -- so ``--emit`` also requires
``--emit-length`` to keep the file to a stated size and
``--emit-error-estimate`` so the script never invents a value-error claim.
"""

from __future__ import annotations

import argparse
import gzip
import math
import sys
import time
from dataclasses import dataclass
from itertools import pairwise
from math import comb, factorial
from pathlib import Path

import mpmath as mp
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from zeta.moments import (  # noqa: E402
    moment_polynomial,
    moment_polynomial_mean,
    moment_reference,
)
from zeta.statistics import riemann_siegel_z  # noqa: E402

EULER_GAMMA = mp.euler

# Chunk width for the streaming sweep.  40e6 float64 samples would be 320 MB per
# temporary array; chunking keeps the peak in the low hundreds of megabytes.
CHUNK = 2_000_000
OFFSET_THEOREM_TOLERANCE = 0.05
OFFSET_CONJECTURAL_TOLERANCE = 0.15


@dataclass(frozen=True)
class ConvergenceRow:
    """One nested-window/nested-spacing moment comparison."""

    k: int
    window_length: float
    spacing: float
    integral: float
    measured_mean: float
    polynomial_mean: float
    ratio: float


@dataclass(frozen=True)
class ConvergenceDiagnostic:
    """Maximum observed changes under the two nesting operations."""

    k: int
    max_spacing_relative_drift: float
    max_window_ratio_relative_drift: float


@dataclass(frozen=True)
class BlockMomentRow:
    """One moment measurement on a disjoint deterministic block."""

    k: int
    block_index: int
    interval_start: float
    interval_end: float
    integral: float
    measured_mean: float
    polynomial_mean: float
    ratio: float


@dataclass(frozen=True)
class BlockDiagnostic:
    """Observed dispersion of block ratios, with no sampling interpretation."""

    k: int
    aggregate_ratio: float
    block_ratio_coefficient_of_variation: float
    minimum_block_ratio: float
    maximum_block_ratio: float


@dataclass(frozen=True)
class PeakConcentration:
    """Share of a moment integral carried by the largest grid intervals."""

    k: int
    interval_fraction: float
    interval_count: int
    contribution_fraction: float


@dataclass(frozen=True)
class HeightReplicationRow:
    """One moment's diagnostics at one height-normalized window."""

    height: float
    mean_zero_gap: float
    window_length: float
    spacing: float
    sample_count: int
    k: int
    aggregate_ratio: float
    block_ratio_coefficient_of_variation: float
    top_tenth_percent_contribution: float
    top_one_percent_contribution: float


@dataclass(frozen=True)
class OffsetReplicationRow:
    """One whole-window result in the pre-registered offset attack."""

    anchor_height: float
    window_index: int
    interval_start: float
    interval_end: float
    k: int
    measured_integral: float
    predicted_integral: float
    ratio: float
    block_ratio_coefficient_of_variation: float
    top_one_percent_contribution: float


@dataclass(frozen=True)
class OffsetDiagnostic:
    """Observed whole-window spread at one anchor and moment order."""

    anchor_height: float
    k: int
    pooled_ratio: float
    median_ratio: float
    minimum_ratio: float
    maximum_ratio: float
    ratio_coefficient_of_variation: float
    median_top_one_percent_contribution: float


@dataclass(frozen=True)
class OffsetAttackVerdict:
    """Result of the fixed gates declared before the multi-offset run."""

    passed: bool
    theorem_controls_passed: bool
    conjectural_ratios_passed: bool
    concentration_trend_passed: bool
    failures: tuple[str, ...]


def random_matrix_factor(k: int) -> mp.mpf:
    """The Keating--Snaith factor ``prod_{j=0}^{k-1} j! / (j+k)!``.

    This is the random-matrix constant already divided by ``(k^2)!``, so that
    ``c_k = a_k * random_matrix_factor(k)`` is the leading coefficient of
    ``(1/T) integral_0^T |zeta|^(2k) dt`` against ``(log(T/2pi))^(k^2)``.
    """

    value = mp.mpf(1)
    for j in range(k):
        value *= mp.mpf(factorial(j)) / mp.mpf(factorial(j + k))
    return value


def arithmetic_factor(k: int, *, prime_cutoff: int = 200_000) -> mp.mpf:
    """The CFKRS arithmetic factor ``a_k`` as a truncated Euler product.

    ``a_k = prod_p (1 - 1/p)^(k^2) * sum_m d_k(p^m)^2 p^-m`` with
    ``d_k(p^m) = C(m+k-1, k-1)``.  The local factor is ``1 + O(1/p^2)``, so the
    truncation converges; ``k = 2`` reproduces ``6/pi^2`` and that is asserted
    below rather than remembered.
    """

    sieve = bytearray([1]) * (prime_cutoff + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(prime_cutoff**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))

    coefficients = [mp.mpf(comb(m + k - 1, k - 1)) ** 2 for m in range(60 * k)]
    product = mp.mpf(1)
    for prime in (i for i in range(2, prime_cutoff + 1) if sieve[i]):
        x = mp.mpf(1) / prime
        local = mp.mpf(0)
        power = mp.mpf(1)
        for coefficient in coefficients:
            local += coefficient * power
            power *= x
            if power < mp.mpf(10) ** -40:
                break
        product *= (1 - x) ** (k * k) * local
    return product


def leading_coefficient(k: int) -> mp.mpf:
    """``c_k``, cross-checked against ``zeta.moments.moment_reference`` for k<=4."""

    value = arithmetic_factor(k) * random_matrix_factor(k)
    if k <= 4:
        pinned = mp.mpf(str(moment_reference(k=k).leading_coefficient))
        if abs(value - pinned) > mp.mpf("1e-4") * pinned:
            raise AssertionError(
                f"c_{k} derivation disagrees with moment_reference: "
                f"{value} vs {pinned}"
            )
    return value


def pairwise_consistency_threshold(k: int, coefficients: dict[int, mp.mpf]) -> mp.mpf:
    """Threshold for consistency of the leading ``2k``- and ``4k``-moment forms.

    Returns the ``t`` at which ``c_2k L^(4k^2) = c_k^2 L^(2k^2)`` for
    ``L = log(t/2pi)``.  Below it, the leading terms of the ``2k``-th and
    ``4k``-th moments violate Cauchy--Schwarz, so at least one is not dominant.
    It does not identify which one and is not an onset estimate for either
    moment separately.
    """

    log_threshold = (coefficients[k] ** 2 / coefficients[2 * k]) ** (
        mp.mpf(1) / (2 * k * k)
    )
    return mp.e**log_threshold * 2 * mp.pi


def second_moment_main_term(t: float) -> mp.mpf:
    """Main term in Ingham's two-term global second-moment theorem.

    ``integral_0^t |zeta(1/2+iu)|^2 du`` equals the returned expression plus
    ``E(t)``.  On a shifted window, the omitted remainder is ``E(B)-E(A)``.
    """

    with mp.workdps(40):
        u = mp.mpf(t)
        return u * mp.log(u / (2 * mp.pi)) + (2 * EULER_GAMMA - 1) * u


def sweep(
    start: float,
    length: float,
    spacing: float,
    *,
    emit: Path | None = None,
    emit_length: float = 0.0,
    emit_error_estimate: float | None = None,
) -> tuple[dict[int, float], int, float]:
    """Stream the window, accumulating trapezoidal integrals of ``|zeta|^(2k)``.

    Returns the integrals keyed by ``k``, the sample count, and the elapsed
    seconds.  Chunk boundaries contribute their own trapezoid so the composite
    rule stays exact across the seams.
    """

    if not (math.isfinite(start) and start >= 50):
        raise ValueError("start must be finite and at least 50")
    if not (math.isfinite(length) and length > 0):
        raise ValueError("length must be finite and positive")
    if not (math.isfinite(spacing) and spacing > 0):
        raise ValueError("spacing must be finite and positive")
    intervals = int(round(length / spacing))
    if not math.isclose(intervals * spacing, length, rel_tol=1e-12, abs_tol=1e-12):
        raise ValueError("length must be an integer multiple of spacing")
    if emit is not None:
        if emit_error_estimate is None or not (
            math.isfinite(emit_error_estimate) and emit_error_estimate > 0
        ):
            raise ValueError("emit_error_estimate must be finite and positive with emit")
        if not (0 < emit_length <= length):
            raise ValueError("emit_length must be positive and no greater than length")
        emit_intervals = int(round(emit_length / spacing))
        if not math.isclose(
            emit_intervals * spacing, emit_length, rel_tol=1e-12, abs_tol=1e-12
        ):
            raise ValueError("emit_length must be an integer multiple of spacing")

    count = intervals + 1
    totals = {k: 0.0 for k in (1, 2, 3, 4)}
    previous: dict[int, float] | None = None
    emitted = 0
    emit_rows = int(round(emit_length / spacing)) + 1 if emit else 0

    handle = None
    if emit is not None:
        handle = (
            gzip.open(emit, "wt")
            if emit.suffix == ".gz"
            else open(emit, "w", encoding="utf-8")
        )
        handle.write(
            "# critical-line samples, LOCALLY COMPUTED -- not external research data\n"
            f"# source: zeta.statistics.riemann_siegel_z, repo-local, base={start!r}\n"
            "# columns: offset abs_zeta absolute_error (error is an ESTIMATE)\n"
        )

    started = time.time()
    try:
        for begin in range(0, count, CHUNK):
            index = np.arange(begin, min(begin + CHUNK, count))
            ts = start + index * spacing
            squared = riemann_siegel_z(ts) ** 2
            for k in (1, 2, 3, 4):
                column = squared**k
                totals[k] += float(np.trapezoid(column, ts))
                if previous is not None:
                    totals[k] += spacing * (previous[k] + float(column[0])) / 2
            previous = {k: float((squared**k)[-1]) for k in (1, 2, 3, 4)}

            if handle is not None and emitted < emit_rows:
                take = min(emit_rows - emitted, len(ts))
                magnitudes = np.sqrt(squared[:take])
                for offset, magnitude in zip(
                    ts[:take] - start, magnitudes, strict=True
                ):
                    handle.write(
                        f"{offset:.12g} {magnitude:.17g} {emit_error_estimate:.12g}\n"
                    )
                emitted += take
    finally:
        if handle is not None:
            handle.close()

    return totals, count, time.time() - started


def convergence_sweep(
    start: float,
    length: float,
    spacing: float,
) -> tuple[tuple[ConvergenceRow, ...], int, float]:
    """Measure moments on three nested windows and three nested grids.

    The windows are the prefix intervals of width ``length/4``, ``length/2``
    and ``length``.  Their grids use spacing ``spacing``, ``2*spacing`` and
    ``4*spacing``.  All nine combinations are accumulated from one evaluation
    of the finest, longest grid.  The returned changes are diagnostics, not
    statistical errors or rigorous bounds.
    """

    if not (math.isfinite(start) and start >= 50):
        raise ValueError("start must be finite and at least 50")
    if not (math.isfinite(length) and length > 0):
        raise ValueError("length must be finite and positive")
    if not (math.isfinite(spacing) and spacing > 0):
        raise ValueError("spacing must be finite and positive")
    intervals = int(round(length / spacing))
    if not math.isclose(intervals * spacing, length, rel_tol=1e-12, abs_tol=1e-12):
        raise ValueError("length must be an integer multiple of spacing")
    if intervals < 16 or intervals % 4:
        raise ValueError(
            "convergence study requires at least 16 intervals and a count divisible by 4"
        )

    window_intervals = (intervals // 4, intervals // 2, intervals)
    spacing_factors = (1, 2, 4)
    totals = {
        (window_count, factor, k): 0.0
        for window_count in window_intervals
        for factor in spacing_factors
        for k in (1, 2, 3, 4)
    }
    previous: dict[tuple[int, int, int], float] = {}
    count = intervals + 1

    started = time.time()
    for begin in range(0, count, CHUNK):
        index = np.arange(begin, min(begin + CHUNK, count))
        ts = start + index * spacing
        squared = riemann_siegel_z(ts) ** 2
        columns = {k: squared**k for k in (1, 2, 3, 4)}

        for window_count in window_intervals:
            inside = index <= window_count
            for factor in spacing_factors:
                selected = inside & (index % factor == 0)
                if not np.any(selected):
                    continue
                selected_ts = ts[selected]
                for k, column in columns.items():
                    values = column[selected]
                    key = (window_count, factor, k)
                    totals[key] += float(np.trapezoid(values, selected_ts))
                    if key in previous:
                        totals[key] += (
                            factor * spacing * (previous[key] + float(values[0])) / 2
                        )
                    previous[key] = float(values[-1])

    elapsed = time.time() - started
    predictions = {
        (window_count, k): float(
            moment_polynomial_mean(
                moment_polynomial(k),
                str(start),
                str(start + window_count * spacing),
            )
        )
        for window_count in window_intervals
        for k in (1, 2, 3, 4)
    }
    rows = []
    for window_count in window_intervals:
        window_length = window_count * spacing
        for factor in spacing_factors:
            for k in (1, 2, 3, 4):
                integral = totals[window_count, factor, k]
                measured_mean = integral / window_length
                polynomial_mean = predictions[window_count, k]
                rows.append(
                    ConvergenceRow(
                        k=k,
                        window_length=window_length,
                        spacing=factor * spacing,
                        integral=integral,
                        measured_mean=measured_mean,
                        polynomial_mean=polynomial_mean,
                        ratio=measured_mean / polynomial_mean,
                    )
                )
    return tuple(rows), count, elapsed


def convergence_diagnostics(
    rows: tuple[ConvergenceRow, ...],
) -> tuple[ConvergenceDiagnostic, ...]:
    """Summarise observed grid drift and window drift without certifying either."""

    if not rows:
        raise ValueError("convergence diagnostics require rows")
    diagnostics = []
    for k in (1, 2, 3, 4):
        k_rows = tuple(row for row in rows if row.k == k)
        if len(k_rows) != 9:
            raise ValueError("convergence diagnostics require a complete 3 by 3 grid")
        windows = sorted({row.window_length for row in k_rows})
        spacings = sorted({row.spacing for row in k_rows})
        if len(windows) != 3 or len(spacings) != 3:
            raise ValueError("convergence diagnostics require three windows and spacings")
        by_cell = {(row.window_length, row.spacing): row for row in k_rows}
        spacing_drifts = []
        for window_length in windows:
            fine = by_cell[window_length, spacings[0]].measured_mean
            spacing_drifts.extend(
                abs(by_cell[window_length, coarse].measured_mean / fine - 1)
                for coarse in spacings[1:]
            )
        finest_ratios = [by_cell[window, spacings[0]].ratio for window in windows]
        window_drifts = [
            abs(shorter / longer - 1)
            for shorter, longer in pairwise(finest_ratios)
        ]
        diagnostics.append(
            ConvergenceDiagnostic(
                k=k,
                max_spacing_relative_drift=max(spacing_drifts),
                max_window_ratio_relative_drift=max(window_drifts),
            )
        )
    return tuple(diagnostics)


def _retain_largest(
    retained: np.ndarray, additions: np.ndarray, limit: int
) -> np.ndarray:
    """Keep the largest ``limit`` values without sorting the full stream."""

    combined = np.concatenate((retained, additions))
    if len(combined) <= limit:
        return combined
    split = len(combined) - limit
    return np.partition(combined, split)[split:]


def block_peak_sweep(
    start: float,
    length: float,
    spacing: float,
    *,
    blocks: int = 8,
    peak_fractions: tuple[float, ...] = (0.001, 0.01),
) -> tuple[tuple[BlockMomentRow, ...], tuple[PeakConcentration, ...], int, float]:
    """Measure disjoint-block dispersion and moment concentration in one pass.

    Each trapezoidal interval belongs to exactly one equal-width block.  Peak
    concentration ranks interval contributions, not isolated point values, and
    reports the share of the full integral carried by the largest requested
    fractions.  Blocks are deterministic and disjoint, not independent random
    samples; no returned quantity is a confidence interval or error bound.
    """

    if not (math.isfinite(start) and start >= 50):
        raise ValueError("start must be finite and at least 50")
    if not (math.isfinite(length) and length > 0):
        raise ValueError("length must be finite and positive")
    if not (math.isfinite(spacing) and spacing > 0):
        raise ValueError("spacing must be finite and positive")
    if isinstance(blocks, bool) or not isinstance(blocks, int) or blocks < 2:
        raise ValueError("blocks must be an integer at least 2")
    intervals = int(round(length / spacing))
    if not math.isclose(intervals * spacing, length, rel_tol=1e-12, abs_tol=1e-12):
        raise ValueError("length must be an integer multiple of spacing")
    if intervals < blocks * 2 or intervals % blocks:
        raise ValueError(
            "block study requires at least two intervals per block and an exactly divisible grid"
        )
    if (
        not peak_fractions
        or any(not math.isfinite(value) or not 0 < value < 1 for value in peak_fractions)
        or tuple(sorted(set(peak_fractions))) != peak_fractions
    ):
        raise ValueError("peak_fractions must be unique increasing numbers between 0 and 1")

    intervals_per_block = intervals // blocks
    block_totals = {
        (block_index, k): 0.0
        for block_index in range(blocks)
        for k in (1, 2, 3, 4)
    }
    total_integrals = {k: 0.0 for k in (1, 2, 3, 4)}
    largest_count = max(1, math.ceil(peak_fractions[-1] * intervals))
    retained = {k: np.empty(0, dtype=float) for k in (1, 2, 3, 4)}
    previous: dict[int, float] = {}
    count = intervals + 1

    started = time.time()
    for begin in range(0, count, CHUNK):
        index = np.arange(begin, min(begin + CHUNK, count))
        ts = start + index * spacing
        squared = riemann_siegel_z(ts) ** 2
        columns = {k: squared**k for k in (1, 2, 3, 4)}

        for k, values in columns.items():
            if k in previous:
                extended = np.concatenate((np.array([previous[k]]), values))
                first_interval = begin - 1
            else:
                extended = values
                first_interval = begin
            contributions = spacing * (extended[:-1] + extended[1:]) / 2
            if len(contributions):
                left_indices = np.arange(
                    first_interval, first_interval + len(contributions)
                )
                block_indices = left_indices // intervals_per_block
                for block_index in np.unique(block_indices):
                    block_totals[int(block_index), k] += float(
                        np.sum(contributions[block_indices == block_index])
                    )
                total_integrals[k] += float(np.sum(contributions))
                retained[k] = _retain_largest(
                    retained[k], contributions, largest_count
                )
            previous[k] = float(values[-1])

    elapsed = time.time() - started
    block_length = length / blocks
    rows = []
    for block_index in range(blocks):
        block_start = start + block_index * block_length
        block_end = block_start + block_length
        for k in (1, 2, 3, 4):
            integral = block_totals[block_index, k]
            polynomial_mean = float(
                moment_polynomial_mean(
                    moment_polynomial(k), str(block_start), str(block_end)
                )
            )
            measured_mean = integral / block_length
            rows.append(
                BlockMomentRow(
                    k=k,
                    block_index=block_index,
                    interval_start=block_start,
                    interval_end=block_end,
                    integral=integral,
                    measured_mean=measured_mean,
                    polynomial_mean=polynomial_mean,
                    ratio=measured_mean / polynomial_mean,
                )
            )

    concentrations = []
    for k in (1, 2, 3, 4):
        largest = np.sort(retained[k])[::-1]
        for fraction in peak_fractions:
            interval_count = max(1, math.ceil(fraction * intervals))
            concentrations.append(
                PeakConcentration(
                    k=k,
                    interval_fraction=interval_count / intervals,
                    interval_count=interval_count,
                    contribution_fraction=(
                        float(np.sum(largest[:interval_count])) / total_integrals[k]
                    ),
                )
            )
    return tuple(rows), tuple(concentrations), count, elapsed


def block_diagnostics(
    rows: tuple[BlockMomentRow, ...],
) -> tuple[BlockDiagnostic, ...]:
    """Summarise deterministic block ratios without assigning probabilities."""

    if not rows:
        raise ValueError("block diagnostics require rows")
    diagnostics = []
    block_indices = {row.block_index for row in rows}
    if len(block_indices) < 2:
        raise ValueError("block diagnostics require at least two blocks")
    for k in (1, 2, 3, 4):
        k_rows = tuple(row for row in rows if row.k == k)
        if {row.block_index for row in k_rows} != block_indices:
            raise ValueError("block diagnostics require every k on every block")
        ratios = np.array([row.ratio for row in k_rows])
        predicted_integrals = np.array(
            [
                row.polynomial_mean * (row.interval_end - row.interval_start)
                for row in k_rows
            ]
        )
        aggregate_ratio = sum(row.integral for row in k_rows) / float(
            np.sum(predicted_integrals)
        )
        diagnostics.append(
            BlockDiagnostic(
                k=k,
                aggregate_ratio=aggregate_ratio,
                block_ratio_coefficient_of_variation=(
                    float(np.std(ratios, ddof=1)) / abs(float(np.mean(ratios)))
                ),
                minimum_block_ratio=float(np.min(ratios)),
                maximum_block_ratio=float(np.max(ratios)),
            )
        )
    return tuple(diagnostics)


def multi_height_study(
    heights: tuple[float, ...] = (1e4, 1e5, 1e6),
    *,
    zero_gaps: int = 6_000,
    points_per_gap: int = 128,
    blocks: int = 8,
) -> tuple[tuple[HeightReplicationRow, ...], float]:
    """Repeat the block/peak study with resolution normalized by zero spacing.

    Each window spans ``zero_gaps`` local mean zero spacings and samples each
    such spacing at ``points_per_gap`` points.  This holds the nominal number
    of zeros and grid resolution fixed while height changes.  The local mean
    spacing is an asymptotic normalization, not an exact zero count.
    """

    if (
        not heights
        or any(not math.isfinite(height) or height < 50 for height in heights)
        or tuple(sorted(set(heights))) != heights
    ):
        raise ValueError("heights must be unique increasing finite values at least 50")
    if isinstance(zero_gaps, bool) or not isinstance(zero_gaps, int) or zero_gaps < 2:
        raise ValueError("zero_gaps must be an integer at least 2")
    if (
        isinstance(points_per_gap, bool)
        or not isinstance(points_per_gap, int)
        or points_per_gap < 2
    ):
        raise ValueError("points_per_gap must be an integer at least 2")
    intervals = zero_gaps * points_per_gap
    if isinstance(blocks, bool) or not isinstance(blocks, int) or blocks < 2:
        raise ValueError("blocks must be an integer at least 2")
    if intervals % blocks:
        raise ValueError("zero_gaps * points_per_gap must be divisible by blocks")

    rows = []
    elapsed = 0.0
    for height in heights:
        mean_zero_gap = 2 * math.pi / math.log(height / (2 * math.pi))
        spacing = mean_zero_gap / points_per_gap
        window_length = mean_zero_gap * zero_gaps
        block_rows, peaks, sample_count, run_elapsed = block_peak_sweep(
            height,
            window_length,
            spacing,
            blocks=blocks,
        )
        elapsed += run_elapsed
        diagnostics = {item.k: item for item in block_diagnostics(block_rows)}
        by_peak = {
            (item.k, round(item.interval_fraction, 12)): item for item in peaks
        }
        for k in (1, 2, 3, 4):
            rows.append(
                HeightReplicationRow(
                    height=height,
                    mean_zero_gap=mean_zero_gap,
                    window_length=window_length,
                    spacing=spacing,
                    sample_count=sample_count,
                    k=k,
                    aggregate_ratio=diagnostics[k].aggregate_ratio,
                    block_ratio_coefficient_of_variation=(
                        diagnostics[k].block_ratio_coefficient_of_variation
                    ),
                    top_tenth_percent_contribution=(
                        by_peak[k, 0.001].contribution_fraction
                    ),
                    top_one_percent_contribution=(
                        by_peak[k, 0.01].contribution_fraction
                    ),
                )
            )
    return tuple(rows), elapsed


def offset_attack_verdict(
    diagnostics: tuple[OffsetDiagnostic, ...],
    anchor_heights: tuple[float, ...],
) -> OffsetAttackVerdict:
    """Apply the fixed multi-offset gates to a complete diagnostic matrix."""

    by_cell = {(row.anchor_height, row.k): row for row in diagnostics}
    expected = {(height, k) for height in anchor_heights for k in (1, 2, 3, 4)}
    if set(by_cell) != expected:
        raise ValueError("offset verdict requires every moment at every anchor height")
    theorem_controls_passed = all(
        abs(by_cell[height, k].pooled_ratio - 1) <= OFFSET_THEOREM_TOLERANCE
        for height in anchor_heights
        for k in (1, 2)
    )
    conjectural_ratios_passed = all(
        abs(by_cell[height, k].pooled_ratio - 1) <= OFFSET_CONJECTURAL_TOLERANCE
        for height in anchor_heights
        for k in (3, 4)
    )
    concentration_trend_passed = all(
        all(
            left < right
            for left, right in pairwise(
                [
                    by_cell[height, k].median_top_one_percent_contribution
                    for height in anchor_heights
                ]
            )
        )
        for k in (3, 4)
    )
    failures = []
    if not theorem_controls_passed:
        failures.append("theorem controls exceeded 5% pooled-ratio tolerance")
    if not conjectural_ratios_passed:
        failures.append("conjectural rows exceeded 15% pooled-ratio tolerance")
    if not concentration_trend_passed:
        failures.append("median high-moment concentration did not rise with height")
    return OffsetAttackVerdict(
        passed=not failures,
        theorem_controls_passed=theorem_controls_passed,
        conjectural_ratios_passed=conjectural_ratios_passed,
        concentration_trend_passed=concentration_trend_passed,
        failures=tuple(failures),
    )


def multi_offset_attack(
    anchor_heights: tuple[float, ...] = (1e4, 1e5, 1e6),
    *,
    windows_per_height: int = 4,
    zero_gaps: int = 6_000,
    points_per_gap: int = 128,
    blocks: int = 8,
) -> tuple[
    tuple[OffsetReplicationRow, ...],
    tuple[OffsetDiagnostic, ...],
    OffsetAttackVerdict,
    float,
]:
    """Run the pre-registered disjoint-window attack on the candidate pattern.

    Gates fixed in module constants before the first run:

    * pooled theorem-control ratios (2nd/4th) stay within 5% of one;
    * pooled conjectural ratios (6th/8th) stay within 15% of one;
    * median top-one-percent concentration for both 6th and 8th moments rises
      strictly from one anchor height to the next.

    Windows are consecutive and disjoint within each height band.  The verdict
    is a deterministic protocol result, not a p-value, proof, or certificate.
    """

    if (
        not anchor_heights
        or any(not math.isfinite(height) or height < 50 for height in anchor_heights)
        or tuple(sorted(set(anchor_heights))) != anchor_heights
    ):
        raise ValueError(
            "anchor_heights must be unique increasing finite values at least 50"
        )
    if (
        isinstance(windows_per_height, bool)
        or not isinstance(windows_per_height, int)
        or windows_per_height < 2
    ):
        raise ValueError("windows_per_height must be an integer at least 2")
    if isinstance(zero_gaps, bool) or not isinstance(zero_gaps, int) or zero_gaps < 2:
        raise ValueError("zero_gaps must be an integer at least 2")
    if (
        isinstance(points_per_gap, bool)
        or not isinstance(points_per_gap, int)
        or points_per_gap < 2
    ):
        raise ValueError("points_per_gap must be an integer at least 2")
    intervals = zero_gaps * points_per_gap
    if isinstance(blocks, bool) or not isinstance(blocks, int) or blocks < 2:
        raise ValueError("blocks must be an integer at least 2")
    if intervals % blocks:
        raise ValueError("zero_gaps * points_per_gap must be divisible by blocks")

    rows = []
    elapsed = 0.0
    for anchor_height in anchor_heights:
        window_start = anchor_height
        for window_index in range(windows_per_height):
            mean_zero_gap = 2 * math.pi / math.log(window_start / (2 * math.pi))
            spacing = mean_zero_gap / points_per_gap
            window_length = mean_zero_gap * zero_gaps
            block_rows, peaks, _, run_elapsed = block_peak_sweep(
                window_start,
                window_length,
                spacing,
                blocks=blocks,
            )
            elapsed += run_elapsed
            diagnostics = {item.k: item for item in block_diagnostics(block_rows)}
            top_one = {
                item.k: item.contribution_fraction
                for item in peaks
                if math.isclose(item.interval_fraction, 0.01)
            }
            window_end = window_start + window_length
            for k in (1, 2, 3, 4):
                k_rows = tuple(row for row in block_rows if row.k == k)
                measured_integral = sum(row.integral for row in k_rows)
                predicted_integral = sum(
                    row.polynomial_mean * (row.interval_end - row.interval_start)
                    for row in k_rows
                )
                rows.append(
                    OffsetReplicationRow(
                        anchor_height=anchor_height,
                        window_index=window_index,
                        interval_start=window_start,
                        interval_end=window_end,
                        k=k,
                        measured_integral=measured_integral,
                        predicted_integral=predicted_integral,
                        ratio=measured_integral / predicted_integral,
                        block_ratio_coefficient_of_variation=(
                            diagnostics[k].block_ratio_coefficient_of_variation
                        ),
                        top_one_percent_contribution=top_one[k],
                    )
                )
            window_start = window_end

    diagnostics = []
    for anchor_height in anchor_heights:
        for k in (1, 2, 3, 4):
            selected = tuple(
                row
                for row in rows
                if row.anchor_height == anchor_height and row.k == k
            )
            ratios = np.array([row.ratio for row in selected])
            diagnostics.append(
                OffsetDiagnostic(
                    anchor_height=anchor_height,
                    k=k,
                    pooled_ratio=(
                        sum(row.measured_integral for row in selected)
                        / sum(row.predicted_integral for row in selected)
                    ),
                    median_ratio=float(np.median(ratios)),
                    minimum_ratio=float(np.min(ratios)),
                    maximum_ratio=float(np.max(ratios)),
                    ratio_coefficient_of_variation=(
                        float(np.std(ratios, ddof=1)) / abs(float(np.mean(ratios)))
                    ),
                    median_top_one_percent_contribution=float(
                        np.median(
                            [row.top_one_percent_contribution for row in selected]
                        )
                    ),
                )
            )

    verdict = offset_attack_verdict(tuple(diagnostics), anchor_heights)
    return tuple(rows), tuple(diagnostics), verdict, elapsed


def accuracy_probe(start: float, length: float, samples: int = 12) -> float:
    """Largest observed ``|Z_fast - mpmath.siegelz|`` over a spread of the window."""

    worst = 0.0
    with mp.workdps(30):
        for i in range(samples):
            t = start + length * (i + 0.5) / samples
            fast = float(riemann_siegel_z(np.array([t]))[0])
            worst = max(worst, abs(fast - float(mp.siegelz(t))))
    return worst


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--start", type=float, default=1e6, help="window start t")
    parser.add_argument("--length", type=float, default=2e5, help="window width")
    parser.add_argument("--spacing", type=float, default=5e-3, help="sample spacing")
    parser.add_argument(
        "--convergence",
        action="store_true",
        help="compare 3 nested windows and 3 nested spacings in one fine-grid sweep",
    )
    parser.add_argument(
        "--blocks",
        type=int,
        default=0,
        help="run disjoint-block and peak-concentration study with this many blocks",
    )
    parser.add_argument(
        "--replicate",
        action="store_true",
        help="run the fixed 10^4/10^5/10^6 height-normalized replication matrix",
    )
    parser.add_argument(
        "--attack",
        action="store_true",
        help="run four disjoint whole-window attacks in each height band",
    )
    parser.add_argument("--emit", type=Path, default=None, help="write sample rows")
    parser.add_argument(
        "--emit-length",
        type=float,
        default=0.0,
        help="width of the sub-window to emit (required with --emit)",
    )
    parser.add_argument(
        "--emit-error-estimate",
        type=float,
        default=None,
        help="caller-stated absolute value-error estimate (required with --emit)",
    )
    args = parser.parse_args()

    if not (math.isfinite(args.start) and args.start >= 50):
        parser.error("--start must be finite and at least 50")
    if not (math.isfinite(args.length) and args.length > 0):
        parser.error("--length must be finite and positive")
    if not (math.isfinite(args.spacing) and args.spacing > 0):
        parser.error("--spacing must be finite and positive")
    intervals = int(round(args.length / args.spacing))
    if not math.isclose(
        intervals * args.spacing, args.length, rel_tol=1e-12, abs_tol=1e-12
    ):
        parser.error("--length must be an integer multiple of --spacing")
    if args.emit is not None and args.emit_length <= 0:
        parser.error("--emit requires --emit-length so the file size is stated")
    if args.emit is not None and args.emit_error_estimate is None:
        parser.error("--emit requires --emit-error-estimate; no error is invented")
    if args.emit is not None and args.emit_length > args.length:
        parser.error("--emit-length must not exceed --length")
    if args.emit is not None and args.convergence:
        parser.error("--convergence and --emit are separate acquisition modes")
    if args.emit is not None and args.blocks:
        parser.error("--blocks and --emit are separate acquisition modes")
    if args.convergence and args.blocks:
        parser.error("--convergence and --blocks are separate study modes")
    if args.replicate and (
        args.emit is not None or args.convergence or args.blocks or args.attack
    ):
        parser.error("--replicate is a separate study mode")
    if args.attack and (args.emit is not None or args.convergence or args.blocks):
        parser.error("--attack is a separate study mode")
    if args.blocks < 0 or args.blocks == 1:
        parser.error("--blocks must be 0 (disabled) or an integer at least 2")
    if args.convergence and (intervals < 16 or intervals % 4):
        parser.error(
            "--convergence requires at least 16 intervals and a count divisible by 4"
        )

    if args.replicate:
        rows, elapsed = multi_height_study()
        heights = sorted({row.height for row in rows})
        by_cell = {(row.height, row.k): row for row in rows}
        print("Height-normalized moment replication")
        print("=" * 78)
        print("each window: 6,000 local mean zero gaps; 128 points/gap; 8 blocks")
        print()
        print(
            f"  {'height':>10}  {'window':>10}  {'spacing':>10}  {'samples':>10}"
        )
        for height in heights:
            row = by_cell[height, 1]
            print(
                f"  {height:>10.0e}  {row.window_length:>10.2f}  "
                f"{row.spacing:>10.6f}  {row.sample_count:>10,}"
            )

        def print_matrix(title: str, field: str, *, percent: bool = False) -> None:
            print()
            print(title)
            print("-" * 78)
            print(f"  {'height':>10}  {'2nd':>12}  {'4th':>12}  {'6th':>12}  {'8th':>12}")
            for height in heights:
                values = [getattr(by_cell[height, k], field) for k in (1, 2, 3, 4)]
                rendered = (
                    "".join(f"  {value:>11.2%}" for value in values)
                    if percent
                    else "".join(f"  {value:>12.4f}" for value in values)
                )
                print(f"  {height:>10.0e}{rendered}")

        print_matrix("Measured / full-polynomial prediction", "aggregate_ratio")
        print_matrix(
            "Observed coefficient of variation across disjoint block ratios",
            "block_ratio_coefficient_of_variation",
            percent=True,
        )
        print_matrix(
            "Integral share from largest 0.1% of grid intervals",
            "top_tenth_percent_contribution",
            percent=True,
        )
        print_matrix(
            "Integral share from largest 1% of grid intervals",
            "top_one_percent_contribution",
            percent=True,
        )
        print()
        print(f"finest-grid evaluation time: {elapsed:.1f}s")
        print("Deterministic windows only: replication is not a confidence interval,")
        print("a proof of CFKRS, or evidence for RH.")
        return 0

    if args.attack:
        rows, diagnostics, verdict, elapsed = multi_offset_attack()
        del rows
        print("Pre-registered multi-offset attack")
        print("=" * 88)
        print("4 consecutive disjoint windows per height; each has 6,000 nominal gaps,")
        print("128 points/gap and 8 internal blocks.")
        print("Gates fixed before run:")
        print("  theorem controls: pooled 2nd/4th ratios within 5% of one")
        print("  conjectural rows: pooled 6th/8th ratios within 15% of one")
        print("  concentration: median top-1% share rises with height for 6th and 8th")
        print()
        print(
            f"  {'height':>8}  {'2k':>3}  {'pooled':>8}  {'median':>8}  "
            f"{'min':>8}  {'max':>8}  {'window CV':>10}  {'median top 1%':>13}"
        )
        for item in diagnostics:
            print(
                f"  {item.anchor_height:>8.0e}  {2 * item.k:>3}  "
                f"{item.pooled_ratio:>8.4f}  {item.median_ratio:>8.4f}  "
                f"{item.minimum_ratio:>8.4f}  {item.maximum_ratio:>8.4f}  "
                f"{item.ratio_coefficient_of_variation:>9.2%}  "
                f"{item.median_top_one_percent_contribution:>12.2%}"
            )
        print()
        print(f"theorem-control gate:     {'PASS' if verdict.theorem_controls_passed else 'FAIL'}")
        conjectural_status = "PASS" if verdict.conjectural_ratios_passed else "FAIL"
        concentration_status = "PASS" if verdict.concentration_trend_passed else "FAIL"
        print(f"conjectural-ratio gate:   {conjectural_status}")
        print(f"concentration-trend gate: {concentration_status}")
        print(f"VERDICT: {'SURVIVED' if verdict.passed else 'REJECTED'}")
        for failure in verdict.failures:
            print(f"  failure: {failure}")
        print(f"finest-grid evaluation time: {elapsed:.1f}s")
        print("This deterministic attack is not a confidence interval, proof of CFKRS,")
        print("or evidence for RH.")
        return 0

    start, length, spacing = args.start, args.length, args.spacing
    stop = start + length

    print("Critical-line moments from locally computed values")
    print("=" * 70)
    print(f"window      t in [{start:.6g}, {stop:.6g}]   width {length:.6g}")
    print(f"spacing     {spacing:g}")

    gap = 2 * math.pi / math.log(start / (2 * math.pi))
    print(f"mean zero gap at this height ~ {gap:.4f} ({gap / spacing:.0f} pts/gap)")

    worst = accuracy_probe(start, length)
    print(f"accuracy    max |fast - mpmath.siegelz| over 12 probes: {worst:.2e}")
    print()

    convergence_rows: tuple[ConvergenceRow, ...] | None = None
    block_rows: tuple[BlockMomentRow, ...] | None = None
    peak_concentrations: tuple[PeakConcentration, ...] | None = None
    if args.convergence:
        try:
            convergence_rows, count, elapsed = convergence_sweep(
                start, length, spacing
            )
        except ValueError as exc:
            parser.error(str(exc))
        largest_window = max(row.window_length for row in convergence_rows)
        finest_spacing = min(row.spacing for row in convergence_rows)
        totals = {
            row.k: row.integral
            for row in convergence_rows
            if row.window_length == largest_window and row.spacing == finest_spacing
        }
    elif args.blocks:
        try:
            block_rows, peak_concentrations, count, elapsed = block_peak_sweep(
                start, length, spacing, blocks=args.blocks
            )
        except ValueError as exc:
            parser.error(str(exc))
        totals = {
            k: sum(row.integral for row in block_rows if row.k == k)
            for k in (1, 2, 3, 4)
        }
    else:
        totals, count, elapsed = sweep(
            start,
            length,
            spacing,
            emit=args.emit,
            emit_length=args.emit_length,
            emit_error_estimate=args.emit_error_estimate,
        )
    print(f"swept {count:,} samples in {elapsed:.0f}s ({count / elapsed:,.0f} pts/s)")
    if args.emit is not None:
        print(f"emitted sample rows to {args.emit}")
    print()

    print("Calibration -- against Ingham's proved global 2nd-moment main term")
    print("-" * 70)
    predicted = float(second_moment_main_term(stop) - second_moment_main_term(start))
    measured = totals[1]
    print(f"  measured   integral |zeta|^2 = {measured:,.4f}")
    print(f"  main term  T log(T/2pi)+(2g-1)T = {predicted:,.4f}")
    print(f"  ratio      {measured / predicted:.6f}")
    print(
        f"  residual   {(measured - predicted) / predicted:+.4%}  "
        "(E(B)-E(A), plus numerical error)"
    )
    print()

    polynomials = {k: moment_polynomial(k) for k in (1, 2, 3, 4)}
    coefficients = {k: leading_coefficient(k) for k in (1, 2, 3, 4, 6, 8)}

    print("Moments against FULL-POLYNOMIAL global extrapolations (not a test)")
    print("-" * 70)
    print(f"  {'2k':>3}  {'status':>10}  {'measured mean':>16}  {'P_k mean':>16}  {'ratio':>9}")
    for k in (1, 2, 3, 4):
        mean = totals[k] / length
        prediction = float(
            moment_polynomial_mean(polynomials[k], str(start), str(stop))
        )
        status = polynomials[k].literature_status
        print(
            f"  {2 * k:>3}  {status:>10}  {mean:>16,.4f}  "
            f"{prediction:>16,.4f}  {mean / prediction:>9,.3f}"
        )
    print()

    if convergence_rows is not None:
        diagnostics = convergence_diagnostics(convergence_rows)
        windows = sorted({row.window_length for row in convergence_rows})
        spacings = sorted({row.spacing for row in convergence_rows})
        by_cell = {
            (row.k, row.window_length, row.spacing): row
            for row in convergence_rows
        }
        print("Nested convergence: measured / full-polynomial prediction")
        print("-" * 70)
        print(
            f"  {'2k':>3}  {'window':>10}  "
            f"{'h ratio':>10}  {'2h ratio':>10}  {'4h ratio':>10}"
        )
        for window_length in windows:
            for k in (1, 2, 3, 4):
                ratios = [by_cell[k, window_length, grid].ratio for grid in spacings]
                print(
                    f"  {2 * k:>3}  {window_length:>10,.0f}  "
                    f"{ratios[0]:>10.4f}  {ratios[1]:>10.4f}  {ratios[2]:>10.4f}"
                )
        print()
        print(
            f"  {'2k':>3}  {'max relative grid drift':>23}  "
            f"{'max window-ratio drift':>23}"
        )
        for diagnostic in diagnostics:
            print(
                f"  {2 * diagnostic.k:>3}  "
                f"{diagnostic.max_spacing_relative_drift:>23.3e}  "
                f"{diagnostic.max_window_ratio_relative_drift:>22.3%}"
            )
        print("  Observed changes only: neither column is an error bound or certificate.")
        print()

    if block_rows is not None and peak_concentrations is not None:
        diagnostics = block_diagnostics(block_rows)
        block_indices = sorted({row.block_index for row in block_rows})
        by_block = {(row.block_index, row.k): row for row in block_rows}
        print("Disjoint blocks: measured / full-polynomial prediction")
        print("-" * 70)
        print(
            f"  {'block':>5}  {'window':>19}  {'2nd':>8}  {'4th':>8}  "
            f"{'6th':>8}  {'8th':>8}"
        )
        for block_index in block_indices:
            first = by_block[block_index, 1]
            ratios = [by_block[block_index, k].ratio for k in (1, 2, 3, 4)]
            print(
                f"  {block_index + 1:>5}  "
                f"[{first.interval_start:>8.0f},{first.interval_end:>8.0f}]  "
                f"{ratios[0]:>8.3f}  {ratios[1]:>8.3f}  "
                f"{ratios[2]:>8.3f}  {ratios[3]:>8.3f}"
            )
        print()
        print(
            f"  {'2k':>3}  {'aggregate':>10}  {'block CV':>10}  "
            f"{'block min':>10}  {'block max':>10}"
        )
        for diagnostic in diagnostics:
            print(
                f"  {2 * diagnostic.k:>3}  {diagnostic.aggregate_ratio:>10.4f}  "
                f"{diagnostic.block_ratio_coefficient_of_variation:>9.2%}  "
                f"{diagnostic.minimum_block_ratio:>10.4f}  "
                f"{diagnostic.maximum_block_ratio:>10.4f}"
            )
        print()
        fractions = sorted(
            {item.interval_fraction for item in peak_concentrations}
        )
        by_peak = {
            (item.k, item.interval_fraction): item for item in peak_concentrations
        }
        print("Moment integral carried by the largest grid-interval contributions")
        print("-" * 70)
        header = "  2k" + "".join(
            f"  top {fraction:>7.3%}" for fraction in fractions
        )
        print(header)
        for k in (1, 2, 3, 4):
            shares = "".join(
                f"  {by_peak[k, fraction].contribution_fraction:>11.2%}"
                for fraction in fractions
            )
            print(f"  {2 * k:>2}{shares}")
        print("  Deterministic disjoint blocks: dispersion is not a confidence interval;")
        print("  peak shares are not error bounds.")
        print()

    print("Pairwise consistency thresholds for leading-order forms")
    print("-" * 70)
    print(f"  {'pair':>13}  {'threshold t':>14}  {'this window is below by':>24}")
    for k in (2, 3, 4):
        threshold = pairwise_consistency_threshold(k, coefficients)
        ratio = float(threshold) / start
        pair = f"{2 * k}th/{4 * k}th"
        print(f"  {pair:>13}  {float(threshold):>14.2e}  {ratio:>24.1e}x")
    print()
    print("  Each threshold is a necessary condition on the named pair only.")
    print("  It is not an onset estimate for either member and not a reachability")
    print("  bound.  These thresholds diagnose the separate leading-only forms;")
    print("  the full CFKRS polynomial is the comparison used in the table above.")
    print()
    print("Nothing above settles, supports or weakens RH.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
