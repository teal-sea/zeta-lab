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

Nothing here settles, supports or weakens the Riemann Hypothesis, and finite
moment measurements could not do so in principle.

Usage
-----
    .venv/bin/python scripts/14_moment_experiment.py
    .venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 2e4
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
