"""Run the finite-height concentration statistics against a null model.

The zeta side of this comparison measures how much of the ``2k``-th moment
integral is carried by the largest one percent of grid intervals, and how much
the integral varies between disjoint blocks.  The null side measures exactly
the same two statistics on a randomised Euler product surrogate
(``zeta.surrogate``), which has the Selberg variance and log-decaying
correlation but no arithmetic structure and no functional equation.

The comparison is adversarial.  If the surrogate reproduces the zeta numbers,
the concentration pattern is a generic consequence of a log-correlated field
and carries no zeta-specific content.  A matching control kills a candidate
finding; it does not support one.  Nothing computed here settles, supports or
weakens the Riemann Hypothesis, and finite moment measurements could not do so
in principle.

Both sides run on grids with identical spacing, identical interval counts and
identical block counts, so the two columns differ only in the field being
sampled.  The surrogate is stationary while zeta is not; the surrogate's window
is therefore placed at the origin and only its shape statistics are compared,
never its absolute scale.

Usage::

    .venv/bin/python scripts/15_null_control.py --verify
    .venv/bin/python scripts/15_null_control.py
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from zeta.statistics import riemann_siegel_z  # noqa: E402
from zeta.surrogate import (  # noqa: E402
    exact_intensity_moment,
    field_variance,
    interval_statistics,
    primes_up_to,
    sample_intensity,
)

HEIGHTS = (1e4, 1e5, 1e6)
GAPS = 750
POINTS_PER_GAP = 64
BLOCKS = 8
TOP_FRACTION = 0.01
SEED = 20260804


def _load_script_14():
    """Import the moment experiment script (its name begins with a digit)."""

    path = ROOT / "scripts" / "14_moment_experiment.py"
    spec = importlib.util.spec_from_file_location("moment_experiment", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def mean_gap(height: float) -> float:
    """Nominal mean spacing between zeros near ``height``."""

    return 2.0 * math.pi / math.log(height / (2.0 * math.pi))


def grid_for(height: float) -> tuple[np.ndarray, float]:
    """Uniform grid of ``GAPS * POINTS_PER_GAP`` intervals anchored at ``height``."""

    spacing = mean_gap(height) / POINTS_PER_GAP
    count = GAPS * POINTS_PER_GAP + 1
    return height + np.arange(count) * spacing, spacing


def verify_adapter() -> None:
    """Check the reusable interval statistic against the pinned zeta pipeline.

    ``zeta.surrogate.interval_statistics`` re-expresses the interval algorithm
    of ``scripts/14_moment_experiment.py`` so it can accept an arbitrary value
    array.  The two must agree on real zeta data or the null comparison is
    meaningless, so this reproduces the pinned width-4000 configuration and
    compares the top-one-percent shares directly.
    """

    module = _load_script_14()
    start, length, spacing = 1e5, 4e3, 5e-3
    print(f"verifying adapter against block_peak_sweep at t={start:g} ...")
    started = time.time()
    _, concentrations, _, _ = module.block_peak_sweep(
        start, length, spacing, blocks=BLOCKS, peak_fractions=(0.01,)
    )
    reference = {item.k: item.contribution_fraction for item in concentrations}

    count = int(round(length / spacing)) + 1
    ts = start + np.arange(count) * spacing
    values = riemann_siegel_z(ts) ** 2
    mine = {
        item.k: item.top_contribution
        for item in interval_statistics(
            values, spacing, blocks=BLOCKS, top_fraction=0.01
        )
    }

    print(f"  {'k':>2}  {'pipeline':>10}  {'adapter':>10}  {'rel diff':>10}")
    worst = 0.0
    for k in (1, 2, 3, 4):
        diff = abs(mine[k] - reference[k]) / reference[k]
        worst = max(worst, diff)
        print(f"  {k:>2}  {reference[k]:>10.6f}  {mine[k]:>10.6f}  {diff:>10.2e}")
    print(f"  worst relative difference {worst:.2e}  ({time.time() - started:.1f}s)")
    if worst > 1e-9:
        raise SystemExit("adapter does not reproduce the pipeline statistic")


def run_comparison() -> None:
    """Print zeta and surrogate shape statistics side by side at each height."""

    print(
        f"grid: {GAPS} nominal zero gaps, {POINTS_PER_GAP} points/gap, "
        f"{GAPS * POINTS_PER_GAP} intervals, {BLOCKS} blocks, "
        f"top {TOP_FRACTION:.0%} of intervals, seed {SEED}"
    )
    print(
        "surrogate primes are taken up to the height, so its variance is "
        "(1/2) sum_{p<=T} 1/p\n"
    )

    for height in HEIGHTS:
        ts, spacing = grid_for(height)
        primes = primes_up_to(int(height))
        sigma_squared = field_variance(primes)

        started = time.time()
        zeta_values = riemann_siegel_z(ts) ** 2
        zeta_stats = {
            item.k: item
            for item in interval_statistics(
                zeta_values, spacing, blocks=BLOCKS, top_fraction=TOP_FRACTION
            )
        }
        zeta_seconds = time.time() - started

        started = time.time()
        null_ts = np.arange(len(ts)) * spacing
        null_values = sample_intensity(null_ts, primes, seed=SEED)
        null_stats = {
            item.k: item
            for item in interval_statistics(
                null_values, spacing, blocks=BLOCKS, top_fraction=TOP_FRACTION
            )
        }
        null_seconds = time.time() - started

        print(
            f"t = {height:g}   spacing {spacing:.6f}   "
            f"primes {len(primes)}   sigma^2 {sigma_squared:.4f}   "
            f"(zeta {zeta_seconds:.1f}s, null {null_seconds:.1f}s)"
        )
        print(
            f"  {'moment':>6}  {'zeta top1%':>11}  {'null top1%':>11}"
            f"  {'zeta blkCV':>11}  {'null blkCV':>11}  {'null ratio':>11}"
        )
        for k in (1, 2, 3, 4):
            exact = exact_intensity_moment(k, primes)
            measured_mean = null_stats[k].integral / (spacing * (len(ts) - 1))
            print(
                f"  {2 * k:>6}"
                f"  {zeta_stats[k].top_contribution:>10.2%}"
                f"  {null_stats[k].top_contribution:>10.2%}"
                f"  {zeta_stats[k].block_dispersion:>10.2%}"
                f"  {null_stats[k].block_dispersion:>10.2%}"
                f"  {measured_mean / exact:>11.4f}"
            )
        print()

    print(
        "Read the last column as the null's own analogue of a moment ratio: the\n"
        "measured window mean of exp(2kX) divided by its exact expectation\n"
        "prod_p I_0(2k p^-1/2).  It is exact for the surrogate, so departures\n"
        "from one measure finite-window luck alone, with no conjecture involved."
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verify",
        action="store_true",
        help="check the reusable statistic against the pinned zeta pipeline",
    )
    args = parser.parse_args()
    if args.verify:
        verify_adapter()
    else:
        run_comparison()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
