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
    euler_field_variance,
    euler_intensity_moment,
    exact_intensity_moment,
    field_variance,
    interval_statistics,
    primes_up_to,
    sample_cue_log_field,
    sample_euler_intensity,
    sample_euler_log_field,
    sample_field,
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

        null_ts = np.arange(len(ts)) * spacing

        started = time.time()
        first_stats = {
            item.k: item
            for item in interval_statistics(
                sample_intensity(null_ts, primes, seed=SEED),
                spacing,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            )
        }
        first_seconds = time.time() - started

        started = time.time()
        euler_stats = {
            item.k: item
            for item in interval_statistics(
                sample_euler_intensity(null_ts, primes, seed=SEED),
                spacing,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            )
        }
        euler_seconds = time.time() - started

        print(
            f"t = {height:g}   spacing {spacing:.6f}   primes {len(primes)}   "
            f"sigma^2 first-order {sigma_squared:.4f} / Euler "
            f"{euler_field_variance(primes):.4f}   "
            f"(zeta {zeta_seconds:.1f}s, first {first_seconds:.1f}s, "
            f"euler {euler_seconds:.1f}s)"
        )
        print(
            f"  {'moment':>6}  {'zeta top1%':>10}  {'1st top1%':>10}"
            f"  {'eul top1%':>10}  {'zeta blkCV':>10}  {'eul blkCV':>10}"
            f"  {'1st ratio':>10}  {'eul ratio':>10}"
        )
        span = spacing * (len(ts) - 1)
        for k in (1, 2, 3, 4):
            first_ratio = first_stats[k].integral / span / exact_intensity_moment(
                k, primes
            )
            euler_ratio = euler_stats[k].integral / span / euler_intensity_moment(
                k, primes
            )
            print(
                f"  {2 * k:>6}"
                f"  {zeta_stats[k].top_contribution:>9.2%}"
                f"  {first_stats[k].top_contribution:>9.2%}"
                f"  {euler_stats[k].top_contribution:>9.2%}"
                f"  {zeta_stats[k].block_dispersion:>9.2%}"
                f"  {euler_stats[k].block_dispersion:>9.2%}"
                f"  {first_ratio:>10.5f}"
                f"  {euler_ratio:>10.5f}"
            )
        print()

    print(
        "Read the last column as the null's own analogue of a moment ratio: the\n"
        "measured window mean of exp(2kX) divided by its exact expectation\n"
        "prod_p I_0(2k p^-1/2).  It is exact for the surrogate, so departures\n"
        "from one measure finite-window luck alone, with no conjecture involved."
    )


def tail_profile(height: float, *, seed: int = SEED) -> dict[str, dict[str, float]]:
    """Variance, median and upper quantiles of ``log|f|`` for zeta and both nulls.

    High moments are governed by the upper tail alone, so comparing variances is
    misleading for a function with zeros: ``log|zeta|`` diverges to minus
    infinity at every zero, which inflates the variance from the left while
    saying nothing about the peaks.  Both surrogates are zero-free by
    construction and cannot reproduce that left tail at all.  This profile
    separates the two sides so the comparison is made where it matters.
    """

    ts, spacing = grid_for(height)
    primes = primes_up_to(int(height))
    null_ts = np.arange(len(ts)) * spacing

    zeta_log = np.log(np.abs(riemann_siegel_z(ts)))
    fields = {
        "zeta": zeta_log[np.isfinite(zeta_log)],
        "first-order": sample_field(null_ts, primes, seed=seed),
        "euler": sample_euler_log_field(null_ts, primes, seed=seed),
    }
    profile = {}
    for name, values in fields.items():
        median, p99, p999 = np.percentile(values, [50, 99, 99.9])
        profile[name] = {
            "variance": float(np.var(values)),
            "median": float(median),
            "p99": float(p99),
            "p999": float(p999),
            "max": float(np.max(values)),
        }
    return profile


def run_tails() -> None:
    """Print the tail profile at each height beside the Selberg variance."""

    for height in HEIGHTS:
        selberg = 0.5 * math.log(math.log(height))
        print(f"t = {height:g}   Selberg (1/2) log log T = {selberg:.4f}")
        print(
            f"  {'field':>12}  {'variance':>9}  {'median':>8}"
            f"  {'p99':>8}  {'p99.9':>8}  {'max':>8}"
        )
        for name, row in tail_profile(height).items():
            print(
                f"  {name:>12}  {row['variance']:>9.4f}  {row['median']:>8.4f}"
                f"  {row['p99']:>8.4f}  {row['p999']:>8.4f}  {row['max']:>8.4f}"
            )
        print()
    print(
        "A larger variance for zeta alongside a smaller upper tail is the\n"
        "signature of the zeros: they pull the left tail down without adding\n"
        "peaks.  Calibrating a zero-free surrogate to match zeta's variance\n"
        "would therefore widen its upper tail and worsen the comparison."
    )


def run_cue() -> None:
    """Compare zeta against the CUE control, the only surrogate with zeros.

    The matrix dimension is ``N = round(log(T / 2 pi))``, the standard
    identification that matches the CUE mean eigenvalue spacing to the mean
    zero spacing at height ``T``.  Enough independent matrices are concatenated
    to cover the same nominal gap count as the zeta window.
    """

    for height in HEIGHTS:
        dimension = int(round(math.log(height / (2.0 * math.pi))))
        matrices = math.ceil(GAPS / dimension)
        ts, spacing = grid_for(height)
        zeta_stats = {
            item.k: item
            for item in interval_statistics(
                riemann_siegel_z(ts) ** 2,
                spacing,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            )
        }

        field = sample_cue_log_field(
            dimension, matrices, POINTS_PER_GAP, seed=SEED
        )
        values = np.exp(2.0 * field)
        # The concatenated grid carries its own spacing in eigenangle units;
        # every statistic below is scale free, so the unit does not matter.
        cue_spacing = 2.0 * math.pi / (dimension * POINTS_PER_GAP)
        usable = len(values) - (len(values) - 1) % BLOCKS
        cue_stats = {
            item.k: item
            for item in interval_statistics(
                values[:usable],
                cue_spacing,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            )
        }

        finite = field[np.isfinite(field)]
        zeta_log = np.log(np.abs(riemann_siegel_z(ts)))
        zeta_log = zeta_log[np.isfinite(zeta_log)]
        print(
            f"t = {height:g}   N = {dimension}   matrices {matrices}   "
            f"{dimension * matrices} nominal gaps"
        )
        print(
            f"  log|f| variance: zeta {np.var(zeta_log):.4f}   "
            f"cue {np.var(finite):.4f}   |   p99.9: zeta "
            f"{np.percentile(zeta_log, 99.9):.4f}   "
            f"cue {np.percentile(finite, 99.9):.4f}"
        )
        print(
            f"  {'moment':>6}  {'zeta top1%':>10}  {'cue top1%':>10}"
            f"  {'zeta blkCV':>10}  {'cue blkCV':>10}"
        )
        for k in (1, 2, 3, 4):
            print(
                f"  {2 * k:>6}"
                f"  {zeta_stats[k].top_contribution:>9.2%}"
                f"  {cue_stats[k].top_contribution:>9.2%}"
                f"  {zeta_stats[k].block_dispersion:>9.2%}"
                f"  {cue_stats[k].block_dispersion:>9.2%}"
            )
        print()
    print(
        "The CUE field has zeros on its own contour, so unlike either Euler\n"
        "surrogate it can reproduce the left tail of log|zeta|.  Concatenated\n"
        "matrices carry no correlation beyond one matrix, so read block\n"
        "dispersion with that limit in mind."
    )


APPROACH_HEIGHTS = (1e3, 1e4, 1e5, 1e6, 1e7, 1e8)
APPROACH_SEEDS = 200


def run_approach(seeds: int = APPROACH_SEEDS) -> None:
    """Test whether zeta's concentration enters the CUE distribution with height.

    The CUE control has no free parameter once the height fixes ``N``, so
    repeating it over many seeds gives an empirical distribution rather than a
    single number, and the comparison band is read off that distribution
    instead of being chosen by hand.  The question is narrow and quantitative:
    at each height, does zeta's top-one-percent share fall inside the central
    ninety-five percent of the CUE shares?

    A band from simulation is not a confidence interval for zeta, and being
    inside it is not evidence for the Riemann Hypothesis or for anything else;
    it only says the control and the function are indistinguishable by this
    statistic at this exposure.
    """

    print(
        f"{GAPS} nominal gaps, {POINTS_PER_GAP} points/gap, "
        f"{seeds} CUE seeds per height, top {TOP_FRACTION:.0%} of intervals\n"
    )
    inside_by_k: dict[int, list[bool]] = {k: [] for k in (1, 2, 3, 4)}

    for height in APPROACH_HEIGHTS:
        ts, spacing = grid_for(height)
        zeta_stats = {
            item.k: item.top_contribution
            for item in interval_statistics(
                riemann_siegel_z(ts) ** 2,
                spacing,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            )
        }

        dimension = int(round(math.log(height / (2.0 * math.pi))))
        matrices = math.ceil(GAPS / dimension)
        cue_spacing = 2.0 * math.pi / (dimension * POINTS_PER_GAP)
        samples: dict[int, list[float]] = {k: [] for k in (1, 2, 3, 4)}
        for index in range(seeds):
            values = np.exp(
                2.0
                * sample_cue_log_field(
                    dimension, matrices, POINTS_PER_GAP, seed=SEED + index
                )
            )
            usable = len(values) - (len(values) - 1) % BLOCKS
            for item in interval_statistics(
                values[:usable],
                cue_spacing,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            ):
                samples[item.k].append(item.top_contribution)

        print(f"t = {height:g}   N = {dimension}   matrices {matrices}")
        print(
            f"  {'moment':>6}  {'zeta':>8}  {'CUE median':>11}"
            f"  {'CUE 2.5%':>9}  {'CUE 97.5%':>9}  {'inside':>7}  {'gap':>9}"
        )
        for k in (1, 2, 3, 4):
            low, median, high = np.percentile(samples[k], [2.5, 50, 97.5])
            inside = bool(low <= zeta_stats[k] <= high)
            inside_by_k[k].append(inside)
            print(
                f"  {2 * k:>6}  {zeta_stats[k]:>8.2%}  {median:>11.2%}"
                f"  {low:>9.2%}  {high:>9.2%}  {str(inside):>7}"
                f"  {zeta_stats[k] - median:>+9.2%}"
            )
        print()

    print("inside the central 95% of the CUE distribution, by height:")
    header = "  ".join(f"{h:>8.0e}" for h in APPROACH_HEIGHTS)
    print(f"  {'moment':>6}  {header}")
    for k in (1, 2, 3, 4):
        row = "  ".join(f"{str(v):>8}" for v in inside_by_k[k])
        print(f"  {2 * k:>6}  {row}")
    print(
        "\nA transition from outside to inside as height grows would say the\n"
        "finite-height gap closes; entries that never leave, or never enter,\n"
        "say the statistic does not discriminate at this exposure."
    )


DH_GAPS = 150
DH_HEIGHTS = (200.0, 2000.0)


def _dh_chunk(arguments: tuple[float, ...]) -> list[float]:
    """Evaluate ``Z_dh`` on a chunk of ordinates (module level so it pickles)."""

    from zeta.epstein import Z_dh

    return [float(Z_dh(float(t), dps=15)) for t in arguments]


def run_dh(workers: int = 8) -> None:
    """Run the concentration statistics on the Davenport-Heilbronn function.

    ``f`` satisfies a functional equation, has real Dirichlet coefficients and
    a real Hardy-style ``Z``, and violates the Riemann Hypothesis.  The
    repository's standing rule is that any structural property claimed to
    explain RH must be run through this counterexample: a property ``f`` also
    has distinguishes nothing.  Here the property under test is the rise of
    moment concentration with moment order.

    No CFKRS-style moment polynomial exists for ``f``, so only the shape
    statistics are computed; there is no ratio column and none is implied.
    """

    import concurrent.futures

    from zeta.epstein import _dh_mean_spacing

    for height in DH_HEIGHTS:
        spacing = float(_dh_mean_spacing(height)) / POINTS_PER_GAP
        count = DH_GAPS * POINTS_PER_GAP + 1
        ts = height + np.arange(count) * spacing

        started = time.time()
        chunks = np.array_split(ts, workers * 4)
        with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
            pieces = list(pool.map(_dh_chunk, [tuple(c) for c in chunks]))
        values = np.array([v for piece in pieces for v in piece]) ** 2
        elapsed = time.time() - started

        dh_stats = {
            item.k: item
            for item in interval_statistics(
                values, spacing, blocks=BLOCKS, top_fraction=TOP_FRACTION
            )
        }

        # Zeta on an identically sized grid, for reference only.
        zeta_ts = 1e6 + np.arange(count) * (mean_gap(1e6) / POINTS_PER_GAP)
        zeta_stats = {
            item.k: item
            for item in interval_statistics(
                riemann_siegel_z(zeta_ts) ** 2,
                mean_gap(1e6) / POINTS_PER_GAP,
                blocks=BLOCKS,
                top_fraction=TOP_FRACTION,
            )
        }

        print(
            f"Davenport-Heilbronn at t = {height:g}   spacing {spacing:.6f}   "
            f"{DH_GAPS} nominal gaps   ({elapsed:.0f}s)"
        )
        print(
            f"  {'moment':>6}  {'DH top1%':>10}  {'zeta top1%':>10}"
            f"  {'DH blkCV':>10}  {'zeta blkCV':>10}"
        )
        for k in (1, 2, 3, 4):
            print(
                f"  {2 * k:>6}"
                f"  {dh_stats[k].top_contribution:>9.2%}"
                f"  {zeta_stats[k].top_contribution:>9.2%}"
                f"  {dh_stats[k].block_dispersion:>9.2%}"
                f"  {zeta_stats[k].block_dispersion:>9.2%}"
            )
        print()
    print(
        "The zeta column is a same-sized grid at t=1e6, shown for scale only;\n"
        "the two functions are at different heights and are not calibrated to\n"
        "each other.  What matters is whether the rise with moment order is\n"
        "present for a function known to violate RH."
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verify",
        action="store_true",
        help="check the reusable statistic against the pinned zeta pipeline",
    )
    parser.add_argument(
        "--tails",
        action="store_true",
        help="compare variance and upper quantiles of log|f| instead of moments",
    )
    parser.add_argument(
        "--cue",
        action="store_true",
        help="compare against the CUE characteristic polynomial control",
    )
    parser.add_argument(
        "--dh",
        action="store_true",
        help="run the Davenport-Heilbronn counterexample control",
    )
    parser.add_argument(
        "--approach",
        action="store_true",
        help="test whether zeta enters the CUE distribution as height grows",
    )
    args = parser.parse_args()
    if args.verify:
        verify_adapter()
    elif args.tails:
        run_tails()
    elif args.cue:
        run_cue()
    elif args.dh:
        run_dh()
    elif args.approach:
        run_approach()
    else:
        run_comparison()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
