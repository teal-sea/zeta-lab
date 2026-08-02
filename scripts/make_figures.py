#!/usr/bin/env python
"""Generate every figure of the zeta laboratory into ``figures/``.

Usage
-----
    .venv/bin/python scripts/make_figures.py --quick   # small/fast parameters
    .venv/bin/python scripts/make_figures.py --full    # publication parameters
    .venv/bin/python scripts/make_figures.py --quick --only spacing_histogram

``--quick`` (the default) uses reduced heights, grid sizes and zero counts so a
cold run finishes in a couple of minutes and a warm run (everything cached under
``data/``) in seconds.  ``--full`` uses the publication parameters; its heat-flow
sweep recomputes H_t trajectories at 13 flow times, which is the one genuinely
expensive step on a cold cache.

Each figure is one function of :mod:`zeta.plots`; this script only chooses
parameters, times the calls, and reports the files written.
"""

from __future__ import annotations

import argparse
import math
import os
import sys
import time

import matplotlib

matplotlib.use("Agg")  # headless, before pyplot

import matplotlib.pyplot as plt  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from zeta import plots  # noqa: E402

FIG_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "figures")


def _specs(mode: str) -> list[tuple[str, str, dict]]:
    """(file stem, plots-function name, kwargs) for every figure, per mode."""
    quick = mode == "quick"
    return [
        ("zeta_critical_line", "plot_zeta_critical_line",
         dict(t_max=50.0, n_points=1200) if quick else dict(t_max=100.0, n_points=3200)),
        ("hardy_Z", "plot_hardy_Z",
         dict(t_max=80.0) if quick else dict(t_max=150.0)),
        ("zeta_domain_coloring", "plot_zeta_domain_coloring",
         dict(nx=260, ny=400) if quick else dict(nx=480, ny=740)),
        ("theta_modularity", "plot_theta_modularity",
         dict(n_points=220, n_defect=60) if quick else dict(n_points=400, n_defect=120)),
        ("theta_heat_evolution", "plot_theta_heat_evolution",
         dict(n_points=321) if quick else dict(n_points=721)),
        ("explicit_formula", "plot_explicit_formula",
         dict(x_max=100.0, zero_counts=(0, 10, 100, 500), n_points=1800)
         if quick else
         dict(x_max=150.0, zero_counts=(0, 10, 100, 1000), n_points=4000)),
        ("prime_spectrum", "plot_prime_spectrum",
         dict(n_zeros=300, x_max=32.0, n_points=4000)
         if quick else
         dict(n_zeros=1000, x_max=50.0, n_points=8000)),
        ("spacing_histogram", "plot_spacing_histogram",
         dict(t_max=5000.0, bins=36) if quick else dict(t_max=10000.0, bins=44)),
        ("pair_correlation", "plot_pair_correlation",
         dict(t_max=5000.0, bins=50) if quick else dict(t_max=10000.0, bins=60)),
        ("zero_counting", "plot_zero_counting",
         dict(t_max=150.0) if quick else dict(t_max=300.0)),
        ("heatflow_trajectories", "plot_heatflow_trajectories",
         dict(t_values=(-0.4, -0.2, 0.0, 0.2, 0.4, 0.6))          # matches the cache
         if quick else
         dict(t_values=tuple(round(-0.6 + 0.1 * k, 1) for k in range(13)))),
        ("polynomial_root_repulsion", "plot_polynomial_root_repulsion",
         dict(n_t=121) if quick else dict(n_t=241)),
        ("weil_positivity", "plot_weil_positivity",
         dict(gaussian_points=7, fejer_points=5)
         if quick else
         dict(gaussian_points=11, fejer_points=8)),
        ("offline_zero", "plot_offline_zero",
         dict(nx=240, ny=340) if quick else dict(nx=420, ny=600)),
    ]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    grp = ap.add_mutually_exclusive_group()
    grp.add_argument("--quick", action="store_true", help="small/fast parameters (default)")
    grp.add_argument("--full", action="store_true", help="publication parameters")
    ap.add_argument("--only", metavar="STEM", default=None,
                    help="generate only the figure whose file stem contains STEM")
    ap.add_argument("--dpi", type=int, default=None,
                    help="override dpi (default 140 quick, 200 full)")
    args = ap.parse_args(argv)

    mode = "full" if args.full else "quick"
    dpi = args.dpi if args.dpi is not None else (140 if mode == "quick" else 200)
    os.makedirs(FIG_DIR, exist_ok=True)

    specs = _specs(mode)
    if args.only:
        specs = [s for s in specs if args.only in s[0]]
        if not specs:
            ap.error(f"no figure stem matches {args.only!r}")

    print(f"mode = {mode}, dpi = {dpi}, output -> {FIG_DIR}")
    written: list[tuple[str, float, int]] = []
    for stem, fn_name, kwargs in specs:
        path = os.path.join(FIG_DIR, f"{stem}.png")
        fn = getattr(plots, fn_name)
        t0 = time.perf_counter()
        fig = fn(save_path=path, dpi=dpi, **kwargs)
        plt.close(fig)
        dt = time.perf_counter() - t0
        size = os.path.getsize(path)
        written.append((path, dt, size))
        print(f"  [{dt:7.2f} s] {stem}.png  ({size / 1024:.0f} KiB)")

    total = sum(dt for _, dt, _ in written)
    print(f"done: {len(written)} figures in {total:.1f} s "
          f"({sum(sz for *_, sz in written) / 1024:.0f} KiB total)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
