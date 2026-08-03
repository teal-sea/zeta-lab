"""Tests for the phase-3 figures in :mod:`zeta.plots` and the scripts 09-12.

Figures are hard to assert about, so this module tests the two things that can
actually be wrong:

* **the plumbing** — every new ``plot_*`` function runs headless, returns a
  ``matplotlib.figure.Figure``, and writes a non-trivial PNG to ``save_path``;
  and every name it exports is really there.
* **the claims** — each figure's docstring makes numerical statements
  ("the bands are nested", "the imaginary parts are a hundred orders below the
  tolerance", "M(1)/√1 = 1 and M(5)/√5 = −0.894"), and the house rule is that a
  docstring claim which is not tested is a defect.  Those are re-derived here
  from the same public routines the figures use, so the assertions fail if
  either the claim or the underlying mathematics moves.

The demo scripts ``09``–``12`` are exercised as subprocesses with ``--help``
(they must document themselves and exit 0) and, for the two cheap ones, in
full.

Matplotlib is forced onto the Agg backend before ``pyplot`` is ever imported,
per the repo's headless rule.
"""

from __future__ import annotations

import os
import subprocess
import sys

import matplotlib

matplotlib.use("Agg")  # headless: must precede pyplot / zeta.plots

import matplotlib.pyplot as plt  # noqa: E402
import pytest  # noqa: E402
from matplotlib.figure import Figure  # noqa: E402

from zeta import plots  # noqa: E402

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(REPO_ROOT, "scripts")

#: The phase-3 additions, with parameters small enough for the fast tier.
NEW_FIGURES = [
    ("plot_certified_enclosures", dict(t_min=14.0, t_max=26.0, n_points=40,
                                       width_bits=(16, 32, 64))),
    ("plot_li_coefficients", dict(n_max=24)),
    ("plot_jensen_roots", dict(d_values=(2, 3, 4), n=1, n_compare=6)),
    ("plot_finite_field_rh", dict(primes=(13, 101))),
    ("plot_sato_tate", dict(p_values=(503,), n_bins=20)),
    ("plot_mertens", dict(limit=200_000)),
]


# ---------------------------------------------------------------------------
# plumbing
# ---------------------------------------------------------------------------


def test_new_figures_are_exported():
    for name, _ in NEW_FIGURES:
        assert name in plots.__all__, name
        assert callable(getattr(plots, name)), name


def test_every_exported_name_exists():
    for name in plots.__all__:
        assert hasattr(plots, name), name


@pytest.mark.parametrize("name,kwargs", NEW_FIGURES, ids=[n for n, _ in NEW_FIGURES])
def test_figure_runs_and_writes_a_png(name, kwargs, tmp_path):
    path = tmp_path / f"{name}.png"
    fig = getattr(plots, name)(save_path=str(path), dpi=70, **kwargs)
    try:
        assert isinstance(fig, Figure)
        assert path.exists()
        # a blank canvas would still be a few KiB; require an actually drawn plot
        assert path.stat().st_size > 15_000, path.stat().st_size
    finally:
        plt.close(fig)


def test_make_figures_lists_every_new_figure():
    """``scripts/make_figures.py`` must know about all six, in both modes."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "make_figures", os.path.join(SCRIPTS, "make_figures.py")
    )
    mf = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mf)
    for mode in ("quick", "full"):
        names = {fn for _, fn, _ in mf._specs(mode)}
        for name, _ in NEW_FIGURES:
            assert name in names, (mode, name)
        for _, fn, _ in mf._specs(mode):
            assert hasattr(plots, fn), fn


# ---------------------------------------------------------------------------
# the claims each figure makes
# ---------------------------------------------------------------------------


def test_certified_enclosure_bands_are_nested_and_shrink():
    """plot_certified_enclosures: higher precision ⊂ lower, width falls fast.

    Both are properties of ball arithmetic rather than of the drawing: every
    enclosure contains the true value, so two enclosures of the same point must
    overlap, and the tighter one must sit inside the looser one.
    """
    from zeta.rigor import enclose_Z

    widths = {}
    for t in (14.5, 20.0, 25.5):
        boxes = {bits: enclose_Z(t, bits) for bits in (12, 16, 20, 64)}
        for coarse, fine in ((12, 16), (16, 20), (20, 64)):
            lo_c, hi_c = boxes[coarse]
            lo_f, hi_f = boxes[fine]
            assert lo_c <= lo_f <= hi_f <= hi_c, (t, coarse, fine)
        for bits, (lo, hi) in boxes.items():
            widths.setdefault(bits, []).append(float(hi - lo))
    # geometric decay: each 4 extra bits buys at least a factor 8 in width
    for coarse, fine in ((12, 16), (16, 20)):
        assert max(widths[fine]) < max(widths[coarse]) / 8.0
    # the drawn band at 12 bits is wide enough to see against |Z| ~ 1
    assert 1e-3 < max(widths[12]) < 3.0
    assert max(widths[64]) < 1e-15


def test_li_figure_inputs_are_positive_and_track_the_asymptotic():
    """plot_li_coefficients: every λ_n > 0, and λ_n/asymptotic → 1 slowly."""
    from zeta.li import li_positivity_scan

    rows = li_positivity_scan(60, dps=25)
    assert all(r["positive"] for r in rows)
    assert rows[0]["margin"] > 0.023 and rows[0]["margin"] < 0.024
    # the residual is an oscillation, not a constant: its envelope grows
    resid = [r["margin"] - r["asymptotic"] for r in rows]
    env_early = max(abs(v) for v in resid[:20])
    env_late = max(abs(v) for v in resid)
    assert env_late > env_early
    assert abs(rows[-1]["relative_to_asymptotic"] - 1.0) < 0.05


def test_jensen_figure_roots_are_real_negative_and_far_from_the_tolerance():
    """plot_jensen_roots: the panel's two claims, re-derived.

    (i) every root is real and negative; (ii) the relative |Im root| is a
    hundred orders of magnitude or more below the root-finder tolerance
    10^{−dps/2}.  Measured here at dps = 30 for d ∈ {2, 3, 4, 6}, n = 1: the
    worst relative |Im root| is 8.6e-170 (at d = 6), against a tolerance of
    1.0e-15 — so the assertion below has ~55 orders of headroom and would still
    fail on any real regression.
    """
    from mpmath import mp

    from zeta.li import is_hyperbolic, jensen_polynomial, xi_taylor_coefficients

    dps = 30
    tol = 10.0 ** (-dps / 2.0)
    gammas = xi_taylor_coefficients(12, dps=dps)
    worst_imag = 0.0
    for d in (2, 3, 4, 6):
        coeffs = jensen_polynomial(d, 1, dps=dps, gammas=gammas, normalise=True)
        info = is_hyperbolic(coeffs, dps=dps, method="both")
        assert info["hyperbolic"] and info["agree"]
        assert info["n_real_exact"] == info["degree"] == d
        with mp.workdps(dps):
            assert all(mp.re(r) < 0 for r in info["roots"])
        worst_imag = max(worst_imag, info["max_rel_imag"])
    assert worst_imag < tol * 1e-100, worst_imag


def test_finite_field_figure_points_are_on_the_circle_and_the_line():
    """plot_finite_field_rh: |α| = √p and Re(s) = ½ for every plotted point."""
    from mpmath import mp

    from zeta.finitefield import traces_mod_p

    dps = 25
    for p in (13, 101):
        traces = sorted(set(int(a) for a in traces_mod_p(p)))
        assert traces  # every |a_p| <= 2 sqrt p, exactly (Hasse)
        assert all(a * a <= 4 * p for a in traces)
        with mp.workdps(dps + 10):
            for a in traces:
                alpha = mp.mpc(mp.mpf(a) / 2, mp.sqrt(mp.mpf(4 * p - a * a)) / 2)
                assert abs(abs(alpha) - mp.sqrt(p)) < mp.mpf(10) ** (-dps)
                re_s = mp.re(mp.log(alpha) / mp.log(p))
                assert abs(re_s - mp.mpf(1) / 2) < mp.mpf(10) ** (-dps)


def test_sato_tate_figure_inputs():
    """plot_sato_tate: bounded support, exact second moment, no violations."""
    from zeta.finitefield import sato_tate_histogram

    h = sato_tate_histogram(503, n_bins=20)
    assert h["hasse_violations"] == 0
    assert h["sum_a_p"] == 0
    assert h["second_moment_exact"] == h["second_moment_closed_form"]
    assert abs(h["moments"][0] - 0.25) < 1e-4
    # the histogram is a density on [-1, 1]
    assert abs(float(h["density"].sum()) * (2.0 / 20) - 1.0) < 1e-12


def test_mertens_figure_reference_points():
    """plot_mertens: the degenerate small-x values the figure excludes."""
    import math

    from zeta.criteria import mertens_M, mertens_ratio, mertens_ratio_extremes

    assert mertens_M(1) == 1
    assert mertens_ratio(1) == 1.0
    assert mertens_M(5) == -2
    assert abs(mertens_ratio(5) - (-2.0 / math.sqrt(5))) < 1e-15
    # and the honest statement the figure makes about x >= 100
    ext = mertens_ratio_extremes(200_000, x_min=100)
    assert ext["max_abs_ratio"] < 1.0
    assert ext["argmax_abs"] == 199


# ---------------------------------------------------------------------------
# the demo scripts
# ---------------------------------------------------------------------------

SCRIPT_NAMES = [
    "09_certified_verification.py",
    "10_li_and_jensen.py",
    "11_finite_field_rh.py",
    "12_equivalence_faces.py",
]


@pytest.mark.parametrize("script", SCRIPT_NAMES)
def test_script_help_exits_zero_and_explains_itself(script):
    out = subprocess.run(
        [sys.executable, os.path.join(SCRIPTS, script), "--help"],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    assert out.returncode == 0, out.stderr
    assert "usage:" in out.stdout.lower()
    # the house rule: the help text carries the mathematics, not just flags
    assert len(out.stdout) > 900, len(out.stdout)


@pytest.mark.parametrize("script", ["11_finite_field_rh.py", "12_equivalence_faces.py"])
def test_cheap_scripts_run_end_to_end(script):
    args = {
        "11_finite_field_rh.py": ["--primes", "13", "101", "--curves-per-prime", "6",
                                  "--skip-sato-tate"],
        "12_equivalence_faces.py": ["--mertens-limit", "200000", "--bd-N", "10",
                                    "--robin-max-log-n", "30", "--robin-ca-steps", "60",
                                    "--speiser-t-max", "60"],
    }[script]
    out = subprocess.run(
        [sys.executable, os.path.join(SCRIPTS, script)] + args,
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    assert out.returncode == 0, out.stderr[-2000:]
    assert "HEADLINE" in out.stdout or "DASHBOARD" in out.stdout


@pytest.mark.slow
@pytest.mark.parametrize("script", ["09_certified_verification.py", "10_li_and_jensen.py"])
def test_remaining_scripts_run_end_to_end(script):
    args = {
        "09_certified_verification.py": ["--T", "50", "--no-compare"],
        "10_li_and_jensen.py": ["--n-lambda", "4", "--n-both-routes", "2",
                                "--n-scan", "12", "--defect-n", "1", "--d-max", "3",
                                "--n-max", "3", "--skip-gue"],
    }[script]
    out = subprocess.run(
        [sys.executable, os.path.join(SCRIPTS, script)] + args,
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    assert out.returncode == 0, out.stderr[-2000:]
    assert "HEADLINE" in out.stdout
