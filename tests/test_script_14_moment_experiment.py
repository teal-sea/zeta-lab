"""Tests for ``scripts/14_moment_experiment.py`` — locally generated moments.

The script makes four kinds of claim, and each is pinned here rather than
trusted:

* **the constants** — ``c_k`` is re-derived from an Euler product and the
  Keating--Snaith ratio on every run.  ``a_2 = 6/pi^2`` and ``c_2 = 1/(2 pi^2)``
  are theorems, so they are checked against closed forms, not against the
  script's own cross-check;
* **the calibration** — the measured 2nd moment must agree with the difference
  of Ingham's two-term global main term across the chosen window.  This is a
  numerical instrument test, not a short-interval theorem;
* **the pairwise thresholds** — Cauchy--Schwarz is checked algebraically and the
  output must not promote a two-moment consistency condition into a reachability
  claim about either moment alone;
* **the honest-scope statements** — the output must label local comparisons as
  diagnostics and say that nothing settles RH. A console whose caveats can be
  deleted without a test failing will eventually have them deleted.

The sweep is the expensive part, so the calibration test uses a short window
for which the remainder difference ``E(B)-E(A)`` is empirically stable.
"""

from __future__ import annotations

import importlib.util
import math
import os
from decimal import Decimal
import subprocess
import sys

import mpmath as mp
import numpy as np
import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = os.path.join(REPO_ROOT, "scripts", "14_moment_experiment.py")


def _load():
    spec = importlib.util.spec_from_file_location("moment_experiment", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def script():
    return _load()


def test_arithmetic_factor_reproduces_closed_forms(script):
    """``a_1 = 1`` and ``a_2 = 6/pi^2`` are theorems; the Euler product must find them."""

    assert abs(float(script.arithmetic_factor(1)) - 1.0) < 1e-9
    expected = 6 / math.pi**2
    assert abs(float(script.arithmetic_factor(2)) - expected) < 1e-5


def test_leading_coefficients_match_known_moments(script):
    """``c_1 = 1`` and ``c_2 = 1/(2 pi^2)`` are the proved 2nd/4th moment constants."""

    assert abs(float(script.leading_coefficient(1)) - 1.0) < 1e-9
    assert abs(float(script.leading_coefficient(2)) - 1 / (2 * math.pi**2)) < 1e-6


def test_random_matrix_factor_small_cases(script):
    """``prod_{j<k} j!/(j+k)!`` is 1 at k=1 and 1/12 at k=2."""

    assert abs(float(script.random_matrix_factor(1)) - 1.0) < 1e-12
    assert abs(float(script.random_matrix_factor(2)) - 1 / 12) < 1e-12


def test_pairwise_consistency_thresholds_are_ordered_and_huge(script):
    """The thresholds grow with k; they are properties of named moment pairs."""

    coefficients = {k: script.leading_coefficient(k) for k in (1, 2, 3, 4, 6, 8)}
    thresholds = {
        k: float(script.pairwise_consistency_threshold(k, coefficients))
        for k in (2, 3, 4)
    }

    assert thresholds[2] < thresholds[3] < thresholds[4]
    assert 1e7 < thresholds[2] < 1e10
    assert 1e16 < thresholds[3] < 1e20
    assert 1e28 < thresholds[4] < 1e32
    assert thresholds[2] == pytest.approx(3.6e8, rel=0.02)
    assert thresholds[3] == pytest.approx(1.2e18, rel=0.05)
    assert thresholds[4] == pytest.approx(1.1e30, rel=0.05)

    with mp.workdps(40):
        for k, threshold in thresholds.items():
            log_height = mp.log(mp.mpf(threshold) / (2 * mp.pi))
            left = coefficients[2 * k] * log_height ** (4 * k * k)
            right = coefficients[k] ** 2 * log_height ** (2 * k * k)
            assert abs(left / right - 1) < mp.mpf("1e-12")


def test_second_moment_main_term_matches_mpmath_quadrature(script):
    """The closed-form main term must agree with direct quadrature of its derivative.

    The local density is ``log(t/2pi) + 2 gamma``; integrating it is an
    independent route to the same cumulative, so a factor slip in either is
    caught here without computing a single value of zeta.
    """

    with mp.workdps(30):
        a, b = mp.mpf(1000), mp.mpf(3000)
        direct = mp.quad(lambda u: mp.log(u / (2 * mp.pi)) + 2 * mp.euler, [a, b])
        closed = script.second_moment_main_term(float(b)) - script.second_moment_main_term(
            float(a)
        )
        assert abs(direct - closed) < mp.mpf("1e-12") * abs(direct)


@pytest.mark.slow
def test_measured_second_moment_calibrates(script):
    """The generated values must reproduce the global main-term difference here.

    This is the calibration the whole script rests on.  The tolerance covers
    ``E(B)-E(A)`` and the numerical errors: 2% is loose enough to be stable and
    tight enough to catch a real defect.
    """

    start, length, spacing = 1e5, 4e3, 5e-3
    totals, count, _ = script.sweep(start, length, spacing)
    assert count == int(round(length / spacing)) + 1

    predicted = float(
        script.second_moment_main_term(start + length)
        - script.second_moment_main_term(start)
    )
    ratio = totals[1] / predicted
    assert abs(ratio - 1.0) < 0.02, f"2nd-moment calibration drifted: ratio={ratio}"


@pytest.mark.slow
def test_higher_moments_exceed_leading_order_in_calibration_window(script):
    """Regression-pin the exploratory ratios in this specific finite window.

    The assertions carry no asymptotic interpretation; they catch changes in
    the generated values or quadrature that need investigation.
    """

    start, length, spacing = 1e5, 4e3, 5e-3
    totals, _, _ = script.sweep(start, length, spacing)
    log_mid = math.log((start + length / 2) / (2 * math.pi))

    ratios = {}
    for k in (2, 3, 4):
        mean = totals[k] / length
        prediction = float(script.leading_coefficient(k)) * log_mid ** (k * k)
        ratios[k] = mean / prediction

    assert ratios[2] > 1.5
    assert ratios[3] > 10
    assert ratios[4] > 100
    # This observed ordering is pinned for the specific finite window only.
    assert ratios[2] < ratios[3] < ratios[4]


def test_full_polynomial_prediction_integrates_the_window(script):
    """The script-facing API uses every polynomial term, not midpoint leading order."""

    polynomial = script.moment_polynomial(4)
    prediction = script.moment_polynomial_mean(polynomial, "100000", "104000")
    leading_midpoint = polynomial.coefficients[0] * Decimal(
        str(math.log(102000 / (2 * math.pi)) ** 16)
    )

    assert prediction > leading_midpoint * Decimal("100")


def test_emit_requires_a_stated_length():
    """``--emit`` without ``--emit-length`` must fail rather than write a huge file."""

    result = subprocess.run(
        [sys.executable, SCRIPT, "--emit", "unused.txt"],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    assert result.returncode != 0
    assert "--emit-length" in result.stderr


def test_emit_requires_a_caller_stated_error_estimate():
    """The emitter must not fabricate a numerical error for locally computed values."""

    result = subprocess.run(
        [
            sys.executable,
            SCRIPT,
            "--emit",
            "unused.txt",
            "--emit-length",
            "10",
        ],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    assert result.returncode != 0
    assert "--emit-error-estimate" in result.stderr


@pytest.mark.slow
def test_emitted_rows_are_labelled_and_well_formed(script, tmp_path):
    """Emitted samples carry the documented columns and say they are local."""

    target = tmp_path / "samples.txt"
    script.sweep(
        1e5,
        50.0,
        0.01,
        emit=target,
        emit_length=10.0,
        emit_error_estimate=2.5e-9,
    )
    lines = target.read_text(encoding="utf-8").splitlines()

    header = [line for line in lines if line.startswith("#")]
    assert any("LOCALLY COMPUTED" in line for line in header)
    assert any("not external research data" in line for line in header)
    assert any("offset abs_zeta absolute_error" in line for line in header)

    rows = [line for line in lines if not line.startswith("#")]
    assert rows
    for row in rows:
        fields = row.split()
        assert len(fields) == 3
        offset, magnitude, error = (float(field) for field in fields)
        assert offset >= 0
        assert magnitude >= 0
        assert error > 0


def test_sweep_integrates_chunk_seams_once(script, monkeypatch):
    """Composite trapezoids neither omit nor duplicate chunk-boundary intervals."""

    monkeypatch.setattr(script, "CHUNK", 3)
    monkeypatch.setattr(script, "riemann_siegel_z", np.sqrt)
    totals, count, _ = script.sweep(100.0, 10.0, 1.0)

    assert count == 11
    assert totals[1] == pytest.approx((100.0 + 110.0) * 10.0 / 2.0)
@pytest.mark.slow
def test_console_states_its_scope():
    """The caveats are load-bearing claims, so their absence must fail a test."""

    result = subprocess.run(
        [sys.executable, SCRIPT, "--start", "1e5", "--length", "2e3"],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    assert result.returncode == 0, result.stderr
    out = result.stdout

    assert "FULL-POLYNOMIAL global extrapolations (not a test)" in out
    assert "Nothing above settles, supports or weakens RH." in out
    assert "necessary condition" in out
    assert "not a reachability" in out
    assert "full CFKRS polynomial is the comparison used" in out
    # The calibration must be shown, not just the unfalsifiable comparisons.
    assert "Ingham's proved global 2nd-moment main term" in out
