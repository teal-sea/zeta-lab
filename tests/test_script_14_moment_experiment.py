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
from dataclasses import replace
from decimal import Decimal
from itertools import pairwise
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
    sys.modules[spec.name] = module
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


def test_convergence_sweep_reuses_one_grid_and_integrates_chunk_seams(
    script, monkeypatch
):
    """All nested cells come from one evaluation and join chunk seams exactly."""

    calls = []

    def fake_zeta(ts):
        calls.extend(float(value) for value in ts)
        return np.sqrt(ts)

    monkeypatch.setattr(script, "CHUNK", 3)
    monkeypatch.setattr(script, "riemann_siegel_z", fake_zeta)
    rows, count, _ = script.convergence_sweep(100.0, 16.0, 1.0)

    assert count == 17
    assert calls == list(np.arange(100.0, 117.0))
    assert len(rows) == 36
    for row in rows:
        ts = np.arange(100.0, 100.0 + row.window_length + row.spacing, row.spacing)
        expected = float(np.trapezoid(ts**row.k, ts))
        assert row.integral == pytest.approx(expected)

    diagnostics = script.convergence_diagnostics(rows)
    assert diagnostics[0].max_spacing_relative_drift < 1e-14
    assert all(
        diagnostic.max_window_ratio_relative_drift >= 0
        for diagnostic in diagnostics
    )


def test_convergence_sweep_rejects_non_nested_interval_count(script):
    with pytest.raises(ValueError, match="divisible by 4"):
        script.convergence_sweep(100.0, 18.0, 1.0)


def test_block_peak_sweep_reuses_grid_and_partitions_every_interval(
    script, monkeypatch
):
    """Block integrals and ranked contributions cover each trapezoid exactly once."""

    calls = []

    def fake_zeta(ts):
        calls.extend(float(value) for value in ts)
        return np.sqrt(ts)

    monkeypatch.setattr(script, "CHUNK", 3)
    monkeypatch.setattr(script, "riemann_siegel_z", fake_zeta)
    rows, concentrations, count, _ = script.block_peak_sweep(
        100.0,
        16.0,
        1.0,
        blocks=4,
        peak_fractions=(0.125, 0.25),
    )

    assert count == 17
    assert calls == list(np.arange(100.0, 117.0))
    assert len(rows) == 16 and len(concentrations) == 8
    for row in rows:
        ts = np.arange(row.interval_start, row.interval_end + 1, 1.0)
        expected = float(np.trapezoid(ts**row.k, ts))
        assert row.integral == pytest.approx(expected)

    for item in concentrations:
        ts = np.arange(100.0, 117.0)
        contributions = (ts[:-1] ** item.k + ts[1:] ** item.k) / 2
        expected = np.sum(np.sort(contributions)[-item.interval_count :]) / np.sum(
            contributions
        )
        assert item.contribution_fraction == pytest.approx(expected)

    diagnostics = script.block_diagnostics(rows)
    assert len(diagnostics) == 4
    assert all(
        item.minimum_block_ratio <= item.maximum_block_ratio
        for item in diagnostics
    )


def test_block_peak_sweep_rejects_non_divisible_blocks(script):
    with pytest.raises(ValueError, match="exactly divisible"):
        script.block_peak_sweep(100.0, 18.0, 1.0, blocks=4)


@pytest.mark.slow
def test_real_convergence_separates_grid_stability_from_window_variation(script):
    """At the pinned window quadrature is stable while window ratios vary."""

    rows, count, _ = script.convergence_sweep(1e5, 4e3, 5e-3)
    diagnostics = script.convergence_diagnostics(rows)

    assert count == 800_001
    assert all(item.max_spacing_relative_drift < 2e-6 for item in diagnostics)
    window_drifts = [item.max_window_ratio_relative_drift for item in diagnostics]
    assert window_drifts[0] < window_drifts[1] < window_drifts[2] < window_drifts[3]
    assert 0.05 < window_drifts[2] < 0.10
    assert 0.15 < window_drifts[3] < 0.22

    largest = max(row.window_length for row in rows)
    finest = min(row.spacing for row in rows)
    ratios = {
        row.k: row.ratio
        for row in rows
        if row.window_length == largest and row.spacing == finest
    }
    assert ratios == pytest.approx(
        {1: 0.998218, 2: 0.989319, 3: 0.965322, 4: 0.922880},
        rel=2e-5,
    )


@pytest.mark.slow
def test_real_block_study_pins_dispersion_and_peak_concentration(script):
    """The high-moment window variation is accompanied by concentrated mass."""

    rows, peaks, count, _ = script.block_peak_sweep(
        1e5, 4e3, 5e-3, blocks=8
    )
    diagnostics = script.block_diagnostics(rows)

    assert count == 800_001
    coefficients = [
        item.block_ratio_coefficient_of_variation for item in diagnostics
    ]
    assert coefficients == pytest.approx(
        [0.012752, 0.074340, 0.192046, 0.346265], rel=2e-5
    )
    assert all(left < right for left, right in pairwise(coefficients))

    by_peak = {(item.k, item.interval_fraction): item for item in peaks}
    fractions = sorted({item.interval_fraction for item in peaks})
    for fraction in fractions:
        shares = [
            by_peak[k, fraction].contribution_fraction for k in (1, 2, 3, 4)
        ]
        assert all(left < right for left, right in pairwise(shares))
    assert by_peak[4, 0.001].contribution_fraction == pytest.approx(
        0.560262, rel=2e-5
    )
    assert tuple(
        by_peak[k, 0.01].contribution_fraction for k in (1, 2, 3, 4)
    ) == pytest.approx(
        (0.2581, 0.6706, 0.8867, 0.9649), abs=1e-4
    )


@pytest.mark.slow
def test_multi_height_replication_pins_ratios_and_concentration_trend(script):
    rows, _ = script.multi_height_study()

    assert len(rows) == 12
    assert {row.sample_count for row in rows} == {768_001}
    by_cell = {(row.height, row.k): row for row in rows}
    expected_ratios = {
        1e4: (1.0004, 1.0014, 1.0052, 1.0199),
        1e5: (0.9996, 0.9947, 0.9755, 0.9368),
        1e6: (1.0061, 1.0154, 1.0084, 0.9677),
    }
    for height, expected in expected_ratios.items():
        measured = tuple(by_cell[height, k].aggregate_ratio for k in (1, 2, 3, 4))
        assert measured == pytest.approx(expected, abs=1e-4)

    for k in (1, 2, 3, 4):
        concentration = [
            by_cell[height, k].top_one_percent_contribution
            for height in (1e4, 1e5, 1e6)
        ]
        dispersion = [
            by_cell[height, k].block_ratio_coefficient_of_variation
            for height in (1e4, 1e5, 1e6)
        ]
        assert all(left < right for left, right in pairwise(concentration))
        assert all(left < right for left, right in pairwise(dispersion))

    assert tuple(
        by_cell[height, 4].top_one_percent_contribution
        for height in (1e4, 1e5, 1e6)
    ) == pytest.approx((0.9025, 0.9652, 0.9896), abs=1e-4)
    assert by_cell[1e6, 4].block_ratio_coefficient_of_variation == pytest.approx(
        0.7681, abs=1e-4
    )


def test_replication_console_preserves_scope(script, monkeypatch, capsys):
    rows = tuple(
        script.HeightReplicationRow(
            height=height,
            mean_zero_gap=1.0,
            window_length=10.0,
            spacing=0.1,
            sample_count=101,
            k=k,
            aggregate_ratio=1.0,
            block_ratio_coefficient_of_variation=0.1,
            top_tenth_percent_contribution=0.2,
            top_one_percent_contribution=0.5,
        )
        for height in (1e4, 1e5, 1e6)
        for k in (1, 2, 3, 4)
    )
    monkeypatch.setattr(script, "multi_height_study", lambda: (rows, 1.0))
    monkeypatch.setattr(sys, "argv", [SCRIPT, "--replicate"])

    assert script.main() == 0
    out = capsys.readouterr().out
    assert "Height-normalized moment replication" in out
    assert "Measured / full-polynomial prediction" in out
    assert "Integral share from largest 1%" in out
    assert "not a confidence interval" in out
    assert "a proof of CFKRS, or evidence for RH" in out


def _passing_offset_diagnostics(script):
    return tuple(
        script.OffsetDiagnostic(
            anchor_height=height,
            k=k,
            pooled_ratio=1.0,
            median_ratio=1.0,
            minimum_ratio=0.9,
            maximum_ratio=1.1,
            ratio_coefficient_of_variation=0.1,
            median_top_one_percent_contribution=0.5 + height_index / 10,
        )
        for height_index, height in enumerate((1e4, 1e5, 1e6))
        for k in (1, 2, 3, 4)
    )


def test_offset_attack_gates_have_mutation_teeth(script):
    heights = (1e4, 1e5, 1e6)
    diagnostics = _passing_offset_diagnostics(script)
    assert script.offset_attack_verdict(diagnostics, heights).passed

    mutated = tuple(
        replace(row, pooled_ratio=1.06)
        if (row.anchor_height, row.k) == (1e4, 1)
        else replace(row, pooled_ratio=1.16)
        if (row.anchor_height, row.k) == (1e5, 3)
        else replace(row, median_top_one_percent_contribution=0.4)
        if (row.anchor_height, row.k) == (1e6, 4)
        else row
        for row in diagnostics
    )
    verdict = script.offset_attack_verdict(mutated, heights)
    assert not verdict.passed
    assert not verdict.theorem_controls_passed
    assert not verdict.conjectural_ratios_passed
    assert not verdict.concentration_trend_passed
    assert len(verdict.failures) == 3


@pytest.mark.slow
def test_real_multi_offset_diagnostic_matches_historical_results(script):
    rows, diagnostics, verdict, _ = script.multi_offset_attack()

    assert len(rows) == 48 and len(diagnostics) == 12
    assert verdict.passed
    assert verdict.failures == ()
    by_cell = {(row.anchor_height, row.k): row for row in diagnostics}
    expected_pooled = {
        1e4: (1.0000, 1.0002, 1.0006, 1.0001),
        1e5: (1.0003, 0.9986, 0.9866, 0.9633),
        1e6: (1.0001, 1.0075, 1.0301, 1.0628),
    }
    for height, expected in expected_pooled.items():
        measured = tuple(by_cell[height, k].pooled_ratio for k in (1, 2, 3, 4))
        assert measured == pytest.approx(expected, abs=1e-4)

    highest_eighth = by_cell[1e6, 4]
    assert highest_eighth.minimum_ratio == pytest.approx(0.5831, abs=1e-4)
    assert highest_eighth.maximum_ratio == pytest.approx(1.4362, abs=1e-4)
    assert highest_eighth.median_top_one_percent_contribution == pytest.approx(
        0.9912, abs=1e-4
    )


@pytest.mark.slow
def test_shifted_anchor_w7_audit_reproduces_near_unity_pooling(script):
    rows, diagnostics, _, _ = script.multi_offset_attack((1.5e4,))

    expected_windows = {
        0: (0.998992, 0.992625, 0.984079, 0.972911),
        1: (1.002209, 1.011846, 1.027001, 1.044684),
        2: (0.999394, 0.993951, 0.987101, 0.975328),
        3: (1.000177, 1.002749, 1.004286, 1.009597),
    }
    for window_index, expected in expected_windows.items():
        measured = tuple(
            row.ratio
            for row in rows
            if row.window_index == window_index
        )
        assert measured == pytest.approx(expected, abs=1e-6)

    assert tuple(row.pooled_ratio for row in diagnostics) == pytest.approx(
        (1.000191, 1.000374, 1.000942, 1.001560), abs=1e-6
    )


def test_attack_console_discloses_contamination_and_scope(script, monkeypatch, capsys):
    diagnostics = _passing_offset_diagnostics(script)
    verdict = script.offset_attack_verdict(diagnostics, (1e4, 1e5, 1e6))
    monkeypatch.setattr(
        script,
        "multi_offset_attack",
        lambda: ((), diagnostics, verdict, 1.0),
    )
    monkeypatch.setattr(sys, "argv", [SCRIPT, "--attack"])

    assert script.main() == 0
    out = capsys.readouterr().out
    assert "NOT PRE-REGISTERED" in out
    assert "NO FALSIFICATION WEIGHT" in out
    assert "reused already-seen data" in out
    assert "not a confidence interval" in out
    assert "proof of CFKRS" in out
    assert "evidence for RH" in out


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
        [
            sys.executable,
            SCRIPT,
            "--start",
            "1e5",
            "--length",
            "2e3",
            "--convergence",
        ],
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
    assert "Nested convergence" in out
    assert "neither column is an error bound or certificate" in out
    # The calibration must be shown, not just the unfalsifiable comparisons.
    assert "Ingham's proved global 2nd-moment main term" in out


@pytest.mark.slow
def test_block_console_states_its_scope():
    result = subprocess.run(
        [
            sys.executable,
            SCRIPT,
            "--start",
            "1e5",
            "--length",
            "2e3",
            "--blocks",
            "8",
        ],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    assert result.returncode == 0, result.stderr
    out = result.stdout

    assert "Disjoint blocks" in out
    assert "Moment integral carried by the largest grid-interval contributions" in out
    assert "dispersion is not a confidence interval" in out
    assert "peak shares are not error bounds" in out
