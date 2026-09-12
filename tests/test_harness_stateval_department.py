"""Department #6 (stateval), the audits beyond structural conformance.

Pinned here: the measured anatomy of each protocol sham (reported vs fresh),
the null band that forced ``run_null_band`` into the protocol, the two
detectors' power split (the direct scan full-power, the behavioral gap
detector measurably blind below its floor), and the department's preserved
false start, a "sham" rival that turned out to have genuine skill, caught
by the calibration re-derivation before it shipped.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness.departments import stateval_department as S  # noqa: E402
from harness.integrity import CALIBRATED, audit_department  # noqa: E402
from harness.protocol import (  # noqa: E402
    run_ablation,
    run_battery,
    run_detector,
    run_null_band,
)


def _reported(name: str) -> float:
    subject = S.TARGET if name == "target" else next(r for r in S.RIVALS if r.name == name)
    return subject.payload()["reported_improvement"]()


def _fresh_ratios(subject) -> list[float]:
    payload = subject.payload()
    return [
        payload["candidate_fresh_mse"](seed) / S.oracle_fresh_mean_mse(seed)
        for seed in S.FRESH_SEEDS
    ]


# ---------------------------------------------------------------------------
# 1. The anatomy: everything reports green, only the target survives fresh air
# ---------------------------------------------------------------------------


def test_every_subject_reports_an_improvement() -> None:
    assert _reported("target") == pytest.approx(0.8269, abs=1e-3)
    assert _reported("memorizer-leak") == pytest.approx(1.0, abs=1e-6)
    assert _reported("seed-hacked") > 0.15
    assert _reported("crippled-baseline") == pytest.approx(1.0, abs=1e-3)


def test_every_public_export_exists() -> None:
    for name in S.__all__:
        assert hasattr(S, name), f"__all__ names {name!r}, which does not exist"


def test_only_the_target_beats_the_oracle_on_fresh_draws() -> None:
    target_ratios = _fresh_ratios(S.TARGET)
    assert max(target_ratios) < 0.4, target_ratios  # genuine skill, with margin
    for rival in S.RIVALS:
        ratios = _fresh_ratios(rival)
        assert min(ratios) > S.FRESH_MARGIN, (rival.name, ratios)


def test_the_reference_claims_rederive() -> None:
    killed = run_battery(S.BATTERY, S.claim_reports_improvement, name="reports")
    assert killed.target is True
    assert killed.shared_with == ("crippled-baseline", "memorizer-leak", "seed-hacked")
    passing = run_battery(S.BATTERY, S.claim_improves_when_fresh, name="fresh")
    assert passing.distinguishes is True


def test_the_junk_pool_is_skill_free_by_construction() -> None:
    """The preserved false start, as an invariant. Two drafts of the
    seed-hacked rival acquired genuine skill (selection on signal-bearing
    data is training; and in this task ~a third of unconstrained small
    random predictors genuinely beat the mean). The pool must have no
    access to the signal at all, if this ever fails, the rival may be
    quietly re-acquiring the property it exists to lack."""
    weights = S._junk_weights(12345)
    informative = S.W_TRUE != 0.0
    assert np.all(weights[:, informative] == 0.0)
    assert np.any(weights[:, ~informative] != 0.0)


# ---------------------------------------------------------------------------
# 2. Ablation: the improvement collapses when the relationship is destroyed
# ---------------------------------------------------------------------------


def test_shuffled_labels_collapse_the_measured_improvement() -> None:
    verdict = run_ablation(
        S.BATTERY, S.ridge_improvement_on, tolerance=0.05, payload=S._decoy_probe()
    )
    assert verdict.baseline == pytest.approx(0.875, abs=0.01)
    assert verdict.survives is True, verdict.decoys
    for value in verdict.decoys.values():
        assert value < 0.2, verdict.decoys  # in-sample ridge luck on 64x8, not signal


# ---------------------------------------------------------------------------
# 3. The null band, what this department forced into the protocol
# ---------------------------------------------------------------------------


def test_the_null_band_never_reaches_the_observed_improvement() -> None:
    verdict = run_null_band(
        S.BATTERY,
        lambda p: float(p["reported_improvement"]()),
        draws=50,
        name="reported_improvement",
    )
    assert verdict.observed == pytest.approx(0.8269, abs=1e-3)
    assert verdict.total_draws == 100  # 50 per surrogate, stated in the verdict
    assert verdict.survives is True, verdict.summary()
    lo, hi = verdict.band
    assert hi < 0.3, verdict.summary()  # the multiple-comparison luck ceiling
    assert lo < 0.0  # selection can also lose, and the band shows it


def test_the_selection_null_draws_vary_across_calls() -> None:
    """A distributional surrogate must actually be one: repeated draws move.
    (The deterministic surrogates of other departments give degenerate
    bands, which NullBandVerdict displays rather than hides.)"""
    surrogate = S.SURROGATES[0]
    values = {round(surrogate.sample()["reported_improvement"](), 12) for _ in range(5)}
    assert len(values) > 1


# ---------------------------------------------------------------------------
# 4. Detector power: the direct scan vs the behavioral gap
# ---------------------------------------------------------------------------


def test_the_overlap_scan_sees_every_planted_contamination() -> None:
    verdict = run_detector(S.BATTERY, S.DETECTORS[0])
    assert verdict.false_alarm is False
    assert verdict.has_power is True
    assert verdict.smallest_detected == pytest.approx(0.03125)


def test_the_gap_detector_is_blind_below_its_floor_and_says_so() -> None:
    """Two leaked rows of 64 move the generalization gap by ~0.08, under
    the 0.1 threshold: measured blindness, pinned like the compiler
    department's poison case. The power *difference* between the two
    detectors is the measurement, the direct scan reads the violation,
    the behavioral one reads its consequences, and consequences fade first."""
    verdict = run_detector(S.BATTERY, S.DETECTORS[1])
    assert verdict.false_alarm is False
    assert verdict.blind_to == ("leak-0_03125",)
    assert verdict.smallest_detected == pytest.approx(0.25)


def test_the_gap_response_curve_is_the_declared_one() -> None:
    for lesion, expected_gap in zip(S.LESIONS, (0.082, 0.315, 0.850)):
        reported, fresh = S._run_protocol(lesion.apply(dict(S.CLEAN_PROTOCOL)))
        assert reported - fresh == pytest.approx(expected_gap, abs=0.02), lesion.name
    reported, fresh = S._run_protocol(dict(S.CLEAN_PROTOCOL))
    assert reported - fresh == pytest.approx(0.0, abs=1e-9)


# ---------------------------------------------------------------------------
# 5. The whole department, through the audit
# ---------------------------------------------------------------------------


def test_the_department_audits_calibrated() -> None:
    report = audit_department(S.DEPARTMENT)
    assert report.grade == CALIBRATED, report.render_text()
    assert report.unseen_lesions == ()  # union power: the scan covers the gap's floor
