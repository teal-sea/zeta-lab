"""Department #5 (referee) — the audits beyond structural conformance.

The conformance suite already runs this department like any other. What is
pinned here is the anatomy: that the 431cc74 reconstruction fails for
exactly the reason the original was a sham (the label leak, nothing else),
that the measured lesion magnitudes are real numbers derived at import,
that the unguided-bundle null is conditioned on structural validity (the
null class worth beating), and that the recursion closes — the audit grades
the department that carries it, and no meta-meta-layer exists or is needed.
"""

from __future__ import annotations

import ast
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import shams  # noqa: E402
from harness.departments import referee_department as R  # noqa: E402
from harness.integrity import (  # noqa: E402
    CALIBRATED,
    DETECTOR_INADEQUATE,
    FAIL,
    HOLLOW,
    PASS,
    audit_department,
    report_claim,
)
from harness.protocol import (  # noqa: E402
    department_reasons,
    run_ablation,
    run_battery,
    run_detector,
    run_nulls,
)


# ---------------------------------------------------------------------------
# 1. The headline measurement: structural completeness distinguishes nothing
# ---------------------------------------------------------------------------


def test_every_sham_rival_validates_structurally() -> None:
    """The killed reference claim's anatomy: all three rivals pass the same
    structural door the specimen passes. If any stopped validating, it would
    stop demonstrating that validation is not verification."""
    verdict = run_battery(R.BATTERY, R.claim_validates_structurally, name="validates")
    assert verdict.target is True
    assert verdict.shared_with == (
        "constant-detector-sham",
        "inert-instrument-sham",
        "sham-431cc74-reconstruction",
    )
    assert verdict.errors == {}


def test_the_audit_separates_what_structure_cannot() -> None:
    verdict = run_battery(R.BATTERY, R.claim_audits_calibrated, name="audits")
    assert verdict.distinguishes is True


# ---------------------------------------------------------------------------
# 2. The 431cc74 reconstruction fails for the historical reason
# ---------------------------------------------------------------------------


def test_the_sham_reconstruction_is_caught_by_the_label_leak_alone() -> None:
    """The sham's precise anatomy, pinned: its calibration re-derives (the
    leak-reading claim really does 'distinguish'), its co-designed detector
    really has mechanical power — every check a sham author could co-design
    passes. What catches it is the one thing its author could not hide: the
    payload asymmetry the label leak *is*."""
    sham = R.build_sham_431cc74()
    report = audit_department(sham)
    assert report.grade == HOLLOW
    assert report.check("payload-symmetry").status == FAIL
    assert "virtual_a_p" in report.check("payload-symmetry").evidence
    # The co-designed parts pass — that is what made it dangerous.
    assert report.check("calibration-rederived").status == PASS
    assert report.check("detector-specificity").status == PASS
    assert report.check("detector-power").status == PASS


def test_a_green_claim_from_the_sham_renders_as_dangerous() -> None:
    """The sham's own distinguishing claim, through the pairing that makes
    hollow green unmistakable."""
    sham = R.build_sham_431cc74()
    report = report_claim(sham, lambda p: "virtual_a_p" not in p, name="no-virtual-trace")
    assert report.claim_status == "distinguishes"
    assert report.integrity.grade == HOLLOW
    assert report.dangerous is True


# ---------------------------------------------------------------------------
# 3. Instruments: measured magnitudes, moving decoys, a strong null
# ---------------------------------------------------------------------------


def test_lesion_magnitudes_are_measured_and_positive() -> None:
    magnitudes = {lesion.name: lesion.magnitude for lesion in R.LESIONS}
    assert all(m > 0 for m in magnitudes.values()), magnitudes
    assert len(set(magnitudes.values())) > 1, magnitudes
    # Pinned: the fraction of the audit's checks each corruption flips.
    # These move whenever the audit grows a check, which is the point of
    # measuring them at import rather than asserting them: the 2026-08-09
    # rival-distance and detector-independence build took the audit from 16
    # named checks to 19, and every magnitude here fell accordingly.
    assert magnitudes["plant-constant-true-detector"] == pytest.approx(0.1053)  # 2/19
    assert magnitudes["plant-target-as-rival"] == pytest.approx(0.0526)  # 1/19


def test_ablation_moves_when_the_calibration_content_is_stripped() -> None:
    verdict = run_ablation(
        R.BATTERY, R.integrity_pass_count, tolerance=0.5, payload=R.SPECIMEN
    )
    assert verdict.baseline == 18.0
    assert verdict.survives is True, verdict.decoys


def test_the_unguided_null_is_conditioned_on_structural_validity() -> None:
    """The null class worth beating is 'validates, with random content' —
    every sham this department hunts validates too. A null that mostly
    failed at the door would flatter the audit by never reaching it (the
    same reason the compiler department keeps its mutants compilable)."""
    for surrogate in R.SURROGATES:
        bundle = surrogate.sample()
        assert department_reasons(bundle) == (), (
            f"{surrogate.name} produced a structurally invalid bundle — a weak null"
        )


def test_no_unguided_bundle_reproduces_the_specimen_pass_count() -> None:
    verdict = run_nulls(R.BATTERY, R.integrity_pass_count, tolerance=0.5)
    assert verdict.observed == 18.0
    assert verdict.survives is True, verdict.surrogates
    # The luck floor, pinned as a *margin* rather than an absolute count.
    # It was `<= 12.0` against a 16-check audit; the 2026-08-09 build took the
    # audit to 19 checks and the nulls rose to 12-13 with it, which is
    # arithmetic and not erosion — as a fraction they went from 12/16 = 0.75
    # to 13/19 = 0.68, i.e. the separation got *better*. An absolute pin would
    # have had to be raised on every future check and would have hidden the
    # day the separation genuinely shrank; a margin does not.
    best_null = max(verdict.surrogates.values())
    assert best_null <= 13.0, verdict.surrogates
    assert verdict.observed - best_null >= 5.0, (
        f"random valid bundles now come within {verdict.observed - best_null:g} checks "
        f"of the specimen ({verdict.surrogates}): the audit's checks are becoming "
        "reproducible by chance and the statistic must be rethought"
    )


# ---------------------------------------------------------------------------
# 4. The recursion, closed
# ---------------------------------------------------------------------------


def test_the_audit_as_detector_has_measured_power_and_specificity() -> None:
    verdict = run_detector(R.BATTERY, R.DETECTORS[0])
    assert verdict.false_alarm is False
    assert verdict.has_power is True
    assert set(verdict.fired) == {lesion.name for lesion in R.LESIONS}


def test_the_referee_department_does_not_survive_its_own_audit() -> None:
    """The recursion bit back, and the result is recorded rather than reframed.

    This test asserted ``CALIBRATED`` until 2026-08-09. Then the audit grew
    ``detector-claim-agreement`` — the mechanical form of the countermeasure
    that ``SHAM_MODES["detector-is-the-claim"]`` had been carrying as prose —
    and the first thing it flagged was this department. It is right on the
    facts: the referee's declared detector is the integrity audit as a
    predicate ("fires when a bundle's grade is not CALIBRATED") and its
    passing reference claim is ``audits_calibrated``. They are the same
    computation, one negated, on all 13 payloads both answer. The power this
    department measures for its detector is its claim measuring itself.

    Whether that is fatal or benign is exactly the judgment the audit cannot
    make — the mode has a second conjunct, "the lesion family was chosen to
    be exactly what it looks for", and only the first is visible from this
    layer (``docs/23`` §8). The department's own module docstring already
    called this "the recursion, and also where it stops"; what is new is that
    the recursion is now *measured* rather than argued, and it comes back
    negative.

    Kept as an assertion and not an xfail, because it is a fact about the
    current tree and not an aspiration: the referee department is
    DETECTOR_INADEQUATE and the repository owes it an answer. When somebody
    stakes this department's power on a detector independent of its claim,
    this test fails and gets rewritten to assert CALIBRATED again.
    """
    report = audit_department(R.DEPARTMENT)
    assert report.grade == DETECTOR_INADEQUATE, report.render_text()
    result = report.check("detector-claim-agreement")
    assert result.status == "fail"
    assert "integrity-audit" in result.evidence
    # Everything else about the department still holds: the failure is one
    # named check, not a collapse.
    assert [c.name for c in report.checks if c.status == "fail"] == [
        "detector-claim-agreement"
    ], report.render_text()


def test_a_corrupted_referee_is_caught_by_its_own_machinery() -> None:
    """The audit turned on a corrupted copy of the department that carries
    it: sabotage the referee's own battery and the same machinery flags it.
    This is the strongest recursion the architecture supports without a
    second trust root, and its limit is already pinned elsewhere: a
    co-designed corruption of the audit itself would need the held-out
    conformance suite to catch, which is why that suite is the kernel."""
    corrupted = shams.with_target_as_rival(R.DEPARTMENT)
    assert audit_department(corrupted).grade == HOLLOW


# ---------------------------------------------------------------------------
# 5. The meta-domain needs no subject knowledge
# ---------------------------------------------------------------------------


def test_the_referee_department_imports_no_laboratory_package() -> None:
    """Departments may import their laboratories; this one's laboratory is
    the harness itself, and importing a subject package would mean the
    meta-domain had quietly grown domain content."""
    source = (_REPO_ROOT / "harness/departments/referee_department.py").read_text(
        encoding="utf-8"
    )
    tree = ast.parse(source)
    imported: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            imported.append(node.module)
    for name in imported:
        root = name.split(".")[0]
        assert root in ("harness", "dataclasses", "typing", "__future__"), (
            f"referee_department imports {name}"
        )
