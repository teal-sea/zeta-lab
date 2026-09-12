"""The integrity audit, measured the way it measures everyone else.

This file is the audit's own power calibration: every catchable sham mode
from ``harness.integrity.SHAM_MODES`` is planted into a known-good specimen
department by ``harness.shams`` and the audit must (a) fail the named check
and (b) leave the CALIBRATED grade. The two modes the catalog declares
mechanically uncatchable are pinned *as* uncatchable, the same convention
as ``test_the_detector_is_blind_to_the_poison_lesion`` in the compiler
department: a blind spot that is measured and pinned cannot be quietly
forgotten, and the day somebody builds a check that catches it, the pin
fails and the catalog gets corrected.

Everything here is deliberately arithmetic-free, like the protocol tests:
if measuring the audit needed a laboratory, the seam would already be gone.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import shams  # noqa: E402
from harness.integrity import (  # noqa: E402
    AUDIT_BLIND_SPOTS,
    CALIBRATED,
    CONTAMINATED,
    DETECTOR_INADEQUATE,
    FAIL,
    HOLLOW,
    PASS,
    SHAM_MODES,
    UNKNOWN,
    audit_department,
    report_claim,
)
from harness.protocol import (  # noqa: E402
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
)
from harness.provenance import Provenance  # noqa: E402


# ---------------------------------------------------------------------------
# The specimen: a genuinely calibrated department in a neutral toy domain.
# Payloads are mappings so every check, including payload symmetry, can run.
# Three lesions, so that dropping the hardest one leaves the magnitude
# spread intact, the drop must be *genuinely* invisible for the blind-spot
# pin to mean anything.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ToySubject:
    name: str
    value: float
    def describe(self) -> str:
        return f"toy subject at {self.value}"
    def payload(self) -> dict:
        return {"value": self.value}


@dataclass(frozen=True)
class ToyDecoy:
    name: str = "increment-all"
    def describe(self) -> str:
        return "adds one to every probe entry"
    def substitute(self, probe: Any) -> list:
        return [x + 1 for x in probe]


@dataclass(frozen=True)
class ToySurrogate:
    name: str = "far-null"
    def describe(self) -> str:
        return "a payload far from the target's"
    def sample(self) -> dict:
        return {"value": 99.0}


@dataclass(frozen=True)
class ToyLesion:
    name: str
    magnitude: float
    probe: Any = (0.0,)
    def describe(self) -> str:
        return f"appends a violation of size {self.magnitude}"
    def apply(self, payload: Any) -> tuple:
        return (*payload, self.magnitude)


def _specimen(**overrides) -> Department:
    battery = Battery(
        name="specimen",
        target=ToySubject("target", 1.0),
        rivals=(ToySubject("rival-a", 2.0), ToySubject("rival-b", 3.0)),
        decoys=(ToyDecoy(),),
        surrogates=(ToySurrogate(),),
        lesions=(
            ToyLesion("large", 1.0),
            ToyLesion("medium", 0.1),
            ToyLesion("small", 0.001),
        ),
    )
    kwargs = dict(
        name="specimen",
        summary="a calibrated specimen for measuring the audit",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("shared-everywhere", lambda p: True, distinguishes=False),
            ReferenceClaim("target-only", lambda p: p["value"] == 1.0, distinguishes=True),
        ),
        detectors=(
            NamedDetector(
                "size-scan", lambda p: any(x > 0 for x in p), probe=(0.0,),
                note="fires when any planted entry is positive",
            ),
        ),
        scope="distinguishes the toy target from its two toy rivals; nothing else",
        provenance=Provenance(
            authored_by="this test file",
            independent_of_subject_author=False,
            results_visible_when_authored=False,
            frozen_before_execution=True,
        ),
    )
    kwargs.update(overrides)
    return Department(**kwargs)


# ---------------------------------------------------------------------------
# 1. The specimen is calibrated, the audit can say yes
# ---------------------------------------------------------------------------


def test_the_specimen_audits_calibrated() -> None:
    report = audit_department(_specimen())
    assert report.grade == CALIBRATED
    assert report.failures == ()
    assert report.unseen_lesions == ()


def test_the_audit_reports_its_own_blind_spots_on_every_report() -> None:
    report = audit_department(_specimen())
    named = {mode.name for mode in AUDIT_BLIND_SPOTS}
    assert named, "the audit claims to have no blind spots, which is itself a red flag"
    rendered = report.render_text()
    for name in named:
        assert name in rendered, f"blind spot {name!r} missing from the rendered report"


# ---------------------------------------------------------------------------
# 2. Power: every catchable sham mode is caught, by the check the catalog
#    names. This is run_detector applied to the audit itself.
# ---------------------------------------------------------------------------

_CATCHABLE = [
    pytest.param(
        lambda dep: shams.with_constant_detector(dep, value=True),
        "constant-true-detector",
        "detector-specificity",
        DETECTOR_INADEQUATE,
        id="constant-true-detector",
    ),
    pytest.param(
        lambda dep: shams.with_constant_detector(dep, value=False),
        "constant-false-detector",
        "detector-power",
        DETECTOR_INADEQUATE,
        id="constant-false-detector",
    ),
    pytest.param(
        shams.with_target_as_rival,
        "target-as-rival",
        "calibration-rederived",
        HOLLOW,
        id="target-as-rival",
    ),
    pytest.param(
        shams.with_inert_lesions,
        "inert-lesion",
        "lesions-plant-something",
        HOLLOW,
        id="inert-lesion",
    ),
    pytest.param(
        shams.with_leaked_label,
        "key-asymmetry-label-leak",
        "payload-symmetry",
        HOLLOW,
        id="leaked-label",
    ),
    pytest.param(
        shams.with_vacuous_calibration,
        "co-designed-calibration",  # the *vacuous* variant is catchable
        "calibration-rederived",
        HOLLOW,
        id="vacuous-calibration",
    ),
    pytest.param(
        shams.with_detector_as_claim,
        "detector-is-the-claim",
        "detector-claim-agreement",
        DETECTOR_INADEQUATE,
        id="detector-as-claim",
    ),
    pytest.param(
        shams.with_agreeable_absent_fields,
        "agreeable-absent-field-oracle",
        "undeclared-field-symmetry",
        HOLLOW,
        id="agreeable-absent-fields",
    ),
]


@pytest.mark.parametrize("mutate, mode, expected_check, expected_grade", _CATCHABLE)
def test_each_planted_sham_is_caught_by_the_named_check(
    mutate, mode, expected_check, expected_grade
) -> None:
    corrupted = mutate(_specimen())
    report = audit_department(corrupted)
    assert report.grade == expected_grade, report.render_text()
    assert report.check(expected_check).status == FAIL, report.render_text()


def test_the_specimen_and_its_shams_are_distinguishable_in_one_line() -> None:
    """The whole point, in miniature: structural validity is identical across
    the specimen and every sham; the audit grade is not."""
    from harness.protocol import department_reasons

    specimen = _specimen()
    corrupted = shams.with_target_as_rival(specimen)
    assert department_reasons(specimen) == ()
    assert department_reasons(corrupted) == ()  # structurally identical twins
    assert audit_department(specimen).grade == CALIBRATED
    assert audit_department(corrupted).grade == HOLLOW


# ---------------------------------------------------------------------------
# 3. Blindness: the two uncatchable modes, pinned as uncatchable
# ---------------------------------------------------------------------------


def test_the_audit_is_blind_to_a_silently_dropped_hardest_lesion() -> None:
    """Pinned on purpose, like the compiler department's poison blindness.

    With three lesions, dropping the hardest leaves the magnitude spread
    intact and every remaining check green. No audit of the remaining
    battery can know what was meant to be there. The countermeasure is
    preregistration (pin the lesion set in tests), which is exactly what
    the conformance suite does for the real departments. If this test ever
    fails, somebody has built a check that catches the drop, update
    SHAM_MODES before deleting the pin.
    """
    corrupted = shams.without_hardest_lesion(_specimen())
    report = audit_department(corrupted)
    assert report.grade == CALIBRATED
    assert any(m.name == "dropped-hardest-lesion" for m in AUDIT_BLIND_SPOTS)


def test_the_audit_is_blind_to_gross_rival_distance_at_the_frozen_threshold() -> None:
    """``rival-separator-abundance`` measures the distance and does not act on it.

    Pinned with its numbers, because the numbers are the finding. The check
    was specified in ``docs/23`` §4.2 with a threshold frozen at 0.5 *before*
    the calibration was read, and the calibration came back an order of
    magnitude lower: the six registered departments score 0.00 to 0.05 and
    this planted gross-distance corruption scores 0.24, so the statistic
    separates cleanly and the cut sits above the entire range. Moving it is a
    separate change with its own frozen criteria, a threshold set after
    reading its own calibration has no falsification weight, which is why
    ``docs/23`` refused to retune it and why this pin exists instead.

    If this test fails, the threshold moved. Update ``SHAM_MODES`` and
    ``docs/23`` §8 together, or the catalog starts lying about what it catches.
    """
    corrupted = shams.with_distant_rivals(_specimen())
    report = audit_department(corrupted)
    assert report.grade == CALIBRATED, report.render_text()
    result = report.check("rival-separator-abundance")
    assert result.status == PASS
    assert "0.24" in result.evidence, result.evidence
    mode = next(m for m in SHAM_MODES if m.name == "distant-rivals")
    assert mode.caught_by is None, "the catalog must not claim a catch it does not have"


def test_the_audit_is_blind_to_structure_matched_value_disjoint_rivals() -> None:
    """The mode six independent parties used to reach CALIBRATED, six for six.

    Rivals sharing the target's key set, types and shape while agreeing with
    it on no substantive value. No single field is the tell, so
    ``payload-symmetry`` passes; the shape is identical, so
    ``rival-separator-abundance`` measures ~0. Pinned as blind because the
    obvious fix inverts: comparing values leaf by leaf scores this
    repository's honest departments *more* separated than the sham, since a
    genuine rival differs from its target in its numbers too.
    """
    battery = Battery(
        name="value-disjoint",
        target=ToySubject("target", 1.0),
        rivals=(ToySubject("rival-a", 41.0), ToySubject("rival-b", 97.0)),
        decoys=(ToyDecoy(),),
        surrogates=(ToySurrogate(),),
        lesions=(ToyLesion("large", 1.0), ToyLesion("small", 0.001)),
    )
    department = Department(
        name="value-disjoint",
        summary="rivals matched in shape, disjoint in value",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("shared", lambda p: True, distinguishes=False),
            # Absurd, and it distinguishes: the rivals share no value with
            # the target, so any predicate keyed to a target value is
            # target-exclusive by construction.
            ReferenceClaim("absurd", lambda p: p["value"] < 1.5, distinguishes=True),
        ),
        detectors=(
            NamedDetector("size-scan", lambda p: any(x > 0 for x in p), probe=(0.0,)),
        ),
        scope="(pinned blind spot) distinguishes nothing it is about",
    )
    report = audit_department(department)
    assert report.grade == CALIBRATED, report.render_text()
    assert report.check("payload-symmetry").status == PASS
    assert report.check("rival-separator-abundance").status == PASS
    assert any(
        m.name == "structure-matched-value-disjoint-rivals" for m in AUDIT_BLIND_SPOTS
    )


def test_the_audit_is_blind_to_a_value_encoded_label_leak() -> None:
    """The co-designed sham: identity encoded in the *values* of a shared
    key, with claims written to read it. Key sets are symmetric, calibration
    re-derives, the detector is real, every mechanical check passes, and
    the "distinguishing" claim is reading a tell, not measuring. Pinned as
    the audit's measured limit; the countermeasure is independent authorship
    of battery content, declared in provenance, which no mechanical check
    can verify.
    """
    battery = Battery(
        name="co-designed",
        target=ToySubject("target", 1.0),
        # The leak: rival values are all above 1.5. A claim keyed on that
        # threshold reads identity while looking like a measurement.
        rivals=(ToySubject("rival-a", 2.0), ToySubject("rival-b", 3.0)),
        decoys=(ToyDecoy(),),
        surrogates=(ToySurrogate(),),
        lesions=(ToyLesion("large", 1.0), ToyLesion("small", 0.001)),
    )
    sham = Department(
        name="co-designed",
        summary="a fully co-designed sham that defeats every mechanical check",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("shared-everywhere", lambda p: True, distinguishes=False),
            # Reads the planted tell; mechanically indistinguishable from honest.
            ReferenceClaim("reads-the-tell", lambda p: p["value"] < 1.5, distinguishes=True),
        ),
        detectors=(
            NamedDetector("size-scan", lambda p: any(x > 0 for x in p), probe=(0.0,)),
        ),
        scope="(sham) claims anything it likes",
    )
    report = audit_department(sham)
    assert report.grade == CALIBRATED, (
        "the audit caught the value-encoded leak: SHAM_MODES must be updated "
        "to record the new check before this pin is changed"
    )
    assert any(m.name == "value-encoded-label-leak" for m in AUDIT_BLIND_SPOTS)


def test_every_sham_mode_names_a_real_check_or_a_countermeasure() -> None:
    from harness.integrity import audit_department as _audit  # noqa: F401

    check_names = {c.name for c in audit_department(_specimen()).checks}
    for mode in SHAM_MODES:
        if mode.caught_by is not None:
            assert mode.caught_by in check_names, (
                f"{mode.name} claims to be caught by {mode.caught_by!r}, "
                "which is not a check the audit runs"
            )
        else:
            assert mode.countermeasure.strip(), f"{mode.name} names no countermeasure"


# ---------------------------------------------------------------------------
# 4. Contamination and provenance
# ---------------------------------------------------------------------------


def test_declared_contamination_is_terminal() -> None:
    """The W2 mode: everything mechanical passes, and the pass still cannot
    be taken at face value because the criteria saw their own answers."""
    contaminated = _specimen(
        provenance=Provenance(
            authored_by="this test file",
            results_visible_when_authored=True,
        )
    )
    report = audit_department(contaminated)
    assert report.check("provenance-contamination").status == FAIL
    assert report.grade == CONTAMINATED


def test_an_absent_provenance_record_is_unknown_not_fine() -> None:
    report = audit_department(_specimen(provenance=None))
    assert report.check("provenance-declared").status == UNKNOWN
    assert report.check("provenance-contamination").status == UNKNOWN
    assert report.grade == CALIBRATED  # unknown is carried, not punished


def test_dependence_is_carried_but_not_fatal() -> None:
    report = audit_department(_specimen())
    assert report.dependence, "self-authorship was declared and must be carried"
    assert report.grade == CALIBRATED


# ---------------------------------------------------------------------------
# 5. The claim report: outcome and integrity, inseparable
# ---------------------------------------------------------------------------


def test_a_distinguishing_claim_under_a_calibrated_battery_is_not_dangerous() -> None:
    report = report_claim(_specimen(), lambda p: p["value"] == 1.0, name="target-only")
    assert report.claim_status == "distinguishes"
    assert report.dangerous is False
    assert "DANGER" not in report.render_text()


def test_a_green_claim_from_a_hollow_battery_is_marked_dangerous() -> None:
    """A claim passing a weak battery must never look like one passing a
    strong battery, the requirement, as a test."""
    hollow = shams.with_inert_lesions(_specimen())
    report = report_claim(hollow, lambda p: p["value"] == 1.0, name="target-only")
    assert report.claim_status == "distinguishes"
    assert report.integrity.grade == HOLLOW
    assert report.dangerous is True
    assert "DANGER" in report.render_text()
    assert "worth nothing" in report.headline()


def test_the_claim_report_serializes_with_its_integrity_attached() -> None:
    report = report_claim(_specimen(), lambda p: True, name="always")
    payload = json.loads(report.to_json())
    assert payload["claim_status"] == "shared"
    assert payload["integrity"]["grade"] == CALIBRATED
    assert payload["integrity"]["checks"], "the integrity checks must travel with the claim"
    assert "audit_blind_spots" in payload["integrity"]


def test_a_crashing_instrument_fails_its_check_rather_than_the_audit() -> None:
    @dataclass(frozen=True)
    class ExplodingDecoy:
        name: str = "exploding"
        def describe(self) -> str:
            return "raises on contact"
        def substitute(self, probe: Any) -> Any:
            raise RuntimeError("boom")

    specimen = _specimen()
    battery = replace(specimen.battery, decoys=(ExplodingDecoy(),))
    report = audit_department(replace(specimen, battery=battery))
    assert report.check("decoys-move-their-probe").status == FAIL
    assert "boom" in report.check("decoys-move-their-probe").evidence
    assert report.grade == HOLLOW


def test_an_undecided_hollow_check_caps_the_grade() -> None:
    """Undecided is not passed.

    Until 2026-08-09 ``UNKNOWN`` capped the grade for the two detector checks
    and for nothing else, so a hollow-class check that could not decide let
    the battery through to ``CALIBRATED``. An independent party found it on
    its first attempt: ``payload-symmetry`` returned ``UNKNOWN`` for any
    payload that was not a mapping, so callable payloads sidestepped it for
    free. The numeric arm has obeyed the opposite rule from the start,
    ``proven_sign`` returns 0 for "not decided", and this is that rule,
    here.
    """
    from harness.integrity import CheckResult, IntegrityReport, UNMEASURED

    decided = [
        CheckResult(name, PASS, "ok")
        for name in (
            "structural",
            "teeth-always-true",
            "detector-power",
            "detector-specificity",
        )
    ]
    report = IntegrityReport(
        department="undecided",
        checks=tuple(decided) + (CheckResult("payload-symmetry", UNKNOWN, "not decided"),),
    )
    assert report.grade == UNMEASURED
    assert report.undecided == ("payload-symmetry",)
    assert "payload-symmetry" in report.render_text()

    all_decided = IntegrityReport(
        department="decided",
        checks=tuple(decided) + (CheckResult("payload-symmetry", PASS, "ok"),),
    )
    assert all_decided.grade == CALIBRATED
    assert all_decided.undecided == ()


def test_payload_symmetry_decides_off_mappings_instead_of_shrugging() -> None:
    """A department whose payloads are bare callables is measured, not skipped.

    ``croniter``, a real department, authored outside this tree, hands out
    plain functions as payloads, so the callable-payload sidestep was never
    only a sham author's trick. Three of the six registered departments were
    undecided here before this change.
    """

    @dataclass(frozen=True)
    class CallableSubject:
        name: str
        value: float

        def describe(self) -> str:
            return "a subject whose payload is a bare function"

        def payload(self) -> Any:
            value = self.value
            return lambda: value

    battery = Battery(
        name="callable-payloads",
        target=CallableSubject("target", 1.0),
        rivals=(CallableSubject("rival", 2.0),),
        decoys=(ToyDecoy(),),
        surrogates=(ToySurrogate(),),
        lesions=(ToyLesion("large", 1.0), ToyLesion("small", 0.001)),
    )
    department = Department(
        name="callable-payloads",
        summary="payloads are functions",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("shared", lambda p: True, distinguishes=False),
            ReferenceClaim("target-only", lambda p: p() == 1.0, distinguishes=True),
        ),
        detectors=(
            NamedDetector("size-scan", lambda p: any(x > 0 for x in p), probe=(0.0,)),
        ),
        scope="a shape the audit used to shrug at",
    )
    result = audit_department(department).check("payload-symmetry")
    assert result.status == PASS, result.evidence
    assert "no named fields" in result.evidence


def test_an_instrument_faithful_to_its_own_payload_is_not_called_inert() -> None:
    """The audit must not select against domain-faithful instruments.

    Measured on 2026-08-09: four independent parties asked to author *honest*
    departments each wrote decoys and lesions that understood their own
    payloads and raised on anything else, and all four were graded HOLLOW for
    it on ``decoys-move-their-probe`` and ``lesions-plant-something``, while
    the party that reverse-engineered the audit's private probe shapes and
    wrote a generic fallback passed. The ``probe`` attribute those checks read
    is declared nowhere in ``harness/protocol.py`` and nowhere in
    ``harness/README.md``. An instrument now has to move *one* candidate
    probe, its own department's payload counts.
    """

    @dataclass(frozen=True)
    class NarrowDecoy:
        name: str = "only-understands-mappings"

        def describe(self) -> str:
            return "raises on anything that is not this department's payload"

        def substitute(self, payload: Any) -> Any:
            return {key: 0.0 for key in payload.keys()}  # raises on a list of ints

    @dataclass(frozen=True)
    class NarrowLesion:
        name: str
        magnitude: float

        def describe(self) -> str:
            return "raises on anything that is not this department's payload"

        def apply(self, payload: Any) -> Any:
            return {**payload, "value": payload["value"] + self.magnitude}

    battery = Battery(
        name="faithful-instruments",
        target=ToySubject("target", 1.0),
        rivals=(ToySubject("rival", 2.0),),
        decoys=(NarrowDecoy(),),
        surrogates=(ToySurrogate(),),
        lesions=(NarrowLesion("large", 1.0), NarrowLesion("small", 0.001)),
    )
    department = Department(
        name="faithful-instruments",
        summary="instruments that understand only their own payloads",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("shared", lambda p: True, distinguishes=False),
            ReferenceClaim("target-only", lambda p: p["value"] == 1.0, distinguishes=True),
        ),
        detectors=(
            NamedDetector(
                "moved-scan", lambda p: p["value"] != 1.0, probe={"value": 1.0}
            ),
        ),
        scope="an honest department that declares no probe attribute",
    )
    report = audit_department(department)
    assert report.check("decoys-move-their-probe").status == PASS, report.render_text()
    assert report.check("lesions-plant-something").status == PASS, report.render_text()

    # and the power is not bought at the cost of the inert-instrument catch
    inert = audit_department(shams.with_inert_lesions(_specimen()))
    assert inert.check("lesions-plant-something").status == FAIL


def test_the_grades_are_a_closed_vocabulary() -> None:
    from harness.integrity import GRADES

    assert set(GRADES) == {
        CALIBRATED, DETECTOR_INADEQUATE, "UNMEASURED", CONTAMINATED, HOLLOW,
    }
    report = audit_department(_specimen())
    assert report.grade in GRADES
    for check in report.checks:
        assert check.status in (PASS, FAIL, UNKNOWN)
