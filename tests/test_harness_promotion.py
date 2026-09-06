"""The promotion gate, scored against the pre-registration that authorised it.

``docs/21-forward-deployed-verification.md`` §5 froze nine success conditions
before ``harness/promotion.py`` and ``harness/preregistration.py`` existed.
This file is those conditions as assertions, and nothing else: the section
comments below carry the same S-numbers, so a reader can hold the doc beside
the file and see which criteria are actually pinned and which are prose.

The load-bearing one is **S2**. ``NaiveGate``, fifteen lines that read
declarations and recompute nothing, handles the clean case, the
blind-detector case and the honestly-declared-contaminated case exactly as
well as the real gate. Three cases are three constraints, and a lookup table
satisfies three constraints, so the only test in this file that measures
anything about the gate is the one that produces a case where the naive gate
ALLOWs and ``decide`` BLOCKs *without consulting any declared field*. If that
case ever stops firing, the gate is the sham and K1 has fired.

Everything here is arithmetic-free, like the protocol and integrity tests: if
measuring the gate needed a laboratory, the seam would already be gone.
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass, field, replace
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
    FAIL,
    GRADES,
    SHAM_MODES,
    ClaimReport,
    audit_department,
    report_claim,
)
from harness.preregistration import (  # noqa: E402
    CRITERIA_DRIFT,
    EVIDENCE_VISIBLE_AT_FREEZE,
    Preregistration,
    declared_vs_derived,
    derived_findings,
    digest,
)
from harness.promotion import (  # noqa: E402
    ALLOW,
    BLOCK,
    CHECKS,
    POLICY_VERSION,
    Boundary,
    Decision,
    ProducerView,
    PromotionError,
    ReasonCode,
    audit,
    decide,
    naive_decide,
    recheck,
)
from harness.protocol import (  # noqa: E402
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
)
from harness.provenance import Provenance  # noqa: E402
from harness.provenance import _DECLARABLE  # noqa: E402


# ---------------------------------------------------------------------------
# The specimen: the same neutral toy department the integrity tests use, so
# the two files can be read against one another. Three lesions, so that
# dropping the hardest one leaves every mechanical check green, the drop has
# to be genuinely invisible to the audit for case H to mean anything.
# ---------------------------------------------------------------------------

PRODUCER = "toy-producer"
REFEREE = "toy-referee"
CLAIM_ID = "toy-target-only"

#: The claim under test, and one that is shared with every rival (S7).
DISTINGUISHING_CLAIM = lambda payload: payload["value"] == 1.0  # noqa: E731
SHARED_CLAIM = lambda payload: payload["value"] > 0.0  # noqa: E731

EVIDENCE = {"run": "toy-2026-08-09", "observations": [1.0, 2.0, 3.0]}
EVIDENCE_DIGEST = digest(EVIDENCE)
OTHER_EVIDENCE = {"run": "toy-2026-08-01", "observations": [7.0]}

CLAIM_RECORD = {
    "claim_id": CLAIM_ID,
    "producer_id": PRODUCER,
    "statement": "the toy target is the only subject at value 1.0",
}

FIXED_NOW = "2026-08-09T00:00:00+00:00"

CLEAN_PROVENANCE = Provenance(
    authored_by="this test file",
    authored_on="2026-08-09",
    independent_of_subject_author=False,
    results_visible_when_authored=False,
    frozen_before_execution=True,
)

#: Maximally clean, every declarable field set the flattering way. Used by the
#: anti-circularity assertion: the block must survive this record.
IMMACULATE_PROVENANCE = Provenance(
    authored_by="this test file",
    authored_on="2026-08-09",
    independent_of_subject_author=True,
    results_visible_when_authored=False,
    frozen_before_execution=True,
    oracle_calls_subject=False,
    instruments_share_critical_dependency=False,
    edited_after_observing_failures=False,
)


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
        summary="a calibrated specimen for measuring the promotion gate",
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
        provenance=CLEAN_PROVENANCE,
    )
    kwargs.update(overrides)
    return Department(**kwargs)


def _criteria(department: Department) -> dict:
    """The criteria a preregistration freezes, *including the rosters*.

    This is the whole mechanism behind case H. Once the lesion roster is
    inside the criteria, silently removing a lesion changes the criteria
    digest, so the criteria applied are no longer the criteria frozen,
    mechanically, without anybody having to notice which lesion went missing.
    """
    return {
        "scope": department.scope,
        "reference_claims": sorted(
            [r.name, bool(r.distinguishes)] for r in department.reference_claims
        ),
        "detectors": sorted(d.name for d in department.detectors),
        "lesions": sorted(
            [lesion.name, float(lesion.magnitude)] for lesion in department.battery.lesions
        ),
        "rivals": sorted(r.name for r in department.battery.rivals),
    }


def _freeze(department: Department, *, already_existing=()) -> Preregistration:
    return Preregistration.freeze(
        _criteria(department),
        criteria_id="toy-criteria-v1",
        author_id=REFEREE,
        frozen_at="2026-08-08T00:00:00+00:00",
        already_existing_evidence=already_existing,
    )


def _kwargs(
    department: Department,
    prereg: Preregistration,
    *,
    criteria_applied: Any = None,
    evidence_digest: str = EVIDENCE_DIGEST,
    current_evidence_digest: str = EVIDENCE_DIGEST,
    claim_id: str = CLAIM_ID,
    producer_id: str = PRODUCER,
    verifier_id: str = REFEREE,
    requested_scope: str | None = None,
) -> dict:
    return {
        "prereg": prereg,
        "criteria_applied": _criteria(department) if criteria_applied is None else criteria_applied,
        "evidence_digest": evidence_digest,
        "current_evidence_digest": current_evidence_digest,
        "claim_id": claim_id,
        "producer_id": producer_id,
        "verifier_id": verifier_id,
        "requested_scope": department.scope if requested_scope is None else requested_scope,
    }


@dataclass(frozen=True)
class Case:
    """One submission, with everything both gates need to judge it."""

    name: str
    report: ClaimReport
    kwargs: dict
    provenance: Any
    expected: str
    note: str = ""

    def decide(self, **extra) -> Decision:
        return decide(self.report, **{**self.kwargs, "now": FIXED_NOW, **extra})

    def naive(self) -> Decision:
        return naive_decide(
            self.report, provenance=self.provenance, claim_id=CLAIM_ID, now=FIXED_NOW
        )


def _build_cases() -> tuple[Case, ...]:
    """The case table: the pre-registered attacks *and* the ordinary
    well-formed submissions a real boundary spends most of its day on.

    The mix matters for K3. A table containing only attacks would block close
    to 100% and would measure nothing about whether the gate can ever say yes;
    a table containing only clean cases would measure nothing about whether it
    can say no. Both halves are listed explicitly so the blocked fraction
    reported by the K3 test is readable rather than tuned.
    """
    cases: list[Case] = []

    # --- ordinary, well-formed submissions ---------------------------------
    clean = _specimen()
    prereg_clean = _freeze(clean)
    report_clean = report_claim(clean, DISTINGUISHING_CLAIM, name=CLAIM_ID)
    cases.append(
        Case("clean", report_clean, _kwargs(clean, prereg_clean), clean.provenance, ALLOW)
    )

    # Criteria frozen while *other* evidence was visible: set membership is
    # about this evidence, not about the list being non-empty.
    prereg_other = _freeze(clean, already_existing=(OTHER_EVIDENCE,))
    cases.append(
        Case(
            "clean-unrelated-evidence-visible-at-freeze",
            report_clean,
            _kwargs(clean, prereg_other),
            clean.provenance,
            ALLOW,
        )
    )

    # Scope quoted with different whitespace and case, normalised, not refused.
    cases.append(
        Case(
            "clean-scope-requoted",
            report_clean,
            _kwargs(clean, prereg_clean, requested_scope="  " + clean.scope.upper() + "\n"),
            clean.provenance,
            ALLOW,
        )
    )

    # Declared dependence, carried loudly by the audit, fatal to nothing.
    dependent = _specimen(
        provenance=Provenance(
            authored_by="this test file",
            independent_of_subject_author=False,
            oracle_calls_subject=True,
            instruments_share_critical_dependency=True,
            results_visible_when_authored=False,
            frozen_before_execution=True,
        )
    )
    cases.append(
        Case(
            "clean-declared-dependence",
            report_claim(dependent, DISTINGUISHING_CLAIM, name=CLAIM_ID),
            _kwargs(dependent, _freeze(dependent)),
            dependent.provenance,
            ALLOW,
        )
    )

    # No provenance record at all: unknown is carried, not punished.
    silent = _specimen(provenance=None)
    cases.append(
        Case(
            "clean-no-provenance-record",
            report_claim(silent, DISTINGUISHING_CLAIM, name=CLAIM_ID),
            _kwargs(silent, _freeze(silent)),
            None,
            ALLOW,
        )
    )

    # The anti-paranoia case (S6), described at its own test.
    alarming = _alarming_specimen()
    cases.append(
        Case(
            "alarming-but-fine",
            report_claim(alarming, DISTINGUISHING_CLAIM, name=CLAIM_ID),
            _kwargs(alarming, _freeze(alarming)),
            alarming.provenance,
            ALLOW,
            note="undeclared provenance, a detector with a measured floor, no support beyond the battery",
        )
    )

    # --- the pre-registered attacks ----------------------------------------
    blind = shams.with_constant_detector(_specimen(), value=True)
    cases.append(
        Case(
            "blind-detector",
            report_claim(blind, DISTINGUISHING_CLAIM, name=CLAIM_ID),
            _kwargs(blind, _freeze(blind)),
            blind.provenance,
            BLOCK,
        )
    )

    prereg_contaminated = _freeze(clean, already_existing=(EVIDENCE,))
    cases.append(
        Case(
            "derived-contaminated",
            report_clean,
            _kwargs(clean, prereg_contaminated),
            clean.provenance,
            BLOCK,
            note="declares itself clean; its digests say the criteria saw this evidence",
        )
    )

    dropped = shams.without_hardest_lesion(_specimen())
    cases.append(
        Case(
            "dropped-hardest-lesion",
            report_claim(dropped, DISTINGUISHING_CLAIM, name=CLAIM_ID),
            _kwargs(dropped, prereg_clean),
            dropped.provenance,
            BLOCK,
            note="the mode the audit is pinned blind to; prior state comes from the freeze",
        )
    )

    cases.append(
        Case(
            "claim-shared-with-a-rival",
            report_claim(clean, SHARED_CLAIM, name=CLAIM_ID),
            _kwargs(clean, prereg_clean),
            clean.provenance,
            BLOCK,
        )
    )

    cases.append(
        Case(
            "presented-for-another-claim",
            report_clean,
            _kwargs(clean, prereg_clean, claim_id="some-other-claim"),
            clean.provenance,
            BLOCK,
        )
    )

    cases.append(
        Case(
            "evidence-moved-underneath",
            report_clean,
            _kwargs(clean, prereg_clean, current_evidence_digest=digest({"run": "later"})),
            clean.provenance,
            BLOCK,
        )
    )

    cases.append(
        Case(
            "graded-by-its-own-producer",
            report_clean,
            _kwargs(clean, prereg_clean, verifier_id=PRODUCER),
            clean.provenance,
            BLOCK,
        )
    )

    return tuple(cases)


def _alarming_specimen() -> Department:
    """Everything a nervous reader would flag, and nothing actually wrong.

    Six undeclared provenance fields, and a detector with a *measured* floor:
    it never notices the smallest lesion, so the department reports a power
    limit on its own front page. Neither is a defect. If this case ever
    blocks, K3 has fired and the gate has become a referee that only says no.
    """
    return _specimen(
        provenance=Provenance(authored_by="a party that declared nothing else"),
        detectors=(
            NamedDetector(
                "coarse-scan",
                lambda p: any(x > 0.01 for x in p),
                probe=(0.0,),
                note="blind below 0.01 by construction; the floor is the point",
            ),
        ),
    )


_CASES: tuple[Case, ...] = _build_cases()
_BY_NAME = {case.name: case for case in _CASES}
_PARAMS = [pytest.param(case, id=case.name) for case in _CASES]


def _invariant(decision: Decision) -> None:
    assert (decision.verdict == BLOCK) == bool(decision.reasons), (
        f"the S4 invariant broke: verdict={decision.verdict!r} with "
        f"reasons={[str(r) for r in decision.reasons]}"
    )


# ---------------------------------------------------------------------------
# S1, the three cases, with the claim's own numbers held fixed
# ---------------------------------------------------------------------------


def test_s1_the_three_cases_decide_as_pre_registered() -> None:
    """Clean ALLOWs, a blind detector BLOCKs, derived contamination BLOCKs."""
    assert _BY_NAME["clean"].decide().verdict == ALLOW
    blind = _BY_NAME["blind-detector"].decide()
    assert blind.verdict == BLOCK
    assert ReasonCode.BATTERY_INTEGRITY_NOT_CALIBRATED in blind.reasons
    contaminated = _BY_NAME["derived-contaminated"].decide()
    assert contaminated.verdict == BLOCK
    assert ReasonCode.PROVENANCE_CONTAMINATED_DERIVED in contaminated.reasons


def test_s1_the_claims_own_battery_verdict_is_unmoved_across_the_three_cases() -> None:
    """The premise of the whole document, and the one that K7 kills.

    If the contaminated or blind case only fires once the claim's own numbers
    have been perturbed, then what changed is the claim, not the referee, and
    nothing here demonstrates that verifier integrity moves a decision. So the
    three ``BatteryVerdict`` objects are compared field by field, and the
    assertion is written to name the field that moved.
    """
    verdicts = {
        name: _BY_NAME[name].report.verdict
        for name in ("clean", "blind-detector", "derived-contaminated")
    }
    reference = verdicts["clean"]
    for name, verdict in verdicts.items():
        assert verdict.target == reference.target, f"{name}: target fired differently"
        assert verdict.shared_with == reference.shared_with, f"{name}: shared_with moved"
        assert dict(verdict.rivals) == dict(reference.rivals), f"{name}: rival answers moved"
        assert dict(verdict.errors) == dict(reference.errors), f"{name}: errors moved"
        assert verdict.distinguishes is True, f"{name}: the claim stopped distinguishing"


# ---------------------------------------------------------------------------
# Case H, the headline: a silently dropped hardest lesion
# ---------------------------------------------------------------------------


def test_case_h_a_dropped_hardest_lesion_blocks_while_the_audit_stays_blind() -> None:
    """The sharpest case, and the one that is *not* a restatement of docs/20.

    ``harness.shams.without_hardest_lesion`` removes the smallest-magnitude
    lesion. Every mechanical check still passes: the grade is CALIBRATED, the
    claim distinguishes, and ``ClaimReport.dangerous`` is False, so the banner
    layer has nothing to say. The audit is *correctly* blind here,
    ``test_the_audit_is_blind_to_a_silently_dropped_hardest_lesion`` in
    ``tests/test_harness_integrity.py`` pins that blindness and must keep
    passing. Nothing in this file repairs the audit; the freeze supplies a
    prior state the audit has no access to, and the roster digest moves.
    """
    case = _BY_NAME["dropped-hardest-lesion"]
    assert case.report.claim_status == "distinguishes"
    assert case.report.integrity.grade == CALIBRATED
    assert case.report.dangerous is False
    assert case.naive().verdict == ALLOW
    decision = case.decide()
    assert decision.verdict == BLOCK
    assert ReasonCode.CRITERIA_DRIFTED in decision.reasons


def test_case_h_the_roster_difference_is_what_the_digest_records() -> None:
    """The block must be traceable to the missing lesion, not to noise."""
    frozen = _criteria(_specimen())["lesions"]
    applied = _criteria(shams.without_hardest_lesion(_specimen()))["lesions"]
    assert [name for name, _ in frozen] == ["large", "medium", "small"]
    assert [name for name, _ in applied] == ["large", "medium"]
    findings = dict(
        derived_findings(
            _freeze(_specimen()),
            criteria_applied={"lesions": applied},
            evidence_digest=EVIDENCE_DIGEST,
        )
    )
    assert CRITERIA_DRIFT in findings


# ---------------------------------------------------------------------------
# S2, the load-bearing divergence. Without this the gate is NaiveGate.
# ---------------------------------------------------------------------------


def test_s2_at_least_one_case_the_naive_gate_allows_and_the_real_gate_blocks() -> None:
    """K1, negated. The single measurement that entitles this module to exist.

    ``NaiveGate`` gets the clean case, the blind case and the honestly
    declared contaminated case right. If no case separates the two gates, the
    real one is a boolean flag with extra steps and should be scored as one.
    """
    separating = [
        case.name
        for case in _CASES
        if case.naive().verdict == ALLOW and case.decide().verdict == BLOCK
    ]
    assert separating, (
        "no case separates decide() from naive_decide(): K1 has fired and the "
        "gate is the sham it was written to beat"
    )
    assert "derived-contaminated" in separating
    assert "dropped-hardest-lesion" in separating


def test_s2_the_block_does_not_rest_on_any_declared_field() -> None:
    """The anti-circularity assertion.

    The same contaminated case, rebuilt with a provenance record that declares
    itself immaculate on every tri-state field, must still BLOCK for the same
    reason. A block that softened here would be a block on the annotation
    (K10), not on the artifacts.
    """
    immaculate = _specimen(provenance=IMMACULATE_PROVENANCE)
    report = report_claim(immaculate, DISTINGUISHING_CLAIM, name=CLAIM_ID)
    assert report.integrity.grade == CALIBRATED
    prereg = _freeze(immaculate, already_existing=(EVIDENCE,))
    decision = decide(report, **_kwargs(immaculate, prereg), now=FIXED_NOW)
    assert decision.verdict == BLOCK
    assert ReasonCode.PROVENANCE_CONTAMINATED_DERIVED in decision.reasons
    assert naive_decide(report, provenance=IMMACULATE_PROVENANCE, claim_id=CLAIM_ID).verdict == ALLOW


def test_s2_no_self_declaration_can_buy_an_allow() -> None:
    """K5, in the direction that matters: a producer cannot annotate its way in.

    Every tri-state provenance field is swept through True and False over the
    derived-contaminated case. None of them may turn the BLOCK into an ALLOW.
    (The opposite direction, a self-declaration *costing* a producer an ALLOW,
    does exist, and is pinned separately below as the safe direction.)
    """
    for name in _DECLARABLE:
        for value in (True, False, None):
            provenance = replace(
                Provenance(authored_by="sweep"), **{name: value}
            )
            department = _specimen(provenance=provenance)
            report = report_claim(department, DISTINGUISHING_CLAIM, name=CLAIM_ID)
            prereg = _freeze(department, already_existing=(EVIDENCE,))
            decision = decide(report, **_kwargs(department, prereg), now=FIXED_NOW)
            assert decision.verdict == BLOCK, (
                f"declaring {name}={value!r} bought an ALLOW over contaminated "
                "artifacts: K5 has fired in the permissive direction"
            )
            assert ReasonCode.PROVENANCE_CONTAMINATED_DERIVED in decision.reasons


def test_s2_a_self_declaration_can_only_cost_a_producer_an_allow() -> None:
    """The asymmetry, pinned so it cannot drift.

    A declared contamination reaches ``decide`` only through the integrity
    grade, which the audit computes and the gate re-reads. So a producer can
    talk itself *out* of a promotion and never into one. That is the
    conservative direction; recording it here keeps the K5 reading honest
    rather than silently narrowing it.
    """
    honest = _specimen(
        provenance=replace(CLEAN_PROVENANCE, results_visible_when_authored=True)
    )
    report = report_claim(honest, DISTINGUISHING_CLAIM, name=CLAIM_ID)
    assert report.integrity.grade != CALIBRATED
    decision = decide(report, **_kwargs(honest, _freeze(honest)), now=FIXED_NOW)
    assert decision.verdict == BLOCK
    assert ReasonCode.BATTERY_INTEGRITY_NOT_CALIBRATED in decision.reasons


def test_s2_the_divergence_object_names_the_same_case() -> None:
    """``declared_vs_derived`` and ``decide`` must agree on which case diverges."""
    clean = _specimen()
    divergence = declared_vs_derived(
        clean.provenance,
        _freeze(clean, already_existing=(EVIDENCE,)),
        criteria_applied=_criteria(clean),
        evidence_digest=EVIDENCE_DIGEST,
    )
    assert divergence.diverges is True
    assert divergence.declared_clean is True
    assert divergence.declared_reasons == ()
    assert divergence.derived_reasons
    agreeing = declared_vs_derived(
        clean.provenance,
        _freeze(clean),
        criteria_applied=_criteria(clean),
        evidence_digest=EVIDENCE_DIGEST,
    )
    assert agreeing.diverges is False


@pytest.mark.xfail(
    strict=True,
    reason=(
        "S2-prime is unreachable with one consistent provenance record: any "
        "declared contamination makes audit_department grade the battery "
        "CONTAMINATED, and decide() blocks on the grade, so both gates block "
        "together. The mirror is only expressible when the record shown to "
        "naive_decide differs from the record the audit graded, see the test "
        "below. Design gap, reported rather than papered over."
    ),
)
def test_s2_prime_with_one_consistent_record_declared_dirty_can_be_allowed() -> None:
    department = _specimen(
        provenance=replace(CLEAN_PROVENANCE, frozen_before_execution=False)
    )
    report = report_claim(department, DISTINGUISHING_CLAIM, name=CLAIM_ID)
    naive = naive_decide(report, provenance=department.provenance, claim_id=CLAIM_ID)
    real = decide(report, **_kwargs(department, _freeze(department)), now=FIXED_NOW)
    assert naive.verdict == BLOCK
    assert real.verdict == ALLOW


def test_s2_prime_a_producer_declaring_dirty_over_clean_artifacts_is_allowed() -> None:
    """The mirror, in the one shape the API can express.

    ``naive_decide`` takes the provenance record separately from the report,
    so a producer that hedges, submitting a record declaring unfrozen
    criteria while the battery it actually ran was graded on a clean record,
    is BLOCKed by the naive gate and ALLOWed by the real one, whose reading of
    the artifacts finds nothing wrong. This guards against a gate that is
    merely stricter than the sham rather than different from it. The stronger
    single-record form of S2-prime is unreachable; see the xfail above.
    """
    clean = _BY_NAME["clean"]
    hedged = replace(CLEAN_PROVENANCE, frozen_before_execution=False)
    naive = naive_decide(clean.report, provenance=hedged, claim_id=CLAIM_ID)
    assert naive.verdict == BLOCK
    assert ReasonCode.PROVENANCE_CONTAMINATED_DERIVED in naive.reasons
    assert clean.decide().verdict == ALLOW


# ---------------------------------------------------------------------------
# S3, every reason reproduces its own BLOCK in isolation
# ---------------------------------------------------------------------------


def test_s3_every_reason_produced_anywhere_reproduces_its_own_block_alone() -> None:
    """A reason that cannot re-derive its verdict on its own is a caption.

    Written as one loop over every reason the whole case table produces, so a
    new reason code cannot be added without landing here.
    """
    seen: set[ReasonCode] = set()
    for case in _CASES:
        decision = case.decide()
        for code in decision.reasons:
            seen.add(code)
            kwargs = {k: v for k, v in case.kwargs.items()}
            single = recheck(case.report, only=code, **kwargs, now=FIXED_NOW)
            assert single.verdict == BLOCK, (
                f"{case.name}: {code} does not reproduce its own BLOCK alone"
            )
            assert code in single.reasons
            assert single.complete is False, (
                "a one-check decision must never look like a promotion"
            )
    assert seen, "the case table produced no reasons at all"
    # The two scope codes are exercised by their own test just below, because
    # a scope failure is an argument to decide(), not a property of a report.
    from harness.promotion import _CHECK_FOR_REASON

    uncovered = {str(code) for code in _CHECK_FOR_REASON} - {str(code) for code in seen}
    assert uncovered == {
        str(ReasonCode.SCOPE_MISSING),
        str(ReasonCode.SCOPE_WIDENED),
    }, f"a reproducible reason code is exercised nowhere in this file: {uncovered}"


@pytest.mark.parametrize(
    "requested, expected",
    [
        pytest.param("", ReasonCode.SCOPE_MISSING, id="scope-missing"),
        pytest.param("   ", ReasonCode.SCOPE_MISSING, id="scope-blank"),
        pytest.param(
            "distinguishes the toy target from anything at all",
            ReasonCode.SCOPE_WIDENED,
            id="scope-widened",
        ),
    ],
)
def test_s3_the_two_scope_codes_also_reproduce_their_own_block_alone(
    requested, expected
) -> None:
    """Scope is free text, so containment is undecidable and identity is
    demanded; both refusals are reasons in their own right, not one blurred
    reason, and each must re-derive on its own."""
    case = _BY_NAME["clean"]
    kwargs = {**case.kwargs, "requested_scope": requested}
    decision = decide(case.report, **kwargs, now=FIXED_NOW)
    assert decision.verdict == BLOCK
    assert decision.reasons == (expected,)
    single = recheck(case.report, only=expected, **kwargs, now=FIXED_NOW)
    assert single.verdict == BLOCK
    assert expected in single.reasons
    assert single.complete is False


@pytest.mark.parametrize(
    "code", [ReasonCode.INTEGRITY_NOT_ESTABLISHED, ReasonCode.GATE_CHECK_ERRORED]
)
def test_s3_decision_level_codes_refuse_to_be_rechecked_in_isolation(code) -> None:
    """The two codes that are properties of the decision, not of one check."""
    with pytest.raises(PromotionError):
        recheck(_BY_NAME["clean"].report, only=code, **_BY_NAME["clean"].kwargs)


# ---------------------------------------------------------------------------
# S4, (BLOCK == having reasons), for every input including garbage
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", _PARAMS)
def test_s4_the_verdict_and_the_reasons_never_disagree(case: Case) -> None:
    decision = case.decide()
    _invariant(decision)
    assert decision.verdict == case.expected, (
        f"{case.name}: expected {case.expected}, got {decision.verdict} with "
        f"{[str(r) for r in decision.reasons]}"
    )
    assert decision.checks_run == CHECKS
    assert decision.complete is True


_GARBAGE = [
    pytest.param(None, id="none"),
    pytest.param("", id="empty-string"),
    pytest.param(0, id="zero"),
    pytest.param(object(), id="bare-object"),
    pytest.param([1, 2, 3], id="list"),
    pytest.param(float("nan"), id="nan"),
]


@pytest.mark.parametrize("junk", _GARBAGE)
def test_s4_a_garbage_report_blocks_instead_of_raising(junk) -> None:
    decision = decide(junk, **_BY_NAME["clean"].kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.verdict == BLOCK


_ARGUMENTS = [
    "prereg",
    "criteria_applied",
    "evidence_digest",
    "current_evidence_digest",
    "claim_id",
    "producer_id",
    "verifier_id",
    "requested_scope",
]

_ARGUMENTS_THAT_BLOCK_ON_JUNK = list(_ARGUMENTS)


@pytest.mark.parametrize("junk", _GARBAGE)
@pytest.mark.parametrize("field_name", _ARGUMENTS)
def test_s4_garbage_in_any_single_argument_keeps_the_invariant_without_raising(
    field_name, junk
) -> None:
    """S4 as the document froze it: nothing raises out of ``decide``, and the
    verdict never disagrees with the reasons, whatever is handed in."""
    kwargs = {**_BY_NAME["clean"].kwargs, field_name: junk}
    decision = decide(_BY_NAME["clean"].report, **kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.checks_run == CHECKS


@pytest.mark.parametrize("junk", _GARBAGE)
@pytest.mark.parametrize("field_name", _ARGUMENTS_THAT_BLOCK_ON_JUNK)
def test_s4_garbage_in_a_load_bearing_argument_blocks(field_name, junk) -> None:
    kwargs = {**_BY_NAME["clean"].kwargs, field_name: junk}
    decision = decide(_BY_NAME["clean"].report, **kwargs, now=FIXED_NOW)
    assert decision.verdict == BLOCK, f"{field_name}={junk!r} was waved through"


@pytest.mark.parametrize("junk", [None, 0, object(), [1, 2, 3], float("nan")])
@pytest.mark.parametrize("field_name", ["producer_id", "verifier_id"])
def test_s4_an_ill_formed_party_identifier_blocks(field_name, junk) -> None:
    """A party nobody set is an unknown, and an unknown blocks.

    This began as a measured gap and is kept as a regression pin because the
    defect was the exact shape this module argues against. ``_check_independence``
    used to coerce with ``str()`` before comparing, and ``None``, ``0``, ``[]``
    and a bare ``object()`` all stringify to something non-empty and mutually
    unequal, so a caller who named no parties at all read as two independent
    ones and the check returned ``PASS``. Default-open, in the one file whose
    thesis is that default-open must be structurally impossible.

    ``Boundary.promote()`` never reached it (``_checked_id`` refuses these
    first), which is why it survived the smoke run: the bug lived only on the
    direct ``decide()`` path, and the happy path went through the door.
    """
    kwargs = {**_BY_NAME["clean"].kwargs, field_name: junk}
    decision = decide(_BY_NAME["clean"].report, **kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.verdict == BLOCK, f"{field_name}={junk!r} was waved through"
    assert ReasonCode.INTEGRITY_NOT_ESTABLISHED in decision.reasons
    assert decision.check_status["independence"] != "pass"


@pytest.mark.parametrize("junk", _GARBAGE)
def test_s4_everything_garbage_at_once_blocks_instead_of_raising(junk) -> None:
    decision = decide(
        junk,
        prereg=junk,
        criteria_applied=junk,
        evidence_digest=junk,
        current_evidence_digest=junk,
        claim_id=junk,
        producer_id=junk,
        verifier_id=junk,
        requested_scope=junk,
        now=FIXED_NOW,
    )
    _invariant(decision)
    assert decision.verdict == BLOCK


def test_s4_a_report_whose_own_fields_are_garbage_blocks() -> None:
    """A ``ClaimReport``-shaped object with nonsense inside it, not beside it."""
    mangled = replace(
        _BY_NAME["clean"].report, verdict=object(), integrity=object(), scope=object()
    )
    decision = decide(mangled, **_BY_NAME["clean"].kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.verdict == BLOCK
    assert ReasonCode.GATE_CHECK_ERRORED in decision.reasons
    assert decision.errors, "a check that raised must be named in errors"


# ---------------------------------------------------------------------------
# S5, default-open sweep. The mutation most likely to be a real bug.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _StubIntegrity:
    """An integrity report whose grade is whatever the sweep hands it."""

    grade: Any
    checks: tuple = ()

    def to_dict(self) -> dict:
        return {"grade": self.grade}


_NON_CALIBRATED_GRADES = [g for g in GRADES if g != CALIBRATED]

_BAD_GRADES = (
    [
        pytest.param(None, id="none"),
        pytest.param("", id="empty"),
        pytest.param("CALIBRATED ", id="trailing-space"),
        pytest.param(" CALIBRATED", id="leading-space"),
        pytest.param("calibrated", id="lowercase"),
        pytest.param("GOOD", id="unrelated-word"),
        pytest.param(True, id="true"),
        pytest.param(object(), id="bare-object"),
    ]
    + [pytest.param(g, id=f"grade-{g.lower()}") for g in _NON_CALIBRATED_GRADES]
)


@pytest.mark.parametrize("grade", _BAD_GRADES)
def test_s5_anything_that_is_not_exactly_calibrated_blocks(grade) -> None:
    """Default-open, swept.

    ``"CALIBRATED "`` and ``"calibrated"`` are the shapes a careless
    serialisation round-trip produces, and each of them passing would be a
    silent promotion of every claim in the tree. Nothing but the exact
    constant may clear this check.
    """
    report = replace(_BY_NAME["clean"].report, integrity=_StubIntegrity(grade=grade))
    decision = decide(report, **_BY_NAME["clean"].kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.verdict == BLOCK, f"grade {grade!r} was accepted as CALIBRATED"
    assert {
        ReasonCode.BATTERY_INTEGRITY_NOT_CALIBRATED,
        ReasonCode.INTEGRITY_NOT_ESTABLISHED,
    } & set(decision.reasons), decision.reasons


def test_s5_the_one_grade_that_clears_the_check_is_the_named_constant() -> None:
    report = replace(_BY_NAME["clean"].report, integrity=_StubIntegrity(grade=CALIBRATED))
    assert decide(report, **_BY_NAME["clean"].kwargs, now=FIXED_NOW).verdict == ALLOW


@pytest.mark.parametrize(
    "blank_field",
    ["evidence_digest", "current_evidence_digest", "claim_id", "producer_id", "verifier_id"],
)
def test_s5_silence_on_a_load_bearing_field_blocks_rather_than_passes(blank_field) -> None:
    """An UNKNOWN check leaves a reason behind; it never clears anything."""
    kwargs = {**_BY_NAME["clean"].kwargs, blank_field: ""}
    decision = decide(_BY_NAME["clean"].report, **kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.verdict == BLOCK
    assert ReasonCode.INTEGRITY_NOT_ESTABLISHED in decision.reasons


@pytest.mark.parametrize("blank_field", ["evidence_digest", "current_evidence_digest"])
def test_s5_a_whitespace_only_digest_blocks_but_not_as_silence(blank_field) -> None:
    """A measured inconsistency, pinned in the safe direction.

    ``_check_claim_identity`` and ``_check_independence`` strip before testing
    for emptiness; ``_check_evidence_freshness`` does not, so a
    whitespace-only digest is read as a *different* digest rather than as an
    absent one. The crossing is refused either way, only the reason code
    differs, which is why this is pinned rather than left failing.
    """
    kwargs = {**_BY_NAME["clean"].kwargs, blank_field: "   "}
    decision = decide(_BY_NAME["clean"].report, **kwargs, now=FIXED_NOW)
    _invariant(decision)
    assert decision.verdict == BLOCK
    assert decision.reasons == (ReasonCode.EVIDENCE_STALE,)


# ---------------------------------------------------------------------------
# S6, anti-paranoia. A referee that only says no is the K3 death condition.
# ---------------------------------------------------------------------------


def test_s6_an_alarming_looking_case_is_nevertheless_allowed() -> None:
    """Six undeclared provenance fields, a detector with a measured floor, and
    no support of any other kind, and none of it is a defect.

    This is the case ``ReferenceClaim`` exists to catch one layer down: a
    battery shown only one answer cannot be told apart from one that always
    gives it. If this test goes red, the gate has become an alarm that is
    always on.
    """
    case = _BY_NAME["alarming-but-fine"]
    assert case.report.integrity.provenance_unknowns, "the specimen declared too much"
    assert case.report.integrity.unseen_lesions == ("small",), (
        "the detector floor is the point of this case"
    )
    decision = case.decide()
    assert decision.verdict == ALLOW, [str(r) for r in decision.reasons]
    assert decision.blind_spots, "an allowance without its blind spots printed"


def test_s6_the_blocked_fraction_over_the_case_table_stays_under_the_k3_ceiling() -> None:
    """K3: more than 60% of the case set blocking is a pre-registered kill.

    Measured over the whole table, the attacks and the ordinary well-formed
    submissions together, because a fraction taken over attacks alone would
    be a number about the attacks.
    """
    verdicts = [case.decide().verdict for case in _CASES]
    blocked = sum(1 for v in verdicts if v == BLOCK)
    fraction = blocked / len(verdicts)
    assert fraction <= 0.60, (
        f"{blocked}/{len(verdicts)} = {fraction:.1%} of the case table blocks; "
        "K3 fires above 60%"
    )
    assert blocked, "a table nothing blocks measures nothing either"


# ---------------------------------------------------------------------------
# S7, a claim-side failure, with the verifier side spotless
# ---------------------------------------------------------------------------


def test_s7_a_claim_shared_with_a_rival_blocks_on_the_claim_side_only() -> None:
    case = _BY_NAME["claim-shared-with-a-rival"]
    assert case.report.claim_status == "shared"
    assert case.report.integrity.grade == CALIBRATED
    decision = case.decide()
    assert decision.verdict == BLOCK
    assert decision.reasons == (ReasonCode.CLAIM_NOT_DISTINGUISHING,)


def test_s7_the_claim_side_code_is_disjoint_from_the_verifier_side_codes() -> None:
    """Two axes, never conflated, the requirement docs/20 built and this
    gate must not undo. A single code covering both would make "the claim is
    weak" and "the referee is weak" indistinguishable to any reader counting
    codes."""
    claim_side = set(_BY_NAME["claim-shared-with-a-rival"].decide().reasons)
    verifier_side = set(_BY_NAME["derived-contaminated"].decide().reasons) | set(
        _BY_NAME["dropped-hardest-lesion"].decide().reasons
    )
    assert claim_side and verifier_side
    assert claim_side.isdisjoint(verifier_side), claim_side & verifier_side


# ---------------------------------------------------------------------------
# S8, identity binding and staleness
# ---------------------------------------------------------------------------


def test_s8_a_report_presented_for_a_different_claim_blocks() -> None:
    """Otherwise a good report could be stapled to any claim at all."""
    decision = _BY_NAME["presented-for-another-claim"].decide()
    assert decision.verdict == BLOCK
    assert ReasonCode.CLAIM_IDENTITY_MISMATCH in decision.reasons


def test_s8_evidence_that_moved_after_the_report_was_written_blocks() -> None:
    decision = _BY_NAME["evidence-moved-underneath"].decide()
    assert decision.verdict == BLOCK
    assert decision.reasons == (ReasonCode.EVIDENCE_STALE,)
    assert decision.digests["evidence_at_report"] != decision.digests["evidence_now"]


def test_s8_a_claim_graded_by_its_own_producer_blocks() -> None:
    """`a claim may not promote itself`, enforced rather than asserted in prose."""
    decision = _BY_NAME["graded-by-its-own-producer"].decide()
    assert decision.verdict == BLOCK
    assert decision.reasons == (ReasonCode.SELF_VERIFIED,)


# ---------------------------------------------------------------------------
# S9, every decision carries the audit's declared blind spots
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", _PARAMS)
def test_s9_every_decision_carries_the_audits_declared_blind_spots(case: Case) -> None:
    """An allowance is exactly when a reader stops looking for the limits, so
    the limits ride on the ALLOWs too."""
    payload = case.decide().to_dict()
    named = {mode.name for mode in AUDIT_BLIND_SPOTS}
    assert named
    for name in named:
        assert name in payload["blind_spots"], f"blind spot {name!r} did not travel"


def test_s9_the_naive_gate_carries_them_too() -> None:
    payload = _BY_NAME["clean"].naive().to_dict()
    for mode in AUDIT_BLIND_SPOTS:
        assert mode.name in payload["blind_spots"]


# ---------------------------------------------------------------------------
# The boundary on disk
# ---------------------------------------------------------------------------


def _promote(boundary: Boundary, case: Case, claim=None):
    kwargs = dict(case.kwargs)
    kwargs.pop("claim_id")
    kwargs.pop("producer_id")
    return boundary.promote(
        CLAIM_RECORD if claim is None else claim, case.report, now=FIXED_NOW, **kwargs
    )


def test_a_producer_may_not_reach_the_promoted_side(tmp_path: Path) -> None:
    """A speed bump, and the module says so, but an accidental reach must
    still be impossible, so that a deliberate one shows up in a diff."""
    view = ProducerView(Boundary(tmp_path))
    assert view.submit(CLAIM_RECORD).exists()
    for reached in ("promote", "decisions", "root", "_dir"):
        with pytest.raises(PromotionError):
            getattr(view, reached)


def test_the_boundary_writes_a_decision_whether_it_allows_or_blocks(tmp_path: Path) -> None:
    """A boundary that logged only its allowances would make its refusals
    unauditable, which is the failure this whole layer is about."""
    boundary = Boundary(tmp_path)
    allowed = _promote(boundary, _BY_NAME["clean"])
    assert allowed.verdict == ALLOW
    assert len(boundary.decisions()) == 1
    blocked = _promote(boundary, _BY_NAME["dropped-hardest-lesion"])
    assert blocked.verdict == BLOCK
    assert len(boundary.decisions()) == 2
    assert (tmp_path / "blocked" / f"{CLAIM_ID}.json").exists()
    assert not (tmp_path / "promoted" / f"{CLAIM_ID}.json").exists(), (
        "a BLOCK left an earlier allowance standing"
    )


def test_a_clean_boundary_audits_without_discrepancies(tmp_path: Path) -> None:
    boundary = Boundary(tmp_path)
    _promote(boundary, _BY_NAME["clean"])
    assert (tmp_path / "promoted" / f"{CLAIM_ID}.json").exists()
    assert audit(boundary) == ()


def test_the_audit_catches_a_file_written_past_the_door(tmp_path: Path) -> None:
    """The API claim is worth little; this is what makes the boundary real."""
    boundary = Boundary(tmp_path)
    _promote(boundary, _BY_NAME["clean"])
    (tmp_path / "promoted" / "smuggled.json").write_text(
        json.dumps({"claim_id": "smuggled", "producer_id": PRODUCER}), encoding="utf-8"
    )
    problems = audit(boundary)
    assert any("smuggled" in p and "past the door" in p for p in problems), problems


def test_the_audit_catches_a_promoted_claim_that_changed_after_crossing(tmp_path: Path) -> None:
    boundary = Boundary(tmp_path)
    _promote(boundary, _BY_NAME["clean"])
    (tmp_path / "promoted" / f"{CLAIM_ID}.json").write_text(
        json.dumps({**CLAIM_RECORD, "statement": "quietly reworded after crossing"}),
        encoding="utf-8",
    )
    problems = audit(boundary)
    assert any("changed after crossing" in p for p in problems), problems


def test_the_boundary_refuses_an_identifier_that_would_escape_it(tmp_path: Path) -> None:
    boundary = Boundary(tmp_path)
    for bad in ("../escape", "with/slash", "", "a" * 200):
        with pytest.raises(PromotionError):
            boundary.submit({"claim_id": bad, "producer_id": PRODUCER})


def test_a_decision_round_trips_through_strict_json(tmp_path: Path) -> None:
    """Every reason must survive as a string: a code nothing downstream can
    count is prose again."""
    for case in _CASES:
        decision = case.decide()
        text = json.dumps(decision.to_dict(), allow_nan=False, sort_keys=True)
        payload = json.loads(text)
        assert payload["verdict"] in (ALLOW, BLOCK)
        assert payload["policy_version"] == POLICY_VERSION
        assert payload["reasons"] == [str(r) for r in decision.reasons]
        for code in decision.reasons:
            assert isinstance(str(code), str)
            assert ReasonCode(str(code)) is code
        assert isinstance(payload["complete"], bool)


def test_every_reason_code_is_a_distinct_stable_string() -> None:
    values = [str(code) for code in ReasonCode]
    assert len(values) == len(set(values)) == 11
    assert all(value == value.strip().lower() for value in values)


# ---------------------------------------------------------------------------
# Determinism
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("case", _PARAMS)
def test_the_same_inputs_decide_the_same_way_twice(case: Case) -> None:
    """A gate whose answer depends on when you asked cannot be audited."""
    first, second = case.decide(), case.decide()
    assert first.to_dict() == second.to_dict()
    loose_a = decide(case.report, **case.kwargs)
    loose_b = decide(case.report, **case.kwargs)
    assert loose_a.verdict == loose_b.verdict
    assert loose_a.reasons == loose_b.reasons
    assert dict(loose_a.check_status) == dict(loose_b.check_status)


def test_the_digest_is_order_independent_and_refuses_non_finite_floats() -> None:
    assert digest({"a": 1, "b": 2}) == digest({"b": 2, "a": 1})
    with pytest.raises(ValueError):
        digest({"x": float("nan")})


def test_the_findings_keys_are_the_ones_the_gate_maps_onto_reasons() -> None:
    """The two layers agree through keys, never through wording."""
    clean = _specimen()
    keys = {
        key
        for key, _ in derived_findings(
            _freeze(clean, already_existing=(EVIDENCE,)),
            criteria_applied={"different": "criteria"},
            evidence_digest=EVIDENCE_DIGEST,
        )
    }
    assert keys == {EVIDENCE_VISIBLE_AT_FREEZE, CRITERIA_DRIFT}


# ---------------------------------------------------------------------------
# The gate's own declared blind spot, measured rather than asserted.
#
# Everything above this line tests what the gate catches. This section tests
# what it does not, because a gate that only ever demonstrates its successes
# is the thing `docs/20` §4 exists to prevent, one level up.
# ---------------------------------------------------------------------------


def _hollow_specimen():
    """A battery that is measurably empty and grades ``CALIBRATED`` anyway.

    Reconstructed from a held-out exercise: an independent party, told only
    what `harness/protocol.py` and `harness/README.md` say and forbidden from
    reading `integrity.py` or its sham catalog, was asked to build a battery
    that the audit would grade ``CALIBRATED`` while being unable to kill
    anything. It succeeded on the first attempt with no adaptation.

    The mechanism is the one thing no mechanical check in the audit reaches:
    **rivals that are not near the target**. Nothing requires a rival to share
    the structure the claim leans on, so a rival can differ in gross, arbitrary
    ways, the modus tollens never bites, and any claim of the form
    ``anything AND target_only_property`` distinguishes.
    """

    @dataclass(frozen=True)
    class _Sub:
        name: str
        base: float

        def describe(self) -> str:
            return f"signal at {self.base}"

        def payload(self):
            # Exactly zero-mean over 29 samples when base is 0, so the target
            # has the property and every rival misses it by its own offset.
            return lambda n: self.base + (0.0 if n == 0 else (-1.0) ** n)

    @dataclass(frozen=True)
    class _Decoy:
        name: str = "rectify"

        def describe(self) -> str:
            return "replaces the signal with its absolute value"

        def substitute(self, payload):
            return lambda n: abs(payload(n))

    @dataclass(frozen=True)
    class _Sur:
        name: str = "flat"

        def describe(self) -> str:
            return "a null signal carrying no structure"

        def sample(self):
            return lambda n: 0.7

    @dataclass(frozen=True)
    class _Les:
        name: str
        magnitude: float

        def describe(self) -> str:
            return f"adds a DC offset of {self.magnitude}"

        def apply(self, payload):
            return lambda n: payload(n) + self.magnitude

    def zero_mean(f) -> bool:
        return abs(sum(f(n) for n in range(29)) / 29.0) < 1e-9

    def bounded(f) -> bool:
        return all(abs(f(n)) <= 100.0 for n in range(29))

    battery = Battery(
        name="hollow",
        target=_Sub("target", 0.0),
        # Not near the target in any way a claim could lean on.
        rivals=(_Sub("ramp", 40.0), _Sub("const", 12.5), _Sub("geom", 90.0)),
        decoys=(_Decoy(),),
        surrogates=(_Sur(),),
        lesions=(_Les("dc-1e-3", 0.001), _Les("dc-0.5", 0.5), _Les("dc-5", 5.0)),
    )
    return Department(
        name="hollow",
        summary="a structurally admissible battery that can refute nothing",
        battery=battery,
        door="docs/21-forward-deployed-verification.md",
        scope="nothing: this specimen exists to be promoted and to be wrong",
        detectors=(
            # Independent of the claim on purpose, since 2026-08-09. The
            # original detector here was ``lambda f: not zero_mean(f)``, the
            # reference claim negated, and ``detector-claim-agreement`` now
            # catches exactly that, which graded this specimen
            # DETECTOR_INADEQUATE and made the negative result below
            # unreachable for the wrong reason. The hollowness this file is
            # about never lived in the detector; it lives in the rivals. This
            # detector has real power (every DC offset lifts the peak past
            # 1.0) and real specificity (the clean signal peaks exactly at
            # 1.0), and it agrees with ``zero-mean`` on the surrogate and the
            # decoy, so it is nobody's negation.
            NamedDetector(
                "peak-detector",
                lambda f: max(f(n) for n in range(29)) > 1.0 + 1e-9,
                note="fires when the signal's peak rises above the clean bound",
            ),
        ),
        reference_claims=(
            ReferenceClaim(name="bounded", claim=bounded, distinguishes=False),
            ReferenceClaim(name="zero-mean", claim=zero_mean, distinguishes=True),
        ),
        provenance=Provenance(
            authored_by="held-out-contractor",
            independent_of_subject_author=True,
            results_visible_when_authored=False,
            frozen_before_execution=True,
            edited_after_observing_failures=False,
            oracle_calls_subject=False,
            instruments_share_critical_dependency=False,
        ),
    ), zero_mean


def test_a_hollow_battery_still_grades_calibrated() -> None:
    """The audit's limit, restated here so the next test cannot be misread."""
    dept, _ = _hollow_specimen()
    report = audit_department(dept)
    assert report.grade == CALIBRATED
    assert not [c for c in report.checks if c.status == FAIL]


def test_the_gate_promotes_a_worthless_claim_from_a_hollow_battery() -> None:
    """**The gate inherits every blind spot of the audit it consumes.**

    This is the most important negative result in this file, and it is pinned
    rather than mentioned. ``decide`` requires the grade to be ``CALIBRATED``;
    it does not and cannot re-derive whether that grade was *earned*. So a
    battery whose rivals are strawmen promotes a claim with an arbitrary
    conjunct smuggled into it, here, literally an astrological one, with an
    empty reason list and nothing anywhere reading ``dangerous``.

    Forward-deployed verification therefore does **not** make a hollow referee
    safe. It makes an *unrecorded change* to a referee visible. Those are
    different properties and only the second is claimed.

    If this test ever fails, somebody has taught the gate to audit the
    substance of a battery rather than its process, update `docs/21` §8 and
    this docstring before deleting the pin.
    """
    dept, zero_mean = _hollow_specimen()

    def astrology_and_zero_mean(f) -> bool:
        return bool("the author is trustworthy") and zero_mean(f)

    claim_report = report_claim(dept, astrology_and_zero_mean, name="astrology")
    assert claim_report.claim_status == "distinguishes"
    assert claim_report.integrity.grade == CALIBRATED
    assert claim_report.dangerous is False

    criteria = {"battery": "hollow", "lesions": ["dc-1e-3", "dc-0.5", "dc-5"]}
    prereg = Preregistration.freeze(
        criteria=criteria,
        criteria_id="hollow-v1",
        author_id="held-out-contractor",
        frozen_at="2026-08-09T09:00:00Z",
        already_existing_evidence=(),
    )
    evidence = digest({"payload": "hollow-evidence"})
    decision = decide(
        claim_report,
        prereg=prereg,
        criteria_applied=criteria,
        evidence_digest=evidence,
        current_evidence_digest=evidence,
        claim_id="astrology",
        producer_id="toy-lab",
        verifier_id="held-out-contractor",
        requested_scope=dept.scope,
        now=FIXED_NOW,
    )
    assert decision.verdict == ALLOW
    assert decision.reasons == ()


def test_the_two_modes_the_held_out_exercise_found_are_in_the_catalog() -> None:
    """`docs/20` §8 set the scoring rule: a mode the catalog lacks is a hole.

    The held-out contractor's battery was hollow in two ways `SHAM_MODES` did
    not name, rivals too distant to make a shared claim embarrassing, and a
    detector that is the claim negated. Both went into the catalog with
    ``caught_by=None``.

    One of the two has since been closed and the other has not, and this test
    is where the difference is recorded. ``detector-claim-agreement``
    (``docs/23`` §4.1) catches the detector-is-the-claim mode, and its first
    catch was this very specimen, a battery authored by an independent party
    before that check existed, which is the only reason the catch counts for
    anything. ``distant-rivals`` is still open: the check built for it
    measures the distance and reports it, and the threshold frozen before the
    calibration was read sits above the whole measured range, so it acts on
    nothing (``docs/23`` §8).
    """
    blind = {mode.name for mode in AUDIT_BLIND_SPOTS}
    assert "distant-rivals" in blind
    assert "detector-is-the-claim" not in blind, (
        "detector-is-the-claim is caught by detector-claim-agreement since "
        "2026-08-09; if it has gone blind again, docs/23 §8 is now wrong"
    )

    distant = next(m for m in SHAM_MODES if m.name == "distant-rivals")
    assert distant.caught_by is None
    assert distant.countermeasure.strip(), "a blind mode with no countermeasure is a shrug"

    caught = next(m for m in SHAM_MODES if m.name == "detector-is-the-claim")
    assert caught.caught_by == "detector-claim-agreement"
