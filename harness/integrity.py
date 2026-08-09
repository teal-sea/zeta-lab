"""``harness.integrity`` — the referee, refereed.

Two incidents forced this module into existence, and both are in the tree.

The first is the sham battery that department #2 replaced (commit
``431cc74``): decoys, surrogates and lesions that were placeholders written
to the conformance tests' shapes — a surrogate returning ``[1, 2, 3]`` — and
rivals whose payloads carried a field a claim could read as a label. It was
structurally complete. It validated. It passed the conformance suite of its
day. It could never have killed anything, and a human caught it, not a test.

The second is a measurement: the dossier resumption benchmark (ROADMAP,
2026-08-09) ran blinded agents against planted failures from this
repository's own incident history and found they caught *recorded
contradictions* nearly everywhere while reliably missing *hollow
verification* — a structurally admissible battery whose instruments are
placeholders, a battery PASS read as substantive truth, an instrument whose
stated precondition never ran.

The distinction both incidents draw is the one this module makes
mechanical where it can be made mechanical:

    **the structural audit catches missing instruments; this audit catches
    measurably empty ones; what remains is named, not hidden.**

Two axes, never conflated
-------------------------
A claim outcome and the trustworthiness of the battery that produced it are
different measurements, and a report that shows one without the other is how
a green result from a hollow referee gets believed. This module therefore
produces two things and always pairs them:

* a **claim outcome** — the harness's own vocabulary (distinguishes /
  shared / does-not-fire / inconclusive), deliberately *not* a truth
  vocabulary, because per the honest-scope rule the harness adjudicates
  only whether a demonstration is about its subject;
* a **battery integrity grade** — one of five, each with crisp semantics:

  - ``CALIBRATED`` — every mechanical check passed and detector power was
    measured; named blind spots may remain, and they travel with the grade.
  - ``DETECTOR_INADEQUATE`` — the structure is present but no declared
    detector carries information: each one either fires on the clean probe
    (an alarm that is always on) or notices no planted violation at all.
  - ``UNMEASURED`` — the audit could not run a load-bearing measurement
    (typically: no declared detectors on a bundle that bypassed admission).
  - ``CONTAMINATED`` — the provenance record *declares* a condition under
    which the pass probability cannot be taken at face value (criteria
    authored after results were visible, thresholds unfrozen, tests edited
    after failures). Nothing mechanical can restore a contaminated pass.
  - ``HOLLOW`` — a mechanical check failed: the battery could not kill
    anything, or an instrument is measurably empty. A claim verdict from a
    hollow battery is worthless whatever colour it is.

There is deliberately no scalar score. A number would invite exactly the
misreading — "integrity 0.87" — that a named failing check makes impossible.

What this audit cannot see
--------------------------
:data:`SHAM_MODES` is the catalog of known ways a battery can be hollow,
and for each mode it records either the check that catches it or the fact
that no mechanical check can — with the countermeasure named. The entries
with ``caught_by=None`` are the audit's own declared blind spots; they are
printed on every report, because an audit that hides its own limits is the
thing this module exists to prevent.

Like :mod:`harness.protocol`, this module is domain-agnostic in the strict
sense and sits under the same three seam checks.
"""

from __future__ import annotations

import json
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Final

from harness.protocol import (
    Battery,
    BatteryVerdict,
    ClaimOutcome,
    Department,
    battery_reasons,
    department_reasons,
    run_battery,
    run_detector,
)
from harness.provenance import (
    contamination_reasons,
    dependence_reasons,
    undeclared_fields,
)

__all__ = [
    "PASS",
    "FAIL",
    "UNKNOWN",
    "CALIBRATED",
    "DETECTOR_INADEQUATE",
    "UNMEASURED",
    "CONTAMINATED",
    "HOLLOW",
    "GRADES",
    "CheckResult",
    "IntegrityReport",
    "ClaimReport",
    "ShamMode",
    "SHAM_MODES",
    "AUDIT_BLIND_SPOTS",
    "audit_department",
    "payloads_same",
    "report_claim",
]

# ---------------------------------------------------------------------------
# Statuses and grades
# ---------------------------------------------------------------------------

PASS: Final = "pass"
FAIL: Final = "fail"
#: The audit could not decide — the measurement did not run, or is not
#: mechanically decidable for this department's shapes. Unknown is never
#: silently treated as pass.
UNKNOWN: Final = "unknown"

CALIBRATED: Final = "CALIBRATED"
DETECTOR_INADEQUATE: Final = "DETECTOR_INADEQUATE"
UNMEASURED: Final = "UNMEASURED"
CONTAMINATED: Final = "CONTAMINATED"
HOLLOW: Final = "HOLLOW"

GRADES: Final = (CALIBRATED, DETECTOR_INADEQUATE, UNMEASURED, CONTAMINATED, HOLLOW)

#: Historical probe defaults, identical to the conformance suite's: an
#: instrument that declares no ``probe`` is poked with department #1's
#: shapes, exactly as ``compiler/FINDINGS.md`` §7 standardised.
_HISTORICAL_DECOY_PROBE: Final = tuple(range(2, 60))
_HISTORICAL_LESION_PROBE: Final = ()

#: Checks whose failure means the battery could not kill anything or an
#: instrument is measurably empty — the HOLLOW class.
_HOLLOW_CHECKS: Final = (
    "structural",
    "teeth-always-true",
    "teeth-always-false",
    "rivals-answer",
    "calibration-both-directions",
    "calibration-rederived",
    "killed-for-the-stated-reason",
    "decoys-move-their-probe",
    "lesions-plant-something",
    "lesion-magnitudes-span-scales",
    "payload-symmetry",
)


@dataclass(frozen=True)
class CheckResult:
    """One named integrity check: what was measured and what it showed."""

    name: str
    status: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"name": self.name, "status": self.status, "evidence": self.evidence}


# ---------------------------------------------------------------------------
# The sham catalog — what the audit catches, and what it admits it cannot
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ShamMode:
    """One known way a structurally valid battery can be hollow."""

    name: str
    description: str
    #: The integrity check that catches this mode, or ``None`` when no
    #: mechanical check can. ``None`` entries are the audit's declared
    #: blind spots and are carried on every report.
    caught_by: str | None
    countermeasure: str


SHAM_MODES: Final[tuple[ShamMode, ...]] = (
    ShamMode(
        name="placeholder-instruments",
        description=(
            "decoys, surrogates or lesions written to satisfy the structural "
            "checks' shapes while measuring nothing (the 431cc74 sham's "
            "surrogate returned [1, 2, 3])"
        ),
        caught_by="lesions-plant-something",
        countermeasure=(
            "probe checks catch identity instruments; semantic emptiness that "
            "still changes the probe needs measured magnitudes or review"
        ),
    ),
    ShamMode(
        name="constant-true-detector",
        description=(
            "a detector that fires on everything: perfect sensitivity on every "
            "lesion, and no information in any alarm"
        ),
        caught_by="detector-specificity",
        countermeasure="show the detector the clean probe as well as the lesioned ones",
    ),
    ShamMode(
        name="constant-false-detector",
        description="a detector that never fires: its silence on real data is blindness, not absence",
        caught_by="detector-power",
        countermeasure="measure power against planted violations; consult the measurement",
    ),
    ShamMode(
        name="target-as-rival",
        description=(
            "a rival that is the target under another name: nothing can ever "
            "distinguish, and the battery's strictness is an artifact"
        ),
        caught_by="calibration-rederived",
        countermeasure=(
            "a reference claim the battery is expected to pass stops passing; "
            "name-identity is also refused structurally"
        ),
    ),
    ShamMode(
        name="inert-lesion",
        description="a lesion that plants nothing, so every detector shown it reports blindness to a violation that was never there",
        caught_by="lesions-plant-something",
        countermeasure="apply(probe) must differ from probe (the strengthened rule from compiler/FINDINGS.md §7)",
    ),
    ShamMode(
        name="dropped-hardest-lesion",
        description=(
            "silently removing the lesion the detectors struggle with, leaving "
            "an easier battery under the same name"
        ),
        caught_by=None,
        countermeasure=(
            "no mechanical check can know what was meant to be there; pin the "
            "lesion set in tests, declare frozen_before_execution in provenance"
        ),
    ),
    ShamMode(
        name="key-asymmetry-label-leak",
        description=(
            "rival payloads carry a field the target's lack (or vice versa), "
            "so a claim can read identity instead of measuring (the 431cc74 "
            "sham's virtual_a_p field)"
        ),
        caught_by="payload-symmetry",
        countermeasure="target and rival payloads must be structurally indistinguishable",
    ),
    ShamMode(
        name="value-encoded-label-leak",
        description=(
            "identity encoded in the *values* of a shared field, "
            "indistinguishable from honest data by any structural comparison"
        ),
        caught_by=None,
        countermeasure=(
            "independent authorship of battery content (provenance); a claim "
            "author who never saw the payloads cannot have keyed on them"
        ),
    ),
    ShamMode(
        name="co-designed-calibration",
        description=(
            "reference claims and instruments authored together so every "
            "mechanical check passes while the pair measures nothing"
        ),
        caught_by=None,
        countermeasure=(
            "independent authorship, held-out mutations authored by a party "
            "that has not seen the detectors"
        ),
    ),
    ShamMode(
        name="contaminated-preregistration",
        description=(
            "criteria authored after their results were visible, so the pass "
            "probability given the seen data was near 1 (REDTEAM.md W2)"
        ),
        caught_by="provenance-contamination",
        countermeasure=(
            "a truthful declaration is caught here; an untruthful one is caught "
            "only where a preregistration record exists, because "
            "harness.preregistration recomputes the condition from evidence "
            "digests instead of reading the flag (docs/21 §10.1). Without such "
            "a record the boundary stands: a lying provenance record is outside "
            "mechanical reach, which is the point of keeping it human-attested"
        ),
    ),
    ShamMode(
        name="distant-rivals",
        description=(
            "rivals that do not share the structure the claim leans on — they "
            "differ from the target in gross, arbitrary ways, so the modus "
            "tollens never bites and any claim of the form 'anything AND a "
            "target-only property' distinguishes"
        ),
        caught_by=None,
        countermeasure=(
            "no mechanical check knows how near a rival must be; that is the "
            "department's substantive judgment. Declare, per rival, the "
            "structure it shares and the property it lacks, and have a party "
            "that did not author the battery say whether the pair is close "
            "enough to make a shared claim embarrassing"
        ),
    ),
    ShamMode(
        name="detector-is-the-claim",
        description=(
            "the detector whose power is measured is the claim under test, "
            "negated: power and specificity both pass while the detector "
            "carries no information the claim did not already assert, because "
            "the lesion family was chosen to be exactly what it looks for"
        ),
        caught_by=None,
        countermeasure=(
            "compare the detector and the claim on the same payloads and treat "
            "agreement everywhere as a finding, not a comfort; better, have the "
            "lesion family authored by a party that has not seen the detector"
        ),
    ),
)

#: The audit's own declared blind spots: every sham mode no mechanical check
#: catches. Printed on every report, because the audit's honesty about its
#: limits is the property the whole layer exists to protect.
AUDIT_BLIND_SPOTS: Final[tuple[ShamMode, ...]] = tuple(
    mode for mode in SHAM_MODES if mode.caught_by is None
)


# ---------------------------------------------------------------------------
# The report objects
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class IntegrityReport:
    """Every integrity check run against one department, with its grade.

    ``unseen_lesions`` are planted violations no declared detector notices —
    a *measured* limit of the department's power, reported loudly and not
    treated as a defect: a battery whose lesions are all easy would report
    power the detectors do not have (department #1 plants one below its
    detectors' reach on purpose).

    ``dependence`` carries every declared dependence between the evidence
    and its subject. Dependence bounds what "independent lines of evidence"
    may be claimed; it does not change the grade.
    """

    department: str
    checks: tuple[CheckResult, ...]
    unseen_lesions: tuple[str, ...] = ()
    dependence: tuple[str, ...] = ()
    provenance_unknowns: tuple[str, ...] = ()

    def check(self, name: str) -> CheckResult:
        for result in self.checks:
            if result.name == name:
                return result
        raise KeyError(f"no integrity check named {name!r}")

    @property
    def failures(self) -> tuple[CheckResult, ...]:
        return tuple(r for r in self.checks if r.status == FAIL)

    @property
    def unknowns(self) -> tuple[CheckResult, ...]:
        return tuple(r for r in self.checks if r.status == UNKNOWN)

    @property
    def grade(self) -> str:
        by_name = {r.name: r for r in self.checks}
        contamination = by_name.get("provenance-contamination")
        if contamination is not None and contamination.status == FAIL:
            return CONTAMINATED
        if any(by_name[name].status == FAIL for name in _HOLLOW_CHECKS if name in by_name):
            return HOLLOW
        power = by_name.get("detector-power")
        specificity = by_name.get("detector-specificity")
        if power is not None and specificity is not None:
            if power.status == FAIL or specificity.status == FAIL:
                return DETECTOR_INADEQUATE
            if power.status == UNKNOWN or specificity.status == UNKNOWN:
                return UNMEASURED
        else:  # pragma: no cover - audit always emits both
            return UNMEASURED
        return CALIBRATED

    def to_dict(self) -> dict[str, Any]:
        return {
            "department": self.department,
            "grade": self.grade,
            "checks": [r.to_dict() for r in self.checks],
            "unseen_lesions": list(self.unseen_lesions),
            "dependence": list(self.dependence),
            "provenance_unknowns": list(self.provenance_unknowns),
            "audit_blind_spots": [m.name for m in AUDIT_BLIND_SPOTS],
        }

    def render_text(self) -> str:
        lines = [f"battery integrity [{self.department}]: {self.grade}"]
        for result in self.checks:
            marker = {PASS: " ok ", FAIL: "FAIL", UNKNOWN: " ?? "}[result.status]
            lines.append(f"  [{marker}] {result.name}: {result.evidence}")
        if self.unseen_lesions:
            lines.append(
                "  measured power limit: no declared detector sees "
                + ", ".join(self.unseen_lesions)
            )
        for reason in self.dependence:
            lines.append(f"  dependence: {reason}")
        if self.provenance_unknowns:
            lines.append(
                "  provenance undeclared: " + ", ".join(self.provenance_unknowns)
            )
        for mode in AUDIT_BLIND_SPOTS:
            lines.append(f"  audit blind spot: {mode.name} — {mode.countermeasure}")
        return "\n".join(lines)


@dataclass(frozen=True)
class ClaimReport:
    """One claim outcome, permanently paired with its battery's integrity.

    The pairing is the whole point. A claim that distinguishes under a
    hollow battery must never look like a claim that distinguishes under a
    calibrated one, and the only way to guarantee that is to make the
    report object incapable of stating one without the other.
    """

    department: str
    claim: str
    scope: str
    verdict: BatteryVerdict
    integrity: IntegrityReport

    @property
    def claim_status(self) -> str:
        if self.verdict.errors:
            return "inconclusive"
        if not self.verdict.target:
            return "does-not-fire"
        if self.verdict.shared_with:
            return "shared"
        return "distinguishes"

    @property
    def dangerous(self) -> bool:
        """A green outcome from a referee that has not earned trust."""
        return self.claim_status == "distinguishes" and self.integrity.grade != CALIBRATED

    def headline(self) -> str:
        status = self.claim_status.upper()
        grade = self.integrity.grade
        if self.dangerous:
            return (
                f"{self.claim}: {status} — but battery integrity is {grade}; "
                "this outcome is worth nothing until the referee is repaired"
            )
        return f"{self.claim}: {status} (battery integrity {grade})"

    def to_dict(self) -> dict[str, Any]:
        return {
            "department": self.department,
            "claim": self.claim,
            "scope": self.scope,
            "claim_status": self.claim_status,
            "dangerous": self.dangerous,
            "target_fired": bool(self.verdict.target),
            "shared_with": list(self.verdict.shared_with),
            "errors": dict(self.verdict.errors),
            "integrity": self.integrity.to_dict(),
        }

    def to_json(self, **kwargs: Any) -> str:
        return json.dumps(self.to_dict(), **kwargs)

    def render_text(self) -> str:
        lines = [f"claim {self.claim!r} [{self.department}]"]
        if self.dangerous:
            lines.append("  !! DANGER: outcome without integrity — do not act on this verdict")
        lines.append(f"  outcome: {self.verdict.summary()}")
        if self.scope:
            lines.append(f"  scope of a pass: {self.scope}")
        lines.append("  " + self.integrity.render_text().replace("\n", "\n  "))
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# The audit
# ---------------------------------------------------------------------------


def _guard(name: str, thunk: Any) -> CheckResult:
    """Run one check; a check that crashes measured nothing, which is FAIL.

    An instrument that raises during its own audit is not usable, and a
    crash silently treated as unknown would be the flattering direction.
    """
    try:
        return thunk()
    except Exception as exc:  # noqa: BLE001 - recorded, never swallowed
        return CheckResult(name, FAIL, f"check raised {type(exc).__name__}: {exc}")


def _decoy_probe(decoy: Any) -> Any:
    probe = getattr(decoy, "probe", None)
    return list(_HISTORICAL_DECOY_PROBE) if probe is None else probe


def _lesion_probe(lesion: Any) -> Any:
    return getattr(lesion, "probe", _HISTORICAL_LESION_PROBE)


def payloads_same(before: Any, after: Any) -> bool:
    """Structural equality across the payload shapes departments actually use.

    The first draft compared with ``list(after) != list(before)``, which
    encodes two earlier departments' habits: on mappings it compares *keys
    only* (a lesion that changes a value "plants nothing"), and on array
    payloads elementwise comparison raises. Department #6 exposed both —
    the probe convention's lesson repeated one layer down: the reusable
    audit had payload shapes baked in, and nobody could know which until a
    foreign shape arrived. This walks structure instead: mappings by key
    and value, sized non-strings elementwise, scalars by ``==`` with a
    raise treated as inequality (never as sameness — that would be the
    flattering direction).
    """
    if isinstance(before, Mapping) and isinstance(after, Mapping):
        if set(before.keys()) != set(after.keys()):
            return False
        return all(payloads_same(before[key], after[key]) for key in before)
    if isinstance(before, str) or isinstance(after, str):
        return before == after
    sized = hasattr(before, "__len__") and hasattr(after, "__len__")
    if sized:
        try:
            if len(before) != len(after):
                return False
        except TypeError:
            return False
        return all(payloads_same(a, b) for a, b in zip(before, after))
    try:
        return bool(before == after)
    except Exception:  # noqa: BLE001 - ambiguous comparison is not sameness
        return False


def _differs(before: Any, after: Any) -> bool:
    return not payloads_same(before, after)


def audit_department(department: Department) -> IntegrityReport:
    """Run every integrity check against ``department`` and grade the result.

    The checks deliberately re-derive everything the conformance suite pins,
    in independent code: the suite and this audit are two expressions of the
    same requirements, in the same sense the laboratory keeps two numeric
    backends — where one has a bug the other is the cross-check. The audit
    additionally measures what the suite cannot: declared detector power and
    specificity, payload symmetry, and the provenance record.
    """
    battery = department.battery
    checks: list[CheckResult] = []

    # -- structural ---------------------------------------------------------
    def _structural() -> CheckResult:
        reasons = department_reasons(department)
        if reasons:
            return CheckResult("structural", FAIL, "; ".join(reasons))
        return CheckResult(
            "structural",
            PASS,
            f"admissible: {len(battery.rivals)} rival(s), "
            f"{len(battery.decoys)} decoy(s), {len(battery.surrogates)} surrogate(s), "
            f"{len(battery.lesions)} lesion(s)",
        )

    checks.append(_guard("structural", _structural))
    if checks[0].status == FAIL:
        # Nothing below can run against a battery that does not validate;
        # report the one failure rather than a cascade of crashes.
        return IntegrityReport(department=department.name, checks=tuple(checks))

    # -- teeth --------------------------------------------------------------
    def _teeth_true() -> CheckResult:
        verdict = run_battery(battery, lambda payload: True, name="always_true")
        if verdict.distinguishes:
            return CheckResult(
                "teeth-always-true",
                FAIL,
                "a claim true of everything distinguished: the rivals are not rivals",
            )
        return CheckResult(
            "teeth-always-true",
            PASS,
            f"an unconditional claim is shared with {len(verdict.shared_with)} rival(s)",
        )

    def _teeth_false() -> CheckResult:
        verdict = run_battery(battery, lambda payload: False, name="always_false")
        if verdict.distinguishes:
            return CheckResult("teeth-always-false", FAIL, "a claim true of nothing distinguished")
        return CheckResult("teeth-always-false", PASS, "an unconditional refusal does not distinguish")

    def _rivals_answer() -> CheckResult:
        verdict = run_battery(battery, lambda payload: True, name="always_true")
        if verdict.errors:
            return CheckResult(
                "rivals-answer",
                FAIL,
                f"subject(s) raised instead of answering: {dict(verdict.errors)}",
            )
        return CheckResult("rivals-answer", PASS, "target and every rival answered without raising")

    checks.append(_guard("teeth-always-true", _teeth_true))
    checks.append(_guard("teeth-always-false", _teeth_false))
    checks.append(_guard("rivals-answer", _rivals_answer))

    # -- calibration --------------------------------------------------------
    def _both_directions() -> CheckResult:
        expected = {bool(r.distinguishes) for r in department.reference_claims}
        if expected == {True, False}:
            return CheckResult(
                "calibration-both-directions",
                PASS,
                f"{len(department.reference_claims)} reference claim(s), both verdict directions declared",
            )
        return CheckResult(
            "calibration-both-directions",
            FAIL,
            "reference claims do not cover both directions: a battery shown only "
            "one answer cannot be told apart from one that always gives it",
        )

    def _rederived() -> CheckResult:
        mismatches = []
        for reference in department.reference_claims:
            verdict = run_battery(battery, reference.claim, name=reference.name)
            if verdict.distinguishes != reference.distinguishes:
                mismatches.append(
                    f"{reference.name}: declared distinguishes={reference.distinguishes}, "
                    f"measured {verdict.distinguishes}"
                )
        if mismatches:
            return CheckResult("calibration-rederived", FAIL, "; ".join(mismatches))
        return CheckResult(
            "calibration-rederived",
            PASS,
            "every declared reference verdict re-derives from a fresh run",
        )

    def _killed_reason() -> CheckResult:
        killed = [r for r in department.reference_claims if not r.distinguishes]
        if not killed:
            return CheckResult(
                "killed-for-the-stated-reason", FAIL, "no reference claim the battery kills"
            )
        problems = []
        for reference in killed:
            verdict = run_battery(battery, reference.claim, name=reference.name)
            if not verdict.target:
                problems.append(f"{reference.name} does not fire for the target")
            elif not verdict.shared_with:
                problems.append(f"{reference.name} is not shared with any rival")
        if problems:
            return CheckResult("killed-for-the-stated-reason", FAIL, "; ".join(problems))
        return CheckResult(
            "killed-for-the-stated-reason",
            PASS,
            "every killed reference claim fires for the target and is shared with a rival "
            "(killed by the modus tollens, not by failing to fire)",
        )

    checks.append(_guard("calibration-both-directions", _both_directions))
    checks.append(_guard("calibration-rederived", _rederived))
    checks.append(_guard("killed-for-the-stated-reason", _killed_reason))

    # -- instruments do something ------------------------------------------
    def _decoys_move() -> CheckResult:
        inert = []
        for decoy in battery.decoys:
            probe = _decoy_probe(decoy)
            if not _differs(probe, decoy.substitute(probe)):
                inert.append(decoy.name)
        if inert:
            return CheckResult(
                "decoys-move-their-probe",
                FAIL,
                f"decoy(s) returned their input unchanged and ablate nothing: {', '.join(inert)}",
            )
        return CheckResult(
            "decoys-move-their-probe", PASS, f"all {len(battery.decoys)} decoy(s) change their probe"
        )

    def _lesions_plant() -> CheckResult:
        inert = []
        for lesion in battery.lesions:
            probe = _lesion_probe(lesion)
            if not _differs(probe, lesion.apply(probe)) or not float(lesion.magnitude) > 0:
                inert.append(lesion.name)
        if inert:
            return CheckResult(
                "lesions-plant-something",
                FAIL,
                f"lesion(s) plant nothing (or have no magnitude): {', '.join(inert)}",
            )
        return CheckResult(
            "lesions-plant-something",
            PASS,
            f"all {len(battery.lesions)} lesion(s) change their probe and carry a magnitude",
        )

    def _magnitude_spread() -> CheckResult:
        magnitudes = {float(lesion.magnitude) for lesion in battery.lesions}
        if len(magnitudes) <= 1:
            return CheckResult(
                "lesion-magnitudes-span-scales",
                FAIL,
                "all lesions share one magnitude: power is measured at a single "
                "threshold, so where the detectors go blind is unreported",
            )
        return CheckResult(
            "lesion-magnitudes-span-scales",
            PASS,
            f"magnitudes span {min(magnitudes):g} to {max(magnitudes):g}",
        )

    checks.append(_guard("decoys-move-their-probe", _decoys_move))
    checks.append(_guard("lesions-plant-something", _lesions_plant))
    checks.append(_guard("lesion-magnitudes-span-scales", _magnitude_spread))

    # -- payload symmetry ---------------------------------------------------
    def _payload_symmetry() -> CheckResult:
        target_payload = battery.target.payload()
        if not isinstance(target_payload, Mapping):
            return CheckResult(
                "payload-symmetry",
                UNKNOWN,
                "payloads are not mappings; structural symmetry is not mechanically "
                "comparable for this department's shapes",
            )
        target_keys = set(target_payload.keys())
        asymmetries = []
        for rival in battery.rivals:
            rival_payload = rival.payload()
            if not isinstance(rival_payload, Mapping):
                asymmetries.append(f"{rival.name}: payload is not a mapping while the target's is")
                continue
            extra = set(rival_payload.keys()) - target_keys
            missing = target_keys - set(rival_payload.keys())
            if extra or missing:
                asymmetries.append(
                    f"{rival.name}: extra keys {sorted(extra)}, missing keys {sorted(missing)} — "
                    "a claim can read identity from the difference (the 431cc74 leak)"
                )
        if asymmetries:
            return CheckResult("payload-symmetry", FAIL, "; ".join(asymmetries))
        tells = sorted(target_keys & {"name", "label", "id", "identity"})
        note = (
            f"; note: shared key(s) {tells} could carry identity in their values, "
            "which no structural comparison can see" if tells else ""
        )
        return CheckResult(
            "payload-symmetry",
            PASS,
            f"target and {len(battery.rivals)} rival payload(s) expose identical key sets{note}",
        )

    checks.append(_guard("payload-symmetry", _payload_symmetry))

    # -- detectors ----------------------------------------------------------
    unseen: tuple[str, ...] = ()

    def _specificity() -> CheckResult:
        if not department.detectors:
            return CheckResult(
                "detector-specificity", UNKNOWN, "no declared detectors to measure"
            )
        alarms = []
        for detector in department.detectors:
            verdict = run_detector(battery, detector)
            if verdict.false_alarm:
                alarms.append(detector.name)
        if alarms:
            return CheckResult(
                "detector-specificity",
                FAIL,
                f"detector(s) fire on the clean probe: {', '.join(alarms)} — an alarm "
                "that is always on has perfect sensitivity and no information",
            )
        return CheckResult(
            "detector-specificity",
            PASS,
            f"all {len(department.detectors)} declared detector(s) stay quiet on the clean probe",
        )

    def _power() -> tuple[CheckResult, tuple[str, ...]]:
        if not department.detectors:
            return (
                CheckResult("detector-power", UNKNOWN, "no declared detectors to measure"),
                (),
            )
        seen_by: dict[str, list[str]] = {lesion.name: [] for lesion in battery.lesions}
        informative = 0
        for detector in department.detectors:
            verdict = run_detector(battery, detector)
            if verdict.false_alarm:
                continue  # an always-on alarm sees nothing, whatever it fired on
            hits = [name for name, hit in verdict.fired.items() if hit]
            if hits:
                informative += 1
            for name in hits:
                seen_by[name].append(detector.name)
        unseen_names = tuple(sorted(name for name, seers in seen_by.items() if not seers))
        if informative == 0:
            return (
                CheckResult(
                    "detector-power",
                    FAIL,
                    "no declared detector notices any planted violation while staying "
                    "quiet when clean: silence from this department is not a result",
                ),
                unseen_names,
            )
        detail = "; ".join(
            f"{name} seen by {', '.join(seers) if seers else 'nobody'}"
            for name, seers in sorted(seen_by.items())
        )
        return (CheckResult("detector-power", PASS, detail), unseen_names)

    checks.append(_guard("detector-specificity", _specificity))
    try:
        power_result, unseen = _power()
    except Exception as exc:  # noqa: BLE001
        power_result, unseen = (
            CheckResult("detector-power", FAIL, f"check raised {type(exc).__name__}: {exc}"),
            (),
        )
    checks.append(power_result)

    # -- scope and provenance ----------------------------------------------
    def _scope() -> CheckResult:
        if str(department.scope).strip():
            return CheckResult("scope-declared", PASS, department.scope)
        return CheckResult(
            "scope-declared", FAIL, "no declared scope: a pass here would mean an unstated amount"
        )

    checks.append(_guard("scope-declared", _scope))

    dependence: tuple[str, ...] = ()
    unknowns: tuple[str, ...] = ()
    if department.provenance is None:
        checks.append(
            CheckResult(
                "provenance-declared",
                UNKNOWN,
                "no provenance record: authorship and independence are unknown, not fine",
            )
        )
        checks.append(
            CheckResult(
                "provenance-contamination",
                UNKNOWN,
                "nothing declared, so contamination can be neither shown nor excluded",
            )
        )
    else:
        provenance = department.provenance
        checks.append(
            CheckResult("provenance-declared", PASS, provenance.describe())
        )
        contamination = contamination_reasons(provenance)
        if contamination:
            checks.append(
                CheckResult("provenance-contamination", FAIL, "; ".join(contamination))
            )
        else:
            checks.append(
                CheckResult(
                    "provenance-contamination",
                    PASS,
                    "no declared contamination (declarations only; the audit cannot "
                    "verify them)",
                )
            )
        dependence = dependence_reasons(provenance)
        unknowns = undeclared_fields(provenance)

    return IntegrityReport(
        department=department.name,
        checks=tuple(checks),
        unseen_lesions=unseen,
        dependence=dependence,
        provenance_unknowns=unknowns,
    )


def report_claim(
    department: Department, claim: ClaimOutcome, *, name: str = ""
) -> ClaimReport:
    """Run ``claim`` through the department's battery and pair the outcome
    with a fresh integrity audit of that battery. The pairing is mandatory —
    there is deliberately no way to get the outcome alone from this module."""
    verdict = run_battery(department.battery, claim, name=name)
    integrity = audit_department(department)
    return ClaimReport(
        department=department.name,
        claim=verdict.claim,
        scope=department.scope,
        verdict=verdict,
        integrity=integrity,
    )
