"""``harness.integrity``, the referee, refereed.

Two incidents forced this module into existence, and both are in the tree.

The first is the sham battery that department #2 replaced (commit
``431cc74``): decoys, surrogates and lesions that were placeholders written
to the conformance tests' shapes, a surrogate returning ``[1, 2, 3]``, and
rivals whose payloads carried a field a claim could read as a label. It was
structurally complete. It validated. It passed the conformance suite of its
day. It could never have killed anything, and a human caught it, not a test.

The second is a measurement: the dossier resumption benchmark (ROADMAP,
2026-08-09) ran blinded agents against planted failures from this
repository's own incident history and found they caught *recorded
contradictions* nearly everywhere while reliably missing *hollow
verification*, a structurally admissible battery whose instruments are
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

* a **claim outcome**, the harness's own vocabulary (distinguishes /
  shared / does-not-fire / inconclusive), deliberately *not* a truth
  vocabulary, because per the honest-scope rule the harness adjudicates
  only whether a demonstration is about its subject;
* a **battery integrity grade**, one of five, each with crisp semantics:

  - ``CALIBRATED``: every mechanical check passed and detector power was
    measured; named blind spots may remain, and they travel with the grade.
  - ``DETECTOR_INADEQUATE``: the structure is present but no declared
    detector carries information: each one either fires on the clean probe
    (an alarm that is always on) or notices no planted violation at all.
  - ``UNMEASURED``: the audit could not run a load-bearing measurement
    (typically: no declared detectors on a bundle that bypassed admission).
  - ``CONTAMINATED``: the provenance record *declares* a condition under
    which the pass probability cannot be taken at face value (criteria
    authored after results were visible, thresholds unfrozen, tests edited
    after failures). Nothing mechanical can restore a contaminated pass.
  - ``HOLLOW``, a mechanical check failed: the battery could not kill
    anything, or an instrument is measurably empty. A claim verdict from a
    hollow battery is worthless whatever colour it is.

There is deliberately no scalar score. A number would invite exactly the
misreading, "integrity 0.87", that a named failing check makes impossible.

What this audit cannot see
--------------------------
:data:`SHAM_MODES` is the catalog of known ways a battery can be hollow,
and for each mode it records either the check that catches it or the fact
that no mechanical check can, with the countermeasure named. The entries
with ``caught_by=None`` are the audit's own declared blind spots; they are
printed on every report, because an audit that hides its own limits is the
thing this module exists to prevent.

Like :mod:`harness.protocol`, this module is domain-agnostic in the strict
sense and sits under the same three seam checks.
"""

from __future__ import annotations

import json
from collections.abc import Callable, Mapping, Sequence
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
#: The audit could not decide, the measurement did not run, or is not
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
#: instrument is measurably empty, the HOLLOW class.
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
    "undeclared-field-symmetry",
    "rival-separator-abundance",
)

#: How near a rival must be, expressed as the observable consequence of
#: nearness: the fraction of *arbitrary* structural predicates that separate
#: it from the target. Frozen by ``docs/23`` §4.2 before the calibration set
#: was read, and deliberately not retuned afterwards.
_RIVAL_DISTANCE_THRESHOLD: Final = 0.5

#: Below this many predicates actually running on a target/rival pair, the
#: separator fraction is a ratio of small integers and is reported as
#: undecided rather than as a measurement.
_SEPARATOR_MIN_PREDICATES: Final = 8

#: A hard cap on the generated predicate family, so a payload with many keys
#: cannot turn one audit into a combinatorial explosion.
_SEPARATOR_PREDICATE_CAP: Final = 512

#: Below this many payloads on which a detector and a claim *both* answered,
#: their agreement is not a measurement.
_MIN_COMMON_PAYLOADS: Final = 2


@dataclass(frozen=True)
class CheckResult:
    """One named integrity check: what was measured and what it showed."""

    name: str
    status: str
    evidence: str

    def to_dict(self) -> dict[str, str]:
        return {"name": self.name, "status": self.status, "evidence": self.evidence}


# ---------------------------------------------------------------------------
# The sham catalog, what the audit catches, and what it admits it cannot
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
            "no mechanical check *inside the audit* can know what was meant to "
            "be there, so this remains a blind spot of the audit itself. The "
            "removal is nonetheless caught from outside it: "
            "tests/test_lesion_sets_are_pinned.py pins every department's lesion "
            "set and carries a negative control that plants this exact sham and "
            "asserts the pin goes red. That test was written on 2026-08-20, "
            "after docs/28 measured that no checker, model or otherwise, caught "
            "this mode; the instruction to write it had sat unfollowed in this "
            "very string. Still declare frozen_before_execution in provenance"
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
            "rivals that do not share the structure the claim leans on, they "
            "differ from the target in gross, arbitrary ways, so the modus "
            "tollens never bites and any claim of the form 'anything AND a "
            "target-only property' distinguishes"
        ),
        caught_by=None,
        countermeasure=(
            "``rival-separator-abundance`` measures the observable consequence "
            "of distance and prints it on every report, but does not act on "
            "it: the threshold frozen before its calibration was read sits "
            "above the whole measured range (docs/23 §8.4), and retuning a cut "
            "after reading its own calibration would give it no falsification "
            "weight. Declare, per rival, the structure it shares and the "
            "property it lacks, and have a party that did not author the "
            "battery say whether the pair is close enough to make a shared "
            "claim embarrassing"
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
        caught_by="detector-claim-agreement",
        countermeasure=(
            "compare the detector and the claim on the same payloads and treat "
            "agreement everywhere as a finding, not a comfort, which is what "
            "``detector-claim-agreement`` now does, flagging a pair whose "
            "outcome vectors are identical or exactly complementary; better "
            "still, have the lesion family authored by a party that has not "
            "seen the detector"
        ),
    ),
    ShamMode(
        name="agreeable-absent-field-oracle",
        description=(
            "a payload whose declared surface is identical to the target's and "
            "whose *undeclared* surface is not: a permissive ``__missing__`` or "
            "``__getattr__`` answers names the key set never mentions, so "
            "identity lives on the complement of the declared fields and a "
            "claim naming a field that does not exist can still distinguish"
        ),
        caught_by="undeclared-field-symmetry",
        countermeasure=(
            "probe every payload with names nobody declared and require the "
            "target and every rival to answer them identically, and refuse a "
            "payload whose absent-field answer compares equal to an arbitrary "
            "sentinel. Found by an independent party that reached CALIBRATED "
            "with it, so its discovery was a measurement; note that the same "
            "battery therefore cannot be an independent test of the check "
            "built from it"
        ),
    ),
    ShamMode(
        name="structure-matched-value-disjoint-rivals",
        description=(
            "the generalisation of the value-encoded label leak from one field "
            "to the whole payload: rivals sharing the target's key set, types "
            "and shape while agreeing with it on no substantive value, so no "
            "single field is the tell and the joint value vector is the label. "
            "Any predicate keyed to a target value is then a target-only "
            "property, and 'anything AND a target-only property' distinguishes"
        ),
        caught_by=None,
        countermeasure=(
            "measured, not argued: six independent parties given only the "
            "public contract reached CALIBRATED this way, six for six "
            "(docs/23 §8.2). The obvious mechanical fix was tried and "
            "*inverts*, comparing payload values leaf by leaf scores this "
            "repository's own honest departments more separated than the "
            "sham, because a genuine rival differs from its target in its "
            "numbers too (§8.3). Which differences are load-bearing is the "
            "domain knowledge the seam forbids the audit to have. State, per "
            "rival, the coordinates it is matched on and those it is not, and "
            "have the claim authored by a party that has not seen the payloads"
        ),
    ),
    ShamMode(
        name="detector-claim-shapes-disjoint",
        description=(
            "a department whose detectors and claims consume different payload "
            "shapes, so ``detector-claim-agreement`` never finds a payload both "
            "answered and reports UNKNOWN, the residue that check leaves "
            "behind, and an evasion an author can choose deliberately"
        ),
        caught_by=None,
        countermeasure=(
            "partial and structural: a detector consuming a different shape "
            "cannot literally *be* the claim, so the disjointness that blinds "
            "the check also raises the cost of the mode it looks for. That is "
            "a mitigation, not a closure, the author picks both shapes. The "
            "real countermeasure is the same as for co-designed calibration: "
            "a lesion family and a detector authored by a party that has not "
            "seen the claim"
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

    ``unseen_lesions`` are planted violations no declared detector notices,
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
        """The five grades, in order of severity: every FAIL first, then every
        undecided check.

        ``UNKNOWN`` caps the grade for *every* hollow-class check, not only for
        the two detector checks. It did not until 2026-08-09, and the hole was
        found by an independent party hollowing the audit on its first attempt:
        ``payload-symmetry`` returns ``UNKNOWN`` for any payload that is not a
        mapping, so a battery of callable payloads sidestepped it for free and
        still reached ``CALIBRATED``. That contradicted the safe-failure rule
        the numeric arm has obeyed from the start, ``proven_sign`` returns 0
        for "not decided" and ``certified`` is False whenever a step could not
        be closed. Undecided is not passed there and is not passed here.
        """
        by_name = {r.name: r for r in self.checks}
        contamination = by_name.get("provenance-contamination")
        if contamination is not None and contamination.status == FAIL:
            return CONTAMINATED
        hollow = [by_name[name] for name in _HOLLOW_CHECKS if name in by_name]
        if any(result.status == FAIL for result in hollow):
            return HOLLOW
        power = by_name.get("detector-power")
        specificity = by_name.get("detector-specificity")
        agreement = by_name.get("detector-claim-agreement")
        detector_checks = [c for c in (power, specificity, agreement) if c is not None]
        if any(c.status == FAIL for c in detector_checks):
            return DETECTOR_INADEQUATE
        if power is None or specificity is None:  # pragma: no cover - audit emits both
            return UNMEASURED
        if power.status == UNKNOWN or specificity.status == UNKNOWN:
            return UNMEASURED
        if any(result.status == UNKNOWN for result in hollow):
            return UNMEASURED
        return CALIBRATED

    @property
    def undecided(self) -> tuple[str, ...]:
        """Names of the hollow-class checks that could not be decided.

        A reader who sees ``UNMEASURED`` should be able to find out *what* was
        not measured without re-running anything.
        """
        return tuple(
            result.name
            for result in self.checks
            if result.status == UNKNOWN and result.name in _HOLLOW_CHECKS
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "department": self.department,
            "grade": self.grade,
            "checks": [r.to_dict() for r in self.checks],
            "unseen_lesions": list(self.unseen_lesions),
            "undecided": list(self.undecided),
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
        if self.undecided:
            lines.append(
                "  undecided (these cap the grade, they do not pass): "
                + ", ".join(self.undecided)
            )
        for reason in self.dependence:
            lines.append(f"  dependence: {reason}")
        if self.provenance_unknowns:
            lines.append(
                "  provenance undeclared: " + ", ".join(self.provenance_unknowns)
            )
        for mode in AUDIT_BLIND_SPOTS:
            lines.append(f"  audit blind spot: {mode.name}, {mode.countermeasure}")
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
                f"{self.claim}: {status}, but battery integrity is {grade}; "
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
            lines.append("  !! DANGER: outcome without integrity, do not act on this verdict")
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


def _decoy_probes(decoy: Any, battery: Battery) -> list[Any]:
    """Every payload it is fair to poke a decoy with, best candidate first.

    The first version poked an instrument that declared no ``probe`` with
    department #1's shapes and nothing else, and reported "ablates nothing"
    when the instrument raised on them. That measured *totality over foreign
    shapes*, not substance, and it selected against exactly the authors it
    should have selected for: on 2026-08-09 four independent parties asked to
    build honest departments each wrote decoys and lesions faithful to their
    own payloads, and all four were graded HOLLOW for it, while the party who
    instrumented its own decoy to discover the foreign probe and wrote a
    generic fallback for it passed. The ``probe`` attribute the old code read
    is declared nowhere in ``harness/protocol.py`` and nowhere in
    ``harness/README.md``, so an author working from the public contract could
    not have known to supply it.

    An instrument now has to move *one* of these, not a particular one: an
    inert instrument returns every candidate unchanged and is still caught,
    while a faithful instrument that only understands its own department's
    payloads is no longer punished for it.
    """
    probes: list[Any] = []
    declared = getattr(decoy, "probe", None)
    if declared is not None:
        probes.append(declared)
    try:
        probes.append(battery.target.payload())
    except Exception:  # noqa: BLE001 - a target that will not answer is another check's business
        pass
    probes.append(list(_HISTORICAL_DECOY_PROBE))
    return probes


def _lesion_probes(lesion: Any, battery: Battery) -> list[Any]:
    """The same, for lesions. See :func:`_decoy_probes` for why there is a list."""
    probes: list[Any] = []
    declared = getattr(lesion, "probe", None)
    if declared is not None:
        probes.append(declared)
    try:
        probes.append(battery.target.payload())
    except Exception:  # noqa: BLE001
        pass
    probes.append(_HISTORICAL_LESION_PROBE)
    return probes


def _moves_any(instrument: Callable[[Any], Any], probes: Sequence[Any]) -> tuple[bool, str]:
    """``(moved, why)``, did the instrument change *any* candidate probe?"""
    reasons: list[str] = []
    for index, probe in enumerate(probes):
        try:
            after = instrument(probe)
        except Exception as exc:  # noqa: BLE001 - raising on a foreign shape is not inertness
            reasons.append(f"probe{index} raised {type(exc).__name__}: {exc}")
            continue
        if _differs(probe, after):
            return True, f"moved probe{index}"
        reasons.append(f"probe{index} returned unchanged")
    return False, "; ".join(reasons)


def payloads_same(before: Any, after: Any) -> bool:
    """Structural equality across the payload shapes departments actually use.

    The first draft compared with ``list(after) != list(before)``, which
    encodes two earlier departments' habits: on mappings it compares *keys
    only* (a lesion that changes a value "plants nothing"), and on array
    payloads elementwise comparison raises. Department #6 exposed both,
    the probe convention's lesson repeated one layer down: the reusable
    audit had payload shapes baked in, and nobody could know which until a
    foreign shape arrived. This walks structure instead: mappings by key
    and value, sized non-strings elementwise, scalars by ``==`` with a
    raise treated as inequality (never as sameness, that would be the
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


def _feature_names(payload: Any) -> tuple[str, ...]:
    """The named fields a payload exposes, the surface a label leak hides on.

    The first version of ``payload-symmetry`` understood mappings and returned
    ``UNKNOWN`` for everything else, which was a hole in two directions at
    once. An author could sidestep the check for free by handing out callable
    payloads (``UNKNOWN`` did not stop the top grade until 2026-08-09), and
    two departments that were never trying to sidestep anything, one whose
    payloads are department bundles, one whose payloads are plain functions,
    went unmeasured for the same reason.

    Mappings expose their keys. Objects expose their public attributes, which
    also catches a rival of a *different class* from the target: differing
    method sets are an asymmetry an ``isinstance`` claim reads just as easily
    as a leaked key. Numbers, strings, tuples and bare callables expose no
    names at all, and a payload with no names cannot carry a *named*-field
    leak, so the empty tuple is a decision, not an absence of one. What
    remains invisible here is identity hidden in a shared field's *value*,
    which is a declared blind spot, and positional asymmetry, which is
    ``rival-separator-abundance``'s business.
    """
    if isinstance(payload, Mapping):
        return tuple(sorted(repr(key) for key in payload.keys()))
    if isinstance(payload, (str, bytes, int, float, complex, bool)) or payload is None:
        return ()
    try:
        attributes = dir(payload)
    except Exception:  # noqa: BLE001 - an object that will not be inspected
        return ()
    return tuple(sorted(name for name in attributes if not name.startswith("_")))


# ---------------------------------------------------------------------------
# Structural predicates, the observable consequence of rival nearness
# ---------------------------------------------------------------------------
#
# Nearness is the department's substantive judgment and no check knows it. Its
# *consequence* is mechanical: a rival that shares the structure a claim leans
# on should not be separable from the target by an arbitrary structural
# predicate. Only the claim's own property should separate them. So generate a
# family of arbitrary, domain-blind predicates from the payloads themselves and
# count how many of them separate, the fraction is a distance, and a rival
# almost everything separates is a rival the modus tollens never reaches.
#
# The family sees *structure*, never substance. Two payloads holding different
# numbers score zero distance, which is correct: the difference in their values
# is what the department's claims are for. What the family sees is the gross
# kind of difference the recorded incident used, a rival of another type,
# another length, another key set, another value shape.


def _type_name(value: Any) -> str:
    return type(value).__name__


def _length_of(value: Any) -> int | None:
    try:
        return len(value)
    except Exception:  # noqa: BLE001 - unsized is a fact about the value
        return None


def _shape_probes() -> list[tuple[str, Callable[[Any], Any]]]:
    """The payload-independent half of the family: seven crude shape questions."""
    return [
        ("is-none", lambda v: v is None),
        ("truthy", lambda v: bool(v)),
        ("callable", lambda v: callable(v)),
        ("is-mapping", lambda v: isinstance(v, Mapping)),
        ("is-str", lambda v: isinstance(v, str)),
        ("is-sized", lambda v: hasattr(v, "__len__")),
        ("is-number", lambda v: isinstance(v, (int, float)) and not isinstance(v, bool)),
    ]


def _observed_probes(values: Sequence[Any]) -> list[tuple[str, Callable[[Any], Any]]]:
    """Type-name and length probes, one per distinct feature actually observed.

    Derived from the values rather than hard-coded, so the family adapts to
    whatever shapes a department uses without this module learning any of them.
    """
    probes: list[tuple[str, Callable[[Any], Any]]] = []
    for name in sorted({_type_name(v) for v in values}):
        probes.append((f"type=={name}", lambda v, name=name: _type_name(v) == name))
    lengths = sorted({n for n in (_length_of(v) for v in values) if n is not None})
    for length in lengths:
        probes.append((f"len=={length}", lambda v, length=length: len(v) == length))
        probes.append((f"len>{length}", lambda v, length=length: len(v) > length))
    return probes


def _structural_predicates(values: Sequence[Any]) -> list[tuple[str, Callable[[Any], Any]]]:
    """Generate the domain-blind predicate family for one set of payloads.

    Deterministic in construction order and capped, so an audit of a payload
    with many keys stays an audit rather than a combinatorial explosion. The
    order is: shape probes, observed type/length probes, key-membership probes,
    per-key value probes, positional value probes.
    """
    family: list[tuple[str, Callable[[Any], Any]]] = []
    family.extend(_shape_probes())
    family.extend(_observed_probes(values))

    mappings = [v for v in values if isinstance(v, Mapping)]
    keys: list[Any] = []
    seen_keys: set[str] = set()
    for mapping in mappings:
        for key in mapping.keys():
            token = repr(key)
            if token not in seen_keys:
                seen_keys.add(token)
                keys.append(key)
    keys.sort(key=repr)

    for key in keys:
        family.append((f"has[{key!r}]", lambda v, key=key: key in v))
    for key in keys:
        held = [m[key] for m in mappings if key in m]
        if not held:
            continue
        for label, probe in _shape_probes() + _observed_probes(held):
            family.append(
                (f"[{key!r}].{label}", lambda v, key=key, probe=probe: probe(v[key]))
            )

    sequences = [
        v
        for v in values
        if not isinstance(v, (str, bytes))
        and not isinstance(v, Mapping)
        and _length_of(v) is not None
    ]
    if sequences:
        shortest = min(_length_of(v) or 0 for v in sequences)
        for index in range(min(shortest, 8)):
            held = []
            for sequence in sequences:
                try:
                    held.append(sequence[index])
                except Exception:  # noqa: BLE001 - not indexable is a fact
                    pass
            if not held:
                continue
            for label, probe in _shape_probes() + _observed_probes(held):
                family.append(
                    (
                        f"[{index}].{label}",
                        lambda v, index=index, probe=probe: probe(v[index]),
                    )
                )

    return family[:_SEPARATOR_PREDICATE_CAP]


class _AuditSentinel:
    """A value equal to nothing honest.

    Handed to a payload's ``__eq__`` to find out whether the payload is
    *agreeable*, whether it answers "yes, that is me" to an arbitrary object
    it has never seen. Nothing a department legitimately computes compares
    equal to this.
    """

    __slots__ = ()

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return "<audit sentinel>"


_SENTINEL: Final = _AuditSentinel()

#: Field names no department declares, used to ask a payload what it does with
#: a name nobody gave it. Deliberately unpronounceable so a collision with a
#: real field is a coincidence worth investigating rather than a false alarm.
_UNDECLARED_TOKENS: Final = (
    "zzq_undeclared_alpha",
    "qxv_undeclared_beta",
    "wjn_undeclared_gamma",
)


def _absent_field_signature(payload: Any, token: str) -> tuple:
    """How ``payload`` answers a name nobody declared, by item and by attribute.

    An honest payload raises both ways, and its signature is the same as every
    other honest payload's. A payload with a permissive ``__missing__`` or
    ``__getattr__`` answers instead, and what it answers is a channel outside
    the declared key set entirely.
    """
    signature: list[tuple] = []
    for how, access in (
        ("item", lambda p: p[token]),
        ("attr", lambda p: getattr(p, token)),
    ):
        try:
            value = access(payload)
        except Exception as exc:  # noqa: BLE001 - raising is the honest answer
            signature.append((how, "raised", type(exc).__name__))
            continue
        try:
            agreeable = bool(value == _SENTINEL)
        except Exception:  # noqa: BLE001
            agreeable = False
        try:
            truthy = bool(value)
        except Exception:  # noqa: BLE001
            truthy = False
        signature.append((how, "answered", truthy, agreeable))
    return tuple(signature)


def _answer(probe: Callable[[Any], Any], value: Any) -> tuple[bool, bool]:
    """``(outcome, ran)``, a probe that raises did not answer, and an
    unanswered probe is never counted as agreement or as difference."""
    try:
        return bool(probe(value)), True
    except Exception:  # noqa: BLE001 - a probe that raises measured nothing
        return False, False


def _separator_counts(
    family: Sequence[tuple[str, Callable[[Any], Any]]], left: Any, right: Any
) -> tuple[int, int, tuple[str, ...]]:
    """``(separating, ran, first few separating labels)`` for one pair."""
    separating = 0
    ran = 0
    labels: list[str] = []
    for label, probe in family:
        left_value, left_ran = _answer(probe, left)
        right_value, right_ran = _answer(probe, right)
        if not (left_ran and right_ran):
            continue
        ran += 1
        if left_value != right_value:
            separating += 1
            if len(labels) < 6:
                labels.append(label)
    return separating, ran, tuple(labels)


def audit_department(department: Department) -> IntegrityReport:
    """Run every integrity check against ``department`` and grade the result.

    The checks deliberately re-derive everything the conformance suite pins,
    in independent code: the suite and this audit are two expressions of the
    same requirements, in the same sense the laboratory keeps two numeric
    backends, where one has a bug the other is the cross-check. The audit
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
            moved, why = _moves_any(decoy.substitute, _decoy_probes(decoy, battery))
            if not moved:
                inert.append(f"{decoy.name} ({why})")
        if inert:
            return CheckResult(
                "decoys-move-their-probe",
                FAIL,
                "decoy(s) changed no candidate probe and ablate nothing: "
                + "; ".join(inert),
            )
        return CheckResult(
            "decoys-move-their-probe",
            PASS,
            f"all {len(battery.decoys)} decoy(s) change at least one candidate probe",
        )

    def _lesions_plant() -> CheckResult:
        inert = []
        for lesion in battery.lesions:
            moved, why = _moves_any(lesion.apply, _lesion_probes(lesion, battery))
            if not moved:
                inert.append(f"{lesion.name} ({why})")
            elif not float(lesion.magnitude) > 0:
                inert.append(f"{lesion.name} (no positive magnitude)")
        if inert:
            return CheckResult(
                "lesions-plant-something",
                FAIL,
                f"lesion(s) plant nothing (or have no magnitude): {'; '.join(inert)}",
            )
        return CheckResult(
            "lesions-plant-something",
            PASS,
            f"all {len(battery.lesions)} lesion(s) change at least one candidate probe "
            "and carry a magnitude",
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
        target_names = _feature_names(target_payload)
        asymmetries = []
        for rival in battery.rivals:
            rival_names = _feature_names(rival.payload())
            extra = sorted(set(rival_names) - set(target_names))
            missing = sorted(set(target_names) - set(rival_names))
            if extra or missing:
                asymmetries.append(
                    f"{rival.name}: extra field(s) {extra}, missing field(s) {missing}, "
                    "a claim can read identity from the difference (the 431cc74 leak)"
                )
        if asymmetries:
            return CheckResult("payload-symmetry", FAIL, "; ".join(asymmetries))
        if not target_names:
            return CheckResult(
                "payload-symmetry",
                PASS,
                "payloads expose no named fields at all (they are numbers, sequences "
                "or bare callables), so a *named*-field leak is not available here; "
                "positional and shape asymmetry is rival-separator-abundance's business",
            )
        tells = sorted(
            name
            for name in target_names
            if name.strip("'\"") in {"name", "label", "id", "identity"}
        )
        note = (
            f"; note: shared field(s) {tells} could carry identity in their values, "
            "which no structural comparison can see" if tells else ""
        )
        return CheckResult(
            "payload-symmetry",
            PASS,
            f"target and {len(battery.rivals)} rival payload(s) expose identical "
            f"field sets ({len(target_names)} name(s)){note}",
        )

    checks.append(_guard("payload-symmetry", _payload_symmetry))

    # -- what the payloads say about fields nobody declared -----------------
    def _undeclared_field_symmetry() -> CheckResult:
        target_payload = battery.target.payload()
        rival_payloads = [(rival.name, rival.payload()) for rival in battery.rivals]
        declared = set(_feature_names(target_payload))
        for _, payload in rival_payloads:
            declared |= set(_feature_names(payload))

        tokens = [t for t in _UNDECLARED_TOKENS if repr(t) not in declared and t not in declared]
        if isinstance(target_payload, Mapping):
            for key in list(target_payload.keys())[:3]:
                if isinstance(key, str):
                    candidate = f"{key}_zzq_undeclared"
                    if repr(candidate) not in declared and candidate not in declared:
                        tokens.append(candidate)
        if not tokens:
            return CheckResult(
                "undeclared-field-symmetry",
                UNKNOWN,
                "every probe name collided with a declared field, so the payloads' "
                "behaviour outside their declared surface could not be sampled",
            )

        agreeable: list[str] = []
        asymmetric: list[str] = []
        for token in tokens:
            target_signature = _absent_field_signature(target_payload, token)
            if any(part[1] == "answered" and part[3] for part in target_signature):
                agreeable.append(f"target on {token!r}")
            for name, payload in rival_payloads:
                rival_signature = _absent_field_signature(payload, token)
                if any(part[1] == "answered" and part[3] for part in rival_signature):
                    agreeable.append(f"{name} on {token!r}")
                if rival_signature != target_signature and len(asymmetric) < 4:
                    asymmetric.append(
                        f"{name} answers the undeclared name {token!r} differently from "
                        f"the target: {target_signature} vs {rival_signature}"
                    )
        if agreeable:
            return CheckResult(
                "undeclared-field-symmetry",
                FAIL,
                f"payload(s) answer a name nobody declared with a value that compares "
                f"equal to an arbitrary sentinel ({'; '.join(sorted(set(agreeable))[:4])}): "
                "such a payload agrees with any assertion whatsoever, so a claim naming "
                "a field that does not exist can still distinguish",
            )
        if asymmetric:
            return CheckResult(
                "undeclared-field-symmetry",
                FAIL,
                "; ".join(asymmetric)
                + ", identity lives outside the declared key set, where payload-symmetry "
                "cannot see it",
            )
        return CheckResult(
            "undeclared-field-symmetry",
            PASS,
            f"target and {len(rival_payloads)} rival(s) answer {len(tokens)} undeclared "
            "field name(s) identically, and none of them agrees with an arbitrary sentinel",
        )

    checks.append(_guard("undeclared-field-symmetry", _undeclared_field_symmetry))

    # -- how near the nearest rival is --------------------------------------
    def _rival_distance() -> CheckResult:
        target_payload = battery.target.payload()
        rival_payloads = [(rival.name, rival.payload()) for rival in battery.rivals]
        family = _structural_predicates(
            [target_payload, *(payload for _, payload in rival_payloads)]
        )
        fractions: dict[str, float] = {}
        witnesses: dict[str, tuple[str, ...]] = {}
        thin: list[str] = []
        for name, payload in rival_payloads:
            separating, ran, labels = _separator_counts(family, target_payload, payload)
            if ran < _SEPARATOR_MIN_PREDICATES:
                thin.append(f"{name} ({ran} predicate(s) answered)")
                continue
            fractions[name] = separating / ran
            witnesses[name] = labels
        if not fractions:
            return CheckResult(
                "rival-separator-abundance",
                UNKNOWN,
                "no target/rival pair answered enough structural predicates to "
                f"measure a distance: {'; '.join(thin) or 'no rivals'}",
            )
        nearest = min(fractions, key=lambda name: fractions[name])
        value = fractions[nearest]
        detail = ", ".join(f"{name} {fractions[name]:.2f}" for name in sorted(fractions))
        skipped = f"; not measurable: {'; '.join(thin)}" if thin else ""
        if value > _RIVAL_DISTANCE_THRESHOLD:
            return CheckResult(
                "rival-separator-abundance",
                FAIL,
                f"even the nearest rival ({nearest}) is separated from the target by "
                f"{value:.2f} of the arbitrary structural predicates that ran, above "
                f"the frozen threshold {_RIVAL_DISTANCE_THRESHOLD:g}: any claim of the "
                f"form 'anything AND a target-only property' distinguishes here. "
                f"Separating predicates include {list(witnesses[nearest])}. "
                f"All rivals: {detail}{skipped}",
            )
        return CheckResult(
            "rival-separator-abundance",
            PASS,
            f"nearest rival ({nearest}) separated by {value:.2f} of "
            f"{len(family)} arbitrary structural predicates, at or below the frozen "
            f"threshold {_RIVAL_DISTANCE_THRESHOLD:g}; all rivals: {detail}{skipped}. "
            "Structural distance only: a rival identical in shape and absurd in "
            "substance scores zero here",
        )

    checks.append(_guard("rival-separator-abundance", _rival_distance))

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
                f"detector(s) fire on the clean probe: {', '.join(alarms)}, an alarm "
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

    # -- is the detector the claim? ----------------------------------------
    def _detector_claim_agreement() -> CheckResult:
        if not department.detectors or not department.reference_claims:
            return CheckResult(
                "detector-claim-agreement",
                UNKNOWN,
                "nothing to compare: the department declares no detector or no "
                "reference claim",
            )

        payloads: list[tuple[str, Any]] = [("target", battery.target.payload())]
        for rival in battery.rivals:
            payloads.append((f"rival:{rival.name}", rival.payload()))
        for detector in department.detectors:
            probe = (
                detector.probe if detector.probe is not None else battery.target.payload()
            )
            for lesion in battery.lesions:
                try:
                    payloads.append((f"lesion:{detector.name}:{lesion.name}", lesion.apply(probe)))
                except Exception:  # noqa: BLE001 - a payload we could not build
                    pass
        target_payload = battery.target.payload()
        for decoy in battery.decoys:
            try:
                payloads.append((f"decoy:{decoy.name}", decoy.substitute(target_payload)))
            except Exception:  # noqa: BLE001
                pass
        for surrogate in battery.surrogates:
            try:
                payloads.append((f"surrogate:{surrogate.name}", surrogate.sample()))
            except Exception:  # noqa: BLE001
                pass

        flagged: list[str] = []
        rates: list[float] = []
        widest = 0
        # Each vector is evaluated exactly once. Both are expensive for a
        # department whose claims are real computations, and the pairing below
        # is a comparison of cached outcomes, not a re-evaluation.
        claim_vectors = [
            (reference, [_answer(reference.claim, p) for _, p in payloads])
            for reference in department.reference_claims
        ]
        for detector in department.detectors:
            detector_vector = [_answer(detector.fires, p) for _, p in payloads]
            for reference, claim_vector in claim_vectors:
                common = [
                    (d_value, c_value)
                    for (d_value, d_ran), (c_value, c_ran) in zip(detector_vector, claim_vector)
                    if d_ran and c_ran
                ]
                if len(common) < _MIN_COMMON_PAYLOADS:
                    continue
                widest = max(widest, len(common))
                detector_side = [d for d, _ in common]
                if len(set(detector_side)) < 2:
                    continue  # a constant detector is detector-specificity's business
                agreement = sum(1 for d, c in common if d == c) / len(common)
                rates.append(agreement)
                if agreement in (0.0, 1.0):
                    relation = "identical to" if agreement == 1.0 else "the exact negation of"
                    flagged.append(
                        f"detector {detector.name!r} is {relation} reference claim "
                        f"{reference.name!r} on all {len(common)} payload(s) both answered"
                    )
        if not rates:
            return CheckResult(
                "detector-claim-agreement",
                UNKNOWN,
                "no detector and claim answered the same "
                f"{_MIN_COMMON_PAYLOADS} payloads with a non-constant detector: this "
                "department's detectors and claims consume different shapes, which "
                "the protocol permits, so the comparison could not run "
                "(SHAM_MODES: detector-claim-shapes-disjoint)",
            )
        if flagged:
            return CheckResult(
                "detector-claim-agreement",
                FAIL,
                "; ".join(flagged)
                + ", the detector's alarms carry no information the claim did not "
                "already assert, so the power measured for it is the claim measuring "
                "itself",
            )
        return CheckResult(
            "detector-claim-agreement",
            PASS,
            f"{len(rates)} detector/claim pair(s) compared on up to {widest} shared "
            f"payload(s); agreement ranges {min(rates):.2f} to {max(rates):.2f}, so no "
            "detector is the claim or its negation",
        )

    checks.append(_guard("detector-claim-agreement", _detector_claim_agreement))

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
    with a fresh integrity audit of that battery. The pairing is mandatory,
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
