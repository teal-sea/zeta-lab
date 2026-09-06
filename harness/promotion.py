"""``harness.promotion``, the integrity grade made enforcing instead of advisory.

:mod:`harness.integrity` measures a battery and pairs the measurement with the
claim outcome, and ``ClaimReport.dangerous`` renders a banner saying the
outcome "is worth nothing until the referee is repaired". Nothing anywhere
*acts* on that. A banner is a request; the claim still travels, and the
repository's own history says which of the two survives a busy afternoon.

This module supplies the missing half: one information boundary, on disk, with
exactly one door into it. A candidate crosses into ``promoted/`` only when a
policy that recomputes everything says so, and the grade is one of the things
it recomputes.

The rule the whole module is built around
-----------------------------------------
**Every BLOCK traces to a digest comparison, a set membership, or a measured
calibration, never to a self-declared boolean.** That is not a style
preference; it is the difference between this gate and :class:`NaiveGate`
below, which is included in the same file precisely so nobody can lose track
of how small the difference is. Both gates get the clean case, the
contaminated-and-admitted case and the blind-detector case right. They part
company on exactly one input: a report that declares itself clean while its
artifacts say otherwise (:func:`harness.preregistration.declared_vs_derived`).
If that case never arises, this module has bought nothing, and saying so up
front is cheaper than discovering it later.

Default-open is structurally impossible
---------------------------------------
Every check must return an explicit ``PASS``, the same three-valued
vocabulary :mod:`harness.integrity` already uses. ``UNKNOWN`` blocks, a check
that raises blocks and is recorded as :attr:`ReasonCode.GATE_CHECK_ERRORED`,
and an unrecognised status decodes to ``UNKNOWN``. There is no place where the
absence of a finding produces an allowance, because no check is ever consulted
for *not* having failed.

What this does not do
---------------------
It adjudicates promotion, never truth. An ``ALLOW`` says: this claim
distinguished its subject under a battery that graded ``CALIBRATED``, against
evidence that has not moved, under criteria frozen before that evidence
existed, graded by a party that is not its producer. Every one of those is a
statement about process. None of them is a statement about the world, and the
audit's own declared blind spots ride on every decision so that no reader can
mistake the one for the other.

Like :mod:`harness.protocol`, this module is domain-agnostic in the strict
sense and sits under the same three seam checks.
"""

from __future__ import annotations

import json
import os
import re
from collections.abc import Mapping
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import StrEnum
from pathlib import Path
from typing import Any, Callable, Final

from harness.integrity import (
    AUDIT_BLIND_SPOTS,
    CALIBRATED,
    FAIL,
    PASS,
    UNKNOWN,
    ClaimReport,
)
from harness.preregistration import (
    CRITERIA_DRIFT,
    EVIDENCE_VISIBLE_AT_FREEZE,
    Preregistration,
    derived_findings,
    digest,
)
from harness.provenance import Provenance, contamination_reasons

__all__ = [
    "ALLOW",
    "BLOCK",
    "CHECKS",
    "POLICY_VERSION",
    "NAIVE_POLICY_VERSION",
    "REQUIRED_GRADE",
    "REQUIRED_CLAIM_STATUS",
    "PromotionError",
    "ReasonCode",
    "Decision",
    "decide",
    "recheck",
    "naive_decide",
    "NaiveGate",
    "Boundary",
    "ProducerView",
    "audit",
]

ALLOW: Final = "ALLOW"
BLOCK: Final = "BLOCK"

#: Bump on any change to what the checks mean. A stored decision states the
#: version that produced it, so a re-audit under new policy is visible rather
#: than retroactive.
POLICY_VERSION: Final = "promotion-1.0"
NAIVE_POLICY_VERSION: Final = "naive-1.0"

#: The one grade that permits a crossing, and the one claim outcome. Named
#: constants so a test can pin them: loosening either is the most attractive
#: way to make this gate stop saying no, and it should cost a visible diff.
REQUIRED_GRADE: Final = CALIBRATED
REQUIRED_CLAIM_STATUS: Final = "distinguishes"

#: Identifiers that become filenames. Anything else is refused rather than
#: sanitised, a claim id containing a path separator is either a mistake or
#: an attempt to write outside the boundary, and quietly rewriting it would
#: hide both.
_SAFE_ID: Final = re.compile(r"\A[A-Za-z0-9][A-Za-z0-9._-]{0,127}\Z")


class PromotionError(Exception):
    """A misuse of the boundary: a bad identifier, or a reach past the door."""


class ReasonCode(StrEnum):
    """Closed, stable, machine-readable. A reason is not a sentence.

    Prose reasons get reworded, truncated into log lines, and then nothing
    downstream can count them. These codes are the contract, and every one is
    independently reproducible through :func:`recheck`, which is what stops a
    code from becoming decorative.
    """

    #: The battery ran and the claim did not distinguish its subject.
    CLAIM_NOT_DISTINGUISHING = "claim-not-distinguishing"
    #: The battery that produced the outcome did not grade ``CALIBRATED``.
    BATTERY_INTEGRITY_NOT_CALIBRATED = "battery-integrity-not-calibrated"
    #: The criteria were frozen while this very evidence was already visible.
    #: Derived by set membership over digests, never read from a declaration.
    PROVENANCE_CONTAMINATED_DERIVED = "provenance-contaminated-derived"
    #: The criteria applied do not digest to the criteria frozen.
    CRITERIA_DRIFTED = "criteria-drifted"
    #: The evidence moved under the report.
    EVIDENCE_STALE = "evidence-stale"
    #: The report is about a differently-identified claim.
    CLAIM_IDENTITY_MISMATCH = "claim-identity-mismatch"
    #: Scope absent on one side; a pass would mean an unstated amount.
    SCOPE_MISSING = "scope-missing"
    #: The scope requested is not the scope the battery's pass covers.
    SCOPE_WIDENED = "scope-widened"
    #: Producer and verifier are the same party.
    SELF_VERIFIED = "self-verified"
    #: A check did not reach a positive finding, the default-open guard. It
    #: fires for silence, not for a finding.
    INTEGRITY_NOT_ESTABLISHED = "integrity-not-established"
    #: A check raised. Recorded as its own code so "the gate broke" can never
    #: be mistaken for "the gate found nothing" (the ``_guard`` idiom, one
    #: layer up).
    GATE_CHECK_ERRORED = "gate-check-errored"


# ---------------------------------------------------------------------------
# The checks
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _Inputs:
    """Everything a check may read. Nothing is fetched from ambient state."""

    claim_report: Any
    prereg: Any
    criteria_applied: Any
    evidence_digest: str
    current_evidence_digest: str
    claim_id: str
    producer_id: str
    verifier_id: str
    requested_scope: str


def _norm(text: Any) -> str:
    return " ".join(str(text).split()).casefold()


def _check_claim_outcome(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    status = inp.claim_report.claim_status
    if status == REQUIRED_CLAIM_STATUS:
        return PASS, ()
    return FAIL, (ReasonCode.CLAIM_NOT_DISTINGUISHING,)


def _check_battery_integrity(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    if inp.claim_report.integrity.grade == REQUIRED_GRADE:
        return PASS, ()
    return FAIL, (ReasonCode.BATTERY_INTEGRITY_NOT_CALIBRATED,)


def _derived_keys(inp: _Inputs) -> frozenset[str]:
    return frozenset(
        key
        for key, _ in derived_findings(
            inp.prereg,
            criteria_applied=inp.criteria_applied,
            evidence_digest=inp.evidence_digest,
        )
    )


def _check_provenance_derived(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    if EVIDENCE_VISIBLE_AT_FREEZE in _derived_keys(inp):
        return FAIL, (ReasonCode.PROVENANCE_CONTAMINATED_DERIVED,)
    return PASS, ()


def _check_criteria_drift(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    if CRITERIA_DRIFT in _derived_keys(inp):
        return FAIL, (ReasonCode.CRITERIA_DRIFTED,)
    return PASS, ()


def _check_evidence_freshness(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    seen, now = str(inp.evidence_digest), str(inp.current_evidence_digest)
    if not seen or not now:
        return UNKNOWN, ()
    if seen != now:
        return FAIL, (ReasonCode.EVIDENCE_STALE,)
    return PASS, ()


def _check_claim_identity(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    """The identifier crossing must be the identifier the battery ran.

    A report is about whatever ``run_battery`` labelled it, and a boundary
    that took the crossing party's word for which report belongs to which
    claim would be trivially defeated by attaching a good report to a
    different claim.
    """
    if not str(inp.claim_id).strip():
        return UNKNOWN, ()
    if str(inp.claim_report.claim) != str(inp.claim_id):
        return FAIL, (ReasonCode.CLAIM_IDENTITY_MISMATCH,)
    return PASS, ()


def _check_scope(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    """Scope is free text, so containment is undecidable; identity is demanded.

    A department's scope is one English sentence. No mechanical check can
    decide whether one such sentence covers another, and a gate that guessed
    would be worse than one that refuses: the guess would be wrong in the
    permissive direction. So anything but the department's own scope sentence,
    modulo whitespace and case, is treated as a widening.
    """
    covered = _norm(getattr(inp.claim_report, "scope", ""))
    requested = _norm(inp.requested_scope)
    if not covered or not requested:
        return FAIL, (ReasonCode.SCOPE_MISSING,)
    if requested != covered:
        return FAIL, (ReasonCode.SCOPE_WIDENED,)
    return PASS, ()


def _check_independence(inp: _Inputs) -> tuple[str, tuple[ReasonCode, ...]]:
    """Two parties, and both of them have to actually be parties.

    The identifiers are required to be strings before anything is compared.
    Coercing with ``str()`` first would be the more forgiving thing to do and
    is exactly the bug this module exists to argue against: ``None``, ``0``,
    ``[]`` and a bare ``object()`` all stringify to something non-empty and
    mutually unequal, so a caller who supplied no party at all would read as
    two independent ones and the check would return ``PASS``. An identifier
    nobody set is an unknown, and an unknown blocks.
    """
    producer, verifier = inp.producer_id, inp.verifier_id
    if not isinstance(producer, str) or not isinstance(verifier, str):
        return UNKNOWN, ()
    producer, verifier = producer.strip(), verifier.strip()
    if not producer or not verifier:
        return UNKNOWN, ()
    if producer == verifier:
        return FAIL, (ReasonCode.SELF_VERIFIED,)
    return PASS, ()


_CHECKS: Final[dict[str, Callable[[_Inputs], tuple[str, tuple[ReasonCode, ...]]]]] = {
    "claim-outcome": _check_claim_outcome,
    "battery-integrity": _check_battery_integrity,
    "provenance-derived": _check_provenance_derived,
    "criteria-drift": _check_criteria_drift,
    "evidence-freshness": _check_evidence_freshness,
    "claim-identity": _check_claim_identity,
    "scope": _check_scope,
    "independence": _check_independence,
}

#: Every check, in report order. A decision whose ``checks_run`` is not this
#: tuple did not decide a promotion, whatever its verdict says.
CHECKS: Final[tuple[str, ...]] = tuple(_CHECKS)

#: Which check reproduces which code, for :func:`recheck`.
_CHECK_FOR_REASON: Final[dict[ReasonCode, str]] = {
    ReasonCode.CLAIM_NOT_DISTINGUISHING: "claim-outcome",
    ReasonCode.BATTERY_INTEGRITY_NOT_CALIBRATED: "battery-integrity",
    ReasonCode.PROVENANCE_CONTAMINATED_DERIVED: "provenance-derived",
    ReasonCode.CRITERIA_DRIFTED: "criteria-drift",
    ReasonCode.EVIDENCE_STALE: "evidence-freshness",
    ReasonCode.CLAIM_IDENTITY_MISMATCH: "claim-identity",
    ReasonCode.SCOPE_MISSING: "scope",
    ReasonCode.SCOPE_WIDENED: "scope",
    ReasonCode.SELF_VERIFIED: "independence",
}


# ---------------------------------------------------------------------------
# The decision
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Decision:
    """One crossing, decided, with everything needed to re-derive it.

    ``blind_spots`` carries :data:`harness.integrity.AUDIT_BLIND_SPOTS` onto
    every decision, ``ALLOW`` ones included. An audit that hides its limits is
    the thing the layer exists to prevent, and an allowance is exactly when a
    reader stops looking for them.
    """

    verdict: str
    reasons: tuple[ReasonCode, ...]
    checks_run: tuple[str, ...]
    grade: str
    claim_id: str
    report_id: str
    decided_at: str
    policy_version: str
    blind_spots: tuple[str, ...] = ()
    check_status: Mapping[str, str] = field(default_factory=dict)
    digests: Mapping[str, str] = field(default_factory=dict)
    errors: tuple[str, ...] = ()

    @property
    def complete(self) -> bool:
        """Did every check run? Only a complete decision decides a promotion."""
        return tuple(self.checks_run) == CHECKS

    def to_dict(self) -> dict[str, Any]:
        return {
            "verdict": self.verdict,
            "reasons": [str(r) for r in self.reasons],
            "checks_run": list(self.checks_run),
            "check_status": dict(self.check_status),
            "grade": self.grade,
            "claim_id": self.claim_id,
            "report_id": self.report_id,
            "decided_at": self.decided_at,
            "policy_version": self.policy_version,
            "blind_spots": list(self.blind_spots),
            "digests": dict(self.digests),
            "errors": list(self.errors),
            "complete": self.complete,
        }

    def to_json(self, **kwargs: Any) -> str:
        return json.dumps(self.to_dict(), **kwargs)


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _safe(fn: Callable[[], Any], fallback: Any) -> Any:
    try:
        return fn()
    except Exception:  # noqa: BLE001 - a digest that cannot be taken is unknown
        return fallback


def _run(names: tuple[str, ...], inp: _Inputs, policy: str, when: str) -> Decision:
    reasons: set[ReasonCode] = set()
    statuses: dict[str, str] = {}
    errors: list[str] = []
    for name in names:
        try:
            status, codes = _CHECKS[name](inp)
        except Exception as exc:  # noqa: BLE001 - recorded, never swallowed
            status, codes = FAIL, (ReasonCode.GATE_CHECK_ERRORED,)
            errors.append(f"{name}: {type(exc).__name__}: {exc}")
        if status not in (PASS, FAIL, UNKNOWN):
            status = UNKNOWN
        statuses[name] = status
        reasons.update(codes)
        # The positive requirement: only an explicit PASS clears a check.
        # Anything else, a finding, silence, or a status this policy does not
        # recognise, must leave at least one reason behind.
        if status != PASS and not codes:
            reasons.add(ReasonCode.INTEGRITY_NOT_ESTABLISHED)
        if status == UNKNOWN:
            reasons.add(ReasonCode.INTEGRITY_NOT_ESTABLISHED)
    if any(statuses.get(name) != PASS for name in names) and not reasons:  # pragma: no cover
        reasons.add(ReasonCode.INTEGRITY_NOT_ESTABLISHED)

    digests = {
        "criteria_applied": _safe(lambda: digest(inp.criteria_applied), "unavailable"),
        "criteria_frozen": _safe(lambda: str(inp.prereg.criteria_digest), "unavailable"),
        "evidence_at_report": str(inp.evidence_digest),
        "evidence_now": str(inp.current_evidence_digest),
    }
    grade = _safe(lambda: str(inp.claim_report.integrity.grade), UNKNOWN)
    ordered = tuple(sorted(reasons, key=str))
    report_id = _safe(
        lambda: digest(
            {
                "claim_id": str(inp.claim_id),
                "checks": list(names),
                "decided_at": when,
                "digests": digests,
                "grade": grade,
                "policy": policy,
                "reasons": [str(r) for r in ordered],
            }
        ),
        "unavailable",
    )
    return Decision(
        verdict=BLOCK if ordered else ALLOW,
        reasons=ordered,
        checks_run=tuple(names),
        grade=grade,
        claim_id=str(inp.claim_id),
        report_id=report_id,
        decided_at=when,
        policy_version=policy,
        blind_spots=tuple(mode.name for mode in AUDIT_BLIND_SPOTS),
        check_status=dict(statuses),
        digests=digests,
        errors=tuple(errors),
    )


def decide(
    claim_report: ClaimReport,
    *,
    prereg: Preregistration,
    criteria_applied: Any,
    evidence_digest: str,
    current_evidence_digest: str,
    claim_id: str,
    producer_id: str,
    verifier_id: str,
    requested_scope: str,
    now: str = "",
) -> Decision:
    """Decide one crossing, running every check and reporting all findings.

    Never first-fault-wins: a claim with three problems should not need three
    submissions to learn about them, the same convention the ``*_reasons()``
    functions follow. ``ALLOW`` requires an explicit ``PASS`` from every check
    in :data:`CHECKS`; malformed input blocks rather than raising through.
    """
    inp = _Inputs(
        claim_report=claim_report,
        prereg=prereg,
        criteria_applied=criteria_applied,
        evidence_digest=evidence_digest,
        current_evidence_digest=current_evidence_digest,
        claim_id=claim_id,
        producer_id=producer_id,
        verifier_id=verifier_id,
        requested_scope=requested_scope,
    )
    return _run(CHECKS, inp, POLICY_VERSION, now or _now())


def recheck(claim_report: ClaimReport, *, only: ReasonCode, **kwargs: Any) -> Decision:
    """Run the single check that produces ``only``, and nothing else.

    A reason nobody can reproduce in isolation is a string, not a finding.
    The resulting decision is deliberately *incomplete*, ``complete`` is
    False and :meth:`Boundary.promote` will not accept it, so a one-check
    ``ALLOW`` can never be mistaken for a promotion.
    """
    name = _CHECK_FOR_REASON.get(only)
    if name is None:
        raise PromotionError(
            f"{only!r} is not produced by a single check; it is a property of the "
            "decision as a whole and cannot be rechecked in isolation"
        )
    now = kwargs.pop("now", "")
    inp = _Inputs(claim_report=claim_report, **kwargs)
    return _run((name,), inp, POLICY_VERSION, now or _now())


# ---------------------------------------------------------------------------
# The null control
# ---------------------------------------------------------------------------


def naive_decide(
    claim_report: ClaimReport,
    *,
    provenance: Provenance | None,
    claim_id: str,
    now: str = "",
) -> Decision:
    """The gate this one has to beat: reads declarations, recomputes nothing.

    It exists to be beaten, and it is kept in this file so the two cannot
    drift apart unnoticed. It blocks a claim that did not distinguish, a
    battery that did not grade ``CALIBRATED``, and a provenance record that
    *admits* contamination, which is to say it handles the clean case, the
    blind-detector case and the honestly-declared-contaminated case exactly as
    well as :func:`decide` does. The only input that separates them is one
    where the declaration and the artifacts disagree: a producer that writes
    ``results_visible_when_authored=False`` over work whose criteria were
    frozen with the evidence already visible. That single case is the entire
    measured delta of this module, and any claim about the gate's value that
    does not rest on it is a claim about nothing.

    The pattern is :mod:`harness.shams` applied to the gate itself: plant the
    hollow version beside the real one, and measure the difference instead of
    asserting it.
    """
    reasons: list[ReasonCode] = []
    if claim_report.claim_status != REQUIRED_CLAIM_STATUS:
        reasons.append(ReasonCode.CLAIM_NOT_DISTINGUISHING)
    if claim_report.integrity.grade != REQUIRED_GRADE:
        reasons.append(ReasonCode.BATTERY_INTEGRITY_NOT_CALIBRATED)
    if provenance is not None and contamination_reasons(provenance):
        reasons.append(ReasonCode.PROVENANCE_CONTAMINATED_DERIVED)
    ordered = tuple(sorted(set(reasons), key=str))
    return Decision(
        verdict=BLOCK if ordered else ALLOW,
        reasons=ordered,
        checks_run=("declared-outcome", "declared-grade", "declared-provenance"),
        grade=str(claim_report.integrity.grade),
        claim_id=str(claim_id),
        report_id="naive",
        decided_at=now or _now(),
        policy_version=NAIVE_POLICY_VERSION,
        blind_spots=tuple(mode.name for mode in AUDIT_BLIND_SPOTS),
    )


@dataclass(frozen=True)
class NaiveGate:
    """:func:`naive_decide` as an object, so a test can parametrize over gates."""

    name: str = "naive"

    def decide(self, claim_report: ClaimReport, **kwargs: Any) -> Decision:
        return naive_decide(claim_report, **kwargs)


# ---------------------------------------------------------------------------
# The boundary
# ---------------------------------------------------------------------------


def _checked_id(value: Any) -> str:
    text = str(value)
    if not _SAFE_ID.match(text):
        raise PromotionError(
            f"unusable identifier {text!r}: identifiers become filenames, so they "
            "must match [A-Za-z0-9][A-Za-z0-9._-]{0,127}"
        )
    return text


def _write_json(path: Path, record: Mapping[str, Any]) -> Path:
    """Write atomically: a half-written decision must never be readable."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(record, indent=2, sort_keys=True), encoding="utf-8")
    os.replace(tmp, path)
    return path


@dataclass(frozen=True)
class Boundary:
    """Four directories, one door.

    ``candidates/`` is writable by anyone; ``promoted/`` is written only by
    :meth:`promote`. That is an *API* claim, and API claims are worth very
    little, nothing stops a process with filesystem access from writing into
    ``promoted/`` directly. What makes the boundary real is :func:`audit`,
    which reconciles the directory against the decision log afterwards.
    """

    root: Path

    def __post_init__(self) -> None:
        object.__setattr__(self, "root", Path(self.root))
        for name in ("candidates", "promoted", "blocked", "decisions"):
            (self.root / name).mkdir(parents=True, exist_ok=True)

    def _dir(self, name: str) -> Path:
        return self.root / name

    def submit(self, claim: Mapping[str, Any]) -> Path:
        """Record a candidate. Submission asserts nothing and grants nothing."""
        claim_id = _checked_id(claim["claim_id"])
        _checked_id(claim["producer_id"])
        return _write_json(self._dir("candidates") / f"{claim_id}.json", dict(claim))

    def promote(
        self,
        claim: Mapping[str, Any],
        claim_report: ClaimReport,
        *,
        prereg: Preregistration,
        criteria_applied: Any,
        evidence_digest: str,
        current_evidence_digest: str,
        verifier_id: str,
        requested_scope: str,
        now: str = "",
    ) -> Decision:
        """The only path into ``promoted/``.

        The decision is written whether it allows or blocks, a boundary that
        logged only its allowances would make its own refusals unauditable,
        and the claim lands in ``promoted/`` or ``blocked/`` accordingly. A
        BLOCK also removes any earlier promotion of the same claim, so a
        stale allowance cannot outlive the finding that overturned it.
        """
        claim_id = _checked_id(claim["claim_id"])
        decision = decide(
            claim_report,
            prereg=prereg,
            criteria_applied=criteria_applied,
            evidence_digest=evidence_digest,
            current_evidence_digest=current_evidence_digest,
            claim_id=claim_id,
            producer_id=str(claim.get("producer_id", "")),
            verifier_id=verifier_id,
            requested_scope=requested_scope,
            now=now,
        )
        record = decision.to_dict()
        record["claim_digest"] = _safe(lambda: digest(dict(claim)), "unavailable")
        _write_json(self._dir("decisions") / f"{decision.report_id[-32:]}.json", record)
        allowed = decision.verdict == ALLOW and decision.complete
        target = self._dir("promoted" if allowed else "blocked") / f"{claim_id}.json"
        _write_json(target, dict(claim))
        stale = self._dir("blocked" if allowed else "promoted") / f"{claim_id}.json"
        if stale.exists():
            stale.unlink()
        return decision

    def decisions(self) -> tuple[dict[str, Any], ...]:
        out: list[dict[str, Any]] = []
        for path in sorted(self._dir("decisions").glob("*.json")):
            try:
                out.append(json.loads(path.read_text(encoding="utf-8")))
            except (OSError, ValueError):
                out.append({"_unreadable": path.name})
        return tuple(out)


@dataclass(frozen=True)
class ProducerView:
    """A handle exposing only :meth:`submit`.

    A speed bump, not a security boundary, and the distinction matters: the
    wrapped boundary is reachable by anyone willing to read this source, and
    the filesystem is reachable without it at all. What this buys is that the
    *ordinary* path, a producer calling what it was handed, cannot reach the
    promoted side by accident, so a reach becomes deliberate and therefore
    visible in a diff. Enforcement lives in :func:`audit`.
    """

    _boundary: Boundary

    def submit(self, claim: Mapping[str, Any]) -> Path:
        return self._boundary.submit(claim)

    def __getattr__(self, name: str) -> Any:
        raise PromotionError(
            f"a producer may not reach {name!r}: the only thing on this side of the "
            "boundary is submit(). Promotion is decided by a party that is not you."
        )


def audit(boundary: Boundary) -> tuple[str, ...]:
    """Reconcile ``promoted/`` against the decision log. Every discrepancy, once.

    **This, and not the shape of the API, is what makes the boundary real.**
    :meth:`Boundary.promote` is the only *polite* way into ``promoted/``; a
    producer with a filesystem call can write there directly, and would, given
    a deadline. So nothing here trusts that the door was used. Every file in
    ``promoted/`` is re-derived from the log: there must be a complete ALLOW
    decision naming that claim id, with no reasons, under this policy, whose
    recorded claim digest still matches the bytes on disk, and every ALLOW
    must have landed. Anything else is reported, including the cases that
    could only be a bug.

    Returns the discrepancies in one pass rather than the first one found: a
    boundary with three holes should not take three runs to describe.
    """
    problems: list[str] = []
    records = boundary.decisions()
    unreadable = [r["_unreadable"] for r in records if "_unreadable" in r]
    problems.extend(f"decision file {name} is unreadable" for name in unreadable)
    log = [r for r in records if "_unreadable" not in r]

    by_claim: dict[str, list[dict[str, Any]]] = {}
    for record in log:
        by_claim.setdefault(str(record.get("claim_id", "")), []).append(record)

    def _latest(entries: list[dict[str, Any]]) -> dict[str, Any]:
        return max(entries, key=lambda r: (str(r.get("decided_at", "")), str(r.get("report_id", ""))))

    promoted_dir = boundary.root / "promoted"
    promoted_ids: set[str] = set()
    for path in sorted(promoted_dir.glob("*.json")):
        claim_id = path.stem
        promoted_ids.add(claim_id)
        try:
            claim = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            problems.append(f"promoted/{path.name}: unreadable ({type(exc).__name__})")
            continue
        if str(claim.get("claim_id", "")) != claim_id:
            problems.append(
                f"promoted/{path.name}: file name and claim_id "
                f"{claim.get('claim_id')!r} disagree"
            )
        entries = by_claim.get(claim_id, [])
        if not entries:
            problems.append(
                f"promoted/{path.name}: no decision names this claim, it was written "
                "past the door"
            )
            continue
        current_digest = _safe(lambda: digest(claim), "unavailable")
        allows = [
            r
            for r in entries
            if r.get("verdict") == ALLOW
            and r.get("complete") is True
            and not r.get("reasons")
            and r.get("policy_version") == POLICY_VERSION
        ]
        if not allows:
            problems.append(
                f"promoted/{path.name}: no complete, reasonless ALLOW under "
                f"{POLICY_VERSION}, the crossing is not accounted for"
            )
            continue
        if not any(r.get("claim_digest") == current_digest for r in allows):
            problems.append(
                f"promoted/{path.name}: the claim on disk digests to {current_digest}, "
                "which no ALLOW decision was made about, it changed after crossing"
            )
        if _latest(entries).get("verdict") != ALLOW:
            problems.append(
                f"promoted/{path.name}: the most recent decision for this claim blocks "
                "it, yet the file is still on the promoted side"
            )

    for claim_id, entries in sorted(by_claim.items()):
        if _latest(entries).get("verdict") == ALLOW and claim_id not in promoted_ids:
            problems.append(
                f"claim {claim_id!r} has a standing ALLOW but no file in promoted/, "
                "the log and the directory disagree"
            )
        if claim_id in promoted_ids and (boundary.root / "blocked" / f"{claim_id}.json").exists():
            problems.append(f"claim {claim_id!r} is on both the promoted and blocked sides")

    return tuple(problems)
