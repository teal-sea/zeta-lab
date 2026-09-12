"""``harness.guards``, detection power as a record, not a feeling.

The 2026-08-11 director run (``docs/25-the-director-run.md``) found that three
of the six defects in recorded claims were *guards that could not do their
job*: a completeness check whose "independent" reference was the same
technique on a coarser grid, a truncation guard that encoded "cannot decide"
as the favourable verdict, and a scan column structurally incapable of reading
False. Each had been trusted because it existed. Existence is the one property
a guard has by default; *power*, that it fires on the fault it was built for,
is a measurement, and this module is where that measurement is recorded.

The question the guard offensive asks of every guard, verbatim from the
adopted decision (``ROADMAP.md``, "The outside memos, triaged"):

    What exact incorrect computation is this guard supposed to detect, and
    has that detection power actually been demonstrated?

A :class:`GuardRecord` answers it in the declared-data style of
:mod:`harness.provenance`: ``fired`` is a tri-state where ``None`` means
*nobody has demonstrated anything*, the docs/25 state, kept visible instead
of defaulting to trust. ``True`` requires a named demonstration artifact;
``False`` is a guard demonstrated *not* to fire, which is a finding to keep
loudly, not a record to delete. ``known_misses`` carries the nearby lesions
the guard is known not to detect, because a guard's true scope is bounded by
its misses the same way a cross-check is bounded by its shared layers
(:mod:`harness.independence`).

This file is machinery only, domain-agnostic under the same three seam checks
as :mod:`harness.protocol`. The repository's actual guard records, which
name real tests and real incidents, live in
``harness/departments/guard_ledger.py``, and their demonstrations run live in
``tests/test_guard_ledger.py``: a ledger whose mutants nothing executes would
be exactly the self-validating log ``meta/ledger.py`` warns about.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "GuardRecord",
    "GuardRecordError",
    "dead_guards",
    "offensive_worklist",
    "undemonstrated",
]


class GuardRecordError(ValueError):
    """A guard record that claims more or less than its fields carry."""


@dataclass(frozen=True)
class GuardRecord:
    """One guard, its intended lesion, and whether its power was ever shown.

    ``name`` says where the guard lives (a test node, a script invocation).
    ``guards_against`` is the exact incorrect computation it exists to catch.
    ``smallest_mutant`` describes the smallest change that exhibits that
    lesion, the thing a demonstration must actually construct. ``fired`` is
    the tri-state measurement; a ``True`` or ``False`` costs a named artifact
    in ``demonstrated_by`` (a demonstration nobody can rerun is a claim, not
    a demonstration), and a ``None`` forbids one (silence stays visible).
    ``known_misses`` are nearby lesions the guard is known not to catch;
    ``scope`` states honestly what its firing does and does not establish;
    ``incident`` cites the recorded failure that motivated it, when there is
    one.
    """

    name: str
    guards_against: str
    smallest_mutant: str
    fired: bool | None
    demonstrated_by: str = ""
    known_misses: tuple[str, ...] = ()
    scope: str = ""
    incident: str = ""

    def __post_init__(self) -> None:
        for field_name in ("name", "guards_against", "smallest_mutant"):
            if not getattr(self, field_name).strip():
                raise GuardRecordError(
                    f"guard record needs a non-empty {field_name!r}: a guard "
                    "whose lesion cannot be stated cannot be measured"
                )
        if self.fired is None and self.demonstrated_by.strip():
            raise GuardRecordError(
                f"guard {self.name!r} names a demonstration but declares no "
                "outcome: record what the demonstration showed"
            )
        if self.fired is not None and not self.demonstrated_by.strip():
            raise GuardRecordError(
                f"guard {self.name!r} declares fired={self.fired!r} with no "
                "demonstration artifact: an outcome nobody can rerun is a "
                "claim, not a measurement"
            )

    def describe(self) -> str:
        status = {
            True: f"fires (demonstrated by {self.demonstrated_by})",
            False: f"DOES NOT FIRE (demonstrated by {self.demonstrated_by})",
            None: "power never demonstrated",
        }[self.fired]
        parts = [f"{self.name}: guards against {self.guards_against}; {status}"]
        if self.known_misses:
            parts.append(f"known misses: {', '.join(self.known_misses)}")
        return "; ".join(parts)


def undemonstrated(records: tuple[GuardRecord, ...]) -> tuple[str, ...]:
    """The guards whose power nobody has shown, the offensive's worklist."""

    return tuple(r.name for r in records if r.fired is None)


def dead_guards(records: tuple[GuardRecord, ...]) -> tuple[str, ...]:
    """Guards demonstrated *not* to fire on their own lesion.

    A non-empty result is a standing finding: every one of these was trusted
    while it could not do its job, and deleting the record would delete the
    finding.
    """

    return tuple(r.name for r in records if r.fired is False)


def offensive_worklist(records: tuple[GuardRecord, ...]) -> tuple[str, ...]:
    """Every open item the ledger implies, one disputable sentence each.

    Undemonstrated guards, dead guards, and every known miss, the same
    reason-tuple convention as the rest of the package. An empty tuple means
    the ledger currently implies no work, which is a statement about the
    ledger's coverage before it is one about the repository's guards.
    """

    reasons: list[str] = []
    for record in records:
        if record.fired is None:
            reasons.append(
                f"guard {record.name!r} has never had its power demonstrated: "
                f"build the mutant ({record.smallest_mutant}) and record the "
                "outcome"
            )
        elif record.fired is False:
            reasons.append(
                f"guard {record.name!r} is demonstrated not to fire on its "
                "own lesion: it provides no protection and its consumers "
                "believe it does"
            )
        for miss in record.known_misses:
            reasons.append(f"guard {record.name!r} does not detect: {miss}")
    return tuple(reasons)
