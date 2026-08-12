"""``harness.graveyard`` — killed results as first-class records.

The specification's claim (`docs/reviews/2026-08-11-decision-memo-next-phase.md`,
"The UI should celebrate killed results") is that a withdrawn result with its
cause, its catcher, its regression test and its permanent guard communicates
more scientific credibility than a page of fifty finds. This repository has
been living that claim in prose — CLEAN-KILL reports, HANDOFF withdrawal
records, ROADMAP "negative results recorded as failures" — but prose kills
scatter, and a scattered kill is a kill someone will re-derive.

A :class:`KilledResult` is the memo's card, typed:

    STATUS / WHY / CAUGHT BY / REGRESSION TEST / FORMAL OBSTRUCTION /
    CAN THIS FAILURE RECUR?

The validation carries the ethic: ``why`` and ``caught_by`` are mandatory (a
kill without a mechanism is gossip), and a record with no regression test,
no formal obstruction and no recurrence guard is *storable but loud* —
:func:`unguarded` surfaces it, because a failure nothing now prevents is a
failure scheduled to recur. Deleting a record is never the fix for its
appearing in that list.

Machinery only, domain-agnostic under the same seam checks as
:mod:`harness.protocol`. The repository's real graves live in
``harness/departments/graveyard_ledger.py``, where a conformance test pins
that every cited artifact exists.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "GraveyardError",
    "KilledResult",
    "unguarded",
]


class GraveyardError(ValueError):
    """A grave that cannot say how its occupant died."""


@dataclass(frozen=True)
class KilledResult:
    """One withdrawn result, with everything a reader needs to trust the kill.

    ``name`` identifies the claim; ``status`` is its terminal state
    (``withdrawn`` for a claim taken back, ``closed`` for a route proven
    dead); ``why`` is the mechanism of failure; ``caught_by`` is what
    actually caught it — an instrument, a control, a counterexample, a
    person. ``regression_test`` and ``formal_obstruction`` are repository
    paths when they exist; ``recurrence_guard`` says in prose what now
    prevents the same failure, or is empty and loud. ``record`` points at
    the full prose account.
    """

    name: str
    status: str  # "withdrawn" | "closed"
    why: str
    caught_by: str
    regression_test: str = ""
    formal_obstruction: str = ""
    recurrence_guard: str = ""
    record: str = ""

    def __post_init__(self) -> None:
        if self.status not in ("withdrawn", "closed"):
            raise GraveyardError(
                f"grave {self.name!r}: status must be 'withdrawn' or "
                f"'closed', not {self.status!r} — the graveyard holds only "
                "the dead"
            )
        for field_name in ("name", "why", "caught_by"):
            if not getattr(self, field_name).strip():
                raise GraveyardError(
                    f"a grave needs a non-empty {field_name!r}: a kill "
                    "without a mechanism is gossip, and gossip gets "
                    "re-derived"
                )

    @property
    def guarded(self) -> bool:
        """Whether anything now prevents this failure from recurring."""
        return bool(
            self.regression_test.strip()
            or self.formal_obstruction.strip()
            or self.recurrence_guard.strip()
        )

    def card(self) -> str:
        """The memo's card, rendered."""
        lines = [
            self.name,
            f"STATUS               {self.status.upper()}",
            f"WHY                  {self.why}",
            f"CAUGHT BY            {self.caught_by}",
            f"REGRESSION TEST      {self.regression_test or 'NONE'}",
            f"FORMAL OBSTRUCTION   {self.formal_obstruction or 'NONE'}",
            "CAN THIS FAILURE RECUR?  "
            + (self.recurrence_guard or ("guarded by the above" if self.guarded else "YES — nothing prevents it")),
        ]
        if self.record:
            lines.append(f"RECORD               {self.record}")
        return "\n".join(lines)


def unguarded(graves: tuple[KilledResult, ...]) -> tuple[str, ...]:
    """Every grave nothing now guards, one sentence each.

    Non-empty output is a worklist: each entry is a failure that can recur
    silently. The fix is a guard (and a :class:`harness.guards.GuardRecord`
    demonstrating it), never deletion of the grave.
    """

    return tuple(
        f"grave {g.name!r} has no regression test, no formal obstruction and "
        "no recurrence guard: this failure can recur silently"
        for g in graves
        if not g.guarded
    )
