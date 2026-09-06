"""``dossier.schema``, what an AI agent needs in order to resume rigorous work.

**This is an experiment and a side project.** It is not a platform, not a
replacement for Mathlib, and not a claim about RH. It tests one question:

    Can mathematical research state, intent, definitions, provenance,
    evidence, failed attempts, proof obligations and verification status, be
    represented in a structured form that helps an agent perform and *resume*
    rigorous mathematical work?

The design premise is a failure mode this repository already knows about in
another guise: `AGENTS.md` devotes a whole section to name collisions in the
laboratory, where one identifier means three unrelated things depending on the
module. Those are naming traps a *person* rereads a docstring to escape. An agent resuming cold has no such reflex, and
the expensive version of the mistake is not a wrong import, it is a
definition that is formally impeccable and denotes the wrong object.

Hence the two load-bearing pieces here:

* :class:`Intent`, what the object is *for*, in prose, before any formula.
  A definition can be checked; an intent can only be stated, and stating it is
  what makes a later mismatch visible.
* :class:`SemanticObligation`, a property the definition must have *in order
  to be the intended object*, each carrying its own evidence. This is the
  answer to "formally valid, semantically wrong": the obligations are where a
  wrong-but-well-typed definition gets caught.

And the piece that is load-bearing by omission: evidence is a
:class:`~dossier.status.Support`, which has four independent axes and no
aggregate. See ``dossier/status.py`` for why.

Reuse, not reinvention
----------------------
Provenance comes from :mod:`ontology.schema`; this module defines none of its
own, and defines no ledger and no verdict vocabulary either. A dossier is a
*description of an object's research state*, not a candidate observation, and
the two must not be confused. If you want to record "here is a lead that might
be new", that is :mod:`ontology`, and it already exists.

The one thing not reused is identity. :func:`ontology.schema.content_hash`
canonicalises a *claim*, it demands a candidate kind, prefixes ids with
``cand-``, and rounds numbers to a dedup tolerance because two runs asserting
the same number should collide. None of that applies to a dossier, whose
identity is over prose and which is not a candidate. Borrowing it would have
made every dossier look like a candidate in any log that read the prefix, so
:func:`dossier_id` hashes its own three fields under its own prefix.

The seam
--------
This module names no quantity any laboratory computes and imports nothing from
one. Subject matter lives in ``dossier/subjects/``. Enforced by
``tests/test_dossier_schema.py`` the same three ways as the other seams.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum
from typing import Any, Final, Mapping, Sequence

import hashlib
import json

from ontology.schema import Provenance

from dossier.status import Support, support_reasons

__all__ = [
    "DossierError",
    "Confidence",
    "Intent",
    "Definition",
    "RejectedAlternative",
    "SemanticObligation",
    "Dependency",
    "OpenQuestion",
    "Dossier",
    "dossier_reasons",
    "validate_dossier",
    "dossier_id",
]

SCHEMA_VERSION: Final[str] = "0.1"


class DossierError(Exception):
    """A dossier is malformed."""


class Confidence(StrEnum):
    """How settled is this piece, not how true, how *settled here*."""

    SETTLED = "settled"
    WORKING = "working"
    UNRESOLVED = "unresolved"


@dataclass(frozen=True)
class Intent:
    """What the object is for, stated before any formula.

    ``purpose`` is prose on purpose: it is the thing a formula cannot carry.
    ``distinguishes_from`` names the objects this one is most likely to be
    confused with, the field exists because the recurring expensive error in
    this repository's own history is a name collision, not an arithmetic slip.
    """

    purpose: str
    distinguishes_from: tuple[str, ...] = ()
    non_goals: tuple[str, ...] = ()


@dataclass(frozen=True)
class Definition:
    """The preferred definition, and the convention decisions inside it.

    ``convention_choices`` is where a normalisation that the literature
    disagrees about gets pinned, with the reason. `AGENTS.md`'s rule is
    "derive conventions, never remember them"; this field records *which*
    derivation was run, so the next agent re-derives rather than trusts.
    """

    statement: str
    notation: str = ""
    convention_choices: Mapping[str, str] = field(default_factory=dict)
    domain_of_validity: str = ""
    reference: str = ""


@dataclass(frozen=True)
class RejectedAlternative:
    """A definition that was tried and put down, with the reason.

    The most valuable field in the schema for an agent resuming cold, and the
    one a human would never write unprompted. Without it the next pass
    re-derives the same dead end, and, worse, may adopt it, because a
    rejected alternative usually looks reasonable.
    """

    statement: str
    why_rejected: str
    would_be_correct_if: str = ""


@dataclass(frozen=True)
class SemanticObligation:
    """A property the definition must have to *be the intended object*.

    Not a theorem to prove for its own sake: a discriminating test. A
    definition that satisfies every obligation is not thereby correct, but one
    that fails any of them is provably not the object the intent describes.

    ``discriminating`` marks the obligations that some plausible wrong
    definition actually fails. An obligation nothing fails is a tautology
    dressed as a check, and :func:`dossier_reasons` requires at least one that
    is not.
    """

    name: str
    statement: str
    rationale: str = ""
    discriminating: bool = False
    support: Support = field(default_factory=Support)


@dataclass(frozen=True)
class Dependency:
    """Something this object is defined in terms of."""

    name: str
    relation: str
    location: str = ""


@dataclass(frozen=True)
class OpenQuestion:
    """What is not settled, and what would settle it.

    ``what_would_settle_it`` is required. A question recorded without one is a
    mood, and it is exactly what an agent resuming cannot act on.

    ``resolution`` is the second half of the same discipline, added after a
    worked example's first real incident: a formal-axis record went stale for
    hours after external evidence satisfied it, because nothing coupled that
    evidence to recorded status (see ``dossier/subjects/`` for the example and
    its tests). An open question has exactly the same failure shape one level
    up, ``what_would_settle_it`` can be satisfied while the record still says
    "open", so it gets the same fix: an explicit field to write the answer
    into, rather than deleting or silently editing the question once it stops
    being open. Left ``""`` (the default), the question is open. A non-blank
    value is a claim that it no longer is, and per this schema's
    history-keeping convention (never erase a superseded record, add the
    correction next to it) the question and ``what_would_settle_it`` stay in
    place as the record of what was asked and what would have answered it,
    ``resolution`` is what did.
    """

    question: str
    what_would_settle_it: str
    blocked_on: str = ""
    resolution: str = ""


@dataclass(frozen=True)
class Dossier:
    """The research state of one mathematical object."""

    name: str
    schema_version: str = SCHEMA_VERSION
    intent: Intent | None = None
    definition: Definition | None = None
    rejected: tuple[RejectedAlternative, ...] = ()
    obligations: tuple[SemanticObligation, ...] = ()
    dependencies: tuple[Dependency, ...] = ()
    open_questions: tuple[OpenQuestion, ...] = ()
    support: Support = field(default_factory=Support)
    provenance: Provenance | None = None
    notes: str = ""

    def obligation(self, name: str) -> SemanticObligation:
        for item in self.obligations:
            if item.name == name:
                return item
        known = ", ".join(o.name for o in self.obligations) or "(none)"
        raise KeyError(f"no obligation {name!r}; declared: {known}")

    @property
    def discriminating_obligations(self) -> tuple[SemanticObligation, ...]:
        return tuple(o for o in self.obligations if o.discriminating)


def dossier_id(dossier: Dossier) -> str:
    """A stable id for the *identity* of the object, not its research state.

    Keyed on the name, the intent's purpose and the definition statement, the
    three things that make it this object. Evidence, obligations and open
    questions deliberately do not enter: they change as work proceeds, and an
    id that changed with them would make the record untraceable across exactly
    the sessions it exists to connect.

    Not :func:`ontology.schema.content_hash`: see the module docstring. A
    dossier is not a candidate, and an id that said ``cand-`` would be read as
    one.
    """
    payload = json.dumps(
        {
            "v": SCHEMA_VERSION,
            "dossier": str(dossier.name),
            "purpose": str(dossier.intent.purpose) if dossier.intent else "",
            "definition": str(dossier.definition.statement) if dossier.definition else "",
        },
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return "doss-" + hashlib.sha256(payload).hexdigest()[:32]


def _text_reasons(value: Any, label: str) -> list[str]:
    return [] if str(value or "").strip() else [f"{label} is empty"]


def dossier_reasons(dossier: Dossier) -> tuple[str, ...]:
    """Every reason ``dossier`` is not usable, in one pass.

    The refusals encode the experiment's thesis. A dossier without an intent
    is a formula with no way to tell whether it is the right formula. One
    without a discriminating obligation has no test that a plausible wrong
    definition would fail. One asserting support with no artifact is
    decoration.
    """
    reasons: list[str] = []
    reasons += _text_reasons(dossier.name, "dossier name")

    if str(dossier.schema_version) != SCHEMA_VERSION:
        reasons.append(
            f"unknown schema version {dossier.schema_version!r} (this build speaks {SCHEMA_VERSION})"
        )

    if dossier.intent is None:
        reasons.append(
            "dossier declares no intent: without a statement of what the object is "
            "for, a formally valid definition of the wrong object cannot be caught"
        )
    else:
        reasons += _text_reasons(dossier.intent.purpose, "intent purpose")

    if dossier.definition is None:
        reasons.append("dossier declares no definition")
    else:
        reasons += _text_reasons(dossier.definition.statement, "definition statement")

    if not dossier.obligations:
        reasons.append("dossier declares no semantic obligation")
    elif not dossier.discriminating_obligations:
        reasons.append(
            "dossier declares no *discriminating* obligation: every obligation is "
            "one that no plausible wrong definition would fail, which tests nothing"
        )

    seen: set[str] = set()
    for obligation in dossier.obligations:
        if not str(obligation.name).strip():
            reasons.append("an obligation has an empty name")
        elif obligation.name in seen:
            reasons.append(f"more than one obligation named {obligation.name!r}")
        seen.add(obligation.name)
        reasons += _text_reasons(obligation.statement, f"obligation {obligation.name!r} statement")
        reasons += [
            f"obligation {obligation.name!r}: {reason}"
            for reason in support_reasons(obligation.support)
        ]

    for rejected in dossier.rejected:
        reasons += _text_reasons(rejected.statement, "a rejected alternative's statement")
        reasons += _text_reasons(
            rejected.why_rejected,
            f"rejected alternative {rejected.statement[:40]!r}: why_rejected",
        )

    for question in dossier.open_questions:
        reasons += _text_reasons(question.question, "an open question's text")
        reasons += _text_reasons(
            question.what_would_settle_it,
            f"open question {question.question[:40]!r}: what_would_settle_it",
        )
        if question.resolution and not question.resolution.strip():
            reasons.append(
                f"open question {question.question[:40]!r}: resolution is set "
                "but blank, leave it '' if still open, or write the answer"
            )

    reasons += list(support_reasons(dossier.support))
    return tuple(reasons)


def validate_dossier(dossier: Dossier) -> None:
    """Raise :class:`DossierError` listing every problem, or return quietly."""
    reasons = dossier_reasons(dossier)
    if reasons:
        raise DossierError(
            f"dossier {dossier.name!r} is not usable:\n  - " + "\n  - ".join(reasons)
        )
