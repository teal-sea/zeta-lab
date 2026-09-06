"""``harness.review``, the standing adversarial review: two attacks per claim.

The adopted specification (`ROADMAP.md`, "The outside memos, triaged";
strategy memo integration #2) makes red-teaming continuous: every promising
result generates two attacks before anyone builds on it,

* a **blind** attack, which sees the claim, its assumptions, its code and
  its controls, but *not* the author's reasoning, so it cannot inherit the
  author's blind spots by reading them;
* a **white-box** attack, which sees everything and hunts specifically for
  correlated assumptions, shared preprocessing, normalization mismatches,
  hidden approximations, and non-independent "independent" checks, the
  failure modes the tree has actually recorded (the u·u* transpose kill;
  docs/25's shared parsing layer; ``compiler/FINDINGS.md`` §6).

The question both briefs carry, verbatim from the specification:

    What modification of the world would preserve the appearance of this
    result while making its interpretation false?

What this module is and is not. It is the *bookkeeping* of the standing
review: it generates the two briefs deterministically, enforces the blind
brief's blindness structurally (the brief is built from a record with the
reasoning field removed, so a leak is a type error rather than a promise),
and refuses to call a review standing until both attacks have recorded
outcomes from attackers other than the author. It does **not** judge
findings, ``meta/operator-functions.md``'s load-bearing guard applies: the
system may not resolve a disagreement it is party to, so an
:class:`AttackOutcome` records what the attacker found and the resolution
stays with the operator.

Domain-agnostic under the same three seam checks as
:mod:`harness.protocol`; the repository's real review records live in
``harness/departments/review_ledger.py``.
"""

from __future__ import annotations

from dataclasses import dataclass

__all__ = [
    "AttackBrief",
    "AttackOutcome",
    "ClaimUnderReview",
    "ReviewError",
    "WHITEBOX_CHECKLIST",
    "generate_briefs",
    "standing_reasons",
]


class ReviewError(ValueError):
    """A review record that cannot mean what it claims."""


#: What the white-box attacker hunts, one named failure mode per line. Each
#: entry earned its place from a recorded incident, not from imagination.
WHITEBOX_CHECKLIST: tuple[str, ...] = (
    "correlated assumptions: two premises that fail together under one fault",
    "shared preprocessing: 'independent' checks fed by one transformation",
    "normalization mismatches: a convention remembered instead of derived",
    "hidden approximations: a float where the argument needs an enclosure",
    "non-independent independent checks: shared layers carrying the verdict",
    "transposes replaced by adjoints, and every other silent symbol swap",
    "non-realizable extremizers: an optimum outside the feasible set",
    "finite-grid artifacts: a floor or spike between the probe points",
)

#: The one question both attacks exist to answer.
THE_QUESTION: str = (
    "What modification of the world would preserve the appearance of this "
    "result while making its interpretation false?"
)


@dataclass(frozen=True)
class ClaimUnderReview:
    """A promising result, packaged for attack.

    ``claim`` is the statement under review; ``assumptions``, ``code_paths``
    and ``controls_run`` are what *both* attackers get; ``author_reasoning``
    is what only the white-box attacker gets, and ``author`` is who the
    attackers must not be.
    """

    name: str
    claim: str
    author: str
    assumptions: tuple[str, ...] = ()
    code_paths: tuple[str, ...] = ()
    controls_run: tuple[str, ...] = ()
    author_reasoning: str = ""

    def __post_init__(self) -> None:
        for field_name in ("name", "claim", "author"):
            if not getattr(self, field_name).strip():
                raise ReviewError(f"a claim under review needs {field_name!r}")


@dataclass(frozen=True)
class AttackBrief:
    """One attacker's packet. ``materials`` is everything they may read."""

    role: str  # "blind" | "white-box"
    claim_name: str
    question: str
    materials: dict[str, object]
    checklist: tuple[str, ...] = ()


def generate_briefs(claim: ClaimUnderReview) -> tuple[AttackBrief, AttackBrief]:
    """The two attacks, generated deterministically from one record.

    Blindness is structural: the blind brief's materials are built here,
    field by field, and ``author_reasoning`` is not among them. A brief is
    data, hand it to whichever attacker (person, session, agent) runs the
    attack, and record what comes back as an :class:`AttackOutcome`.
    """

    shared: dict[str, object] = {
        "claim": claim.claim,
        "assumptions": claim.assumptions,
        "code_paths": claim.code_paths,
        "controls_run": claim.controls_run,
    }
    blind = AttackBrief(
        role="blind",
        claim_name=claim.name,
        question=THE_QUESTION,
        materials=dict(shared),
    )
    whitebox = AttackBrief(
        role="white-box",
        claim_name=claim.name,
        question=THE_QUESTION,
        materials={**shared, "author_reasoning": claim.author_reasoning},
        checklist=WHITEBOX_CHECKLIST,
    )
    return blind, whitebox


@dataclass(frozen=True)
class AttackOutcome:
    """What one attack found. Recording is not resolving.

    ``findings`` may be empty, "the attack ran and found nothing" is an
    outcome worth keeping, and it is not the same as "no attack ran".
    ``artifacts`` names what makes the attack rerunnable or checkable; an
    attack that produced a counterexample names it here or the outcome is
    refused (a kill nobody can rerun is a rumor).
    """

    claim_name: str
    role: str
    attacker: str
    findings: tuple[str, ...] = ()
    artifacts: tuple[str, ...] = ()
    claim_withdrawn: bool = False

    def __post_init__(self) -> None:
        if self.role not in ("blind", "white-box"):
            raise ReviewError(f"unknown attack role {self.role!r}")
        if not self.attacker.strip():
            raise ReviewError("an attack outcome needs a named attacker")
        if self.claim_withdrawn and not self.artifacts:
            raise ReviewError(
                f"attack on {self.claim_name!r} reports a withdrawal with no "
                "artifact: a kill nobody can rerun is a rumor"
            )


def standing_reasons(
    claim: ClaimUnderReview, outcomes: tuple[AttackOutcome, ...]
) -> tuple[str, ...]:
    """Everything still missing before this claim's review is standing.

    Empty means: both roles have recorded outcomes, from attackers who are
    not the author. It does not mean the claim is true, it means the claim
    has survived (or not survived) the two attacks the specification
    requires, and the record says which.
    """

    reasons: list[str] = []
    relevant = [o for o in outcomes if o.claim_name == claim.name]
    for role in ("blind", "white-box"):
        role_outcomes = [o for o in relevant if o.role == role]
        if not role_outcomes:
            reasons.append(
                f"claim {claim.name!r} has no recorded {role} attack: the "
                "review is not standing until one runs"
            )
            continue
        for outcome in role_outcomes:
            if outcome.attacker.strip() == claim.author.strip():
                reasons.append(
                    f"the {role} attack on {claim.name!r} was run by its "
                    "author: one process, however careful, is one line of "
                    "evidence, find another attacker"
                )
    return tuple(reasons)
