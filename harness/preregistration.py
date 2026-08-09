"""``harness.preregistration`` — contamination as a derived fact, not a declaration.

:mod:`harness.provenance` says it plainly: "a provenance record is a
declaration, and nothing here can verify that a declaration is true". A
producer who writes ``results_visible_when_authored=False`` over work whose
criteria were chosen after the data was seen is, today, undetectable — the
audit reads the annotation, not the contamination. :data:`SHAM_MODES`
records the same limit under ``contaminated-preregistration``: *only a
truthful declaration is catchable*.

This module narrows that gap for one failure mode, and only one. The trick is
to stop asking the producer a question it can answer any way it likes, and
instead ask it to commit to an artifact *before* the artifact it will later be
graded against exists:

    A preregistration lists the payload digests of the evidence that
    **already existed** at the moment its criteria were frozen. If the
    evidence a report was computed against is in that list, the criteria were
    written while that evidence was visible. Nobody had to admit anything.

That makes the W2 failure mode a set membership over digests, and criteria
drift a digest inequality — two facts a checker recomputes from the artifacts
rather than reading off a flag.

A second mode, and the sharper one
----------------------------------
:data:`harness.integrity.SHAM_MODES` pins ``dropped-hardest-lesion`` as caught
by nothing, and names the countermeasure itself: *"no mechanical check can know
what was meant to be there; pin the lesion set in tests"*. That is exactly what
a criteria digest is, once the roster of instruments is inside the criteria.
Remove the smallest-magnitude lesion and the roster digests differently, so the
criteria applied are no longer the criteria frozen — mechanically, without
anyone having to notice which lesion went missing.

Two things this does **not** mean, and both matter:

* The audit is not fixed. :func:`harness.integrity.audit_department` remains
  blind to a dropped lesion and still grades the corrupted battery
  ``CALIBRATED``; that pin stands and should stand. The claim is narrower and
  entirely structural: *the audit alone cannot catch this; the audit plus a
  preregistration record can, because the record supplies a prior state the
  audit has no access to.* An audit sees one battery at one moment. Only a
  record from before can say what that battery used to be.
* What changes is the *kind* of thing preregistration is. "Pin the lesion set
  in tests" is a convention — it holds while everyone remembers. A digest that
  moves is a mechanism. The gap between those two is the whole contribution
  here, and it is a small one; it should not be described as anything larger.

The limit is the same limit as everywhere else in this module: the
preregistration is producer-supplied. This catches an **unrecorded change**,
not a determined forger who simply re-freezes the criteria around the weakened
roster and presents a consistent pair.

**What it still cannot do, stated plainly.** The digests are supplied by the
producer. A producer that fabricates its ``evidence_visible_at_freeze`` list,
or backdates ``frozen_at``, or freezes criteria it never intended to apply, is
outside mechanical reach exactly as before. This moves the trust boundary from
"the producer's summary of its own conduct" to "the producer's record of which
artifacts existed when" — a narrower, more awkward thing to lie about, because
the digests are checkable against any copy of the artifacts anyone else holds.
It does not remove the boundary, and nothing here should be read as though it
did. The honest claim is: a *silent* contamination now requires a *deliberate*
false digest, and the two are distinguishable to anyone holding the artifacts.

Like :mod:`harness.protocol`, this module is domain-agnostic in the strict
sense: stdlib plus :mod:`harness.provenance`, no laboratory import, no
subject-matter vocabulary, under the same three seam checks.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any, Final

from harness.provenance import Provenance, contamination_reasons

__all__ = [
    "DIGEST_PREFIX",
    "EVIDENCE_VISIBLE_AT_FREEZE",
    "CRITERIA_DRIFT",
    "digest",
    "Preregistration",
    "derived_findings",
    "derived_contamination_reasons",
    "Divergence",
    "declared_vs_derived",
]

#: Every digest carries its algorithm, so a stored record stays readable when
#: the algorithm changes rather than becoming a bare hex string of unknown
#: provenance.
DIGEST_PREFIX: Final = "sha256:"

#: Finding keys. A finding is named by a stable key *and* carries prose; the
#: key is what a gate maps onto its own reason vocabulary, so the two layers
#: never have to agree on wording.
EVIDENCE_VISIBLE_AT_FREEZE: Final = "evidence-visible-at-freeze"
CRITERIA_DRIFT: Final = "criteria-drift"


def _canonical(obj: Any) -> Any:
    """Structure, reduced to what JSON can serialise deterministically.

    Mappings become key-sorted objects (so digest is order-independent), sets
    become sorted lists, tuples become lists, and anything else is refused
    rather than coerced: a digest over ``repr()`` of an arbitrary object is a
    digest over an address, which would make identical evidence hash
    differently on every run.
    """
    if obj is None or isinstance(obj, (bool, int, str)):
        return obj
    if isinstance(obj, float):
        if obj != obj or obj in (float("inf"), float("-inf")):
            raise ValueError("cannot digest a non-finite float")
        return obj
    if isinstance(obj, Mapping):
        out = {}
        for key, value in obj.items():
            if not isinstance(key, str):
                raise TypeError(f"digest keys must be strings, got {type(key).__name__}")
            out[key] = _canonical(value)
        return out
    if isinstance(obj, (set, frozenset)):
        return sorted(
            (_canonical(v) for v in obj),
            key=lambda v: json.dumps(v, sort_keys=True, separators=(",", ":")),
        )
    if isinstance(obj, Sequence):
        return [_canonical(v) for v in obj]
    raise TypeError(f"cannot digest {type(obj).__name__}: give it a JSON-shaped form")


def digest(obj: Any) -> str:
    """Stable content digest: ``sha256:`` over canonical JSON.

    Order-independent for mappings, deterministic across processes and
    machines, and refusing ``NaN``/``Infinity`` — a digest that silently
    depended on dict insertion order would let the same evidence look like two
    different artifacts, which is the one thing a digest must not do.
    """
    text = json.dumps(
        _canonical(obj), sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False
    )
    return DIGEST_PREFIX + hashlib.sha256(text.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Preregistration:
    """Criteria frozen at a stated moment, with what was already visible then.

    ``evidence_visible_at_freeze`` is the load-bearing field and the only
    reason this record exists. Everything else here could be prose in a commit
    message; that tuple is what turns "were the results visible when the
    criteria were authored?" from a question the producer answers into a
    computation somebody else can run.
    """

    criteria_id: str
    criteria_text: str
    criteria_digest: str
    author_id: str
    frozen_at: str = ""
    evidence_visible_at_freeze: tuple[str, ...] = ()

    @classmethod
    def freeze(
        cls,
        criteria: Any,
        *,
        criteria_id: str,
        author_id: str,
        frozen_at: str = "",
        already_existing_evidence: Sequence[Any] = (),
    ) -> "Preregistration":
        """Freeze ``criteria``, recording the digest of everything visible now.

        ``already_existing_evidence`` takes either payloads or digest strings:
        anything already carrying the :data:`DIGEST_PREFIX` is taken as a
        digest, everything else is digested here. Passing the payloads is the
        better habit — it is one fewer place for a hand-written string to be
        wrong.
        """
        visible = tuple(
            sorted(
                {
                    item if isinstance(item, str) and item.startswith(DIGEST_PREFIX) else digest(item)
                    for item in already_existing_evidence
                }
            )
        )
        return cls(
            criteria_id=str(criteria_id),
            criteria_text=criteria if isinstance(criteria, str) else json.dumps(
                _canonical(criteria), sort_keys=True, separators=(",", ":")
            ),
            criteria_digest=digest(criteria),
            author_id=str(author_id),
            frozen_at=str(frozen_at),
            evidence_visible_at_freeze=visible,
        )


def derived_findings(
    prereg: Preregistration, *, criteria_applied: Any, evidence_digest: str
) -> tuple[tuple[str, str], ...]:
    """Every contamination finding derivable from the artifacts, as (key, prose).

    Two findings, both mechanical, neither consulting any declaration:

    * the evidence a report was computed against was *already visible* when
      the criteria were frozen — the W2 failure mode, as set membership;
    * the criteria actually applied do not digest to the criteria that were
      frozen — post-hoc drift, as a digest inequality.
    """
    findings: list[tuple[str, str]] = []
    visible = tuple(prereg.evidence_visible_at_freeze)
    if evidence_digest in visible:
        findings.append(
            (
                EVIDENCE_VISIBLE_AT_FREEZE,
                f"the criteria {prereg.criteria_id!r} were frozen at a moment when the "
                f"evidence {evidence_digest} was already visible: whatever the record "
                "declares, these criteria were not authored blind to this evidence",
            )
        )
    applied = digest(criteria_applied)
    if applied != prereg.criteria_digest:
        findings.append(
            (
                CRITERIA_DRIFT,
                f"the criteria applied digest to {applied}, the criteria frozen as "
                f"{prereg.criteria_id!r} digest to {prereg.criteria_digest}: what was "
                "judged is not what was frozen",
            )
        )
    return tuple(findings)


def derived_contamination_reasons(
    prereg: Preregistration, *, criteria_applied: Any, evidence_digest: str
) -> tuple[str, ...]:
    """The prose of :func:`derived_findings`, in the ``*_reasons()`` house shape."""
    return tuple(
        prose
        for _, prose in derived_findings(
            prereg, criteria_applied=criteria_applied, evidence_digest=evidence_digest
        )
    )


@dataclass(frozen=True)
class Divergence:
    """What the record says about itself, beside what its artifacts say.

    This object is the headline of the whole experiment, and the only case
    that separates a gate which recomputes from a gate which reads
    annotations. ``diverges`` is true exactly when a producer declared itself
    clean — :func:`harness.provenance.contamination_reasons` found nothing —
    while the digests show the criteria were frozen with this evidence already
    visible, or show criteria other than the frozen ones being applied. Every
    other combination is a case both gates get right, and therefore measures
    nothing about either.

    The limit, stated so it travels with the result: the digests compared here
    are supplied by the producer. A producer that fabricates its own
    ``evidence_visible_at_freeze`` list defeats this exactly as it defeats the
    declaration it replaces. What changed is *what a lie has to look like* — a
    false digest is checkable against any other copy of the artifacts, and a
    false ``False`` is not. That is a narrower trust boundary, not the absence
    of one, and no reading of this record should say otherwise.
    """

    declared_clean: bool
    declared_reasons: tuple[str, ...]
    derived_reasons: tuple[str, ...]

    @property
    def diverges(self) -> bool:
        return self.declared_clean and bool(self.derived_reasons)

    def describe(self) -> str:
        if self.diverges:
            return (
                "the record declares no contamination while its artifacts show "
                + "; ".join(self.derived_reasons)
            )
        if self.derived_reasons:
            return "declared and derived agree that something is wrong: " + "; ".join(
                self.derived_reasons
            )
        if not self.declared_clean:
            return "declared contaminated, nothing further derivable from the artifacts"
        return "declared clean; nothing contradicts it in the artifacts supplied"

    def to_dict(self) -> dict[str, Any]:
        return {
            "declared_clean": self.declared_clean,
            "declared_reasons": list(self.declared_reasons),
            "derived_reasons": list(self.derived_reasons),
            "diverges": self.diverges,
        }


def declared_vs_derived(
    provenance: Provenance | None,
    prereg: Preregistration,
    *,
    criteria_applied: Any,
    evidence_digest: str,
) -> Divergence:
    """Put the declaration and the derivation side by side.

    ``provenance=None`` is *not* clean: nobody declared anything, so
    ``declared_clean`` is False and no divergence can be measured. Silence
    reads as unknown here for the same reason it does in
    :func:`harness.provenance.undeclared_fields`.
    """
    declared = () if provenance is None else contamination_reasons(provenance)
    return Divergence(
        declared_clean=provenance is not None and not declared,
        declared_reasons=tuple(declared),
        derived_reasons=derived_contamination_reasons(
            prereg, criteria_applied=criteria_applied, evidence_digest=evidence_digest
        ),
    )
