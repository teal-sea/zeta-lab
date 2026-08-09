"""``harness.provenance`` — independence and contamination as declared data.

Every fact this module handles already existed in the repository as prose:
department #4's battery content was first authored blind by a party
independent of the implementer (its module docstring); department #3
measured that two optimisation levels through one toolchain are not two
checks (``compiler/FINDINGS.md`` §6); and ``REDTEAM.md`` W2 records a
"pre-registered" attack whose thresholds were chosen after the data was seen,
making its pass probability near 1. All of it lived in docstrings and commit
messages, where no audit can consult it.

This module turns those facts into a record a machine can carry and an
integrity audit can read. It is deliberately *not* an attestation system:
a provenance record is a declaration, and nothing here can verify that a
declaration is true. What it can do is three things:

* distinguish **declared** facts from **undeclared** ones, so that silence
  reads as "unknown" rather than as "fine";
* name every declared **contamination** — evaluation content authored after
  its results were visible, thresholds unfrozen at execution time, tests
  edited after observing failures — because a battery with any of these has
  a pass probability that cannot be taken at face value;
* name every declared **dependence** — the battery authored by the same
  process as the subject, an oracle that calls the thing it is checking, two
  "independent" instruments sharing the critical dependency — because two
  pieces of code are not two lines of evidence.

Dependence is not contamination. Most of this repository's batteries are
authored by the same process that authored their subjects; that is a fact to
carry loudly, not a disqualification. Contamination is different: it breaks
the probability calculation that makes a pass mean anything, which is why the
integrity layer treats a declared contamination as a terminal grade.

Like :mod:`harness.protocol`, this module is domain-agnostic in the strict
sense: it imports nothing from any laboratory package, names no quantity any
laboratory computes, and is under the same three seam checks.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from typing import Final

__all__ = [
    "Provenance",
    "contamination_reasons",
    "dependence_reasons",
    "undeclared_fields",
]

#: The tri-state fields: ``True`` / ``False`` are declarations, ``None`` is
#: "nobody has said". The audit reads ``None`` as unknown, never as fine.
_DECLARABLE: Final = (
    "independent_of_subject_author",
    "results_visible_when_authored",
    "frozen_before_execution",
    "oracle_calls_subject",
    "instruments_share_critical_dependency",
    "edited_after_observing_failures",
)


@dataclass(frozen=True)
class Provenance:
    """Who authored a battery's content, when, and under what conditions.

    ``authored_by`` names the process or person that wrote the battery
    content — the rivals, decoys, surrogates, lesions and reference claims —
    which is usually not the same question as who wrote the subject.
    Everything else is a tri-state declaration; leave a field ``None`` when
    nobody is in a position to declare it, and the audit will carry the
    silence as an unknown.
    """

    authored_by: str
    authored_on: str = ""
    #: Was the battery content authored by a process independent of the one
    #: that authored the subject under test? (Department #4's admission is
    #: the repository's one ``True`` so far.)
    independent_of_subject_author: bool | None = None
    #: Were the subject's results already visible when the battery content —
    #: thresholds, windows, reference claims — was authored? Declared ``True``
    #: means the pass probability given the seen data cannot be taken at face
    #: value (the W2 failure mode).
    results_visible_when_authored: bool | None = None
    #: Were the pass criteria frozen (in code or otherwise) before the runs
    #: they judge were executed?
    frozen_before_execution: bool | None = None
    #: Does the oracle call, import, or otherwise execute the subject it is
    #: supposed to check independently?
    oracle_calls_subject: bool | None = None
    #: Do two instruments presented as independent share the dependency that
    #: carries the actual verdict? (Two optimisation levels through one
    #: compiler are one check, measured in ``compiler/FINDINGS.md`` §6.)
    instruments_share_critical_dependency: bool | None = None
    #: Were tests or thresholds edited after observing them fail, without the
    #: edit being recorded as a new evaluation?
    edited_after_observing_failures: bool | None = None
    notes: str = ""

    def describe(self) -> str:
        parts = [f"battery content authored by {self.authored_by or '(undeclared)'}"]
        if self.authored_on:
            parts.append(f"on {self.authored_on}")
        declared = {
            name: getattr(self, name) for name in _DECLARABLE if getattr(self, name) is not None
        }
        if declared:
            parts.append(
                "declares " + ", ".join(f"{name}={value}" for name, value in declared.items())
            )
        unknown = undeclared_fields(self)
        if unknown:
            parts.append(f"undeclared: {', '.join(unknown)}")
        return "; ".join(parts)


def contamination_reasons(provenance: Provenance) -> tuple[str, ...]:
    """Every declared contamination, in one pass.

    A contamination is a condition under which a battery's pass probability
    can no longer be taken at face value. Only *declared* conditions appear
    here; an undeclared field is an unknown, reported by
    :func:`undeclared_fields`, never a violation.
    """
    reasons: list[str] = []
    if provenance.results_visible_when_authored is True:
        reasons.append(
            "the subject's results were visible when the battery content was "
            "authored: criteria chosen after seeing the data pass with "
            "probability near 1, and a pass carries no information"
        )
    if provenance.frozen_before_execution is False:
        reasons.append(
            "the pass criteria were not frozen before the runs they judge: "
            "an unfrozen criterion can be tuned to the outcome"
        )
    if provenance.edited_after_observing_failures is True:
        reasons.append(
            "tests or thresholds were edited after observing failures, without "
            "the edit being recorded as a fresh evaluation"
        )
    return tuple(reasons)


def dependence_reasons(provenance: Provenance) -> tuple[str, ...]:
    """Every declared dependence between the evidence and what it checks.

    Dependence does not void a battery — most of this repository's batteries
    are self-authored — but it bounds what "independent lines of evidence"
    may be claimed, and the audit carries it on every report.
    """
    reasons: list[str] = []
    if provenance.independent_of_subject_author is False:
        reasons.append(
            "the battery content was authored by the same process as the "
            "subject: one author, however careful, is one line of evidence"
        )
    if provenance.oracle_calls_subject is True:
        reasons.append(
            "the oracle calls the subject it is supposed to check "
            "independently: agreement with itself is not agreement"
        )
    if provenance.instruments_share_critical_dependency is True:
        reasons.append(
            "instruments presented as independent share the dependency that "
            "carries the verdict: two runs of one dependency are one check"
        )
    return tuple(reasons)


def undeclared_fields(provenance: Provenance) -> tuple[str, ...]:
    """The tri-state fields nobody has declared, so silence stays visible."""
    return tuple(name for name in _DECLARABLE if getattr(provenance, name) is None)


def _all_fields() -> tuple[str, ...]:  # pragma: no cover - introspection helper
    return tuple(f.name for f in fields(Provenance))
