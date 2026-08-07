"""``dossier.status`` — four kinds of support, kept apart on purpose.

This module exists to make one mistake impossible to write down: collapsing
"we checked it numerically", "every step carried an enclosure", "a paper says
so" and "a proof kernel accepted it" into a single ``verified`` flag.

Those four are not degrees of the same thing. They fail differently, they are
falsified by different evidence, and one of them can be true while another is
false without any contradiction:

* a formula can be **numerically checked** to forty digits and still be false
  — this repository's house rule, and the theorem behind it, are in ``docs/08``;
* an **enclosure** proves a numeric statement about a finite computation and
  says nothing about the general case;
* the **literature** can support a statement that the local definitions do not
  actually instantiate — the citation is about a different object;
* a **kernel-checked** proof is about the Lean statement, which may not be the
  statement anyone meant.

So a dossier carries four independent axes and no aggregate. There is
deliberately no ``is_verified`` property, no ``__bool__`` and no ordering
between the axes: any of those would let a caller write ``if dossier.ok:`` and
lose exactly the distinction this module is for. The only summary offered is
:meth:`Support.render`, which prints all four.

The vocabulary is shared with the rest of the repository rather than reinvented.
"Certified" keeps its reserved meaning (``AGENTS.md``): only a quantity every
step of whose computation carried an enclosure, and only the laboratory's
rigorous-arithmetic module is entitled to produce one. A dossier records that a
certificate was obtained; it never issues one.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import StrEnum
from typing import Any, Final, Mapping

__all__ = [
    "AXES",
    "NumericStatus",
    "CertifiedStatus",
    "LiteratureStatus",
    "FormalStatus",
    "AxisRecord",
    "Support",
    "support_reasons",
]


class NumericStatus(StrEnum):
    """Did a floating point or arbitrary-precision computation agree?

    ``AGREES_TO_TOLERANCE`` is the strongest value here and it is still weak:
    it is a statement about the sample points that were tried.
    """

    NOT_ATTEMPTED = "not-attempted"
    AGREES_TO_TOLERANCE = "agrees-to-tolerance"
    DISAGREES = "disagrees"
    INCONCLUSIVE = "inconclusive"


class CertifiedStatus(StrEnum):
    """Did every step carry an enclosure?

    ``NOT_DECIDED`` is the mandatory safe failure mode, mirroring the
    laboratory's rigorous ``proven_sign`` returning 0: an enclosure that could
    not decide the question is not a negative result about the mathematics.
    """

    NOT_ATTEMPTED = "not-attempted"
    CERTIFIED = "certified"
    NOT_DECIDED = "not-decided"
    REFUTED = "refuted"


class LiteratureStatus(StrEnum):
    """What does the published record say?

    ``UNLOCATED`` is the absence of a lookup, never evidence of novelty — the
    same rule ``ontology/README.md`` states for the knownness detector.
    """

    UNLOCATED = "unlocated"
    STANDARD = "standard"
    SUPPORTED = "supported"
    CONTESTED = "contested"
    CONTRADICTED = "contradicted"


class FormalStatus(StrEnum):
    """What has a proof kernel accepted?

    ``STATED_WITH_SORRY`` is tracked rather than hidden: a ``sorry`` is an
    uncertified step and counts as nothing (``AGENTS.md``), but a statement
    that at least exists is a different situation from one that does not, and
    the difference is worth recording.

    ``STATED_UNCHECKED`` was added after the first real use of this schema,
    and the reason it exists is the whole argument for the schema. A source
    file held complete proofs with no ``sorry`` in them, and the toolchain was
    not installed in the environment doing the recording. None of the other
    four values could be written down honestly: ``NOT_ATTEMPTED`` denies work
    that plainly exists, ``STATED_WITH_SORRY`` is false when there is no
    ``sorry``, ``FAILED`` is a lie, and ``PROVED`` would assert that a kernel
    accepted something nobody watched a kernel accept.

    The distinction it draws is *who checked*, and it is the same distinction
    the repository's own rule makes: nothing counts until it compiles. Reading
    a complete-looking proof is not compiling it.
    """

    NOT_ATTEMPTED = "not-attempted"
    STATED_WITH_SORRY = "stated-with-sorry"
    STATED_UNCHECKED = "stated-unchecked"
    PROVED = "proved"
    FAILED = "failed"


#: The four axes, in the order a report prints them. Weakest support first, so
#: that reading top to bottom never suggests a progression that is not there.
AXES: Final[tuple[str, ...]] = ("numeric", "certified", "literature", "formal")

_AXIS_TYPES: Final[dict[str, type[StrEnum]]] = {
    "numeric": NumericStatus,
    "certified": CertifiedStatus,
    "literature": LiteratureStatus,
    "formal": FormalStatus,
}

#: Values that assert something positive, per axis. Used only to refuse an
#: unsupported assertion (see :func:`support_reasons`) — never to compute an
#: aggregate score.
_ASSERTIVE: Final[dict[str, frozenset[str]]] = {
    "numeric": frozenset({NumericStatus.AGREES_TO_TOLERANCE}),
    "certified": frozenset({CertifiedStatus.CERTIFIED}),
    "literature": frozenset({LiteratureStatus.STANDARD, LiteratureStatus.SUPPORTED}),
    "formal": frozenset({FormalStatus.PROVED}),
}


@dataclass(frozen=True)
class AxisRecord:
    """One axis: its status, what produced it, and where to look.

    ``detail`` is required whenever the status asserts something, because an
    assertion nobody can re-derive is decoration. ``artifact`` points at the
    test, the script, the citation or the Lean declaration.
    """

    status: str
    detail: str = ""
    artifact: str = ""
    parameters: Mapping[str, Any] = field(default_factory=dict)

    def asserts_support(self, axis: str) -> bool:
        return str(self.status) in _ASSERTIVE.get(axis, frozenset())


@dataclass(frozen=True)
class Support:
    """The four axes together, with no way to reduce them to one.

    Deliberately absent: ``is_verified``, ``__bool__``, ``score``, any
    ordering. If you find yourself wanting one, the thing you actually want is
    to name which axis you mean.
    """

    numeric: AxisRecord = field(default_factory=lambda: AxisRecord(NumericStatus.NOT_ATTEMPTED))
    certified: AxisRecord = field(
        default_factory=lambda: AxisRecord(CertifiedStatus.NOT_ATTEMPTED)
    )
    literature: AxisRecord = field(
        default_factory=lambda: AxisRecord(LiteratureStatus.UNLOCATED)
    )
    formal: AxisRecord = field(default_factory=lambda: AxisRecord(FormalStatus.NOT_ATTEMPTED))

    def __bool__(self) -> bool:  # pragma: no cover - the raise is the point
        raise TypeError(
            "Support has no truth value on purpose: a dossier is not 'verified' "
            "or 'unverified'. Name the axis you mean — .numeric, .certified, "
            ".literature or .formal — and read its status."
        )

    def record(self, axis: str) -> AxisRecord:
        if axis not in _AXIS_TYPES:
            raise KeyError(f"unknown axis {axis!r}; known: {', '.join(AXES)}")
        return getattr(self, axis)

    def render(self) -> str:
        """All four axes, always. There is no short form."""
        lines = []
        for axis in AXES:
            rec = self.record(axis)
            line = f"  {axis:<11} {rec.status}"
            if rec.detail:
                line += f" — {rec.detail}"
            if rec.artifact:
                line += f"  [{rec.artifact}]"
            lines.append(line)
        return "\n".join(lines)


def support_reasons(support: Support) -> tuple[str, ...]:
    """Every reason ``support`` is malformed, in one pass."""
    reasons: list[str] = []
    for axis in AXES:
        rec = support.record(axis)
        enum_type = _AXIS_TYPES[axis]
        valid = {str(member) for member in enum_type}
        if str(rec.status) not in valid:
            reasons.append(
                f"{axis} status {rec.status!r} is not one of: {', '.join(sorted(valid))}"
            )
            continue
        if rec.asserts_support(axis) and not str(rec.detail).strip():
            reasons.append(
                f"{axis} asserts {rec.status!r} with no detail: an assertion nobody "
                "can re-derive is decoration"
            )
        if rec.asserts_support(axis) and not str(rec.artifact).strip():
            reasons.append(
                f"{axis} asserts {rec.status!r} with no artifact: name the test, "
                "citation or declaration that carries it"
            )
    return tuple(reasons)
