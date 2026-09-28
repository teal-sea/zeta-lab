"""``dossier.report``, the readable status report.

One rule governs the whole module: **print all four axes, always.** A report
that summarised a dossier as "verified" or showed a progress bar would undo the
one thing ``dossier/status.py`` is for. There is no headline number here and no
percentage complete, because there is no scalar that means anything.

Domain-agnostic: it formats a :class:`~dossier.schema.Dossier` and knows
nothing about what the object is.
"""

from __future__ import annotations

from dossier.schema import Dossier, dossier_id, dossier_reasons
from dossier.status import AXES

__all__ = ["render_text", "render_short"]

_RULE = "─" * 72


def _section(lines: list[str], title: str) -> None:
    lines.append("")
    lines.append(title)
    lines.append(_RULE)


def render_short(dossier: Dossier) -> str:
    """One line per axis, for a listing. Still all four."""
    parts = [f"{axis}={dossier.support.record(axis).status}" for axis in AXES]
    return f"{dossier.name}  " + "  ".join(parts)


def render_text(dossier: Dossier) -> str:
    """The full report, in the order an agent resuming cold needs it.

    Intent first, deliberately: the definition means nothing without the
    statement of what it is supposed to denote, and an agent that reads the
    formula first will pattern-match it to whatever it already knows.
    """
    lines: list[str] = []
    lines.append(_RULE)
    lines.append(f"DOSSIER  {dossier.name}")
    lines.append(f"id       {dossier_id(dossier)}")
    lines.append(f"schema   v{dossier.schema_version}")
    lines.append(_RULE)

    problems = dossier_reasons(dossier)
    if problems:
        _section(lines, "NOT VALID, this dossier should not be relied on")
        for reason in problems:
            lines.append(f"  ! {reason}")

    if dossier.intent is not None:
        _section(lines, "INTENT, what this object is for")
        lines.append(f"  {dossier.intent.purpose}")
        if dossier.intent.distinguishes_from:
            lines.append("")
            lines.append("  Do not confuse with:")
            for other in dossier.intent.distinguishes_from:
                lines.append(f"    - {other}")
        if dossier.intent.non_goals:
            lines.append("")
            lines.append("  Explicitly not:")
            for item in dossier.intent.non_goals:
                lines.append(f"    - {item}")

    if dossier.definition is not None:
        d = dossier.definition
        _section(lines, "DEFINITION, preferred")
        lines.append(f"  {d.statement}")
        if d.notation:
            lines.append(f"  notation: {d.notation}")
        if d.domain_of_validity:
            lines.append(f"  valid on: {d.domain_of_validity}")
        if d.reference:
            lines.append(f"  reference: {d.reference}")
        if d.convention_choices:
            lines.append("")
            lines.append("  Conventions pinned (derive, never remember):")
            for key, why in d.convention_choices.items():
                lines.append(f"    - {key}: {why}")

    if dossier.rejected:
        _section(lines, "REJECTED ALTERNATIVES, do not re-derive these")
        for alt in dossier.rejected:
            lines.append(f"  x {alt.statement}")
            lines.append(f"    because: {alt.why_rejected}")
            if alt.would_be_correct_if:
                lines.append(f"    would be right if: {alt.would_be_correct_if}")

    if dossier.dependencies:
        _section(lines, "DEPENDS ON")
        for dep in dossier.dependencies:
            location = f"  [{dep.location}]" if dep.location else ""
            lines.append(f"  - {dep.name} ({dep.relation}){location}")

    if dossier.obligations:
        _section(lines, "SEMANTIC OBLIGATIONS, where a wrong definition gets caught")
        for obligation in dossier.obligations:
            mark = "*" if obligation.discriminating else " "
            lines.append(f"  {mark} {obligation.name}: {obligation.statement}")
            if obligation.rationale:
                lines.append(f"      why: {obligation.rationale}")
            for support_line in obligation.support.render().splitlines():
                lines.append("    " + support_line)
            lines.append("")
        lines.append("  (* = discriminating: some plausible wrong definition fails it)")

    _section(lines, "SUPPORT, four axes, no aggregate")
    lines.append(dossier.support.render())
    lines.append("")
    lines.append("  These are not degrees of one thing. A numeric check is not a")
    lines.append("  proof; an enclosure is a proof about a finite computation; a")
    lines.append("  citation may be about a different object; a kernel-checked")
    lines.append("  theorem is about the statement as formalised.")

    if dossier.open_questions:
        _section(lines, "OPEN, and what would settle each")
        for question in dossier.open_questions:
            mark = "x" if question.resolution else "?"
            lines.append(f"  {mark} {question.question}")
            lines.append(f"    settled by: {question.what_would_settle_it}")
            if question.blocked_on:
                lines.append(f"    blocked on: {question.blocked_on}")
            if question.resolution:
                lines.append(f"    RESOLVED: {question.resolution}")

    if dossier.provenance is not None:
        _section(lines, "PROVENANCE")
        p = dossier.provenance
        lines.append(f"  generator: {p.generator} v{p.generator_version}")
        if p.code_revision:
            dirty = " (dirty)" if p.code_dirty else ""
            lines.append(f"  revision:  {p.code_revision}{dirty}")
        if p.captured_at:
            lines.append(f"  captured:  {p.captured_at}")

    if dossier.notes:
        _section(lines, "NOTES")
        lines.append(f"  {dossier.notes}")

    lines.append("")
    lines.append(_RULE)
    lines.append("This dossier records research state. It is not evidence for anything.")
    lines.append(_RULE)
    return "\n".join(lines)
