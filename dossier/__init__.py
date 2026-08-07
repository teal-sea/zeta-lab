"""``dossier`` — an experiment in representing mathematical research state.

**Status: experiment, side project, probe.** Not a platform, not a framework,
not a replacement for Mathlib, and not a claim about RH. It exists to test one
question, on one worked example:

    Can mathematical research state — intent, definitions, provenance,
    evidence, failed attempts, proof obligations and verification status — be
    represented in a structured form that helps an agent perform and *resume*
    rigorous mathematical work?

The two ideas being tested
--------------------------
1. **Intent is data.** A definition can be checked; what the definition is
   *for* can only be stated. Writing it down is what lets a later reader
   notice that a formally impeccable formula denotes the wrong object.
2. **"Verified" is four different things.** Numeric agreement, enclosure
   arithmetic, the published record, and a proof kernel fail differently and
   are falsified by different evidence. :mod:`dossier.status` keeps them
   apart, offers no aggregate, and raises if you try to take the truth value
   of the bundle.

What this deliberately does not do
----------------------------------
It defines no ledger, no verdict vocabulary and no second notion of
provenance. :mod:`ontology` already has those and a dossier is a different
object: a description of one mathematical object's research state, not a
candidate observation with a hit rate. Provenance and content hashing are
imported from :mod:`ontology.schema`.

It also issues no certificates. "Certified" is a reserved word in this
repository (`AGENTS.md`) and only the laboratory's rigorous-arithmetic module
may claim it. A dossier records *that* a certificate was obtained, and points
at it.

The seam
--------
``schema.py``, ``status.py`` and ``report.py`` name no quantity any laboratory
computes and import nothing from one. Subject matter lives in
``dossier/subjects/``. Enforced by ``tests/test_dossier_schema.py``.

Read ``docs/19-research-dossiers.md`` for the design and for what would have to
be true before any of this deserved to be extracted into its own project.
"""

from __future__ import annotations

from dossier.report import render_short, render_text
from dossier.schema import (
    Definition,
    Dependency,
    Dossier,
    DossierError,
    Intent,
    OpenQuestion,
    RejectedAlternative,
    SemanticObligation,
    dossier_id,
    dossier_reasons,
    validate_dossier,
)
from dossier.status import (
    AXES,
    AxisRecord,
    CertifiedStatus,
    FormalStatus,
    LiteratureStatus,
    NumericStatus,
    Support,
    support_reasons,
)

__all__ = [
    "AXES",
    "AxisRecord",
    "CertifiedStatus",
    "Definition",
    "Dependency",
    "Dossier",
    "DossierError",
    "FormalStatus",
    "Intent",
    "LiteratureStatus",
    "NumericStatus",
    "OpenQuestion",
    "RejectedAlternative",
    "SemanticObligation",
    "Support",
    "dossier_id",
    "dossier_reasons",
    "render_short",
    "render_text",
    "support_reasons",
    "validate_dossier",
]
