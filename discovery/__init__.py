"""discovery — the funnel: generate, screen, verify, and log the whole thing.

The package is built around a seam. ``discovery.schema``, ``registry``,
``ledger``, ``funnel`` and ``metrics`` are **domain-agnostic**: they know about
candidates, verdicts, provenance and conversion rates, and about nothing else.
Everything that knows what the laboratory studies lives under
``discovery.domains``, behind the registry.

The seam is the design. A funnel that cannot measure its own hit rate is
measuring its operator's enthusiasm, and a funnel whose bookkeeping is
entangled with its subject cannot be trusted to report an unflattering number.

The ledger lives in ``conjectures/``, which is **gitignored**: it is a private
notebook of unreviewed leads, most of them wrong, and nothing it contains is
evidence for anything.

``discovery.historical_cases`` is the falsification test for the ontology
itself: settled claims replayed through a pipeline, with the answer history gave
demanded of it. It is domain-agnostic like the rest of this level; the cases
live under ``discovery.domains``. It is not imported here, because a package
front door should not drag in a validation harness.

Read ``discovery/README.md`` before adding a candidate kind or a verdict state.
"""

from __future__ import annotations

from discovery.funnel import FunnelRun, Outcome, run_funnel
from discovery.ledger import Ledger, LedgerView
from discovery.metrics import (
    funnel_report,
    generator_scorecard,
    render_text,
    stage_costs,
    time_series,
)
from discovery.registry import (
    Domain,
    Generator,
    KnownnessDetector,
    Screen,
    ScreenResult,
    get_domain,
    list_domains,
    register_domain,
)
from discovery.schema import (
    SCHEMA_VERSION,
    Candidate,
    CandidateKind,
    CandidateLink,
    CandidateRelation,
    KnownEntry,
    Precision,
    Provenance,
    ValidationError,
    Verdict,
    VerdictStatus,
)

__all__ = [
    # ontology
    "SCHEMA_VERSION",
    "Candidate",
    "CandidateKind",
    "CandidateLink",
    "CandidateRelation",
    "KnownEntry",
    "Precision",
    "Provenance",
    "ValidationError",
    "Verdict",
    "VerdictStatus",
    # the seam
    "Domain",
    "Generator",
    "KnownnessDetector",
    "Screen",
    "ScreenResult",
    "get_domain",
    "list_domains",
    "register_domain",
    # the pipeline
    "FunnelRun",
    "Ledger",
    "LedgerView",
    "Outcome",
    "run_funnel",
    # the analytics
    "funnel_report",
    "generator_scorecard",
    "render_text",
    "stage_costs",
    "time_series",
]
