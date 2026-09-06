"""``telemetry``, a minimal, append-only record of how research actually happened.

Not a dashboard, not a score, not a research-state model. This package answers
one question the repository could not previously answer at all: *which run, by
which model, under which prompt, produced this artifact and this commit, and
what did it cost?*

It records **process**, never findings. ``meta/README.md``'s rule applies here
unchanged: a session that produced no mathematics and a tidy log produced
nothing. Nothing in this package may be cited as evidence about a subject.

Read ``RUN-TELEMETRY.md`` at the repository root for the operational contract;
``telemetry/schema.py`` for what a run is and the five honesty rules it
enforces.
"""

from __future__ import annotations

from telemetry.schema import (
    CAPTURE_MODES,
    EVENT_KINDS,
    OUTCOMES,
    SCHEMA_VERSION,
    STATUSES,
    Event,
    Run,
    TelemetryError,
    fold,
    validate_event,
    validate_run,
)

__all__ = [
    "SCHEMA_VERSION",
    "EVENT_KINDS",
    "STATUSES",
    "OUTCOMES",
    "CAPTURE_MODES",
    "Event",
    "Run",
    "TelemetryError",
    "fold",
    "validate_event",
    "validate_run",
]
