"""``telemetry.schema``, what a run record is, and what it refuses to invent.

This module is stdlib-only and domain-agnostic in the same strict sense as
:mod:`harness.protocol`: it imports nothing from any laboratory package and
names no quantity any laboratory computes. It describes *how research
happened*, never *what the research found*, the two must not be traded
against each other (``meta/README.md``).

The storage model, and why it is not one big ledger
---------------------------------------------------
A run is a file: ``telemetry/runs/<run_id>.jsonl``, holding an append-only
sequence of **events**. The current state of a run is the *fold* of its
events, never a rewritten record.

Two properties come out of that choice, and both were picked from recorded
history rather than taste:

* **Cross-run merge conflicts are structurally impossible.** Filenames are
  UUIDs, so two sessions writing at once touch two files. This repository has
  measured the alternative: three avoidable collisions in one day between
  concurrent sessions (``hunts/frontier_math/ACTIVE-CLAIMS.md``), and a private
  ledger that needed ``merge=union`` to survive two machines (``AGENTS.md``,
  "Cached data" / ledger sync).
* **An interrupted run is legible without a guess.** A file with
  ``run_started`` and no ``run_finished`` is *interrupted*, and says so. It is
  not "probably completed", and it is not deleted. Same safe-failure rule
  ``zeta.rigor.proven_sign`` follows when it returns ``0`` for "not decided".

The honesty rules, which are the point of the module
----------------------------------------------------
1. **Unknown stays unknown.** Every optional field defaults to ``None`` and no
   code path fills one in by inference. :meth:`Run.unknown_fields` reports what
   was never captured, so a reader sees the holes without hunting for them.
2. **Model identity is declared, never sniffed.** The environment this ran in
   exposes a session id, a client version and a reasoning-effort setting, and
   **no model identifier at all**. So ``model`` arrives as an explicit input or
   not at all, and ``model_source`` records which. A telemetry system that
   guessed the model would be worse than one that admitted it did not know.
3. **Tokens and cost are provider-reported or absent.** ``estimated_usd`` is
   permitted only with a non-empty ``estimate_basis`` naming how it was
   computed; an estimate that cannot say how it was made is refused.
4. **Duration is measured, not estimated.** It is derived from two recorded
   timestamps or it is ``None``.
5. **Capture mode is a field, not a convention.** ``contemporaneous`` means the
   record was written while the run happened; ``reconstructed`` means someone
   derived it afterwards from git or artifacts, and then ``reconstructed_from``
   must say from what. The two are never rendered alike.

Validation style follows ``harness/protocol.py`` and
``ontology/registry.py``: ``*_reasons`` functions report **every** violation at
once, because a record with three problems should not need three runs to find
them; ``validate_*`` raises with all of them.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Final

__all__ = [
    "TelemetryError",
    "SCHEMA_VERSION",
    "EVENT_KINDS",
    "STATUSES",
    "OUTCOMES",
    "CAPTURE_MODES",
    "TERMINAL_STATUSES",
    "Event",
    "Run",
    "event_reasons",
    "validate_event",
    "run_reasons",
    "validate_run",
    "fold",
]


class TelemetryError(ValueError):
    """A run record that cannot be trusted to mean what it says."""


#: Bumped only when a field changes meaning. Additive fields do not bump it;
#: readers must tolerate unknown keys, which is what keeps old records readable.
SCHEMA_VERSION: Final = 1

#: The three event kinds. Three, and adding a fourth is a schema change.
EVENT_KINDS: Final[tuple[str, ...]] = ("run_started", "run_note", "run_finished")

#: How a run ended. ``running`` and ``interrupted`` are not the same thing:
#: the first is a live run, the second is one whose file never got a finish.
STATUSES: Final[tuple[str, ...]] = (
    "running",
    "completed",
    "failed",
    "interrupted",
    "aborted",
)

#: Terminal statuses, a run in one of these will not gain more events.
TERMINAL_STATUSES: Final[tuple[str, ...]] = ("completed", "failed", "aborted")

#: What the run produced, in the vocabulary the repository already uses for
#: dispositions. ``no-change`` is a first-class outcome: a run that produced
#: nothing records that it produced nothing.
OUTCOMES: Final[tuple[str, ...]] = (
    "landed",
    "no-change",
    "killed",
    "blocked",
    "refused",
    "crashed",
)

#: Whether the record was written as the run happened, or derived later.
CAPTURE_MODES: Final[tuple[str, ...]] = ("contemporaneous", "reconstructed")

_UUID_RE: Final = re.compile(
    r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$"
)
_SHA_RE: Final = re.compile(r"^[0-9a-f]{7,40}$")
_TS_RE: Final = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(\.\d+)?(Z|[+-]\d{2}:\d{2})$"
)


def _is_uuid(value: Any) -> bool:
    return isinstance(value, str) and bool(_UUID_RE.match(value))


def _is_timestamp(value: Any) -> bool:
    return isinstance(value, str) and bool(_TS_RE.match(value))


# ---------------------------------------------------------------------------
# Events
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Event:
    """One append-only line in a run's file.

    ``payload`` carries the fields that kind of event contributes. It is a
    plain mapping rather than a typed union because provider metadata differs
    per provider and pretending otherwise would be the "all providers expose
    equivalent telemetry" mistake this system is built not to make.
    """

    kind: str
    run_id: str
    at: str
    payload: dict[str, Any] = field(default_factory=dict)
    schema: int = SCHEMA_VERSION

    def as_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "kind": self.kind,
            "run_id": self.run_id,
            "at": self.at,
            **self.payload,
        }

    @classmethod
    def from_dict(cls, raw: Any) -> "Event":
        if not isinstance(raw, dict):
            raise TelemetryError(f"event must be a JSON object, got {type(raw).__name__}")
        payload = {
            k: v for k, v in raw.items() if k not in {"schema", "kind", "run_id", "at"}
        }
        return cls(
            kind=raw.get("kind", ""),
            run_id=raw.get("run_id", ""),
            at=raw.get("at", ""),
            payload=payload,
            schema=raw.get("schema", SCHEMA_VERSION),
        )


def event_reasons(event: Event) -> tuple[str, ...]:
    """Every reason this event is inadmissible, at once."""
    reasons: list[str] = []
    if event.kind not in EVENT_KINDS:
        reasons.append(f"kind {event.kind!r} is not one of {list(EVENT_KINDS)}")
    if not _is_uuid(event.run_id):
        reasons.append(f"run_id {event.run_id!r} is not a lowercase UUID")
    if not _is_timestamp(event.at):
        reasons.append(f"at {event.at!r} is not an ISO-8601 timestamp with an offset")
    if not isinstance(event.schema, int) or event.schema < 1:
        reasons.append(f"schema {event.schema!r} is not a positive integer")

    p = event.payload
    if event.kind == "run_started":
        for name in ("capture",):
            if p.get(name) not in CAPTURE_MODES:
                reasons.append(
                    f"run_started.{name} must be one of {list(CAPTURE_MODES)}, "
                    f"got {p.get(name)!r}"
                )
        if p.get("capture") == "reconstructed" and not p.get("reconstructed_from"):
            reasons.append(
                "capture='reconstructed' requires reconstructed_from naming what it "
                "was derived from, a reconstruction that cannot cite its source is "
                "indistinguishable from an invention"
            )
        if p.get("model") is not None and not p.get("model_source"):
            reasons.append(
                "model was supplied without model_source; a model identity with no "
                "stated origin cannot be told apart from a guess"
            )
        if p.get("start_commit") is not None and not _SHA_RE.match(
            str(p.get("start_commit"))
        ):
            reasons.append(f"start_commit {p.get('start_commit')!r} is not a git sha")
    elif event.kind == "run_finished":
        if p.get("status") not in TERMINAL_STATUSES:
            reasons.append(
                f"run_finished.status must be one of {list(TERMINAL_STATUSES)}, "
                f"got {p.get('status')!r}, 'running' and 'interrupted' are states a "
                f"finish event cannot assert"
            )
        if p.get("outcome") is not None and p["outcome"] not in OUTCOMES:
            reasons.append(
                f"outcome {p['outcome']!r} is not one of {list(OUTCOMES)}"
            )
        cost = p.get("cost") or {}
        if isinstance(cost, dict):
            if cost.get("estimated_usd") is not None and not cost.get("estimate_basis"):
                reasons.append(
                    "cost.estimated_usd requires cost.estimate_basis naming how it "
                    "was computed; an estimate that cannot say how it was made is a "
                    "guess wearing a number"
                )
        else:
            reasons.append("cost must be an object or absent")
        for c in p.get("commits") or ():
            if not _SHA_RE.match(str(c)):
                reasons.append(f"commit {c!r} is not a git sha")
        for a in p.get("artifacts") or ():
            if not isinstance(a, dict) or "path" not in a:
                reasons.append(f"artifact {a!r} has no path")
    return tuple(reasons)


def validate_event(event: Event) -> None:
    """Raise :class:`TelemetryError` naming every problem, or return None."""
    reasons = event_reasons(event)
    if reasons:
        raise TelemetryError("; ".join(reasons))


# ---------------------------------------------------------------------------
# Runs, the fold of a run's events
# ---------------------------------------------------------------------------

#: Fields a reader is entitled to ask about. Anything here that folds to
#: ``None`` is reported by :meth:`Run.unknown_fields` rather than hidden.
_INTERROGABLE: Final[tuple[str, ...]] = (
    "provider",
    "model",
    "model_id",
    "agent_session_id",
    "role",
    "task",
    "task_ref",
    "branch",
    "worktree",
    "start_commit",
    "finished_at",
    "outcome",
    "duration_seconds",
    "input_tokens",
    "output_tokens",
    "cache_read_tokens",
    "cache_write_tokens",
    "provider_usd",
    "estimated_usd",
    "prompt_digest",
)


@dataclass(frozen=True)
class Run:
    """The state of one run, folded from its events. Never written directly."""

    run_id: str
    started_at: str
    capture: str
    status: str
    schema: int = SCHEMA_VERSION

    provider: str | None = None
    model: str | None = None
    model_id: str | None = None
    model_source: str | None = None
    agent_session_id: str | None = None
    role: str | None = None
    task: str | None = None
    task_ref: str | None = None

    branch: str | None = None
    worktree: str | None = None
    start_commit: str | None = None
    commits: tuple[str, ...] = ()

    finished_at: str | None = None
    outcome: str | None = None
    duration_seconds: float | None = None
    exit_code: int | None = None

    input_tokens: int | None = None
    output_tokens: int | None = None
    cache_read_tokens: int | None = None
    cache_write_tokens: int | None = None
    provider_usd: float | None = None
    estimated_usd: float | None = None
    estimate_basis: str | None = None

    prompt: dict[str, Any] | None = None
    artifacts: tuple[dict[str, Any], ...] = ()
    ledger_links: tuple[dict[str, Any], ...] = ()
    error: dict[str, Any] | None = None

    reconstructed_from: str | None = None
    provider_meta: dict[str, Any] = field(default_factory=dict)
    notes: tuple[str, ...] = ()

    @property
    def prompt_digest(self) -> str | None:
        return (self.prompt or {}).get("digest")

    def unknown_fields(self) -> tuple[str, ...]:
        """Names of interrogable fields nothing ever supplied.

        The list is the point. A reader who wants to know what a run cost gets
        either a number or this field's name, never a plausible blank.
        """
        return tuple(n for n in _INTERROGABLE if getattr(self, n, None) is None)

    def as_dict(self) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for name in (
            "schema", "run_id", "started_at", "finished_at", "capture", "status",
            "outcome", "provider", "model", "model_id", "model_source",
            "agent_session_id", "role", "task", "task_ref", "branch", "worktree",
            "start_commit", "duration_seconds", "exit_code", "input_tokens",
            "output_tokens", "cache_read_tokens", "cache_write_tokens",
            "provider_usd", "estimated_usd", "estimate_basis", "prompt", "error",
            "reconstructed_from",
        ):
            out[name] = getattr(self, name)
        out["commits"] = list(self.commits)
        out["artifacts"] = [dict(a) for a in self.artifacts]
        out["ledger_links"] = [dict(x) for x in self.ledger_links]
        out["notes"] = list(self.notes)
        out["provider_meta"] = dict(self.provider_meta)
        out["unknown_fields"] = list(self.unknown_fields())
        return out


def run_reasons(run: Run) -> tuple[str, ...]:
    """Every reason this folded run is internally inconsistent, at once."""
    reasons: list[str] = []
    if not _is_uuid(run.run_id):
        reasons.append(f"run_id {run.run_id!r} is not a lowercase UUID")
    if not _is_timestamp(run.started_at):
        reasons.append(f"started_at {run.started_at!r} is not an ISO-8601 timestamp")
    if run.capture not in CAPTURE_MODES:
        reasons.append(f"capture {run.capture!r} is not one of {list(CAPTURE_MODES)}")
    if run.status not in STATUSES:
        reasons.append(f"status {run.status!r} is not one of {list(STATUSES)}")
    if run.status in TERMINAL_STATUSES and run.finished_at is None:
        reasons.append(f"status {run.status!r} without finished_at")
    if run.status in ("running", "interrupted") and run.finished_at is not None:
        reasons.append(f"status {run.status!r} with a finished_at")
    if run.model is not None and run.model_source is None:
        reasons.append("model without model_source")
    if run.estimated_usd is not None and not run.estimate_basis:
        reasons.append("estimated_usd without estimate_basis")
    if run.capture == "reconstructed" and not run.reconstructed_from:
        reasons.append("capture='reconstructed' without reconstructed_from")
    if run.duration_seconds is not None and run.duration_seconds < 0:
        reasons.append(f"duration_seconds {run.duration_seconds} is negative")
    return tuple(reasons)


def validate_run(run: Run) -> None:
    reasons = run_reasons(run)
    if reasons:
        raise TelemetryError("; ".join(reasons))


def _duration(started: str, finished: str) -> float | None:
    """Seconds between two ISO-8601 stamps, or None if either will not parse.

    Measured from two recorded instants. There is no fallback that invents a
    duration when one of them is missing.
    """
    from datetime import datetime

    try:
        a = datetime.fromisoformat(started.replace("Z", "+00:00"))
        b = datetime.fromisoformat(finished.replace("Z", "+00:00"))
    except ValueError:
        return None
    return (b - a).total_seconds()


def fold(events: list[Event]) -> Run:
    """Fold a run's events into its current state.

    A run with no ``run_finished`` folds to ``interrupted``, not to
    ``completed``, and not to an error. Being able to say "this run started and
    we do not know how it ended" is the whole reason the events are separate.
    """
    if not events:
        raise TelemetryError("cannot fold an empty event list")
    started = [e for e in events if e.kind == "run_started"]
    if not started:
        raise TelemetryError(
            f"run {events[0].run_id!r} has no run_started event; the file is "
            f"unreadable as a run rather than merely incomplete"
        )
    if len({e.run_id for e in events}) != 1:
        raise TelemetryError("events in one fold must share a run_id")
    if len(started) > 1:
        raise TelemetryError(
            f"run {started[0].run_id!r} has {len(started)} run_started events"
        )

    s = started[0].payload
    finished = [e for e in events if e.kind == "run_finished"]
    notes = tuple(
        str(e.payload.get("note", "")) for e in events if e.kind == "run_note"
    )

    tokens: dict[str, Any] = {}
    cost: dict[str, Any] = {}
    f: dict[str, Any] = {}
    status = "running" if not finished else "completed"
    finished_at: str | None = None
    duration: float | None = None

    if finished:
        last = finished[-1]
        f = last.payload
        finished_at = last.at
        status = f.get("status", "completed")
        tokens = f.get("tokens") or {}
        cost = f.get("cost") or {}
        duration = f.get("duration_seconds")
        if duration is None:
            duration = _duration(started[0].at, finished_at)
    else:
        # No finish event. Say so; do not infer one.
        status = "interrupted"

    return Run(
        run_id=started[0].run_id,
        started_at=started[0].at,
        capture=s.get("capture", "contemporaneous"),
        status=status,
        schema=started[0].schema,
        provider=s.get("provider"),
        model=s.get("model"),
        model_id=s.get("model_id"),
        model_source=s.get("model_source"),
        agent_session_id=s.get("agent_session_id"),
        role=s.get("role"),
        task=s.get("task"),
        task_ref=s.get("task_ref"),
        branch=s.get("branch"),
        worktree=s.get("worktree"),
        start_commit=s.get("start_commit"),
        commits=tuple(f.get("commits") or ()),
        finished_at=finished_at,
        outcome=f.get("outcome"),
        duration_seconds=duration,
        exit_code=f.get("exit_code"),
        input_tokens=tokens.get("input"),
        output_tokens=tokens.get("output"),
        cache_read_tokens=tokens.get("cache_read"),
        cache_write_tokens=tokens.get("cache_write"),
        provider_usd=cost.get("provider_usd"),
        estimated_usd=cost.get("estimated_usd"),
        estimate_basis=cost.get("estimate_basis"),
        prompt=s.get("prompt"),
        artifacts=tuple(f.get("artifacts") or ()),
        ledger_links=tuple(f.get("ledger_links") or s.get("ledger_links") or ()),
        error=f.get("error"),
        reconstructed_from=s.get("reconstructed_from"),
        provider_meta={**(s.get("provider_meta") or {}), **(f.get("provider_meta") or {})},
        notes=notes,
    )
