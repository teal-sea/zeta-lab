"""discovery.ledger — the append-only log the whole funnel is measured from.

Domain-agnostic, like the rest of this layer: it stores records, it does not
know what they are about.

Two streams, one directory
--------------------------
* **candidates** — ``ledger.jsonl``, one :class:`~discovery.schema.Candidate`
  per line, exactly the format :func:`discovery.schema.read_jsonl` reads. The
  log is append-only and the *last* record for an id wins
  (:func:`~discovery.schema.latest_by_id`), so a candidate that is generated,
  checkpointed and then decided appears two or three times and counts once.
* **runs** — ``ledger.runs.jsonl``, one funnel-run record per line.

The second stream exists because of a gap the schema states about itself
(``discovery/README.md`` §7.1): *a candidate record needs a candidate*, so a
lead source that ran for an hour and emitted nothing leaves no trace in the
first stream — and every conversion rate computed without it has the wrong
denominator. Run records carry the invocation counts, the zero-yield ones
included, and are written twice (``state="started"`` then ``state="finished"``)
so that a run which died mid-way is still in the denominator.

Privacy
-------
The default location is ``<repo>/conjectures/``, which is **gitignored**. A
ledger is a private laboratory notebook: it contains unreviewed leads, most of
them wrong, and publishing one would be publishing a list of things nobody has
checked. Nothing in this module ever writes outside the path it is given.

Concurrency
-----------
Appends take an exclusive :mod:`fcntl` lock (where the platform has one) around
a single write of one complete line to a handle opened ``O_APPEND``, followed by
``flush`` + ``fsync``. Two processes appending at once therefore interleave
whole lines and never half of one. Where :mod:`fcntl` is unavailable the
``O_APPEND`` single-write behaviour is still relied on and the module says so
via :data:`LOCKING`.

:meth:`Ledger.compact` is the exception and is **not** concurrency-safe: it
reads, rewrites and renames, so anything appended in between is lost with the
file it replaced. Appends are safe; compaction is a maintenance operation to be
run alone.
"""

from __future__ import annotations

import json
import os
import tempfile
from collections.abc import Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final

from discovery.schema import (
    Candidate,
    ValidationError,
    from_dict,
    latest_by_id,
    to_json,
    validate_candidate,
)

try:  # pragma: no cover - platform dependent
    import fcntl as _fcntl
except ImportError:  # pragma: no cover - Windows
    _fcntl = None  # type: ignore[assignment]

__all__ = [
    "DEFAULT_LEDGER_DIR",
    "DEFAULT_LEDGER_PATH",
    "LEDGER_ENV_VAR",
    "LOCKING",
    "RUN_RECORD_TYPE",
    "LedgerError",
    "LedgerView",
    "Ledger",
    "default_ledger_path",
    "runs_path_for",
]

#: ``True`` when advisory locking is available on this platform.
LOCKING: Final[bool] = _fcntl is not None

#: Set this to override the default ledger location for a whole process.
LEDGER_ENV_VAR: Final[str] = "DISCOVERY_LEDGER"

#: The tag that marks a line in the run stream, so a mixed file is still safe.
RUN_RECORD_TYPE: Final[str] = "funnel_run"

#: Derived from ``__file__`` — never from a working directory, and never
#: hard-coded, so no machine-local path is baked into a committed file.
DEFAULT_LEDGER_DIR: Final[Path] = Path(__file__).resolve().parent.parent / "conjectures"
DEFAULT_LEDGER_PATH: Final[Path] = DEFAULT_LEDGER_DIR / "ledger.jsonl"


class LedgerError(Exception):
    """The log could not be read or written."""


def default_ledger_path() -> Path:
    """The default candidate log, honouring :data:`LEDGER_ENV_VAR`."""
    override = os.environ.get(LEDGER_ENV_VAR)
    if override:
        return Path(override).expanduser()
    return DEFAULT_LEDGER_PATH


def runs_path_for(path: str | Path) -> Path:
    """The run stream that sits beside a candidate log.

    ``ledger.jsonl`` → ``ledger.runs.jsonl``; the suffix is replaced rather than
    appended so the two stay adjacent when a directory is listed.
    """
    target = Path(path)
    return target.with_name(target.stem + ".runs" + target.suffix)


def _append_line(path: Path, line: str) -> None:
    """Append one complete line, atomically enough for concurrent writers."""
    if not line.endswith("\n"):
        line += "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("a", encoding="utf-8") as handle:
            if _fcntl is not None:
                _fcntl.flock(handle.fileno(), _fcntl.LOCK_EX)
            try:
                handle.write(line)
                handle.flush()
                os.fsync(handle.fileno())
            finally:
                if _fcntl is not None:
                    _fcntl.flock(handle.fileno(), _fcntl.LOCK_UN)
    except OSError as exc:
        raise LedgerError(f"could not append to {path.name}: {exc}") from exc


def _replace_atomically(path: Path, text: str) -> None:
    """Write ``text`` to ``path`` via a temporary file and one rename."""
    path.parent.mkdir(parents=True, exist_ok=True)
    handle = tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=str(path.parent), delete=False
    )
    try:
        with handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(handle.name, path)
    except OSError as exc:  # pragma: no cover - filesystem failure
        Path(handle.name).unlink(missing_ok=True)
        raise LedgerError(f"could not rewrite {path.name}: {exc}") from exc


@dataclass(frozen=True, slots=True)
class LedgerView:
    """An immutable snapshot: what the metrics layer is handed.

    Reading is separated from the store so that a report can be computed from a
    hand-built set of records with no file anywhere — which is how the metrics
    arithmetic is pinned by the test suite.
    """

    candidates: tuple[Candidate, ...] = ()
    runs: tuple[Mapping[str, Any], ...] = ()
    path: str | None = None

    def latest(self) -> dict[str, Candidate]:
        """Collapse the append-only log: last record per id wins."""
        return latest_by_id(self.candidates)

    def latest_runs(self) -> tuple[Mapping[str, Any], ...]:
        """Collapse the run stream: last record per ``run_id`` wins.

        A run appears as ``started`` and then as ``finished``. A run that only
        ever appears as ``started`` died, and stays visible as such — that is
        the point of writing the first record.
        """
        by_id: dict[str, Mapping[str, Any]] = {}
        for i, record in enumerate(self.runs):
            key = str(record.get("run_id") or f"__anonymous-{i}")
            by_id[key] = record
        return tuple(by_id.values())

    def is_empty(self) -> bool:
        return not self.candidates and not self.runs


class Ledger:
    """An append-only store of candidates plus the funnel runs that made them.

    ``Ledger(path)`` never touches the filesystem until something is written or
    read; a ledger that does not exist yet reads as empty rather than raising,
    because "no runs yet" is a legitimate state with a legitimate report.
    """

    def __init__(
        self,
        path: str | Path | None = None,
        *,
        runs_path: str | Path | None = None,
        verify_id: bool = True,
    ) -> None:
        self.path: Path = Path(path) if path is not None else default_ledger_path()
        self.runs_path: Path = (
            Path(runs_path) if runs_path is not None else runs_path_for(self.path)
        )
        self.verify_id = bool(verify_id)

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Ledger({self.path.name!r}, runs={self.runs_path.name!r})"

    # -- writing ----------------------------------------------------------
    def append(self, candidate: Candidate) -> Candidate:
        """Append one candidate record. Never rewrites; the last id wins."""
        validate_candidate(candidate)
        _append_line(self.path, to_json(candidate))
        return candidate

    def extend(self, candidates: Iterable[Candidate]) -> int:
        """Append many candidates; returns how many were written."""
        written = 0
        for candidate in candidates:
            self.append(candidate)
            written += 1
        return written

    def append_run(self, record: Mapping[str, Any]) -> Mapping[str, Any]:
        """Append one funnel-run record to the run stream.

        The run stream is what puts *zero-yield* work into the denominator, so
        a record with no candidates in it is not an edge case — it is the
        common one, and it is refused only if it has no ``run_id``.
        """
        if not isinstance(record, Mapping):
            raise LedgerError(f"a run record must be a mapping, got {record!r}")
        if not str(record.get("run_id", "")).strip():
            raise LedgerError("a run record must carry a run_id")
        payload = dict(record)
        payload.setdefault("record", RUN_RECORD_TYPE)
        try:
            line = json.dumps(payload, allow_nan=False, ensure_ascii=False)
        except (TypeError, ValueError) as exc:
            raise LedgerError(f"run record is not JSON-safe: {exc}") from exc
        _append_line(self.runs_path, line)
        return payload

    # -- reading ----------------------------------------------------------
    def candidates(self) -> tuple[Candidate, ...]:
        """Every candidate record, in write order. Missing file reads empty."""
        return tuple(self.iter_candidates())

    def iter_candidates(self) -> Iterator[Candidate]:
        """Stream candidate records; a large log need not fit in memory."""
        if not self.path.exists():
            return
        with self.path.open("r", encoding="utf-8") as handle:
            for lineno, line in enumerate(handle, start=1):
                if not line.strip():
                    continue
                try:
                    yield from_dict(json.loads(line), verify_id=self.verify_id)
                except (ValidationError, json.JSONDecodeError) as exc:
                    raise LedgerError(f"{self.path.name} line {lineno}: {exc}") from exc

    def runs(self) -> tuple[Mapping[str, Any], ...]:
        """Every run record, in write order. Missing file reads empty."""
        if not self.runs_path.exists():
            return ()
        out: list[Mapping[str, Any]] = []
        with self.runs_path.open("r", encoding="utf-8") as handle:
            for lineno, line in enumerate(handle, start=1):
                if not line.strip():
                    continue
                try:
                    record = json.loads(line)
                except json.JSONDecodeError as exc:
                    raise LedgerError(
                        f"{self.runs_path.name} line {lineno}: {exc}"
                    ) from exc
                if not isinstance(record, Mapping):
                    raise LedgerError(
                        f"{self.runs_path.name} line {lineno}: not a mapping"
                    )
                if record.get("record", RUN_RECORD_TYPE) != RUN_RECORD_TYPE:
                    continue
                out.append(record)
        return tuple(out)

    def view(self) -> LedgerView:
        """An immutable snapshot of both streams."""
        return LedgerView(
            candidates=self.candidates(),
            runs=self.runs(),
            path=self.path.name,
        )

    # -- queries ----------------------------------------------------------
    def latest(self) -> dict[str, Candidate]:
        """The current state of every candidate: last record per id."""
        return latest_by_id(self.iter_candidates())

    def ids(self) -> frozenset[str]:
        """Every candidate id the log has ever seen."""
        return frozenset(c.id for c in self.iter_candidates())

    def get(self, candidate_id: str) -> Candidate | None:
        """The current state of one candidate, or ``None``."""
        return self.latest().get(candidate_id)

    def contains(self, candidate_id: str) -> bool:
        return candidate_id in self.latest()

    def query(
        self,
        *,
        kind: str | None = None,
        status: str | Sequence[str] | None = None,
        generator: str | None = None,
        since: str | None = None,
        until: str | None = None,
    ) -> tuple[Candidate, ...]:
        """Filter the *current* state of the log.

        All filters are conjunctive; ``since``/``until`` compare ISO-8601
        strings against ``provenance.captured_at`` (lexicographic order is
        chronological order for ISO-8601 in one time zone, and the schema
        records UTC).
        """
        statuses: frozenset[str] | None
        if status is None:
            statuses = None
        elif isinstance(status, str):
            statuses = frozenset({status})
        else:
            statuses = frozenset(str(s) for s in status)
        out: list[Candidate] = []
        for candidate in self.latest().values():
            if kind is not None and candidate.kind.value != kind:
                continue
            if statuses is not None and candidate.verdict.status.value not in statuses:
                continue
            if generator is not None and candidate.provenance.generator != generator:
                continue
            captured = candidate.provenance.captured_at
            if since is not None and captured < since:
                continue
            if until is not None and captured > until:
                continue
            out.append(candidate)
        return tuple(sorted(out, key=lambda c: (c.provenance.captured_at, c.id)))

    def unresolved(self) -> tuple[Candidate, ...]:
        """Candidates whose last record is still ``open``.

        These are the residue of a run that died between checkpointing a
        candidate and deciding it. :func:`discovery.funnel.run_funnel` picks
        them up again on the next run rather than leaving them undecided.
        """
        return tuple(
            c for c in self.latest().values() if c.verdict.status.value == "open"
        )

    # -- maintenance ------------------------------------------------------
    def compact(self) -> int:
        """Rewrite the candidate log keeping only the current state of each id.

        The only operation in this module that is not append-only. It is
        exposed because an append-only log grows without bound, and it is
        atomic (temp file plus rename) so an interrupted compaction leaves the
        original in place. Returns the number of records kept.

        **Not safe against a concurrent writer.** Appends are; this is not. A
        record appended between the read and the rename lands in the file that
        the rename replaces and is gone. Compact when nothing else is running.
        """
        current = list(self.latest().values())
        _replace_atomically(
            self.path, "".join(to_json(c) + "\n" for c in current)
        )
        return len(current)

    def size(self) -> int:
        """Number of records in the candidate log, duplicates included."""
        if not self.path.exists():
            return 0
        with self.path.open("r", encoding="utf-8") as handle:
            return sum(1 for line in handle if line.strip())
