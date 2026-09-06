"""``telemetry.registry``, where run records live, and how they are appended.

One run is one file: ``<root>/runs/<run_id>.jsonl``. Appending is the only
write. Nothing here rewrites, deletes or compacts a record, and there is no
code path that removes a run, a run you wish had not happened is still a run
that happened.

Every function takes an explicit ``root``, so tests never touch the live
registry and a caller can never accidentally write into someone else's tree.
There is no module-level default path and no global state.

Stdlib only, on purpose: telemetry that could not run because the laboratory's
numerical dependencies were missing would fail exactly when a session is least
able to fix it. The same reasoning ``harness/protocol.py`` gives for running in
a tenth of a second.
"""

from __future__ import annotations

import json
import os
import subprocess
import uuid
from collections.abc import Iterator
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from telemetry.schema import Event, Run, TelemetryError, fold, validate_event

__all__ = [
    "runs_dir",
    "prompts_dir",
    "run_path",
    "new_run_id",
    "utc_now",
    "append_event",
    "read_events",
    "read_run",
    "list_run_ids",
    "iter_runs",
    "corrupt_lines",
    "probe_context",
    "ENV_ALLOWLIST",
    "ENV_DENIED",
    "sha256_file",
]

#: Environment variables that may be recorded. **Allowlist, not denylist**,
#: an unknown variable is never captured, so a provider that starts exporting
#: something sensitive cannot leak it into a public repository by default.
ENV_ALLOWLIST: tuple[str, ...] = (
    "AI_AGENT",
    "CLAUDE_CODE_VERSION",
    "CLAUDE_CODE_ENTRYPOINT",
    "CLAUDE_CODE_REMOTE",
    "CLAUDE_CODE_REMOTE_ENVIRONMENT_TYPE",
    "CLAUDE_CODE_CHILD_SESSION",
    "CLAUDE_EFFORT",
    "MAX_THINKING_TOKENS",
    "CODEX_VERSION",
    "TERM_PROGRAM",
)

#: Named so the reason is on the record rather than in someone's memory. These
#: are present in this environment and are **never** captured: they identify a
#: person or an organization, or they are credentials.
ENV_DENIED: tuple[str, ...] = (
    "CLAUDE_CODE_USER_EMAIL",
    "CLAUDE_CODE_ACCOUNT_UUID",
    "CLAUDE_CODE_ORGANIZATION_UUID",
    "CLAUDE_CODE_MESSAGING_TOKEN",
    "CLAUDE_SESSION_INGRESS_TOKEN_FILE",
    "GH_TOKEN",
    "GITHUB_TOKEN",
    "CLOUDSDK_AUTH_ACCESS_TOKEN",
    "ANTHROPIC_API_KEY",
    "ARISTOTLE_API_KEY",
)


def utc_now() -> str:
    """An ISO-8601 instant with an explicit offset. Never a local naive time."""
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def new_run_id() -> str:
    """A fresh run id. UUID4, no coordination, no collisions between sessions."""
    return str(uuid.uuid4())


def runs_dir(root: Path | str) -> Path:
    return Path(root) / "runs"


def prompts_dir(root: Path | str) -> Path:
    return Path(root) / "prompts"


def run_path(root: Path | str, run_id: str) -> Path:
    return runs_dir(root) / f"{run_id}.jsonl"


def append_event(root: Path | str, event: Event) -> Path:
    """Validate, then append one line. The only write in this package.

    Refuses a second ``run_started`` for a run that already has one, because
    that is how a duplicate run id would otherwise enter the registry silently.
    """
    validate_event(event)
    path = run_path(root, event.run_id)
    path.parent.mkdir(parents=True, exist_ok=True)
    if event.kind == "run_started" and path.exists():
        existing = read_events(root, event.run_id)
        if any(e.kind == "run_started" for e in existing):
            raise TelemetryError(
                f"run {event.run_id} already has a run_started event; a run id is "
                f"claimed once"
            )
    line = json.dumps(event.as_dict(), sort_keys=True, ensure_ascii=False)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")
    return path


def _parse_lines(path: Path) -> tuple[list[Event], list[tuple[int, str]]]:
    events: list[Event] = []
    corrupt: list[tuple[int, str]] = []
    if not path.exists():
        return events, corrupt
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        try:
            events.append(Event.from_dict(json.loads(stripped)))
        except (json.JSONDecodeError, TelemetryError) as exc:
            corrupt.append((number, str(exc)))
    return events, corrupt


def read_events(root: Path | str, run_id: str) -> list[Event]:
    """Every parseable event for a run, in file order. Corrupt lines are skipped."""
    return _parse_lines(run_path(root, run_id))[0]


def corrupt_lines(root: Path | str, run_id: str) -> list[tuple[int, str]]:
    """Line numbers and reasons for lines that would not parse.

    Surfaced rather than raised: one bad line must not make the other records
    in a file unreadable, and it must not be silently dropped either.
    """
    return _parse_lines(run_path(root, run_id))[1]


def read_run(root: Path | str, run_id: str) -> Run:
    events = read_events(root, run_id)
    if not events:
        raise TelemetryError(f"no events for run {run_id!r} under {root}")
    return fold(events)


def list_run_ids(root: Path | str) -> list[str]:
    directory = runs_dir(root)
    if not directory.is_dir():
        return []
    return sorted(p.stem for p in directory.glob("*.jsonl"))


def iter_runs(root: Path | str) -> Iterator[tuple[str, Run | None, str | None]]:
    """Yield ``(run_id, run, error)`` for every file, never raising.

    A file that cannot be folded yields ``(id, None, reason)``. Reconciliation
    has to be able to report a broken record; it cannot be stopped by one.
    """
    for run_id in list_run_ids(root):
        try:
            yield run_id, read_run(root, run_id), None
        except TelemetryError as exc:
            yield run_id, None, str(exc)


def sha256_file(path: Path | str) -> str:
    import hashlib

    digest = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git(repo: Path | str, *args: str) -> str | None:
    """Run a read-only git command. Returns None rather than raising.

    Every git call in this package is a read. Nothing here checks out,
    switches, resets, merges or writes a ref.
    """
    try:
        out = subprocess.run(
            ["git", *args],
            cwd=str(repo),
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    return out.stdout.strip()


def probe_context(repo: Path | str | None = None) -> dict[str, Any]:
    """What this environment actually exposes about the current session.

    Returns only what was found. **No field is inferred**, and the two most
    valuable fields are usually absent:

    * ``model``, this environment exports no model identifier at all (checked:
      ``ANTHROPIC_MODEL``, ``CLAUDE_MODEL`` are unset). It is therefore not in
      the returned mapping, and a caller who wants it must declare it.
    * token counts and cost, not exported to the session by any provider seen
      here, so they are absent rather than zero.

    ``env`` carries only :data:`ENV_ALLOWLIST` names that are set.
    """
    context: dict[str, Any] = {}

    session = os.environ.get("CLAUDE_CODE_SESSION_ID") or os.environ.get(
        "CODEX_SESSION_ID"
    )
    if session:
        context["agent_session_id"] = session
    remote_session = os.environ.get("CLAUDE_CODE_REMOTE_SESSION_ID")
    if remote_session:
        context["remote_session_id"] = remote_session
    if os.environ.get("CLAUDECODE") or os.environ.get("CLAUDE_CODE_VERSION"):
        context["provider"] = "claude-code"
    elif os.environ.get("CODEX_VERSION"):
        context["provider"] = "codex"

    env = {name: os.environ[name] for name in ENV_ALLOWLIST if os.environ.get(name)}
    if env:
        context["env"] = env

    if repo is not None:
        branch = _git(repo, "rev-parse", "--abbrev-ref", "HEAD")
        commit = _git(repo, "rev-parse", "HEAD")
        top = _git(repo, "rev-parse", "--show-toplevel")
        if branch:
            context["branch"] = branch
        if commit:
            context["start_commit"] = commit
        if top:
            # The worktree's *name*, never its absolute path. Run records are
            # committed to a public repository, and an absolute path leaks a
            # home directory, `tests/test_repo_hygiene.py` scans tracked
            # `.jsonl` for exactly that shape and exists because the leak has
            # happened here before. The name is what distinguishes parallel
            # worktrees, which is the only thing this field is for.
            context["worktree"] = os.path.basename(top.rstrip("/")) or None

    return {k: v for k, v in context.items() if v is not None}
