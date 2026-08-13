"""``telemetry.gitlink`` — the ``Run-Id`` commit trailer, read-only.

The trailer is the join between a run record and the repository's existing
provenance tail. Everything downstream of a commit — the claim it supports, the
grade that claim carries, the artifact it changed — is already recorded
somewhere in this tree. What was missing is which *run* produced it.

Why a new trailer rather than the existing ones
-----------------------------------------------
``Co-Authored-By: Claude <model>`` and ``Claude-Session: <url>`` already appear
on some commits, and neither can carry this join:

* ``Co-Authored-By`` names a model family, not an occasion. Two hundred commits
  share three values; it cannot distinguish two runs by the same model, and it
  is absent from a large share of commits.
* ``Claude-Session`` names a provider-side conversation that may span many
  runs, is not stored anywhere in the tree, and resolves to a service rather
  than to an artifact.

They are kept and read as corroboration. ``Run-Id`` is the primary link.

Every function here is a **read**. Nothing in this module checks out, switches,
resets, merges, rebases, writes a ref, or installs a hook.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

__all__ = [
    "TRAILER_KEY",
    "format_trailer",
    "parse_run_ids",
    "parse_corroborating",
    "commit_run_ids",
    "commit_exists",
    "resolve_commit",
]

TRAILER_KEY = "Run-Id"

_TRAILER_RE = re.compile(
    rf"^{TRAILER_KEY}:[ \t]*([0-9a-fA-F-]{{36}})[ \t]*$", re.MULTILINE
)
_COAUTHOR_RE = re.compile(r"^Co-Authored-By:[ \t]*(.+?)[ \t]*$", re.MULTILINE)
_SESSION_RE = re.compile(r"^Claude-Session:[ \t]*(\S+)[ \t]*$", re.MULTILINE)
_RECORD_SEP = "\x1e"
_FIELD_SEP = "\x1f"


def format_trailer(run_id: str) -> str:
    """The exact line to append to a commit message."""
    return f"{TRAILER_KEY}: {run_id}"


def parse_run_ids(message: str) -> tuple[str, ...]:
    """Run ids declared by a commit message, in order, deduplicated.

    Case is normalized to lowercase so a hand-typed trailer still joins. More
    than one is legal and meaningful: a commit assembled from two runs declares
    both, and reconciliation reports it rather than picking one.
    """
    seen: list[str] = []
    for match in _TRAILER_RE.finditer(message or ""):
        value = match.group(1).lower()
        if value not in seen:
            seen.append(value)
    return tuple(seen)


def parse_corroborating(message: str) -> dict[str, tuple[str, ...]]:
    """The pre-existing trailers, read as corroboration and never as the join."""
    return {
        "co_authored_by": tuple(m.group(1) for m in _COAUTHOR_RE.finditer(message or "")),
        "claude_session": tuple(m.group(1) for m in _SESSION_RE.finditer(message or "")),
    }


def _git(repo: Path | str, *args: str) -> str | None:
    try:
        out = subprocess.run(
            ["git", *args],
            cwd=str(repo),
            capture_output=True,
            text=True,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout if out.returncode == 0 else None


def commit_exists(repo: Path | str, sha: str) -> bool:
    """Does this object exist in this repository, as a commit?

    A shallow clone can answer "no" for a commit that exists upstream. Callers
    must treat a False here as *not present in this checkout*, which is what
    reconciliation reports, rather than as *does not exist*.
    """
    if not sha:
        return False
    return _git(repo, "cat-file", "-e", f"{sha}^{{commit}}") is not None


def resolve_commit(repo: Path | str, sha: str) -> str | None:
    """Full 40-character sha for an abbreviated one, or None if unknown here."""
    out = _git(repo, "rev-parse", "--verify", f"{sha}^{{commit}}")
    return out.strip() if out else None


def commit_run_ids(
    repo: Path | str, rev_range: str | None = None, *, limit: int | None = None
) -> dict[str, dict[str, object]]:
    """Map commit sha -> {run_ids, subject, author_date, corroborating}.

    ``rev_range`` is passed straight to ``git log``; omit it for the current
    branch's history. ``limit`` bounds the scan, because reconciling a whole
    history is not usually what a session wants.
    """
    args = ["log", f"--format=%H{_FIELD_SEP}%s{_FIELD_SEP}%aI{_FIELD_SEP}%B{_RECORD_SEP}"]
    if limit is not None:
        args.append(f"-n{limit}")
    if rev_range:
        args.append(rev_range)
    raw = _git(repo, *args)
    if raw is None:
        return {}

    out: dict[str, dict[str, object]] = {}
    for record in raw.split(_RECORD_SEP):
        record = record.strip("\n")
        if not record.strip():
            continue
        parts = record.split(_FIELD_SEP)
        if len(parts) < 4:
            continue
        sha, subject, when, body = parts[0].strip(), parts[1], parts[2], parts[3]
        out[sha] = {
            "run_ids": parse_run_ids(body),
            "subject": subject,
            "author_date": when,
            "corroborating": parse_corroborating(body),
        }
    return out
