"""``telemetry.cli`` — the emission boundary. ``python -m telemetry ...``

Three ways to emit, all writing the same events. They exist because the
narrowest safe boundary differs per provider, and pretending one wrapper fits
everything is how telemetry ends up optional:

``wrap``
    ``python -m telemetry wrap --task "…" -- <command>`` runs a command and
    emits start and finish around it **automatically**: duration measured, exit
    code recorded, status derived from the exit code, artifacts collected from
    git. Nothing to remember. This is the boundary to prefer.

``start`` / ``finish``
    Explicit boundaries for a unit of work no single command wraps — an agent
    session, a formalization sprint. The shipped hooks call exactly these.

``reconstruct``
    For work that happened before this system existed. It writes
    ``capture="reconstructed"`` and refuses to run without
    ``--reconstructed-from``, so derived metadata can never be read as
    contemporaneously captured telemetry.

What this module will not do, and the reasons are load-bearing:

* it never invents a model, a token count or a cost — ``--model`` is an
  explicit declaration recorded with its ``model_source``, and this environment
  exports no model identifier to sniff even if that were wanted;
* it never writes outside ``--root``;
* it never edits a commit, installs a hook, or touches a branch. ``trailer``
  prints a line for a human or a hook to use.
"""

from __future__ import annotations

import argparse
import json
import os
import shlex
import subprocess
import sys
import time
from pathlib import Path

from telemetry import gitlink, prompts, reconcile as _reconcile
from telemetry.registry import (
    append_event,
    iter_runs,
    new_run_id,
    probe_context,
    read_run,
    sha256_file,
    utc_now,
)
from telemetry.schema import Event, OUTCOMES, TelemetryError

__all__ = ["main", "default_root", "default_repo"]


def default_root() -> Path:
    """``<repo>/telemetry`` — the directory this package lives in."""
    return Path(__file__).resolve().parent


def default_repo() -> Path:
    return default_root().parent


def _git(repo: Path, *args: str) -> str | None:
    try:
        out = subprocess.run(
            ["git", *args], cwd=str(repo), capture_output=True, text=True,
            check=False, timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout.strip() if out.returncode == 0 else None


def _collect_artifacts(repo: Path, start_commit: str | None) -> list[dict]:
    """Files this run appears to have produced, with digests.

    Union of (a) paths changed between ``start_commit`` and HEAD and (b) paths
    dirty or untracked right now. A path that no longer exists is recorded with
    a null digest rather than dropped — a deletion is a thing a run did.
    """
    paths: set[str] = set()
    if start_commit:
        changed = _git(repo, "diff", "--name-only", f"{start_commit}..HEAD")
        if changed:
            paths.update(p for p in changed.splitlines() if p.strip())
    status = _git(repo, "status", "--porcelain=v1", "--untracked-files=all")
    if status:
        for line in status.splitlines():
            if len(line) > 3:
                paths.add(line[3:].strip().strip('"'))
    artifacts: list[dict] = []
    for rel in sorted(paths):
        full = repo / rel
        if full.is_file():
            try:
                artifacts.append(
                    {"path": rel, "sha256": sha256_file(full), "bytes": full.stat().st_size}
                )
            except OSError:
                artifacts.append({"path": rel, "sha256": None, "bytes": None})
        else:
            artifacts.append({"path": rel, "sha256": None, "bytes": None})
    return artifacts


def _commits_since(repo: Path, start_commit: str | None) -> list[str]:
    if not start_commit:
        return []
    out = _git(repo, "rev-list", f"{start_commit}..HEAD")
    return [c for c in (out or "").splitlines() if c.strip()]


def _prompt_ref(root: Path, args: argparse.Namespace) -> prompts.PromptRef:
    if getattr(args, "prompt_file", None):
        return prompts.capture_file(root, args.prompt_file, source=args.prompt_source)
    if getattr(args, "prompt_text", None):
        return prompts.capture_text(root, args.prompt_text, source=args.prompt_source)
    if getattr(args, "prompt_stdin", False):
        return prompts.capture_text(root, sys.stdin.read(), source=args.prompt_source or "stdin")
    if getattr(args, "prompt_external", None):
        digest, _, ref = args.prompt_external.partition(":")
        return prompts.reference_external(digest, ref, source=args.prompt_source)
    return prompts.PromptRef(digest=None, store="absent")


def _started_payload(root: Path, repo: Path, args: argparse.Namespace) -> dict:
    context = probe_context(repo)
    env = context.pop("env", None)
    payload: dict = {
        "capture": args.capture,
        "task": args.task,
        "task_ref": args.task_ref,
        "role": args.role,
        "prompt": _prompt_ref(root, args).as_dict(),
    }
    payload.update(context)
    if args.provider:
        payload["provider"] = args.provider
    if args.model:
        payload["model"] = args.model
        payload["model_id"] = args.model_id or args.model
        payload["model_source"] = args.model_source
    if args.reconstructed_from:
        payload["reconstructed_from"] = args.reconstructed_from
    meta = {}
    if env:
        meta["env"] = env
    if context.get("remote_session_id"):
        meta["remote_session_id"] = payload.pop("remote_session_id", None)
    if meta:
        payload["provider_meta"] = meta
    return {k: v for k, v in payload.items() if v is not None}


def _emit_started(root: Path, repo: Path, args: argparse.Namespace, run_id: str) -> None:
    append_event(
        root,
        Event(kind="run_started", run_id=run_id, at=utc_now(),
              payload=_started_payload(root, repo, args)),
    )


def _emit_finished(root: Path, repo: Path, run_id: str, *, status: str,
                   outcome: str | None, exit_code: int | None,
                   duration: float | None, start_commit: str | None,
                   error: dict | None = None, tokens: dict | None = None,
                   cost: dict | None = None) -> None:
    payload: dict = {"status": status}
    if outcome:
        payload["outcome"] = outcome
    if exit_code is not None:
        payload["exit_code"] = exit_code
    if duration is not None:
        payload["duration_seconds"] = round(duration, 3)
    commits = _commits_since(repo, start_commit)
    if commits:
        payload["commits"] = commits
    artifacts = _collect_artifacts(repo, start_commit)
    if artifacts:
        payload["artifacts"] = artifacts
    if error:
        payload["error"] = error
    # Absent, not zero. No provider seen here reports usage to the session.
    if tokens:
        payload["tokens"] = tokens
    if cost:
        payload["cost"] = cost
    append_event(root, Event(kind="run_finished", run_id=run_id, at=utc_now(),
                             payload=payload))


# ---------------------------------------------------------------------------
# subcommands
# ---------------------------------------------------------------------------


def _cmd_start(args: argparse.Namespace) -> int:
    root, repo = Path(args.root), Path(args.repo)
    run_id = args.run_id or new_run_id()
    _emit_started(root, repo, args, run_id)
    print(run_id)
    return 0


def _cmd_note(args: argparse.Namespace) -> int:
    append_event(Path(args.root), Event(kind="run_note", run_id=args.run_id,
                                        at=utc_now(), payload={"note": args.note}))
    return 0


def _cmd_finish(args: argparse.Namespace) -> int:
    root, repo = Path(args.root), Path(args.repo)
    run = read_run(root, args.run_id)
    tokens = json.loads(args.tokens) if args.tokens else None
    cost = json.loads(args.cost) if args.cost else None
    _emit_finished(root, repo, args.run_id, status=args.status, outcome=args.outcome,
                   exit_code=args.exit_code, duration=None,
                   start_commit=run.start_commit, tokens=tokens, cost=cost)
    print(f"{args.run_id} {args.status}")
    return 0


def _cmd_wrap(args: argparse.Namespace) -> int:
    """Start, run the command, finish — the automatic path."""
    root, repo = Path(args.root), Path(args.repo)
    run_id = args.run_id or new_run_id()
    _emit_started(root, repo, args, run_id)
    run = read_run(root, run_id)
    started = time.monotonic()
    error = None
    try:
        completed = subprocess.run(args.command, cwd=str(repo), check=False)
        code = completed.returncode
    except (OSError, subprocess.SubprocessError) as exc:
        code = 127
        error = {"kind": type(exc).__name__, "message": str(exc)}
    duration = time.monotonic() - started
    status = "completed" if code == 0 else "failed"
    outcome = args.outcome or (None if code == 0 else "crashed")
    _emit_finished(root, repo, run_id, status=status, outcome=outcome, exit_code=code,
                   duration=duration, start_commit=run.start_commit, error=error)
    print(f"run {run_id} {status} exit={code} {duration:.1f}s", file=sys.stderr)
    return code


def _cmd_show(args: argparse.Namespace) -> int:
    run = read_run(Path(args.root), args.run_id)
    print(json.dumps(run.as_dict(), indent=2, sort_keys=True))
    return 0


def _cmd_list(args: argparse.Namespace) -> int:
    rows = 0
    for run_id, run, error in iter_runs(Path(args.root)):
        rows += 1
        if run is None:
            print(f"{run_id}  UNFOLDABLE  {error}")
            continue
        print(
            f"{run_id}  {run.started_at}  {run.status:<11} "
            f"{(run.outcome or '-'):<9} {(run.model or 'model:unknown'):<22} "
            f"{(run.task or '')[:48]}"
        )
    if rows == 0:
        print("(no runs recorded)")
    return 0


def _cmd_trailer(args: argparse.Namespace) -> int:
    print(gitlink.format_trailer(args.run_id))
    return 0


def _cmd_reconcile(args: argparse.Namespace) -> int:
    findings = _reconcile.reconcile(
        Path(args.root), Path(args.repo), rev_range=args.rev_range,
        limit=args.limit, require_trailer_since=args.require_trailer_since,
    )
    if args.json:
        print(json.dumps([f.as_dict() for f in findings], indent=2))
    else:
        sys.stdout.write(_reconcile.render_text(findings))
    if args.strict and any(f.severity == "defect" for f in findings):
        return 1
    return 0


def _add_start_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--task", help="one line: what this run was asked to do")
    parser.add_argument("--task-ref", help="hunt / research-arm / decision anchor")
    parser.add_argument("--role", help="constructor / replicator / skeptic / …")
    parser.add_argument("--provider")
    parser.add_argument("--model", help="declared; never sniffed (see RUN-TELEMETRY.md)")
    parser.add_argument("--model-id", help="exact version string if the provider gives one")
    parser.add_argument(
        "--model-source", default="declared-by-operator",
        choices=["declared-by-operator", "declared-by-agent", "provider-api", "env"],
        help="how the model identity was learned — required whenever --model is given",
    )
    parser.add_argument("--capture", default="contemporaneous",
                        choices=["contemporaneous", "reconstructed"])
    parser.add_argument("--reconstructed-from",
                        help="required when --capture=reconstructed")
    parser.add_argument("--prompt-file")
    parser.add_argument("--prompt-text")
    parser.add_argument("--prompt-stdin", action="store_true")
    parser.add_argument("--prompt-external", metavar="DIGEST:REF",
                        help="prompt held outside this tree")
    parser.add_argument("--prompt-source")
    parser.add_argument("--run-id", help="use a specific id instead of a fresh UUID")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m telemetry",
        description="Minimal run registry: observe how research happened.",
    )
    parser.add_argument("--root", default=str(default_root()),
                        help="telemetry root (default: this package's directory)")
    parser.add_argument("--repo", default=str(default_repo()),
                        help="repository to read git state from")
    # dest is `subcommand`, not `command`: `wrap` has a positional named
    # `command` for the wrapped argv, and two argparse destinations with one
    # name silently overwrite each other. Caught by the wrap tests.
    sub = parser.add_subparsers(dest="subcommand", required=True)

    p = sub.add_parser("start", help="open a run and print its id")
    _add_start_options(p)
    p.set_defaults(func=_cmd_start)

    p = sub.add_parser("note", help="append a note to an open run")
    p.add_argument("run_id")
    p.add_argument("note")
    p.set_defaults(func=_cmd_note)

    p = sub.add_parser("finish", help="close a run")
    p.add_argument("run_id")
    p.add_argument("--status", default="completed",
                   choices=["completed", "failed", "aborted"])
    p.add_argument("--outcome", choices=list(OUTCOMES))
    p.add_argument("--exit-code", type=int)
    p.add_argument("--tokens", help='JSON, provider-reported only, e.g. {"input":1,"output":2}')
    p.add_argument("--cost", help='JSON; estimated_usd requires estimate_basis')
    p.set_defaults(func=_cmd_finish)

    p = sub.add_parser("wrap", help="run a command with automatic start/finish")
    _add_start_options(p)
    p.add_argument("--outcome", choices=list(OUTCOMES))
    p.add_argument("command", nargs=argparse.REMAINDER)
    p.set_defaults(func=_cmd_wrap)

    p = sub.add_parser("reconstruct",
                       help="record a run that happened before instrumentation")
    _add_start_options(p)
    p.set_defaults(func=_cmd_start, capture="reconstructed")

    p = sub.add_parser("show", help="print one folded run as JSON")
    p.add_argument("run_id")
    p.set_defaults(func=_cmd_show)

    p = sub.add_parser("list", help="one line per run")
    p.set_defaults(func=_cmd_list)

    p = sub.add_parser("trailer", help="print the Run-Id line for a commit message")
    p.add_argument("run_id")
    p.set_defaults(func=_cmd_trailer)

    p = sub.add_parser("reconcile", help="compare the registry against git")
    p.add_argument("--rev-range")
    p.add_argument("--limit", type=int, default=200)
    p.add_argument("--require-trailer-since", metavar="REV",
                   help="also report commits in REV..HEAD with no Run-Id "
                        "(off by default: pre-instrumentation work is not a defect)")
    p.add_argument("--json", action="store_true")
    p.add_argument("--strict", action="store_true",
                   help="exit 1 if any finding is a defect")
    p.set_defaults(func=_cmd_reconcile)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if getattr(args, "subcommand", None) == "wrap":
        command = [c for c in (args.command or []) if c != "--"]
        if not command:
            print("wrap needs a command after --", file=sys.stderr)
            return 2
        args.command = command
    try:
        return int(args.func(args))
    except TelemetryError as exc:
        print(f"telemetry refused: {exc}", file=sys.stderr)
        return 2
    except FileNotFoundError as exc:
        print(f"telemetry: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
