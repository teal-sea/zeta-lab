#!/usr/bin/env python3
"""Turn telemetry hooks on for ONE worktree. Idempotent, reversible, per-checkout.

    python3 telemetry/hooks/install.py            # wire the session hooks
    python3 telemetry/hooks/install.py --status   # what is wired here
    python3 telemetry/hooks/install.py --uninstall
    python3 telemetry/hooks/install.py --git-hook # also the commit trailer (see below)

Why an installer rather than a documented snippet: the whole point of this
package is to remove operational bookkeeping from the operator's memory, and a
twelve-line copy-paste block is bookkeeping. It is also the piece most likely to
be typed slightly wrong, and a hook wired slightly wrong fails silently,
which is the failure mode this repository catalogues rather than tolerates.

## What it writes, and what it deliberately does not

`.claude/settings.local.json`: **gitignored and per-checkout**. Enabling
telemetry in one worktree therefore cannot follow a merge into anyone else's
session. The tracked `.claude/settings.json` is never touched; that file is
shared, and a shared file is not where an opt-in belongs.

The **git hook is separate and off by default** (`--git-hook`). `.git/hooks` is
common to every worktree of a clone, so installing it while another worktree
has a live session changes how that session commits. That is the one blast
radius here that crosses the isolation boundary, so it stays a deliberate act.
The installer refuses it outright when another worktree looks active, and
`--force` is required to override.

Existing settings are read, merged, and preserved. A pre-existing hook on the
same event is reported and left alone unless `--replace` is given: silently
overwriting someone's hook would be exactly the kind of quiet mutation the
isolation contract forbids.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HOOK_DIR = Path(__file__).resolve().parent
TELEMETRY_ROOT = HOOK_DIR.parent
MARKER = "telemetry/hooks/session_"

EVENTS = {
    "SessionStart": "telemetry/hooks/session_start.py",
    "Stop": "telemetry/hooks/session_stop.py",
}


def repo_root(start: Path) -> Path:
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=str(start), capture_output=True, text=True, check=False,
    )
    return Path(out.stdout.strip()) if out.returncode == 0 else start


def entry(script: str) -> dict:
    return {
        "hooks": [
            {
                "type": "command",
                "command": f"python3 {script}",
                # Bounded so a telemetry hiccup can never stall a session; the
                # scripts already swallow every exception for the same reason.
                "timeout": 15,
                "statusMessage": "recording run telemetry",
            }
        ]
    }


def is_ours(group: dict) -> bool:
    return any(MARKER in str(h.get("command", "")) for h in group.get("hooks", []))


def other_worktrees_active(root: Path) -> list[str]:
    """Worktrees of this clone other than the one we are installing into."""
    out = subprocess.run(
        ["git", "worktree", "list", "--porcelain"],
        cwd=str(root), capture_output=True, text=True, check=False,
    )
    if out.returncode != 0:
        return []
    others = []
    for line in out.stdout.splitlines():
        if line.startswith("worktree "):
            path = line.split(" ", 1)[1].strip()
            if Path(path).resolve() != root.resolve():
                others.append(path)
    return others


def load(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(
            f"{path} is not valid JSON ({exc}). A malformed settings file "
            f"silently disables every setting in it, fix it before installing."
        )


def cmd_status(settings_path: Path) -> int:
    settings = load(settings_path)
    hooks = settings.get("hooks", {})
    print(f"settings: {settings_path}"
          f"{'' if settings_path.exists() else '  (does not exist)'}")
    for event in EVENTS:
        groups = [g for g in hooks.get(event, []) if is_ours(g)]
        foreign = [g for g in hooks.get(event, []) if not is_ours(g)]
        state = "ON " if groups else "off"
        extra = f"  (+{len(foreign)} other hook group(s) on this event)" if foreign else ""
        print(f"  {event:<13} {state}{extra}")
    git_hook = repo_root(HOOK_DIR) / ".git" / "hooks" / "prepare-commit-msg"
    print(f"  {'commit trailer':<13} "
          f"{'ON ' if git_hook.exists() else 'off'}  ({git_hook})")
    return 0


def cmd_install(settings_path: Path, replace: bool) -> int:
    settings = load(settings_path)
    hooks = settings.setdefault("hooks", {})
    changed = []
    for event, script in EVENTS.items():
        groups = hooks.setdefault(event, [])
        mine = [g for g in groups if is_ours(g)]
        if mine and not replace:
            print(f"  {event}: already wired, left alone")
            continue
        if mine:
            groups[:] = [g for g in groups if not is_ours(g)]
        foreign = [g for g in groups if not is_ours(g)]
        if foreign:
            print(f"  {event}: {len(foreign)} existing hook group(s) preserved")
        groups.append(entry(script))
        changed.append(event)

    settings_path.parent.mkdir(parents=True, exist_ok=True)
    settings_path.write_text(json.dumps(settings, indent=2) + "\n", encoding="utf-8")
    if changed:
        print(f"  wired: {', '.join(changed)}")
    print(f"  wrote: {settings_path}")
    print("\nHooks fire on the NEXT session in this worktree, not this one.")
    print("If they do not fire, open /hooks once (that reloads config) or restart.")
    return 0


def cmd_uninstall(settings_path: Path) -> int:
    settings = load(settings_path)
    hooks = settings.get("hooks", {})
    removed = []
    for event in EVENTS:
        groups = hooks.get(event)
        if not groups:
            continue
        kept = [g for g in groups if not is_ours(g)]
        if len(kept) != len(groups):
            removed.append(event)
        if kept:
            hooks[event] = kept
        else:
            hooks.pop(event, None)
    if not hooks:
        settings.pop("hooks", None)
    settings_path.write_text(json.dumps(settings, indent=2) + "\n", encoding="utf-8")
    print(f"  removed: {', '.join(removed) or '(nothing was wired)'}")
    print("  existing run records are untouched, a run that happened, happened")
    return 0


def cmd_git_hook(root: Path, force: bool) -> int:
    others = other_worktrees_active(root)
    if others and not force:
        print("REFUSED: .git/hooks is shared by every worktree of this clone, and "
              "this clone has others:")
        for path in others:
            print(f"    {path}")
        print("Installing now would change how a session in those worktrees "
              "commits.\nRe-run with --force when nothing else is running.")
        return 1
    target = root / ".git" / "hooks" / "prepare-commit-msg"
    if target.exists():
        print(f"REFUSED: {target} already exists, not overwriting someone's hook")
        return 1
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text((HOOK_DIR / "prepare-commit-msg").read_text(encoding="utf-8"),
                      encoding="utf-8")
    target.chmod(0o755)
    print(f"  installed: {target}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--uninstall", action="store_true")
    parser.add_argument("--replace", action="store_true",
                        help="replace an existing telemetry hook instead of skipping")
    parser.add_argument("--git-hook", action="store_true",
                        help="also install the commit-trailer hook (shared blast radius)")
    parser.add_argument("--force", action="store_true",
                        help="with --git-hook: install even though other worktrees exist")
    parser.add_argument("--worktree", default=".",
                        help="which checkout to wire (default: the current one)")
    args = parser.parse_args(argv)

    root = repo_root(Path(args.worktree).resolve())
    settings_path = root / ".claude" / "settings.local.json"

    if args.status:
        return cmd_status(settings_path)
    if args.uninstall:
        return cmd_uninstall(settings_path)

    print(f"worktree: {root}")
    code = cmd_install(settings_path, args.replace)
    if args.git_hook:
        code = cmd_git_hook(root, args.force) or code
    return code


if __name__ == "__main__":
    raise SystemExit(main())
