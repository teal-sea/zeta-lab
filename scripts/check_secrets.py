#!/usr/bin/env python3
"""Refuse to publish a credential. Scans git objects for secret patterns.

Why this exists
---------------
On 2026-08-20 a live OpenRouter API key was committed in plain text to a local
branch of this repository by a parallel session, in two files, across two
commits. It was caught before any push, by a human asking "is it even any good?"
rather than by anything mechanical. Nothing in this tree would have stopped the
push.

That is the whole argument for this file. A public research repository leaks a
credential exactly once, and the window between `git push` and a scraper bot
finding it is measured in minutes.

Usage
-----
    python scripts/check_secrets.py --range <old>..<new>   # what a push contains
    python scripts/check_secrets.py --all                  # every local ref
    python scripts/check_secrets.py --tree <ref>           # one tree

Exits non-zero and names the offending path when it finds something. Installed
as a pre-push hook by ``scripts/install_hooks.sh``.

Scope, stated plainly: this catches *known key shapes*. It is a backstop, not a
guarantee, and it cannot recognise a credential that looks like ordinary text.
A pattern list is a floor. It does not license keeping secrets in the tree.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys

# Prefix-anchored, so they match a real credential rather than any hex string.
PATTERNS: dict[str, re.Pattern[bytes]] = {
    "OpenRouter key": re.compile(rb"sk-or-v1-[A-Za-z0-9]{16,}"),
    "Anthropic key": re.compile(rb"sk-ant-(?:api|admin)[A-Za-z0-9\-_]{16,}"),
    "OpenAI key": re.compile(rb"sk-proj-[A-Za-z0-9\-_]{16,}"),
    "Perplexity key": re.compile(rb"pplx-[A-Za-z0-9]{32,}"),
    "Google API key": re.compile(rb"AIza[A-Za-z0-9\-_]{30,}"),
    "AWS access key": re.compile(rb"AKIA[A-Z0-9]{16}"),
    "GitHub token": re.compile(rb"gh[pousr]_[A-Za-z0-9]{30,}"),
    "hardcoded key export": re.compile(
        rb'export\s+\w*(?:API_KEY|SECRET|TOKEN)\w*\s*=\s*["\'][A-Za-z0-9\-_]{24,}'
    ),
}

# Paths whose *contents* are allowed to contain the patterns, because they are
# the patterns. Keep this list short and obvious.
ALLOWLIST = (
    "scripts/check_secrets.py",
    "tests/test_check_secrets.py",
)


def _objects(args: list[str]) -> list[tuple[str, str]]:
    """Objects reachable from ``args``.

    A git failure here is fatal, never an empty result.  The first version of
    this function returned ``[]`` on a non-zero exit, so a malformed revision
    range made the scan report *clean* and the pre-push hook let the push
    through.  A guard that fails open is worse than no guard, because it also
    supplies confidence.  That bug was live for about four minutes and is the
    reason ``tests/test_check_secrets.py`` asserts a bad range raises.
    """
    out = subprocess.run(
        ["git", "rev-list", "--objects", *args], capture_output=True, text=True
    )
    if out.returncode != 0:
        raise RuntimeError(
            f"git rev-list failed for {args!r}: {out.stderr.strip()}"
        )
    pairs = []
    for line in out.stdout.splitlines():
        parts = line.split(maxsplit=1)
        if len(parts) == 2:
            pairs.append((parts[0], parts[1]))
    return pairs


def scan(rev_args: list[str], batch: int = 500) -> list[tuple[str, str]]:
    """``(path, pattern name)`` for every object matching a secret pattern."""
    blobs = [(h, p) for h, p in _objects(rev_args) if p not in ALLOWLIST]
    hits: list[tuple[str, str]] = []
    for start in range(0, len(blobs), batch):
        chunk = blobs[start : start + batch]
        stdin = ("\n".join(h for h, _ in chunk) + "\n").encode()
        data = subprocess.run(
            ["git", "cat-file", "--batch"], input=stdin, capture_output=True
        ).stdout
        for name, pattern in PATTERNS.items():
            if not pattern.search(data):
                continue
            # narrow to the specific object, only when the batch matched
            for sha, path in chunk:
                blob = subprocess.run(
                    ["git", "cat-file", "-p", sha], capture_output=True
                ).stdout
                if pattern.search(blob):
                    hits.append((path, name))
    return sorted(set(hits))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--range", help="commit range, e.g. origin/main..HEAD")
    group.add_argument("--all", action="store_true", help="every local ref")
    group.add_argument("--tree", help="a single ref's tree and history")
    args = parser.parse_args()

    if args.all:
        rev_args = ["--all"]
    elif args.range:
        rev_args = args.range.split()  # ranges may be multi-token, e.g. "X --not --remotes=origin"
    else:
        rev_args = [args.tree]

    try:
        hits = scan(rev_args)
    except RuntimeError as exc:
        print(f"check_secrets: FAILED, refusing to report clean: {exc}", file=sys.stderr)
        return 2
    if not hits:
        print("check_secrets: clean")
        return 0

    print("check_secrets: REFUSING, credential-shaped content found\n", file=sys.stderr)
    for path, name in hits:
        print(f"  {name:22s} {path}", file=sys.stderr)
    print(
        "\nRotate the credential first: it is burned the moment it exists in\n"
        "any local history on a machine that pushes. Then remove it from every\n"
        "reachable ref, including backup branches, and expire the reflog.\n"
        "Reading a key at call time beats writing it into a file at all.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
