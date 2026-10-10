"""Build the claim corpus: one row per case-log entry in hunts/README.md.

A "claim" here is deliberately a *recorded* claim, not a mathematical
statement: the unit is one entry in the laboratory's own case log, because
that is the granularity at which this tree decides what it believes.  Each
row carries the hunt directory it names, the commit that first landed the
directory's own claim-bearing files, and every later commit that touched
them.

Nothing in this file classifies anything.  Classification is in
``classify.py`` so the corpus can be rebuilt without re-running a judgement,
and so the two can be audited apart.
"""
from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass, asdict
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CASE_LOG = REPO / "hunts" / "README.md"

#: The corpus is the case log as it stood BEFORE this hunt existed.  Reading the
#: working tree instead would put this hunt's own entries in its own denominator,
#: and would make the numbers move every time a later session adds a hunt.  The
#: ref is the tip of main at the session that built the corpus; pass --worktree
#: to read the live file instead and see how much the answer moves.
CASE_LOG_REF = "2da62eb"

#: `### Hunt #114: title (`dir/`)` and the unnumbered `### Title (`dir/`, date)`.
_ENTRY = re.compile(
    r"^###\s+(?P<head>.*?)\s*\(`(?P<dir>[A-Za-z0-9_./-]+?)/`(?:,\s*(?P<date>[0-9-]+))?\)\s*$",
    re.MULTILINE,
)
_NUMBER = re.compile(r"Hunt\s+#(\d+)")
_STATUS = re.compile(r"\*\*Status:?\s*(?P<status>[^*]+)\*\*")

#: Files inside a hunt directory that carry the hunt's own recorded claims.
CLAIM_FILES = ("RESULTS.md", "README.md", "MISSION.md", "RUNS.md", "FINDINGS.md")


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=REPO, capture_output=True, check=True
    ).stdout.decode("utf-8", errors="replace")


@dataclass
class Commit:
    sha: str
    date: str          # ISO-8601, author date
    subject: str
    body: str
    files: list[str]

    @property
    def message(self) -> str:
        return f"{self.subject}\n{self.body}"


@dataclass
class ClaimRow:
    number: int | None
    heading: str
    directory: str
    status: str
    first_commit: str | None
    first_date: str | None
    later: list[str]           # shas, oldest first


def _commits_touching(path: str) -> list[Commit]:
    """Every commit that touched ``path``, oldest first, with its file list."""
    sep = "\x01"
    fmt = f"%H{sep}%ad{sep}%s{sep}%b"
    raw = git(
        "log", "--reverse", "--date=short", f"--format={fmt}", "--name-only",
        "--", path,
    )
    out: list[Commit] = []
    for block in raw.split("\n\ncommit-boundary\n"):
        pass  # placeholder; parsing is done line-wise below
    cur: Commit | None = None
    for line in raw.splitlines():
        if sep in line:
            parts = line.split(sep)
            if len(parts) >= 4 and len(parts[0]) == 40 and re.fullmatch(r"[0-9a-f]{40}", parts[0]):
                if cur is not None:
                    out.append(cur)
                cur = Commit(sha=parts[0], date=parts[1], subject=parts[2],
                             body=parts[3], files=[])
                continue
        if cur is None:
            continue
        if line.strip() == "":
            continue
        cur.files.append(line.strip())
    if cur is not None:
        out.append(cur)
    return out


def case_log_text(ref: str | None) -> str:
    if ref is None:
        return CASE_LOG.read_text(encoding="utf-8")
    return git("show", f"{ref}:hunts/README.md")


def build(ref: str | None = CASE_LOG_REF) -> tuple[list[ClaimRow], dict[str, Commit]]:
    text = case_log_text(ref)
    rows: list[ClaimRow] = []
    commits: dict[str, Commit] = {}

    for m in _ENTRY.finditer(text):
        head = m.group("head")
        directory = m.group("dir")
        num_m = _NUMBER.search(head)
        # Status is the first **Status ...** after the heading, before the next heading.
        nxt = text.find("\n### ", m.end())
        body = text[m.end(): nxt if nxt != -1 else len(text)]
        st = _STATUS.search(body)

        path = f"hunts/{directory}"
        touching = _commits_touching(path)
        for c in touching:
            commits[c.sha] = c

        claim_commits = [
            c for c in touching
            if any(f.startswith(path + "/") and Path(f).name in CLAIM_FILES for f in c.files)
        ]
        first = claim_commits[0] if claim_commits else (touching[0] if touching else None)
        later = [c.sha for c in touching if first is not None and c.sha != first.sha
                 and c.date >= first.date]
        # keep order: touching is oldest-first, drop anything at or before first
        if first is not None:
            idx = [c.sha for c in touching].index(first.sha)
            later = [c.sha for c in touching[idx + 1:]]

        rows.append(ClaimRow(
            number=int(num_m.group(1)) if num_m else None,
            heading=head.strip(),
            directory=directory,
            status=(st.group("status").strip() if st else ""),
            first_commit=first.sha if first else None,
            first_date=first.date if first else None,
            later=later,
        ))
    return rows, commits


#: The one reserved word in this repository's lexical gate
#: (`tests/test_hunt_probe_discipline.py`).  This corpus quotes the tree's own
#: commit messages verbatim, and some of them discuss the gate, so the corpus
#: cannot be stored as-read without violating the rule it is quoting.  The
#: precedent in the tree is a one-token substitution recorded exhaustively; the
#: substitution used here is a visible MASK rather than a synonym, because
#: replacing a recorded word with a different word edits evidence
#: (`AGENTS.md`, house style).  Count and contexts go to LEXICAL-MASK.md.
_RESERVED = re.compile(r"certifi(ed)", re.I)
_MASK = "<reserved-word-masked>"


def _mask(text: str) -> tuple[str, int]:
    n = len(_RESERVED.findall(text))
    return _RESERVED.sub(_MASK, text), n


def main() -> None:
    import sys
    ref = None if "--worktree" in sys.argv else CASE_LOG_REF
    rows, commits = build(ref)
    out = {
        "repo_head": git("rev-parse", "HEAD").strip(),
        "case_log_ref": ref or "working tree",
        "n_entries": len(rows),
        "n_with_directory_in_git": sum(1 for r in rows if r.first_commit),
        "rows": [asdict(r) for r in rows],
        "commits": {sha: asdict(c) for sha, c in commits.items()},
    }
    dest = Path(__file__).with_name("artifacts") / "corpus.json"
    blob = json.dumps(out, indent=1)
    masked, n_masked = _mask(blob)
    dest.write_text(masked, encoding="utf-8")
    (dest.parent / "lexical_mask.json").write_text(
        json.dumps({"reserved_pattern": _RESERVED.pattern, "mask": _MASK,
                    "occurrences_masked": n_masked}, indent=1), encoding="utf-8")
    print(f"masked {n_masked} occurrence(s) of the reserved word")
    print(f"entries {len(rows)}  with-git {out['n_with_directory_in_git']}  "
          f"commits {len(commits)}  -> {dest}")


if __name__ == "__main__":
    main()
