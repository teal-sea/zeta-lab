"""Classify what happened to each recorded claim, and how it is defended.

Three measurements, kept apart because they answer different questions:

1. **Correction.** Did a later commit revise, withdraw or contradict the
   claim, how long did that take, and what caught it.
2. **Pinning.** Is the claim named by any test in ``tests/``, i.e. is there
   anything mechanical that would notice if it stopped being true.
3. **Assertion.** Does the case-log status assert a finding at all.  A hunt
   that records "probe, no claim promoted" is not an unpinned claim; it is
   not a claim.  Mixing the two flatters the pinning rate in one direction
   and the correction rate in the other, so they are separated first.

Every rule below is lexical and stated here rather than in prose, so that a
reader can disagree with a specific line.  ``audit.py`` samples the output
by hand and reports the confusion matrix, because a classifier nobody
checked is a classifier that measures its own author.
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"

# --- rule set 1: does a status assert a finding? ---------------------------
_DISCLAIMS = re.compile(
    r"artifact only|no write-up|no results|probe, not established|"
    r"in progress|no claim promoted|instrument retained",
    re.I,
)
_ASSERTS = re.compile(
    r"settled|ceiling|barrier|gap|closed|negative|improvement|refut|"
    r"withdraw|audit|retained|complete",
    re.I,
)

# --- rule set 2: correction signals ----------------------------------------
#: added lines in a claim file that negate or revise a recorded statement
_SELF_NEGATING = re.compile(
    r"\b(withdraw\w*|retract\w*|erratum|correction|corrected|invalidat\w*|"
    r"supersed\w*|is false|was false|was wrong|does not survive|no longer|"
    r"unsupported|incorrect|defect|refuted|overstat\w*|mis(?:read|stated|counted))\b",
    re.I,
)
#: commit subjects that announce a revision
_REVISING_SUBJECT = re.compile(
    r"\b(correct\w*|fix\w*|withdraw\w*|retract\w*|revise\w*|repair\w*|erratum|"
    r"stale|wrong|refut\w*|invalidat\w*|supersed\w*|closeout correction)\b",
    re.I,
)
#: a decimal literal of at least four significant figures
_NUMBER = re.compile(r"\d+\.\d{3,}")

CLAIM_FILES = ("RESULTS.md", "README.md", "MISSION.md", "RUNS.md", "FINDINGS.md")


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=REPO, capture_output=True,
                          check=True).stdout.decode("utf-8", errors="replace")


def _diff_of(sha: str, path: str) -> str:
    try:
        return git("show", "--format=", "--unified=0", sha, "--", path)
    except subprocess.CalledProcessError:
        return ""


def _added(diff: str) -> str:
    return "\n".join(l[1:] for l in diff.splitlines()
                     if l.startswith("+") and not l.startswith("+++"))


def _removed(diff: str) -> str:
    return "\n".join(l[1:] for l in diff.splitlines()
                     if l.startswith("-") and not l.startswith("---"))


def classify_commit(sha: str, hunt_dir: str, commits: dict) -> dict:
    """Return the three strictness verdicts and the attribution for one commit."""
    c = commits[sha]
    path = f"hunts/{hunt_dir}"
    claim_paths = [f for f in c["files"]
                   if f.startswith(path + "/") and Path(f).name in CLAIM_FILES]
    diff = "".join(_diff_of(sha, p) for p in claim_paths)
    added, removed = _added(diff), _removed(diff)

    strict = bool(_SELF_NEGATING.search(added))
    medium = strict or bool(_REVISING_SUBJECT.search(c["subject"]))
    # a claim number that changed: a 4+ significant-figure literal removed and
    # a different one added in the same claim file
    old_nums = set(_NUMBER.findall(removed))
    new_nums = set(_NUMBER.findall(added))
    number_moved = bool(old_nums - new_nums) and bool(new_nums - old_nums)
    loose = medium or number_moved

    # What the commit shows about how the correction was handled.  Note the
    # limit, which is the whole reason these are not called "who found it":
    # git records what a commit DID, not what made someone look.  A commit
    # that adds a test alongside a fix has installed a countermeasure; it has
    # not demonstrated that a test caught anything.  Only the message can
    # attribute a find, and only when its author chose to say so.
    files = c["files"]
    text = c["subject"] + "\n" + c["body"]
    countermeasure = "test-added" if any(f.startswith("tests/") for f in files) else "none"
    if any("/audit/" in f for f in files):
        attribution = "outside-audit"
    elif re.search(r"\b(operator|reader|asked|pointed out|a human)\b", text, re.I):
        attribution = "human-stated-in-message"
    elif re.search(r"\b(test|guard|check) (caught|fired|found|refused)\b", text, re.I):
        attribution = "guard-stated-in-message"
    else:
        attribution = "unattributed"
    who = attribution

    return {
        "sha": sha, "date": c["date"], "subject": c["subject"],
        "claim_files_touched": claim_paths,
        "strict": strict, "medium": medium, "loose": loose,
        "number_moved": number_moved, "who": who,
        "countermeasure": countermeasure,
        "n_added_lines": len(added.splitlines()),
    }


def days_between(a: str, b: str) -> int:
    from datetime import date
    ya, ma, da = (int(x) for x in a.split("-"))
    yb, mb, db = (int(x) for x in b.split("-"))
    return (date(yb, mb, db) - date(ya, ma, da)).days


def main() -> None:
    corpus = json.loads((ART / "corpus.json").read_text(encoding="utf-8"))
    commits = corpus["commits"]
    tests = {p.name: p.read_text(encoding="utf-8", errors="replace")
             for p in (REPO / "tests").glob("*.py")}

    out = []
    for r in corpus["rows"]:
        status = r["status"]
        asserts = bool(_ASSERTS.search(status)) and not _DISCLAIMS.search(status)
        pinned = sorted(n for n, t in tests.items() if r["directory"] in t)
        events = [classify_commit(s, r["directory"], commits) for s in r["later"]]
        for e in events:
            e["latency_days"] = days_between(r["first_date"], e["date"])
        out.append({
            "number": r["number"], "directory": r["directory"],
            "heading": r["heading"], "status": status,
            "asserts_a_finding": asserts,
            "pinned_by": pinned,
            "first_date": r["first_date"],
            "n_later_commits": len(r["later"]),
            "events": events,
        })

    (ART / "classified.json").write_text(json.dumps(out, indent=1), encoding="utf-8")

    n = len(out)
    a = [r for r in out if r["asserts_a_finding"]]
    for level in ("strict", "medium", "loose"):
        corrected = [r for r in out if any(e[level] for e in r["events"])]
        corr_a = [r for r in a if any(e[level] for e in r["events"])]
        lat = sorted(e["latency_days"] for r in out for e in r["events"] if e[level])
        med = lat[len(lat) // 2] if lat else None
        print(f"{level:7s} corrected {len(corrected):3d}/{n} ({100*len(corrected)/n:5.1f}%)   "
              f"asserting-only {len(corr_a):3d}/{len(a)} ({100*len(corr_a)/max(len(a),1):5.1f}%)   "
              f"median latency {med} d   n_events {len(lat)}")
    print()
    print(f"asserting a finding      {len(a)}/{n} ({100*len(a)/n:.1f}%)")
    pin_all = sum(1 for r in out if r["pinned_by"])
    pin_a = sum(1 for r in a if r["pinned_by"])
    print(f"pinned by any test       {pin_all}/{n} ({100*pin_all/n:.1f}%)  "
          f"of asserting: {pin_a}/{len(a)} ({100*pin_a/len(a):.1f}%)")
    never = sum(1 for r in out if r["n_later_commits"] == 0)
    print(f"never touched again      {never}/{n} ({100*never/n:.1f}%)")
    from collections import Counter
    who = Counter(e["who"] for r in out for e in r["events"] if e["medium"])
    print("attribution stated in the commit (medium):", dict(who))
    cm = Counter(e["countermeasure"] for r in out for e in r["events"] if e["medium"])
    print("countermeasure installed with the correction:", dict(cm))


if __name__ == "__main__":
    main()
