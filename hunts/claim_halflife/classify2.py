"""The classifier, rebuilt after its blind audit scored it at 53% agreement.

`classify.py` is kept as it was.  It reported that 21% of case-log entries were
later revised, and a blind hand audit of 30 stratified rows agreed with it on
16, precision 0.40 and recall 0.55 against a balanced sample.  That is close
enough to chance that its rate could not be reported, and the audit's row notes
name two structural defects rather than borderline judgement calls:

1. **The hunt's opening was counted as a revision of itself.**  `first_commit`
   was the first commit touching one of five hard-coded filenames, so a hunt
   that landed code or a `MISSION.md` first and its `RESULTS.md` second had that
   second commit classified as a later revision.  Rows 9 and 12 of the sample
   are exactly this, and the auditor caught both from the diff alone.
2. **A withdrawal written into a differently-named file was invisible.**  Row 8
   adds `BLOCKPOS-WITHDRAWN.md`, header "WITHDRAWN / FALSIFIED", and the
   classifier scored it clean because the filename was not in its list of five.

Both are defects on their own terms, independent of the sample that exposed
them, which is why they are repaired rather than tuned around.  The repair:

* the hunt's own first commit is excluded, whatever it touches;
* a claim file is any `.md` in the hunt directory, plus `results*.json`;
* a revision needs evidence of *replacement*, not of addition: either an
  already-existing claim file loses lines and gains self-negating language or a
  changed four-significant-figure number, or a new file arrives whose name or
  first heading declares a withdrawal, correction or erratum.

**The 30 audited rows were used to find these defects, so the agreement figure
recomputed against them is not an independent validation.**  A second blind
audit on a fresh sample is what would be, and `make_audit_sample.py --exclude`
draws one.
"""
from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"

import classify as C  # the rules that survive, and git plumbing

_SELF_NEGATING = C._SELF_NEGATING
_REVISING_SUBJECT = C._REVISING_SUBJECT
_NUMBER = C._NUMBER

#: a file whose arrival is itself a withdrawal
_WITHDRAWAL_NAME = re.compile(
    r"(withdraw|retract|correction|erratum|falsifi|invalid)", re.I)
_WITHDRAWAL_HEADING = re.compile(
    r"^#.*\b(withdrawn|retracted|falsified|correction|erratum|invalidated)\b",
    re.I | re.MULTILINE)


def git(*a: str) -> str:
    return subprocess.run(["git", *a], cwd=REPO, capture_output=True,
                          check=True).stdout.decode("utf-8", "replace")


def is_claim_file(path: str, hunt_dir: str) -> bool:
    p = Path(path)
    if not path.startswith(f"hunts/{hunt_dir}/"):
        return False
    return p.suffix == ".md" or (p.suffix == ".json" and p.name.startswith("results"))


def existed_before(sha: str, path: str) -> bool:
    r = subprocess.run(["git", "cat-file", "-e", f"{sha}^:{path}"],
                       cwd=REPO, capture_output=True)
    return r.returncode == 0


def classify_commit(sha: str, hunt_dir: str, commits: dict) -> dict:
    c = commits[sha]
    claim_paths = [f for f in c["files"] if is_claim_file(f, hunt_dir)]
    evidence, replaced, added_withdrawal = [], False, False
    number_moved = False

    for p in claim_paths:
        diff = C._diff_of(sha, p)
        added, removed = C._added(diff), C._removed(diff)
        pre = existed_before(sha, p)
        if pre:
            if removed.strip():
                if _SELF_NEGATING.search(added):
                    replaced = True
                    evidence.append(f"{p}: existing text replaced, self-negating language added")
                old_n, new_n = set(_NUMBER.findall(removed)), set(_NUMBER.findall(added))
                if (old_n - new_n) and (new_n - old_n):
                    replaced, number_moved = True, True
                    evidence.append(f"{p}: a four-figure number changed")
        else:
            head = "\n".join(added.splitlines()[:6])
            if _WITHDRAWAL_NAME.search(Path(p).name) or _WITHDRAWAL_HEADING.search(head):
                added_withdrawal = True
                evidence.append(f"{p}: new file declaring a withdrawal or correction")

    strict = replaced or added_withdrawal
    medium = strict or (bool(_REVISING_SUBJECT.search(c["subject"])) and bool(claim_paths))
    return {
        "sha": sha, "date": c["date"], "subject": c["subject"],
        "claim_files_touched": claim_paths,
        "strict": strict, "medium": medium, "loose": medium or number_moved,
        "number_moved": number_moved, "evidence": evidence,
        "countermeasure": "test-added" if any(f.startswith("tests/") for f in c["files"]) else "none",
    }


def main() -> None:
    corpus = json.loads((ART / "corpus.json").read_text(encoding="utf-8"))
    commits = corpus["commits"]
    tests = {p.name: p.read_text(encoding="utf-8", errors="replace")
             for p in (REPO / "tests").glob("*.py")}

    out = []
    for r in corpus["rows"]:
        status = r["status"]
        asserts = bool(C._ASSERTS.search(status)) and not C._DISCLAIMS.search(status)
        pinned = sorted(n for n, t in tests.items() if r["directory"] in t)
        # the hunt's own opening commit is excluded whatever it touched
        later = r["later"]
        events = [classify_commit(s, r["directory"], commits) for s in later]
        for e in events:
            e["latency_days"] = C.days_between(r["first_date"], e["date"])
        out.append({
            "number": r["number"], "directory": r["directory"],
            "heading": r["heading"], "status": status,
            "asserts_a_finding": asserts, "pinned_by": pinned,
            "first_date": r["first_date"], "first_commit": r["first_commit"],
            "n_later_commits": len(later), "events": events,
        })

    (ART / "classified2.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    n = len(out)
    a = [r for r in out if r["asserts_a_finding"]]
    for level in ("strict", "medium", "loose"):
        corrected = [r for r in out if any(e[level] for e in r["events"])]
        lat = sorted(e["latency_days"] for r in out for e in r["events"] if e[level])
        med = lat[len(lat) // 2] if lat else None
        print(f"{level:7s} revised {len(corrected):3d}/{n} ({100*len(corrected)/n:5.1f}%)   "
              f"median latency {med} d   events {len(lat)}")
    from collections import Counter
    cm = Counter(e["countermeasure"] for r in out for e in r["events"] if e["strict"])
    print(f"countermeasure installed with a strict revision: {dict(cm)}")


if __name__ == "__main__":
    main()
