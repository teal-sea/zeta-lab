"""Controls for the correction classifier.

Three of them, because a rate with no control is a number with no meaning:

* **Null corpus.**  Run the identical rules over directories that carry no
  research claims (`scripts/`, `.github/`, `interactive_lab/`).  If the
  self-negating-language rule fires there at the same rate it fires on
  claim files, the rule is reading commit-message habit rather than
  correction.
* **Published-page comparison.**  `docs/NN-*.md` are the promoted pages.
  The certainty ladder predicts they should be corrected *less* often than
  `hunts/`, which is the tree's designated place for unvetted claims.  If
  they are corrected more, the ladder is not doing what it says.
* **Depth sensitivity.**  The same measurement on the shallow clone this
  container started with, against the full history, because a study of git
  history run on a truncated history reports a truncated answer and says
  nothing about it.
"""
from __future__ import annotations

import json
import re
import subprocess
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"

import classify as C  # noqa: E402  (same directory; run from here)


def git(*a: str) -> str:
    return subprocess.run(["git", *a], cwd=REPO, capture_output=True,
                          check=True).stdout.decode("utf-8", errors="replace")


def _shas_touching(pathspec: str, since: str | None = None) -> list[str]:
    args = ["log", "--reverse", "--format=%H"]
    if since:
        args += [f"--since={since}"]
    args += ["--", pathspec]
    return git(*args).split()


def rate_over(pathspec: str, suffix: str, since: str | None = None) -> dict:
    """Fraction of commits touching ``pathspec`` whose diff to ``suffix`` files
    adds self-negating language, and whose subject announces a revision."""
    shas = _shas_touching(pathspec, since)
    strict = medium = 0
    for sha in shas:
        files = [f for f in git("show", "--format=", "--name-only", sha).split()
                 if f.startswith(pathspec.rstrip("/*")) and f.endswith(suffix)]
        if not files:
            continue
        diff = "".join(C._diff_of(sha, f) for f in files)
        added = C._added(diff)
        subj = git("show", "--format=%s", "-s", sha).strip()
        s = bool(C._SELF_NEGATING.search(added))
        m = s or bool(C._REVISING_SUBJECT.search(subj))
        strict += s
        medium += m
    return {"pathspec": pathspec, "suffix": suffix, "n_commits": len(shas),
            "strict": strict, "medium": medium,
            "strict_rate": strict / len(shas) if shas else None,
            "medium_rate": medium / len(shas) if shas else None}


def main() -> None:
    rows = []
    for spec, suf in [
        ("hunts/", ".md"),
        ("docs/", ".md"),
        ("scripts/", ".py"),
        (".github/", ".yml"),
        ("interactive_lab/", ".html"),
        ("zeta/", ".py"),
    ]:
        r = rate_over(spec, suf)
        rows.append(r)
        sr = f"{100*r['strict_rate']:.1f}%" if r["strict_rate"] is not None else "n/a"
        mr = f"{100*r['medium_rate']:.1f}%" if r["medium_rate"] is not None else "n/a"
        print(f"{spec:18s}{suf:6s} commits {r['n_commits']:4d}   "
              f"self-negating-added {r['strict']:3d} ({sr:>6s})   "
              f"revising-subject-or-that {r['medium']:3d} ({mr:>6s})")
    (ART / "controls.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
