"""Depth sensitivity: the same measurement on a truncated history.

The container this hunt ran in started with a shallow clone: 262 commits,
reaching back to 2026-08-13.  The full history is 1084 commits reaching back
to 2026-08-01, so the default checkout carried 24 percent of the record.
Nothing announced that, and every count below would have been taken from the
truncated corpus.

This reconstructs the truncated measurement deterministically, by restricting
the corpus to the newest ``--depth`` commits of the current branch, so the
comparison can be rerun by anyone rather than resting on numbers observed once
before ``git fetch --unshallow``.
"""
from __future__ import annotations

import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"


def git(*a: str) -> str:
    return subprocess.run(["git", *a], cwd=REPO, capture_output=True,
                          check=True).stdout.decode("utf-8", "replace")


def horizon(depth: int) -> set[str]:
    return set(git("log", f"-{depth}", "--format=%H").split())


def measure(keep: set[str] | None) -> dict:
    corpus = json.loads((ART / "corpus.json").read_text(encoding="utf-8"))
    rows = corpus["rows"]
    out = {"n_rows": len(rows)}
    later_total = 0
    never = 0
    for r in rows:
        later = [s for s in r["later"] if keep is None or s in keep]
        later_total += len(later)
        if not later:
            never += 1
    out["later_commits_seen"] = later_total
    out["never_revisited"] = never
    out["never_revisited_pct"] = round(100 * never / len(rows), 1)
    out["commits_in_horizon"] = len(keep) if keep is not None else None
    return out


def main() -> None:
    depths = [int(x) for x in (sys.argv[1:] or ["262"])]
    full = measure(None)
    rows = [{"depth": "full", **full}]
    print(f"{'depth':>8s}  {'later seen':>10s}  {'never revisited':>16s}")
    print(f"{'full':>8s}  {full['later_commits_seen']:>10d}  "
          f"{full['never_revisited']:>4d} ({full['never_revisited_pct']:>4.1f}%)")
    for d in depths:
        m = measure(horizon(d))
        rows.append({"depth": d, **m})
        print(f"{d:>8d}  {m['later_commits_seen']:>10d}  "
              f"{m['never_revisited']:>4d} ({m['never_revisited_pct']:>4.1f}%)")
    (ART / "depth.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
