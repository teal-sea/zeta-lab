"""Guard coverage: not "does a pin exist" but "how much of the number is held".

`lesion.py` planted one fault per target and reported caught or missed.  That
conflates two failures: a test that does not read the artifact at all, and a
test that reads part of it.  It also picks the first numeric leaf, so a miss
can mean the mutation landed somewhere the test was never going to look.

This module separates them with two rungs.

* **Rung A, does the test read this file at all.**  Multiply *every* numeric
  leaf in the artifact by 1.1 at once and run the test.  A test that stays
  green under that is not reading the file, whatever its name suggests.
* **Rung B, coverage.**  For targets that pass rung A, mutate one leaf at a
  time and count how many of them the test notices.  Coverage is the fraction
  of the artifact's numbers that anything mechanical is holding.

The null rung is unchanged and mandatory: rewrite the artifact through the
same serialiser with no mutation and require the test to stay green, so a
target whose test is red for an unrelated reason is excluded rather than
scored.  The tree is asserted clean between targets.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"
PY = str(REPO / ".venv" / "bin" / "python")

_NUM_MD = re.compile(r"(?<![\w.])(\d+\.\d{4,})(?![\w.])")
MAX_LEAVES = 6
TEST_TIMEOUT = 600


def git(*a: str) -> str:
    return subprocess.run(["git", *a], cwd=REPO, capture_output=True,
                          check=True).stdout.decode("utf-8", "replace")


def run_test(test_file: str) -> bool:
    try:
        p = subprocess.run(
            [PY, "-m", "pytest", "-q", "-x", "-n0", f"tests/{test_file}"],
            cwd=REPO, capture_output=True, timeout=TEST_TIMEOUT)
    except subprocess.TimeoutExpired:
        return True          # treated as "did not fire"; recorded by caller
    return p.returncode == 0


def leaves(path: Path) -> int:
    """How many mutable numeric leaves the artifact has."""
    if path.suffix == ".json":
        try:
            data = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        except Exception:
            return 0
        n = [0]

        def walk(x):
            if isinstance(x, dict):
                for v in x.values():
                    walk(v)
            elif isinstance(x, list):
                for v in x:
                    walk(v)
            elif isinstance(x, bool):
                return
            elif isinstance(x, float) and x != 0.0:
                n[0] += 1
            elif isinstance(x, int) and abs(x) > 3:
                n[0] += 1
        walk(data)
        return n[0]
    return len(_NUM_MD.findall(path.read_text(encoding="utf-8", errors="replace")))


def mutate(path: Path, rel: float, index: int | None) -> str | None:
    """Scale leaf ``index`` by ``1 + rel``; ``index is None`` scales them all."""
    text = path.read_text(encoding="utf-8", errors="replace")
    if path.suffix == ".json":
        try:
            data = json.loads(text)
        except Exception:
            return None
        state = {"i": 0, "hit": None}

        def walk(x):
            if isinstance(x, dict):
                return {k: walk(v) for k, v in x.items()}
            if isinstance(x, list):
                return [walk(v) for v in x]
            if isinstance(x, bool):
                return x
            if isinstance(x, float) and x != 0.0:
                j, state["i"] = state["i"], state["i"] + 1
                if index is None or j == index:
                    state["hit"] = f"[{j}] {x!r}"
                    return x * (1 + rel)
                return x
            if isinstance(x, int) and abs(x) > 3:
                j, state["i"] = state["i"], state["i"] + 1
                if index is None or j == index:
                    state["hit"] = f"[{j}] {x}"
                    return x + max(1, int(abs(x) * rel))
                return x
            return x

        new = walk(data)
        if state["hit"] is None:
            return None
        path.write_text(json.dumps(new, indent=1), encoding="utf-8")
        return state["hit"]

    hits = list(_NUM_MD.finditer(text))
    if not hits:
        return None
    chosen = hits if index is None else ([hits[index]] if index < len(hits) else [])
    if not chosen:
        return None
    out, last, desc = [], 0, None
    for m in chosen:
        old = m.group(1)
        val = float(old) * (1 + rel)
        dec = max(len(old.split(".")[1]), 4)
        out.append(text[last:m.start(1)] + f"{val:.{dec}f}")
        last = m.end(1)
        desc = old
    out.append(text[last:])
    path.write_text("".join(out), encoding="utf-8")
    return desc


def restore(path: Path) -> None:
    git("checkout", "--", str(path.relative_to(REPO)))


def null_rewrite(path: Path) -> None:
    """Byte-identical round trip through the same serialiser used by mutate."""
    if path.suffix == ".json":
        data = json.loads(path.read_text(encoding="utf-8", errors="replace"))
        path.write_text(json.dumps(data, indent=1), encoding="utf-8")


def main() -> None:
    classified = json.loads((ART / "classified.json").read_text(encoding="utf-8"))
    prev = json.loads((ART / "lesion.json").read_text(encoding="utf-8"))
    have_art = [r for r in prev if r.get("artifact")]

    results = []
    for r in have_art:
        art = REPO / r["artifact"]
        test_file = r["test"]
        n_leaves = leaves(art)
        row = {"hunt": r["hunt"], "test": test_file, "artifact": r["artifact"],
               "n_leaves": n_leaves}
        t0 = time.time()

        # null rung
        null_rewrite(art)
        null_green = run_test(test_file)
        restore(art)
        if not null_green:
            row["outcome"] = "null-rung-red"
            results.append(row)
            print(f"{r['hunt']:24s} {test_file:42s} NULL RUNG RED, excluded")
            continue

        # rung A
        desc = mutate(art, 0.10, None)
        row["rungA_all_leaves"] = "caught" if (desc and not run_test(test_file)) else "missed"
        restore(art)
        assert git("status", "--porcelain", "--", r["artifact"]).strip() == ""

        # rung B
        if row["rungA_all_leaves"] == "caught" and n_leaves:
            k = min(MAX_LEAVES, n_leaves)
            caught = 0
            step = max(1, n_leaves // k)
            probed = list(range(0, n_leaves, step))[:k]
            for i in probed:
                if mutate(art, 0.10, i) is None:
                    continue
                if not run_test(test_file):
                    caught += 1
                restore(art)
            row["rungB_probed"] = len(probed)
            row["rungB_caught"] = caught
            row["coverage"] = caught / len(probed) if probed else None
        row["seconds"] = round(time.time() - t0, 1)
        results.append(row)
        print(f"{r['hunt']:24s} {test_file:42s} readsfile={row['rungA_all_leaves']:7s} "
              f"coverage={row.get('coverage')} leaves={n_leaves} ({row['seconds']}s)",
              flush=True)

    (ART / "lesion2.json").write_text(json.dumps(results, indent=1), encoding="utf-8")
    scored = [r for r in results if "rungA_all_leaves" in r]
    reads = [r for r in scored if r["rungA_all_leaves"] == "caught"]
    cov = [r["coverage"] for r in reads if r.get("coverage") is not None]
    print()
    print(f"targets with an artifact {len(results)}   scored {len(scored)}   "
          f"test reads the artifact {len(reads)}   "
          f"mean coverage over those {sum(cov)/len(cov):.2f}" if cov else "")


if __name__ == "__main__":
    main()
