"""The planted-fault ladder: do the pins that exist actually fire?

`classify.py` measures how many recorded claims are *named* by a test.  That
is presence, not power.  This module measures power: for every hunt whose
claim files are read by a test, plant a fault in the artifact the test reads
and record whether the test goes red.

Three rungs per target, because a single mutation cannot separate a strict
guard from a broken one:

* **null**  rewrite the artifact byte-identically.  The test must stay green.
  If it does not, the target is excluded: whatever it is measuring, it is not
  this file.
* **coarse** move one numeric leaf by 10 percent.  A test that misses this is
  not reading the number at all.
* **fine**  move the same leaf by one part in a million.  A test that catches
  coarse and misses fine is reading the number at a tolerance, which is a
  different and weaker guarantee, and worth separating.

Every mutation is reverted with `git checkout --` before the next one, and
the tree is asserted clean between targets.  A ladder that corrupts the tree
it is measuring has produced nothing.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
ART = HERE / "artifacts"
PY = str(REPO / ".venv" / "bin" / "python")

_NUM_MD = re.compile(r"(?<![\w.])(\d+\.\d{4,})(?![\w.])")


def git(*a: str) -> str:
    return subprocess.run(["git", *a], cwd=REPO, capture_output=True,
                          check=True).stdout.decode("utf-8", "replace")


def tree_is_clean(paths: list[str]) -> bool:
    out = git("status", "--porcelain", "--", *paths).strip()
    return out == ""


def run_test(test_file: str, timeout: int = 900) -> tuple[bool, str]:
    """True when the test file passes."""
    p = subprocess.run(
        [PY, "-m", "pytest", "-q", "-x", "-n0", f"tests/{test_file}"],
        cwd=REPO, capture_output=True, timeout=timeout,
    )
    return p.returncode == 0, p.stdout.decode("utf-8", "replace")[-1500:]


def artifacts_read_by(test_file: str, hunt_dir: str) -> list[Path]:
    """Files inside the hunt directory whose names appear in the test source."""
    src = (REPO / "tests" / test_file).read_text(encoding="utf-8", errors="replace")
    found = []
    for p in sorted((REPO / "hunts" / hunt_dir).rglob("*")):
        if not p.is_file() or p.suffix not in (".json", ".md"):
            continue
        if p.name in src:
            found.append(p)
    return found


def mutate(path: Path, rel: float) -> str | None:
    """Move one numeric leaf by a relative amount.  Returns a description."""
    text = path.read_text(encoding="utf-8", errors="replace")
    if path.suffix == ".json":
        try:
            data = json.loads(text)
        except Exception:
            return None
        target = {"done": False, "desc": None}

        def walk(node):
            if target["done"]:
                return node
            if isinstance(node, dict):
                return {k: walk(v) for k, v in node.items()}
            if isinstance(node, list):
                return [walk(v) for v in node]
            if isinstance(node, float) and node != 0.0:
                target["done"] = True
                target["desc"] = f"float {node!r} -> {node * (1 + rel)!r}"
                return node * (1 + rel)
            if isinstance(node, int) and abs(node) > 3 and not isinstance(node, bool):
                delta = max(1, int(abs(node) * rel))
                target["done"] = True
                target["desc"] = f"int {node} -> {node + delta}"
                return node + delta
            return node

        new = walk(data)
        if not target["done"]:
            return None
        path.write_text(json.dumps(new, indent=1), encoding="utf-8")
        return target["desc"]

    m = _NUM_MD.search(text)
    if not m:
        return None
    old = m.group(1)
    new_val = float(old) * (1 + rel)
    new = f"{new_val:.{max(len(old.split('.')[1]), 4)}f}"
    path.write_text(text[:m.start(1)] + new + text[m.end(1):], encoding="utf-8")
    return f"md {old} -> {new}"


def restore(path: Path) -> None:
    git("checkout", "--", str(path.relative_to(REPO)))


def main() -> None:
    classified = json.loads((ART / "classified.json").read_text(encoding="utf-8"))
    targets = [(r["directory"], t) for r in classified for t in r["pinned_by"]]
    only = sys.argv[1] if len(sys.argv) > 1 else None
    if only:
        targets = [t for t in targets if t[0] == only]

    results = []
    for hunt_dir, test_file in targets:
        arts = artifacts_read_by(test_file, hunt_dir)
        if not arts:
            results.append({"hunt": hunt_dir, "test": test_file,
                            "outcome": "no-artifact-named", "artifacts": []})
            print(f"{hunt_dir:26s} {test_file:42s} no artifact named in the test")
            continue
        art = arts[0]
        rel_art = str(art.relative_to(REPO))

        base_ok, base_out = run_test(test_file)
        if not base_ok:
            results.append({"hunt": hunt_dir, "test": test_file,
                            "outcome": "baseline-red", "artifact": rel_art,
                            "tail": base_out})
            print(f"{hunt_dir:26s} {test_file:42s} BASELINE RED, excluded")
            continue

        row = {"hunt": hunt_dir, "test": test_file, "artifact": rel_art,
               "n_artifacts_named": len(arts)}
        for rung, rel in (("coarse", 0.10), ("fine", 1e-6)):
            desc = mutate(art, rel)
            if desc is None:
                row[rung] = "no-mutable-leaf"
                restore(art)
                continue
            ok, tail = run_test(test_file)
            row[rung] = "caught" if not ok else "missed"
            row[f"{rung}_mutation"] = desc
            restore(art)
            assert tree_is_clean([rel_art]), f"tree dirty after {rung} on {rel_art}"
        results.append(row)
        print(f"{hunt_dir:26s} {test_file:42s} coarse={row.get('coarse')} "
              f"fine={row.get('fine')}  [{rel_art}]")

    (ART / "lesion.json").write_text(json.dumps(results, indent=1), encoding="utf-8")
    caught_c = sum(1 for r in results if r.get("coarse") == "caught")
    caught_f = sum(1 for r in results if r.get("fine") == "caught")
    scored = [r for r in results if r.get("coarse") in ("caught", "missed")]
    print()
    print(f"targets {len(results)}   scored {len(scored)}   "
          f"coarse caught {caught_c}   fine caught {caught_f}")


if __name__ == "__main__":
    main()
