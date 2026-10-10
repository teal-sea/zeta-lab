"""Run every hunt's own tests, one pytest process per directory.

pytest collects only `tests/` (`testpaths` in pyproject.toml), so the tests
that live beside each hunt ran nowhere. They cannot share one process either:
hunts are written as independent studies, several put their own directory on
`sys.path` and import a module named `probe`, and several set python-flint's
process-global precision at import. In one process the first `probe` wins and
the last precision wins; on 2026-10-10 that produced 35 failures and a
collection error that do not occur when each directory runs alone.

So each directory that holds test files runs as its own pytest process, on
its own files only (a parent never collects a child's tests). Files listed in
`hunts/conftest.py`'s `collect_ignore` are left out. A directory that collects
nothing fails, as does a run that changes the git working tree: a test that
writes into the tree is a defect even when it passes.

Usage: .venv/bin/python scripts/run_hunt_tests.py [pytest args...]
"""
from __future__ import annotations

import runpy
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HUNTS = ROOT / "hunts"

#: fewer directories than this means discovery is not reading the tree it
#: thinks it is; refuse to report a pass (28 on 2026-10-10)
MIN_DIRS = 20


def hunt_test_dirs() -> dict[Path, list[Path]]:
    """Each directory holding hunt tests, with its own test files."""
    ignored = {(HUNTS / p).resolve()
               for p in runpy.run_path(str(HUNTS / "conftest.py"))["collect_ignore"]}
    by_dir: dict[Path, list[Path]] = {}
    for f in sorted(HUNTS.rglob("test_*.py")):
        if ".lake" in f.parts or f.resolve() in ignored:
            continue
        by_dir.setdefault(f.parent, []).append(f)
    return by_dir


def _tree_state() -> str:
    proc = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"],
                          cwd=ROOT, capture_output=True, text=True, check=True)
    return proc.stdout


def main(extra: list[str]) -> int:
    dirs = hunt_test_dirs()
    if len(dirs) < MIN_DIRS:
        print(f"only {len(dirs)} hunt test directories found (< {MIN_DIRS}); "
              "refusing to report a pass")
        return 1
    before = _tree_state()
    failed = []
    for d, files in dirs.items():
        rel = d.relative_to(ROOT)
        print(f"\n=== {rel} ({len(files)} files)", flush=True)
        t0 = time.monotonic()
        rc = subprocess.call([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider",
                              *[str(f.relative_to(ROOT)) for f in files], *extra], cwd=ROOT)
        print(f"=== {rel}: exit {rc} in {time.monotonic() - t0:.0f}s", flush=True)
        if rc != 0:
            failed.append((rel, rc))
    after = _tree_state()
    print(f"\n{len(dirs)} directories, {len(dirs) - len(failed)} passed")
    for rel, rc in failed:
        print(f"FAILED {rel} (exit {rc})")
    if after != before:
        print("the run changed the working tree:")
        changed = set(after.splitlines()) ^ set(before.splitlines())
        for line in sorted(changed):
            print(f"  {line}")
        return 1
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
