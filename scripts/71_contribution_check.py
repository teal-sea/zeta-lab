#!/usr/bin/env python3
"""Check that an external research hunt carries the lab's review contract."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
HUNTS = REPO_ROOT / "hunts"


def structural_problems(repo_root: Path, hunt: Path) -> list[str]:
    """Return checkable contract failures without judging the mathematics."""
    root = repo_root.resolve()
    hunts = root / "hunts"
    path = hunt if hunt.is_absolute() else root / hunt
    path = path.resolve()
    try:
        relative = path.relative_to(hunts.resolve())
    except ValueError:
        return [f"hunt must be inside {hunts}"]
    if len(relative.parts) != 1:
        return ["hunt must be one directory directly under hunts/"]
    if not path.is_dir():
        return [f"hunt directory does not exist: {path}"]

    problems: list[str] = []
    required = {
        "MISSION.md": "```huntspec",
        "RUNS.md": "```runmanifest",
        "RESULTS.md": None,
    }
    for name, marker in required.items():
        artifact = path / name
        if not artifact.is_file():
            problems.append(f"missing {artifact.relative_to(root)}")
            continue
        text = artifact.read_text(encoding="utf-8")
        if not text.strip():
            problems.append(f"empty {artifact.relative_to(root)}")
        if marker and marker not in text:
            problems.append(f"{artifact.relative_to(root)} has no {marker[3:]} block")

    case_log = hunts / "README.md"
    if not case_log.is_file() or relative.name not in case_log.read_text(encoding="utf-8"):
        problems.append(f"hunts/README.md does not name {relative.name}")
    return problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("hunt", type=Path, help="one hunt directory under hunts/")
    parser.add_argument(
        "--structure-only",
        action="store_true",
        help="check required files without running the repository governance tests",
    )
    args = parser.parse_args(argv)

    problems = structural_problems(REPO_ROOT, args.hunt)
    if problems:
        for problem in problems:
            print(f"FAIL: {problem}", file=sys.stderr)
        return 1
    if args.structure_only:
        print("contribution structure: PASS")
        return 0

    command = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "-m",
        "not slow",
        "-o",
        "addopts=",
        "tests/test_huntspec.py",
        "tests/test_hunt_probe_discipline.py",
    ]
    completed = subprocess.run(command, cwd=REPO_ROOT, check=False)
    if completed.returncode:
        return completed.returncode
    print("contribution contract: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
