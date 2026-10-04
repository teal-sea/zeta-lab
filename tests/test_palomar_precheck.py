"""Preparation checks reject stale compilers and unapproved public imports."""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
PROJECT = "hunts/ainta_seven_point/lean-four-point"


@pytest.fixture
def prepared_repo(tmp_path):
    package = tmp_path / PROJECT
    package.mkdir(parents=True)
    (tmp_path / "lean").mkdir()
    for name in ["LICENSE", "lean/palomar-pairs.json"]:
        shutil.copyfile(ROOT / name, tmp_path / name)
    for name in [
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "comparator.json", "formalization.yaml",
        "StrongerChallenge.lean", "StrongerSolution.lean",
    ]:
        shutil.copyfile(ROOT / PROJECT / name, package / name)
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "add", "."], check=True)
    return tmp_path


def run_precheck(repo):
    return subprocess.run(
        [sys.executable, str(ROOT / "scripts/palomar_precheck.py"),
         str(repo), f"{PROJECT}/comparator.json"],
        capture_output=True, text=True,
    )


@pytest.mark.parametrize("version,accepted", [
    ("v4.34.0", False),
    ("v4.35.0-rc1", False),
    ("v4.35.0-rc2", True),
    ("v4.35.0-rc10", True),
    ("v4.35.0", True),
    ("v4.35.0-unknown", False),
])
def test_toolchain_floor_orders_release_candidates(prepared_repo, version, accepted):
    (prepared_repo / PROJECT / "lean-toolchain").write_text(f"leanprover/lean4:{version}\n")
    result = run_precheck(prepared_repo)
    assert (result.returncode == 0) is accepted, result.stdout + result.stderr
    verdict = "PASS" if accepted else "FAIL"
    assert f"{verdict}  toolchain {version} >= minimum v4.35.0-rc2" in result.stdout


def test_public_import_cannot_bypass_challenge_guard(prepared_repo):
    challenge = prepared_repo / PROJECT / "StrongerChallenge.lean"
    challenge.write_text(challenge.read_text().replace(
        "public import Mathlib", "public import RequestProject.Spoof",
    ))
    result = run_precheck(prepared_repo)
    assert result.returncode == 1, result.stdout + result.stderr
    assert "FAIL  Challenge imports approved roots only: ['RequestProject.Spoof']" in result.stdout
