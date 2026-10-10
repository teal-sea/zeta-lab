"""`scripts/run_hunt_tests.py`: the nightly's runner for the hunts' own tests.

Discovery is checked on the real tree; the verdicts are checked by planting a
passing hunt, a failing one and one that writes into the tree in a scratch git
repository, since a runner that cannot go red is not a check.
"""
from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import run_hunt_tests  # noqa: E402


def test_discovery_reads_the_real_tree():
    dirs = run_hunt_tests.hunt_test_dirs()
    assert len(dirs) >= run_hunt_tests.MIN_DIRS
    assert ROOT / "hunts" / "frontier_math" in dirs
    for d, files in dirs.items():
        assert files and all(f.parent == d for f in files), d


def test_the_archived_script_is_not_run():
    """It overwrites its committed results when imported (hunts/conftest.py)."""
    archived = (ROOT / "hunts" / "prime_pair_error" / "frontier" / "2026-09-06"
                / "joint_support_analysis" / "test_q20_direction.py")
    assert archived.exists()
    assert not any(archived in files for files in run_hunt_tests.hunt_test_dirs().values())


def _scratch_repo(tmp_path: Path, monkeypatch, tests: dict[str, str]) -> None:
    hunts = tmp_path / "hunts"
    hunts.mkdir()
    (hunts / "conftest.py").write_text("collect_ignore = []\n")
    (tmp_path / ".gitignore").write_text("__pycache__/\n")   # as the real tree
    for rel, body in tests.items():
        p = hunts / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body)
    git = ["git", "-c", "user.email=t@t", "-c", "user.name=t"]
    subprocess.run([*git, "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run([*git, "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run([*git, "commit", "-qm", "plant"], cwd=tmp_path, check=True)
    monkeypatch.setattr(run_hunt_tests, "ROOT", tmp_path)
    monkeypatch.setattr(run_hunt_tests, "HUNTS", hunts)
    monkeypatch.setattr(run_hunt_tests, "MIN_DIRS", 1)


PASS = "def test_ok():\n    assert True\n"


@pytest.mark.skipif(shutil.which("git") is None, reason="needs git")
@pytest.mark.parametrize("planted, verdict", [
    ({"a/test_a.py": PASS, "a/b/test_b.py": PASS}, 0),
    ({"a/test_a.py": PASS, "c/test_c.py": "def test_no():\n    assert False\n"}, 1),
    ({"a/test_a.py": "from pathlib import Path\n\ndef test_writes():\n"
                     "    (Path(__file__).parent / 'junk.json').write_text('{}')\n"}, 1),
])
def test_the_runner_goes_red_on_a_failure_or_a_write(tmp_path, monkeypatch, planted, verdict):
    _scratch_repo(tmp_path, monkeypatch, planted)
    assert run_hunt_tests.main(["-p", "no:xdist"]) == verdict
