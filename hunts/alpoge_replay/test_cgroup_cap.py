"""cgroup_cap.sh: the replay's processes get a memory group of their own, and nothing here can stop a job."""
from __future__ import annotations

import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "cgroup_cap.sh"


def _run(root: Path, *args: str):
    env = dict(os.environ, CGROUP_ROOT=str(root), CGROUP_SUDO="")
    return subprocess.run(["bash", str(SCRIPT), *args], env=env, capture_output=True, text=True, timeout=60)


def _root(tmp_path: Path, controllers: str = "cpuset cpu io memory pids", subtree: str = "cpu memory pids") -> Path:
    """A stand-in for /sys/fs/cgroup: plain files where the kernel has its own."""
    root = tmp_path / "cgroup"
    root.mkdir()
    (root / "cgroup.controllers").write_text(controllers + "\n")
    (root / "cgroup.subtree_control").write_text(subtree + "\n")
    return root


def test_the_pid_is_moved_and_the_limit_is_in_bytes(tmp_path):
    root = _root(tmp_path)
    proc = _run(root, "11500", "4242")
    assert proc.returncode == 0, proc.stderr
    group = root / "alpoge-replay"
    assert (group / "memory.high").read_text().strip() == str(11500 * 1024 * 1024)
    assert (group / "cgroup.procs").read_text().strip() == "4242"
    assert "pid 4242 is in alpoge-replay" in proc.stdout and str(11500 * 1024 * 1024) in proc.stdout
    # the controller was on already: the list of the root's children is left as it was
    assert (root / "cgroup.subtree_control").read_text().strip() == "cpu memory pids"


def test_the_memory_controller_is_switched_on_for_children_where_it_is_not(tmp_path):
    root = _root(tmp_path, subtree="cpu pids")
    proc = _run(root, "8000", "7", "other-name")
    assert proc.returncode == 0, proc.stderr
    assert (root / "cgroup.subtree_control").read_text().strip() == "+memory"
    assert (root / "other-name" / "cgroup.procs").read_text().strip() == "7"


def test_without_cgroup_v2_or_without_the_controller_nothing_is_capped_and_nothing_fails(tmp_path):
    proc = _run(tmp_path / "absent", "8000", "7")
    assert proc.returncode == 0 and "no cgroup v2" in proc.stdout and "nothing capped" in proc.stdout
    root = _root(tmp_path, controllers="cpuset cpu io pids", subtree="cpu pids")
    proc = _run(root, "8000", "7")
    assert proc.returncode == 0 and "no memory controller" in proc.stdout
    assert not (root / "alpoge-replay").exists()


def test_a_group_that_cannot_be_made_is_reported_and_does_not_fail(tmp_path):
    root = _root(tmp_path)
    (root / "alpoge-replay").write_text("a file where the group's directory should go\n")
    proc = _run(root, "8000", "7")
    assert proc.returncode == 0 and "nothing capped" in proc.stdout
    assert "is in alpoge-replay" not in proc.stdout


def test_sizes_and_pids_that_are_not_numbers_are_refused(tmp_path):
    root = _root(tmp_path)
    for args in (("lots", "7"), ("8000", "self"), ("", "7"), ("8000",)):
        proc = _run(root, *args)
        assert proc.returncode == 2, (args, proc.stdout, proc.stderr)
    assert not (root / "alpoge-replay").exists()
