"""io_tune.sh: the two page-fault windows are set where the directory lives, and nothing here can stop a build."""
from __future__ import annotations

import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "io_tune.sh"


def _majmin(path: Path) -> str:
    out = subprocess.run(["findmnt", "-n", "-o", "MAJ:MIN", "--target", str(path)], capture_output=True, text=True)
    return out.stdout.strip()


def _run(sysdir: Path, *args: str):
    env = dict(os.environ, IO_TUNE_SYS=str(sysdir), IO_TUNE_SUDO="")
    return subprocess.run(["bash", str(SCRIPT), *args], env=env, capture_output=True, text=True, timeout=60)


def _sys(tmp_path: Path, partition: bool = False) -> tuple[Path, Path, Path]:
    """A stand-in /sys for the device tmp_path is on."""
    sysdir = tmp_path / "sys"
    mm = _majmin(tmp_path)
    if partition:   # the partition's entry is a link into the disk's directory, which has the queue
        disk = sysdir / "devices" / "disk0"
        (disk / mm).mkdir(parents=True)
        (sysdir / "dev" / "block").mkdir(parents=True)
        (sysdir / "dev" / "block" / mm).symlink_to(disk / mm)
        ra = disk / "queue" / "read_ahead_kb"
    else:
        ra = sysdir / "dev" / "block" / mm / "queue" / "read_ahead_kb"
    ra.parent.mkdir(parents=True)
    ra.write_text("128\n")
    fa = sysdir / "kernel" / "debug" / "fault_around_bytes"
    fa.parent.mkdir(parents=True)
    fa.write_text("65536\n")
    return sysdir, ra, fa


def test_both_windows_are_set_and_reported(tmp_path):
    sysdir, ra, fa = _sys(tmp_path)
    (tmp_path / "a").mkdir()
    (tmp_path / "b").mkdir()
    proc = _run(sysdir, "16", "4096", str(tmp_path / "a"), str(tmp_path / "b"))
    assert proc.returncode == 0, proc.stderr
    assert ra.read_text().strip() == "16" and fa.read_text().strip() == "4096"
    assert proc.stdout.count("read_ahead_kb 128 -> 16") == 1      # two directories on one device: set once
    assert "fault_around_bytes 65536 -> 4096" in proc.stdout


def test_a_partition_uses_the_queue_of_its_disk(tmp_path):
    sysdir, ra, _ = _sys(tmp_path, partition=True)
    proc = _run(sysdir, "16", "4096", str(tmp_path))
    assert proc.returncode == 0, proc.stderr
    assert ra.read_text().strip() == "16"


def test_missing_files_are_reported_and_do_not_fail(tmp_path):
    proc = _run(tmp_path / "empty", "16", "4096", str(tmp_path))
    assert proc.returncode == 0
    assert "no read_ahead_kb found" in proc.stdout and "no fault_around_bytes" in proc.stdout


def test_sizes_that_are_not_numbers_are_refused(tmp_path):
    sysdir, ra, _ = _sys(tmp_path)
    for bad in (["16; reboot", "4096"], ["", "4096"], ["16", "all"]):
        assert _run(sysdir, *bad, str(tmp_path)).returncode == 2
    assert ra.read_text().strip() == "128"
