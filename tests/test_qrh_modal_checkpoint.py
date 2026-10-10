"""Exercise interrupted-build recovery without running Lean or cloud compute."""

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import time

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "qrh_checkpoint", ROOT / "lean/qrh/scripts/modal_checkpoint.py")
checkpoint = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checkpoint)


def ticking_command(path):
    child = (
        "import time; from pathlib import Path; "
        f"p = Path({str(path)!r}); "
        "exec('while True:\\n with p.open(\"a\") as f: f.write(\"tick\\\\n\")"
        "\\n time.sleep(0.01)')"
    )
    parent = (
        "import subprocess, sys, time; "
        f"subprocess.Popen([sys.executable, '-c', {child!r}]); "
        "time.sleep(30)"
    )
    return [sys.executable, "-c", parent]


def test_pause_covers_descendants_and_timeout_stops_them(tmp_path):
    ticks = tmp_path / "ticks"
    observations = []

    def snapshot():
        before = ticks.read_text() if ticks.exists() else ""
        time.sleep(0.04)
        after = ticks.read_text() if ticks.exists() else ""
        assert before == after
        observations.append(before)

    rc = checkpoint.run_checkpointed(
        ticking_command(ticks), env=os.environ, checkpoint=snapshot,
        interval=0.15, timeout=0.5,
    )
    assert rc == 124
    assert len(observations) >= 2
    assert observations[-1]
    final = ticks.read_text()
    time.sleep(0.04)
    assert ticks.read_text() == final


@pytest.mark.parametrize("returncode", [0, 7])
def test_build_exit_code_is_preserved_and_final_checkpoint_runs(returncode):
    saved = []
    assert checkpoint.run_checkpointed(
        [sys.executable, "-c", f"raise SystemExit({returncode})"],
        env=os.environ, checkpoint=lambda: saved.append(True),
    ) == returncode
    assert saved == [True]


def test_failed_checkpoint_still_stops_the_build(tmp_path):
    ticks = tmp_path / "ticks"

    def fail():
        raise OSError("injected storage failure")

    with pytest.raises(OSError, match="injected storage failure"):
        checkpoint.run_checkpointed(
            ticking_command(ticks), env=os.environ, checkpoint=fail,
            interval=0.15, timeout=2,
        )
    final = ticks.read_text()
    time.sleep(0.04)
    assert ticks.read_text() == final


def test_interrupted_archive_keeps_previous_checkpoint(tmp_path, monkeypatch):
    work, persist = tmp_path / "work", tmp_path / "persist"
    work.mkdir()
    persist.mkdir()
    (work / "build-output").write_text("new")
    archive = persist / "cache.tar.zst"
    archive.write_text("previous complete checkpoint")
    committed = []

    def failed_tar(*args, **kwargs):
        (persist / "cache.tar.zst.partial").write_text("incomplete")
        raise subprocess.CalledProcessError(1, args[0])

    monkeypatch.setattr(checkpoint.subprocess, "run", failed_tar)
    with pytest.raises(subprocess.CalledProcessError):
        checkpoint.save_checkpoint(work, persist, "abc", lambda: committed.append(True))
    assert archive.read_text() == "previous complete checkpoint"
    assert committed == []


def test_checkpoint_saves_evidence_and_commits_after_archive(tmp_path, monkeypatch):
    work, persist = tmp_path / "work", tmp_path / "persist"
    work.mkdir()
    persist.mkdir()
    for name in ("source", "evidence/run1", "elan"):
        (work / name).mkdir(parents=True)
    (work / "qrh-build.lock").touch()
    (work / "evidence/run1/timings.txt").write_text("stage exit_code=0\n")

    def tar(command, **kwargs):
        assert command[command.index(str(work)) + 1:] == ["elan"]
        (persist / "cache.tar.zst.partial").write_text("complete archive")

    def commit():
        assert (persist / "cache.tar.zst").read_text() == "complete archive"
        assert (persist / "evidence/abc-run1/timings.txt").read_text() == "stage exit_code=0\n"

    monkeypatch.setattr(checkpoint.subprocess, "run", tar)
    checkpoint.save_checkpoint(work, persist, "abc", commit)


def test_nested_timeout_keeps_the_checkpoint_process_group():
    script = (ROOT / "lean/qrh/scripts/namespace-build.sh").read_text()
    commands = [line for line in script.splitlines() if "timeout --" in line]
    assert commands and all("timeout --foreground " in line for line in commands)
