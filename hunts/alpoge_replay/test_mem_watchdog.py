"""mem_watchdog.py: the policy on paper, then the same policy on live processes.

A guard that cannot fire is worse than none, and one that suspends processes
and forgets them is worse still. The pure tests pin the decision for each
kind of sample; the slow test runs the watchdog against real processes named
`lean` and a scripted memory reading, and checks every step it takes.
"""
from __future__ import annotations

import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import mem_watchdog as w  # noqa: E402

K = dict(soft=2500, floor=700, resume=5000)
BIG, MID, SMALL = (9000, 11, 100), (4000, 22, 100), (300, 33, 100)   # (anon MB, pid, file MB)


def test_nothing_is_done_while_memory_is_fine():
    assert w.decide(8000, [BIG, MID], set(), low_soft=0, low_hard=0, high=5, **K) == []


def test_under_the_soft_floor_everything_but_the_largest_is_suspended():
    got = w.decide(2000, [BIG, MID, SMALL], set(), low_soft=2, low_hard=0, high=0, **K)
    assert got == [("stop", 22), ("stop", 33)]


def test_one_low_sample_is_not_enough():
    assert w.decide(2000, [BIG, MID], set(), low_soft=1, low_hard=0, high=0, **K) == []


def test_a_process_alone_under_the_soft_floor_is_left_alone():
    assert w.decide(2000, [BIG], set(), low_soft=2, low_hard=0, high=0, **K) == []


def test_under_the_hard_floor_a_suspended_process_goes_first_and_the_largest_of_them():
    got = w.decide(300, [BIG, MID, SMALL], {22, 33}, low_soft=2, low_hard=2, high=0, **K)
    assert got == [("kill_crowded", 22)]


def test_under_the_hard_floor_with_nothing_suspended_the_smallest_goes_not_the_largest():
    got = w.decide(300, [BIG, MID, SMALL], set(), low_soft=2, low_hard=2, high=0, **K)
    assert got == [("kill_crowded", 33)]


def test_only_a_process_that_is_alone_is_killed_as_alone():
    assert w.decide(300, [BIG], set(), low_soft=2, low_hard=2, high=0, **K) == [("kill_alone", 11)]


def test_when_nothing_runs_the_largest_suspended_process_is_resumed_whatever_memory_says():
    got = w.decide(900, [MID, SMALL], {22, 33}, low_soft=2, low_hard=0, high=0, **K)
    assert got == [("cont", 22)]


def test_with_room_again_the_smallest_suspended_process_is_resumed():
    got = w.decide(6000, [BIG, MID, SMALL], {22, 33}, low_soft=0, low_hard=0, high=2, **K)
    assert got == [("cont", 33)]


def test_between_the_soft_floor_and_the_resume_line_a_suspended_process_waits():
    assert w.decide(3500, [BIG, MID], {22}, low_soft=0, low_hard=0, high=0, **K) == []


def test_a_compile_is_named_by_its_source_path_and_a_replay_driver_by_its_list(tmp_path):
    root = tmp_path / "src"

    # a live process whose command line carries these arguments after its own
    def name_for(argv: list[str]) -> str:
        proc = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)", *argv])
        try:
            time.sleep(0.3)
            return w.module_of(proc.pid, str(root))
        finally:
            proc.kill()
            proc.wait()

    assert name_for([f"{root}/././Development/Foo/Bar.lean", "-o", "x.olean"]) == "Development.Foo.Bar"
    assert name_for(["./Main.lean"]) == "Main"
    assert name_for(["--run", "/somewhere/ReplayDriver.lean", "/tmp/out/list-3.txt"]) == "run:list-3.txt"
    assert name_for(["--version"]) == "?"


def _state(pid: int) -> str:
    with open(f"/proc/{pid}/stat") as fh:
        return fh.read().rsplit(")", 1)[1].split()[0]


def _wait_for(cond, seconds: float = 6.0) -> bool:
    end = time.time() + seconds
    while time.time() < end:
        if cond():
            return True
        time.sleep(0.05)
    return False


@pytest.mark.slow
def test_on_live_processes_suspend_resume_kill_crowded_then_alone(tmp_path):
    fake = tmp_path / "lean"
    shutil.copy("/bin/sleep", fake)
    mem = tmp_path / "meminfo"

    def reading(avail_mb: int) -> None:
        tmp = tmp_path / "meminfo.tmp"
        tmp.write_text(f"MemTotal: {16000 * 1024} kB\nMemAvailable: {avail_mb * 1024} kB\nSwapFree: 0 kB\n")
        os.replace(tmp, mem)

    reading(10000)
    a = subprocess.Popen([str(fake), "120"])
    b = subprocess.Popen([str(fake), "121"])
    log = tmp_path / "mem.log"
    dog = subprocess.Popen([sys.executable, str(HERE / "mem_watchdog.py"), "--name", "lean", "--log", str(log),
                            "--meminfo", str(mem), "--interval", "0.1", "--log-every", "0.5",
                            "--soft-mb", "2500", "--floor-mb", "700", "--resume-mb", "5000"])
    try:
        time.sleep(1.0)
        assert _state(a.pid) != "T" and _state(b.pid) != "T"          # plenty of memory: hands off

        reading(2000)                                                  # under the soft floor
        assert _wait_for(lambda: [_state(a.pid), _state(b.pid)].count("T") == 1)
        halted, running = (a, b) if _state(a.pid) == "T" else (b, a)

        reading(3500)                                                  # between soft and resume: it waits
        time.sleep(0.8)
        assert _state(halted.pid) == "T"

        reading(6000)                                                  # room again: resumed
        assert _wait_for(lambda: _state(halted.pid) != "T")

        reading(2000)                                                  # suspended again
        assert _wait_for(lambda: [_state(a.pid), _state(b.pid)].count("T") == 1)
        halted, running = (a, b) if _state(a.pid) == "T" else (b, a)

        reading(300)                                                   # hard floor: the suspended one goes
        assert _wait_for(lambda: halted.poll() is not None)
        assert halted.returncode == -signal.SIGKILL
        assert _wait_for(lambda: running.poll() is not None, 12.0)     # still full: the last one, alone
        assert running.returncode == -signal.SIGKILL
    finally:
        dog.send_signal(signal.SIGTERM)
        dog.wait(timeout=20)
        for p in (a, b):
            if p.poll() is None:
                p.kill()
            p.wait()
    text = log.read_text()
    assert " STOP " in text and " CONT " in text
    assert text.index("KILL crowded") < text.index("KILL alone")
    kills = [line.split("\t") for line in (tmp_path / "mem.log.kills.tsv").read_text().splitlines()]
    assert [k[1] for k in kills] == ["crowded", "alone"]
    assert [k[3] for k in kills] == ["2", "1"]
    ends = sorted(line.split("\t")[5] for line in (tmp_path / "mem.log.modules.tsv").read_text().splitlines())
    assert ends == ["killed_alone", "killed_crowded"]


@pytest.mark.slow
def test_a_watchdog_that_is_stopped_resumes_what_it_suspended(tmp_path):
    fake = tmp_path / "lean"
    shutil.copy("/bin/sleep", fake)
    mem = tmp_path / "meminfo"
    mem.write_text(f"MemTotal: {16000 * 1024} kB\nMemAvailable: {2000 * 1024} kB\n")
    a = subprocess.Popen([str(fake), "120"])
    b = subprocess.Popen([str(fake), "121"])
    log = tmp_path / "mem.log"
    dog = subprocess.Popen([sys.executable, str(HERE / "mem_watchdog.py"), "--name", "lean", "--log", str(log),
                            "--meminfo", str(mem), "--interval", "0.1"])
    try:
        assert _wait_for(lambda: [_state(a.pid), _state(b.pid)].count("T") == 1)
        dog.send_signal(signal.SIGTERM)
        dog.wait(timeout=20)
        assert _wait_for(lambda: "T" not in (_state(a.pid), _state(b.pid)))
        assert a.poll() is None and b.poll() is None
    finally:
        if dog.poll() is None:
            dog.kill()
        for p in (a, b):
            p.kill()
            p.wait()
    assert "watchdog: end" in log.read_text()
    ends = sorted(line.split("\t")[5] for line in (tmp_path / "mem.log.modules.tsv").read_text().splitlines())
    assert ends == ["watchdog_exit", "watchdog_exit"]


@pytest.mark.slow
def test_a_suspended_process_is_released_on_the_timer(tmp_path):
    fake = tmp_path / "lean"
    shutil.copy("/bin/sleep", fake)
    mem = tmp_path / "meminfo"
    mem.write_text(f"MemTotal: {16000 * 1024} kB\nMemAvailable: {2000 * 1024} kB\n")
    a = subprocess.Popen([str(fake), "120"])
    b = subprocess.Popen([str(fake), "121"])
    log = tmp_path / "mem.log"
    dog = subprocess.Popen([sys.executable, str(HERE / "mem_watchdog.py"), "--name", "lean", "--log", str(log),
                            "--meminfo", str(mem), "--interval", "0.1", "--max-halt-s", "1"])
    try:
        assert _wait_for(lambda: "released on the timer" in (log.read_text() if log.exists() else ""), 10.0)
    finally:
        dog.send_signal(signal.SIGTERM)
        dog.wait(timeout=20)
        for p in (a, b):
            p.kill()
            p.wait()


@pytest.mark.slow
def test_with_swap_to_fall_back_on_nothing_is_killed_while_swap_has_room(tmp_path):
    fake = tmp_path / "lean"
    shutil.copy("/bin/sleep", fake)
    mem = tmp_path / "meminfo"

    def reading(avail_mb: int, swap_free_mb: int) -> None:
        tmp = tmp_path / "meminfo.tmp"
        tmp.write_text(f"MemTotal: {16000 * 1024} kB\nMemAvailable: {avail_mb * 1024} kB\n"
                       f"SwapFree: {swap_free_mb * 1024} kB\n")
        os.replace(tmp, mem)

    reading(300, 20000)                      # under the hard floor, but 20 GB of swap free
    a = subprocess.Popen([str(fake), "120"])
    b = subprocess.Popen([str(fake), "121"])
    log = tmp_path / "mem.log"
    dog = subprocess.Popen([sys.executable, str(HERE / "mem_watchdog.py"), "--name", "lean", "--log", str(log),
                            "--meminfo", str(mem), "--interval", "0.1", "--swap-floor-mb", "1024"])
    try:
        # the smaller one is suspended (the soft floor does not look at swap), and nobody dies
        assert _wait_for(lambda: [_state(a.pid), _state(b.pid)].count("T") == 1)
        time.sleep(1.5)
        assert a.poll() is None and b.poll() is None
        reading(300, 500)                    # swap nearly gone too: now the suspended one goes, then the last
        assert _wait_for(lambda: a.poll() is not None and b.poll() is not None, 15.0)
    finally:
        dog.send_signal(signal.SIGTERM)
        dog.wait(timeout=20)
        for p in (a, b):
            if p.poll() is None:
                p.kill()
            p.wait()
    kills = [line.split("\t")[1] for line in (tmp_path / "mem.log.kills.tsv").read_text().splitlines()]
    assert kills == ["crowded", "alone"]
    assert "only with free swap under 1024 MB" in log.read_text()

