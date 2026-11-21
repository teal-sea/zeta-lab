"""import_probe.py: the timing harness for import-only files.

The command it times is `lean` on a hosted runner; here it is a stand-in, and
the kernel files it writes to (drop_caches, read_ahead_kb) are files in a
temporary directory. What is pinned: the row per run, the cold run really
asking for the cache to be dropped, the read-ahead set and put back, a run
over its time limit killed with everything under it, and the budget.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import import_probe as ip  # noqa: E402

SCRIPT = HERE / "import_probe.py"


def _probes(tmp_path: Path) -> Path:
    d = tmp_path / "probe"
    d.mkdir()
    (d / "probe-0.lean").write_text("import A\n")
    (d / "probe-1.lean").write_text("import A\nimport B\n")
    (d / "probes.json").write_text(json.dumps([
        {"file": "probe-0.lean", "sinks": 1, "closure": 10},
        {"file": "probe-1.lean", "sinks": 2, "closure": 25}]))
    return d


def _queue(tmp_path: Path, build: Path, value: str = "128", partition: bool = False) -> Path:
    """A stand-in /sys/dev/block with the read-ahead file of the device `build` is on:
    the device's own queue, or, for a partition, the queue of the disk above it."""
    st = os.stat(build)
    dev = tmp_path / "devblock" / ("disk/" if partition else "") / f"{os.major(st.st_dev)}:{os.minor(st.st_dev)}"
    dev.mkdir(parents=True)
    if partition:   # /sys/dev/block/8:1 is a link into the disk's directory
        (tmp_path / "devblock" / dev.name).symlink_to(dev)
    f = (dev.parent if partition else dev) / "queue" / "read_ahead_kb"
    f.parent.mkdir(parents=True)
    f.write_text(value + "\n")
    return f


def _run(tmp_path: Path, plan: str, cmd: list[str], *extra: str):
    build = tmp_path / "build"
    build.mkdir(exist_ok=True)
    out = tmp_path / "out"
    drop = tmp_path / "drop_caches"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--probes", str(tmp_path / "probe"), "--out", str(out),
         "--build-dir", str(build), "--plan", plan, "--sudo", "", "--drop-caches", str(drop),
         "--bdi-root", str(tmp_path / "bdi"), "--sys-dev-block", str(tmp_path / "devblock"),
         "--fault-around", str(tmp_path / "fault_around_bytes"), *extra, "--", *cmd],
        capture_output=True, text=True, timeout=120)
    rows = []
    tsv = out / "import-probe.tsv"
    if tsv.exists():
        lines = tsv.read_text().splitlines()
        rows = [dict(zip(lines[0].split("\t"), ln.split("\t"))) for ln in lines[1:]]
    return proc, rows, out, drop


def test_disk_counters_are_read_and_differenced(tmp_path):
    f = tmp_path / "diskstats"
    f.write_text("   8       0 sda 100 5 2048 40 7 0 0 0 0 0 0\n   7       3 loop3 10 0 4096 9 0 0 0 0 0 0 0\n")
    before = ip.diskstats(str(f))
    assert before == {"sda": (100, 2048, 40), "loop3": (10, 4096, 9)}
    f.write_text("   8       0 sda 300 5 6144 90 7 0 0 0 0 0 0\n   7       3 loop3 10 0 4096 9 0 0 0 0 0 0 0\n"
                 "   7       4 loop4 50 0 409600 20 0 0 0 0 0 0 0\n")
    # loop4 read 200 MB, sda 2 MB, loop3 nothing: most first, idle devices left out
    assert ip.disk_delta(before, ip.diskstats(str(f))) == "loop4:50:200:20;sda:200:2:50"
    assert ip.disk_delta(before, before) == "-"


def test_the_read_ahead_file_is_found_for_btrfs_a_device_and_a_partition(tmp_path):
    build = tmp_path / "vol" / "build"
    build.mkdir(parents=True)
    bdi = tmp_path / "bdi"
    (bdi / "btrfs-2").mkdir(parents=True)
    (bdi / "btrfs-2" / "read_ahead_kb").write_text("4096\n")
    mounts = tmp_path / "mounts"
    mounts.write_text(f"/dev/root / ext4 rw 0 0\n/dev/loop5 {tmp_path / 'vol'} btrfs rw,compress-force=zstd:3 0 0\n")
    assert ip.ra_files(str(build), str(mounts), str(bdi), str(tmp_path / "none")) == [str(bdi / "btrfs-2" / "read_ahead_kb")]
    # the same directory on a filesystem that is not btrfs: the queue of the device it is on
    mounts.write_text("/dev/root / ext4 rw 0 0\n")
    assert ip.ra_files(str(build), str(mounts), str(bdi), str(tmp_path / "none")) == []
    (tmp_path / "a").mkdir()
    own = _queue(tmp_path / "a", build)
    assert ip.ra_files(str(build), str(mounts), str(bdi), str(tmp_path / "a" / "devblock")) == [str(own)]
    # a partition has no queue of its own: the disk's is the one
    (tmp_path / "b").mkdir()
    disk = _queue(tmp_path / "b", build, partition=True)
    found = ip.ra_files(str(build), str(mounts), str(bdi), str(tmp_path / "b" / "devblock"))
    assert len(found) == 1 and os.path.samefile(found[0], disk)


def test_one_row_per_run_and_the_settings_are_set_and_put_back(tmp_path):
    _probes(tmp_path)
    (tmp_path / "build").mkdir()
    ra = _queue(tmp_path, tmp_path / "build", "128")
    fa = tmp_path / "fault_around_bytes"
    fa.write_text("65536\n")
    proc, rows, out, drop = _run(tmp_path, "-1:cold 0:warm ra=16 fa=4096 0:cold ra=restore fa=restore 0:warm",
                                 ["cat", "{file}"])
    assert proc.returncode == 0, proc.stderr
    assert [(r["probe"], r["closure"], r["cache"], r["ra_kb"], r["fa_bytes"], r["rc"]) for r in rows] == [
        ("probe-1.lean", "25", "cold", "128", "65536", "0"),
        ("probe-0.lean", "10", "warm", "128", "65536", "0"),
        ("probe-0.lean", "10", "cold", "16", "4096", "0"),
        ("probe-0.lean", "10", "warm", "128", "65536", "0")]
    assert (out / "import-probe-0.out").read_text() == "import A\nimport B\n"   # the command saw the last probe
    assert drop.read_text().strip() == "3"                                      # a cold run asks for the cache to go
    assert ra.read_text().strip() == "128" and fa.read_text().strip() == "65536"   # and both settings are put back
    assert all(float(r["wall_s"]) >= 0 and int(r["maxrss_mb"]) >= 0 for r in rows)


def test_a_warm_run_does_not_drop_the_cache(tmp_path):
    _probes(tmp_path)
    proc, rows, _, drop = _run(tmp_path, "0:warm", ["cat", "{file}"])
    assert proc.returncode == 0, proc.stderr
    assert len(rows) == 1 and rows[0]["ra_kb"] == "?" and rows[0]["fa_bytes"] == "?"   # no setting was found, and the row says so
    assert not drop.exists()


def test_a_run_over_its_limit_is_killed_with_what_it_started(tmp_path):
    """The planted fault: a command that never returns, with a child of its own."""
    _probes(tmp_path)
    pidfile = tmp_path / "child.pid"
    start = time.time()
    proc, rows, _, _ = _run(tmp_path, "0:warm 1:warm",
                            ["sh", "-c", f"sleep 300 & echo $! > {pidfile}; wait", "{file}"], "--timeout-s", "1")
    assert proc.returncode == 0, proc.stderr
    assert time.time() - start < 60
    assert [r["rc"] for r in rows] == ["124", "124"]
    time.sleep(0.5)
    child = int(pidfile.read_text())
    try:   # a killed process nobody has reaped yet still has an entry, in state Z
        alive = Path(f"/proc/{child}/stat").read_text().rsplit(")", 1)[1].split()[0] != "Z"
    except OSError:
        alive = False
    assert not alive, "the process under the timed command outlived it"


def test_a_failing_command_is_recorded_not_raised(tmp_path):
    _probes(tmp_path)
    proc, rows, out, _ = _run(tmp_path, "0:warm", ["sh", "-c", "echo boom; exit 3", "{file}"])
    assert proc.returncode == 0
    assert rows[0]["rc"] == "3" and (out / "import-probe-0.out").read_text() == "boom\n"


def test_runs_after_the_budget_is_spent_are_recorded_as_skipped(tmp_path):
    _probes(tmp_path)
    proc, rows, _, drop = _run(tmp_path, "0:cold 1:cold", ["cat", "{file}"], "--budget-s", "-1")
    assert proc.returncode == 0, proc.stderr
    assert [r["rc"] for r in rows] == ["skipped", "skipped"]
    assert not drop.exists()


def test_a_command_that_names_no_file_is_refused(tmp_path):
    _probes(tmp_path)
    proc, rows, _, _ = _run(tmp_path, "0:warm", ["true"])
    assert proc.returncode == 2 and rows == []
