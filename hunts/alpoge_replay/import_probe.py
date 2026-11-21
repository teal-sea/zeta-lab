#!/usr/bin/env python3
"""Time a command on import-only Lean files, with the machine's disk counters around it.

  import_probe.py --probes <dir> --out <dir> --build-dir <dir> [--plan "..."] -- <command with {file}>

A module near the top of the archive imports most of it: `Main` imports all
175,187 modules. Before such a module elaborates a line, `lean` maps the
`.olean` file of every module under it, and by round 17 that was what a
compile cost: about 10 s for a module on 10,000 others, two to three minutes
for one on 40,000, on a runner with 16 GB. Nothing built so far imports more
than 50,000, so the price of the last modules was unknown. This measures it
on what is built: `replay_shard.py probe` writes files that hold nothing but
imports, and this runs the given command on them (stdlib only).

The plan is a list of steps, in order:
  <n>:cold   run probe n (as listed in probes.json; -1 is the last, which
             imports everything built) after dropping the page cache
  <n>:warm   run it with the cache as the previous step left it
  ra=<kb>    set the read-ahead of the filesystem under --build-dir (the size
             of the window the kernel reads around a page fault in a mapped
             file); ra=restore puts back what was there

One row per run goes to <out>/import-probe.tsv: wall, user and system seconds,
the command's peak resident memory and major faults, the system's major
faults, and reads, megabytes and busy milliseconds per block device. The
command's output goes to <out>/import-probe-<step>.out. A run over
--timeout-s is killed and recorded with rc 124; once --budget-s is spent the
remaining runs are recorded as skipped. This measures time. It checks no proof.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import signal
import subprocess
import sys
import time

COLUMNS = ["step", "probe", "closure", "sinks", "cache", "ra_kb", "rc", "wall_s", "user_s", "sys_s",
           "maxrss_mb", "majflt", "sys_majfault", "cached_before_mb", "cached_after_mb", "disk"]


def diskstats(path: str = "/proc/diskstats") -> dict[str, tuple[int, int, int]]:
    """device -> (reads completed, sectors read, milliseconds spent reading)."""
    out = {}
    try:
        with open(path) as fh:
            for line in fh:
                f = line.split()
                if len(f) >= 7:
                    out[f[2]] = (int(f[3]), int(f[5]), int(f[6]))
    except (OSError, ValueError):
        pass
    return out


def disk_delta(before, after, top: int = 4) -> str:
    """`dev:reads:MB:ms` for the devices that read most, a sector being 512 bytes."""
    rows = []
    for dev, (r, s, ms) in after.items():
        r0, s0, ms0 = before.get(dev, (0, 0, 0))
        if s - s0 > 0:
            rows.append((s - s0, f"{dev}:{r - r0}:{(s - s0) * 512 // 2**20}:{ms - ms0}"))
    return ";".join(t for _, t in sorted(rows, reverse=True)[:top]) or "-"


def counter(path: str, key: str, sep: str = " ") -> int:
    """One number from /proc/vmstat (`key value`) or /proc/meminfo (`key: value kB`)."""
    try:
        with open(path) as fh:
            for line in fh:
                k, _, v = line.partition(sep)
                if k == key:
                    return int(v.split()[0])
    except (OSError, ValueError, IndexError):
        pass
    return -1


def bdi_files(build_dir: str, mounts: str = "/proc/mounts", sys_bdi: str = "/sys/class/bdi") -> list[str]:
    """The read_ahead_kb files of the filesystem holding build_dir.

    btrfs keeps a device of its own for this, named btrfs-<n>; any other
    filesystem uses the block device it is mounted from.
    """
    real = os.path.realpath(build_dir)
    best = ("", "", "")
    with open(mounts) as fh:
        for line in fh:
            f = line.split()
            if len(f) >= 3 and (real == f[1] or real.startswith(f[1].rstrip("/") + "/")) and len(f[1]) >= len(best[1]):
                best = (f[0], f[1], f[2])
    if best[2] == "btrfs":
        return sorted(glob.glob(os.path.join(sys_bdi, "btrfs-*", "read_ahead_kb")))
    try:
        st = os.stat(real)
        one = os.path.join(sys_bdi, f"{os.major(st.st_dev)}:{os.minor(st.st_dev)}", "read_ahead_kb")
    except OSError:
        return []
    return [one] if os.path.exists(one) else []


def write_root(path: str, text: str, sudo: list[str]) -> bool:
    """Write a kernel setting, through sudo where the runner needs it."""
    return subprocess.run([*sudo, "sh", "-c", 'printf "%s\\n" "$1" > "$2"', "sh", text, path]).returncode == 0


def run(cmd: list[str], out_path: str, timeout_s: float) -> dict:
    """Run cmd to its end or to the time limit; its own counters come from wait4."""
    start = time.time()
    with open(out_path, "wb") as fh:
        p = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
        killed = False
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if not killed and time.time() - start > timeout_s:
                try:
                    os.killpg(p.pid, signal.SIGKILL)  # lake and the lean under it
                except ProcessLookupError:
                    pass
                killed = True
            time.sleep(0.2)
        p.returncode = os.waitstatus_to_exitcode(status)
    rc = 124 if killed else p.returncode
    return {"rc": rc, "wall_s": round(time.time() - start, 1), "user_s": round(ru.ru_utime, 1),
            "sys_s": round(ru.ru_stime, 1), "maxrss_mb": ru.ru_maxrss // 1024, "majflt": ru.ru_majflt}


def main() -> int:
    argv = sys.argv[1:]
    cmd = []
    if "--" in argv:
        cmd = argv[argv.index("--") + 1:]
        argv = argv[:argv.index("--")]
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--probes", required=True, help="directory written by replay_shard.py probe")
    p.add_argument("--out", required=True)
    p.add_argument("--build-dir", required=True, help="where the .olean files are; its filesystem's read-ahead is the one set")
    p.add_argument("--plan", default="-1:cold -1:warm 0:cold 1:cold ra=128 0:cold -1:cold ra=restore")
    p.add_argument("--timeout-s", type=float, default=2400)
    p.add_argument("--budget-s", type=float, default=6600)
    p.add_argument("--sudo", default="sudo", help="prefix for writes to kernel settings; empty for none")
    p.add_argument("--drop-caches", default="/proc/sys/vm/drop_caches")
    p.add_argument("--bdi-root", default="/sys/class/bdi")
    p.add_argument("--diskstats", default="/proc/diskstats")
    a = p.parse_args(argv)
    if not any("{file}" in c for c in cmd):
        print("the command after -- must contain {file}", file=sys.stderr)
        return 2
    sudo = a.sudo.split()
    probes = json.load(open(os.path.join(a.probes, "probes.json")))
    os.makedirs(a.out, exist_ok=True)
    files = bdi_files(a.build_dir, sys_bdi=a.bdi_root)
    saved = {f: open(f).read().strip() for f in files}
    ra = ",".join(sorted(set(saved.values()))) or "?"
    print(f"read-ahead files: {saved or 'none found'}", flush=True)
    began = time.time()
    with open(os.path.join(a.out, "import-probe.tsv"), "w", encoding="utf-8") as tsv:
        tsv.write("\t".join(COLUMNS) + "\n")
        for n, step in enumerate(a.plan.split()):
            if step.startswith("ra="):
                want = step[3:]
                for f in files:
                    write_root(f, saved[f] if want == "restore" else want, sudo)
                now = {f: open(f).read().strip() for f in files}
                ra = ",".join(sorted(set(now.values()))) or "?"
                print(f"step {n} {step}: read-ahead now {now or 'unchanged, no file found'}", flush=True)
                continue
            idx, _, cache = step.partition(":")
            pr = probes[int(idx)]
            row = {"step": n, "probe": pr["file"], "closure": pr["closure"], "sinks": pr["sinks"], "cache": cache, "ra_kb": ra}
            if time.time() - began > a.budget_s:
                row.update(rc="skipped")
            else:
                if cache == "cold":
                    subprocess.run(["sync"])
                    write_root(a.drop_caches, "3", sudo)
                d0, f0 = diskstats(a.diskstats), counter("/proc/vmstat", "pgmajfault")
                row["cached_before_mb"] = counter("/proc/meminfo", "Cached", ":") // 1024
                target = os.path.join(a.probes, pr["file"])
                row.update(run([c.replace("{file}", target) for c in cmd],
                               os.path.join(a.out, f"import-probe-{n}.out"), a.timeout_s))
                row["sys_majfault"] = counter("/proc/vmstat", "pgmajfault") - f0
                row["cached_after_mb"] = counter("/proc/meminfo", "Cached", ":") // 1024
                row["disk"] = disk_delta(d0, diskstats(a.diskstats))
            tsv.write("\t".join(str(row.get(c, "")) for c in COLUMNS) + "\n")
            tsv.flush()
            print(" ".join(f"{c}={row.get(c, '')}" for c in COLUMNS), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
