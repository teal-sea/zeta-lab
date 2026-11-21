#!/usr/bin/env python3
"""Keep a runner alive when the modules it elaborates outgrow its memory.

High in the import graph a single `lean` process holds several gigabytes, and
four side by side exhaust a 15 GB runner. The kernel does not kill one of
them cleanly; the whole runner stops answering and the shard's work is lost
with it (rounds 9 and 10 of the replay lost one and then four runners that
way). This watchdog samples /proc/meminfo, and when available memory stays
under a floor it kills the largest process with a given name. Lake then
reports that module as failed with a signal exit code, the driver records it
as crashed, and the chain retries it with fewer modules compiling at once.

It also writes a line every `--log-every` seconds, so the evidence shows how
much memory a round needed whether or not anything was killed.

  mem_watchdog.py --name lean --floor-mb 700 --log mem.log
"""
from __future__ import annotations

import argparse
import os
import signal
import time


def meminfo() -> dict[str, int]:
    out = {}
    with open("/proc/meminfo") as fh:
        for line in fh:
            k, v = line.split(":", 1)
            out[k] = int(v.split()[0]) // 1024  # MB
    return out


def procs(name: str) -> list[tuple[int, int, int]]:
    """(anonymous_mb, pid, file_backed_mb) of every process named `name`, largest first.

    Anonymous memory is what a process cannot give back: its heap. File-backed
    memory is mostly mapped `.olean` files, which the kernel can drop and read
    again. The first is what fills a runner, so it is what the processes are
    ranked by.
    """
    out = []
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            with open(f"/proc/{pid}/comm") as fh:
                if fh.read().strip() != name:
                    continue
            anon = filemb = 0
            with open(f"/proc/{pid}/status") as fh:
                for line in fh:
                    if line.startswith("RssAnon:"):
                        anon = int(line.split()[1]) // 1024
                    elif line.startswith("RssFile:"):
                        filemb = int(line.split()[1]) // 1024
        except (OSError, ValueError, IndexError):
            continue
        out.append((anon, int(pid), filemb))
    return sorted(out, reverse=True)


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--name", default="lean")
    p.add_argument("--floor-mb", type=int, default=700)
    p.add_argument("--log", required=True)
    p.add_argument("--log-every", type=float, default=30.0)
    p.add_argument("--interval", type=float, default=2.0)
    p.add_argument("--max-seconds", type=float, default=6 * 3600)
    a = p.parse_args()
    start = time.time()
    last_log = 0.0
    low = 0
    kills = 0
    peak_used = 0
    peak_anon = 0
    with open(a.log, "a", buffering=1) as log:
        log.write(f"watchdog: kill the largest '{a.name}' when MemAvailable < {a.floor_mb} MB twice running\n")
        while time.time() - start < a.max_seconds:
            m = meminfo()
            avail = m.get("MemAvailable", 0)
            used = m.get("MemTotal", 0) - avail
            peak_used = max(peak_used, used)
            now = time.time()
            if now - last_log >= a.log_every:
                ps = procs(a.name)
                peak_anon = max([peak_anon] + [a for a, _, _ in ps])
                log.write(f"t={int(now - start)}s avail={avail}MB used={used}MB peak_used={peak_used}MB "
                          f"swap_free={m.get('SwapFree', 0)}MB n={len(ps)} anon_mb={[a for a, _, _ in ps[:6]]} "
                          f"file_mb={[f for _, _, f in ps[:6]]} peak_anon_one={peak_anon}MB kills={kills}\n")
                last_log = now
            low = low + 1 if avail < a.floor_mb else 0
            if low >= 2:
                ps = procs(a.name)
                if ps:
                    anon, pid, filemb = ps[0]
                    try:
                        os.kill(pid, signal.SIGKILL)
                        kills += 1
                        log.write(f"t={int(now - start)}s KILL pid={pid} anon={anon}MB file={filemb}MB avail={avail}MB "
                                  f"others_anon_mb={[a for a, _, _ in ps[1:6]]} kills={kills}\n")
                    except OSError as e:
                        log.write(f"kill failed: {e}\n")
                    time.sleep(5)
                low = 0
            time.sleep(a.interval)


if __name__ == "__main__":
    main()
