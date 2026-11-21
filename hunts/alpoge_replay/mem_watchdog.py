#!/usr/bin/env python3
"""Keep a runner alive when the modules it elaborates outgrow its memory.

High in the import graph a single `lean` process holds several gigabytes, and
four side by side exhaust a 15 GB runner. The kernel does not kill one of
them cleanly; the whole runner stops answering and the shard's work is lost
with it (rounds 9, 10 and 11 of the build lost one, four and one runners that
way). This watchdog samples /proc/meminfo and acts in two steps.

  soft floor  Available memory under `--soft-mb`: every process named
              `--name` except the largest is suspended (SIGSTOP). They keep
              what they hold and stop growing, so the largest, which is the
              hardest to fit and usually the furthest along, gets the room.
              They are resumed when memory is back above `--resume-mb`, or
              when nothing else is running.
  hard floor  Available memory under `--floor-mb`: a suspended process is
              killed, the largest first. That is a "crowded" kill and says
              nothing against its module. Only when the last process left is
              alone and the runner is still full is that one killed: an
              "alone" kill, which says its module does not fit this runner.

Version one killed the largest process at the hard floor. That is the wrong
victim: it throws away the most work, and the module that needed the room
needs it again next time.

Beside the log it writes two tables:

  <log>.modules.tsv  one line per process when it ends: module, peak
                     anonymous MB, peak file-backed MB, seconds seen, seconds
                     suspended, how it ended
  <log>.kills.tsv    one line per kill: module, crowded|alone, anonymous MB,
                     how many processes were alive

  mem_watchdog.py --name lean --log mem.log --root /home/runner/replay/lean
"""
from __future__ import annotations

import argparse
import os
import signal
import time


def meminfo(path: str = "/proc/meminfo") -> dict[str, int]:
    out = {}
    with open(path) as fh:
        for line in fh:
            if ":" not in line:
                continue
            k, v = line.split(":", 1)
            try:
                out[k] = int(v.split()[0]) // 1024  # MB
            except (ValueError, IndexError):
                continue
    return out


def vmstat(path: str = "/proc/vmstat") -> dict[str, int]:
    """Counters that show thrashing: major page faults (a mapped page had to be
    read back from disk) and pages swapped in and out."""
    out = {}
    try:
        with open(path) as fh:
            for line in fh:
                k, _, v = line.partition(" ")
                if k in ("pgmajfault", "pswpin", "pswpout"):
                    out[k] = int(v)
    except (OSError, ValueError):
        pass
    return out


def module_of(pid: int, root: str = "") -> str:
    """What a lean process is working on, read from its command line.

    A compile names its source file: that path, relative to `root`, with dots.
    A `lean --run script list` names its last argument, which is how the
    replay tells its driver processes apart.
    """
    try:
        with open(f"/proc/{pid}/cmdline", "rb") as fh:
            args = [a.decode("utf-8", "replace") for a in fh.read().split(b"\0") if a]
    except OSError:
        return "?"
    if "--run" in args and len(args) > args.index("--run") + 2:
        return "run:" + os.path.basename(args[-1])
    for a in args[1:]:
        if a.endswith(".lean"):
            path = os.path.normpath(a)
            base = os.path.normpath(root) if root else ""
            if base and path.startswith(base + os.sep):
                path = path[len(base) + 1:]
            return path[:-5].lstrip("./").replace(os.sep, ".")
    return "?"


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
            dead = False
            with open(f"/proc/{pid}/status") as fh:
                for line in fh:
                    if line.startswith("State:"):
                        # a zombie holds nothing and cannot be signalled
                        dead = line.split()[1] in ("Z", "X")
                    elif line.startswith("RssAnon:"):
                        anon = int(line.split()[1]) // 1024
                    elif line.startswith("RssFile:"):
                        filemb = int(line.split()[1]) // 1024
        except (OSError, ValueError, IndexError):
            continue
        if dead:
            continue
        out.append((anon, int(pid), filemb))
    return sorted(out, reverse=True)


def decide(avail: int, ps: list[tuple[int, int, int]], halted: set[int], *, soft: int, floor: int,
           resume: int, low_soft: int, low_hard: int, high: int) -> list[tuple[str, int]]:
    """The policy, with no side effects: what to do about this sample.

    `ps` is largest first. `low_soft`, `low_hard` and `high` count how many
    samples running memory has been under the soft floor, under the hard
    floor, and above the resume line. Returns actions in order, each
    ("stop" | "cont" | "kill_crowded" | "kill_alone", pid).
    """
    running = [p for p in ps if p[1] not in halted]
    stopped = [p for p in ps if p[1] in halted]
    if low_hard >= 2:
        if stopped:
            return [("kill_crowded", stopped[0][1])]
        if len(running) > 1:
            # under the hard floor before the soft floor could act: the
            # smaller processes go, the largest stays
            return [("kill_crowded", running[-1][1])]
        if running:
            return [("kill_alone", running[0][1])]
        return []
    if low_soft >= 2 and len(running) > 1:
        return [("stop", p[1]) for p in running[1:]]
    if stopped and not running:
        return [("cont", stopped[0][1])]
    if stopped and high >= 2 and avail >= resume:
        return [("cont", stopped[-1][1])]
    return []


class Seen:
    __slots__ = ("module", "first", "last", "peak_anon", "peak_file", "halted_at", "halted_s", "end")

    def __init__(self, module: str, now: float) -> None:
        self.module = module
        self.first = self.last = now
        self.peak_anon = self.peak_file = 0
        self.halted_at: float | None = None
        self.halted_s = 0.0
        self.end = "exit"


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--name", default="lean")
    p.add_argument("--floor-mb", type=int, default=700, help="hard floor: kill")
    p.add_argument("--soft-mb", type=int, default=2500, help="soft floor: suspend all but the largest")
    p.add_argument("--resume-mb", type=int, default=5000, help="resume one suspended process above this")
    p.add_argument("--max-halt-s", type=float, default=1200.0,
                   help="a process suspended this long is resumed whatever memory says")
    p.add_argument("--log", required=True)
    p.add_argument("--root", default="", help="source root, to turn a path into a module name")
    p.add_argument("--meminfo", default="/proc/meminfo", help="for tests")
    p.add_argument("--log-every", type=float, default=30.0)
    p.add_argument("--interval", type=float, default=2.0)
    p.add_argument("--max-seconds", type=float, default=6 * 3600)
    a = p.parse_args()
    soft = max(a.soft_mb, a.floor_mb)
    resume = max(a.resume_mb, soft)
    start = time.time()
    last_log = 0.0
    low_soft = low_hard = high = 0
    kills = stops = 0
    peak_used = peak_anon = 0
    seen: dict[int, Seen] = {}
    halted: set[int] = set()
    stopping = False
    last_vm = vmstat()

    def on_term(signum, frame):  # noqa: ARG001
        nonlocal stopping
        stopping = True

    signal.signal(signal.SIGTERM, on_term)
    signal.signal(signal.SIGINT, on_term)

    def send(pid: int, sig: int) -> bool:
        try:
            os.kill(pid, sig)
            return True
        except OSError:
            return False

    with open(a.log, "a", buffering=1) as log, \
            open(a.log + ".modules.tsv", "a", buffering=1) as mods, \
            open(a.log + ".kills.tsv", "a", buffering=1) as killed:
        log.write(f"watchdog: '{a.name}': suspend all but the largest when MemAvailable < {soft} MB, "
                  f"resume above {resume} MB, kill under {a.floor_mb} MB (suspended first), twice running\n")

        def close(pid: int, now: float) -> None:
            s = seen.pop(pid)
            if s.halted_at is not None:
                s.halted_s += now - s.halted_at
            mods.write(f"{s.module}\t{s.peak_anon}\t{s.peak_file}\t{s.last - s.first:.0f}\t{s.halted_s:.0f}\t{s.end}\n")
            halted.discard(pid)

        try:
            while not stopping and time.time() - start < a.max_seconds:
                now = time.time()
                try:
                    m = meminfo(a.meminfo)
                except OSError:
                    time.sleep(a.interval)
                    continue
                avail = m.get("MemAvailable", 0)
                used = m.get("MemTotal", 0) - avail
                peak_used = max(peak_used, used)
                ps = procs(a.name)
                alive = {pid for _, pid, _ in ps}
                for anon, pid, filemb in ps:
                    s = seen.get(pid)
                    if s is None:
                        s = seen[pid] = Seen(module_of(pid, a.root), now)
                    elif s.module == "?":
                        s.module = module_of(pid, a.root)
                    s.last = now
                    s.peak_anon = max(s.peak_anon, anon)
                    s.peak_file = max(s.peak_file, filemb)
                    peak_anon = max(peak_anon, anon)
                for pid in [pid for pid in seen if pid not in alive]:
                    close(pid, now)
                # a process suspended too long is let go, whatever memory says
                for pid in list(halted):
                    s = seen.get(pid)
                    if s and s.halted_at is not None and now - s.halted_at > a.max_halt_s:
                        if send(pid, signal.SIGCONT):
                            log.write(f"t={int(now - start)}s CONT pid={pid} {s.module} suspended {a.max_halt_s:.0f}s, "
                                      f"released on the timer\n")
                        s.halted_s += now - s.halted_at
                        s.halted_at = None
                        halted.discard(pid)
                if now - last_log >= a.log_every:
                    vm = vmstat()
                    since = {k: vm.get(k, 0) - last_vm.get(k, 0) for k in ("pgmajfault", "pswpin", "pswpout")}
                    last_vm = vm
                    log.write(f"t={int(now - start)}s avail={avail}MB used={used}MB peak_used={peak_used}MB "
                              f"cached={m.get('Cached', 0)}MB swap_free={m.get('SwapFree', 0)}MB "
                              f"majfault={since['pgmajfault']} swapin={since['pswpin']} swapout={since['pswpout']} "
                              f"n={len(ps)} anon_mb={[x for x, _, _ in ps[:6]]} "
                              f"file_mb={[f for _, _, f in ps[:6]]} peak_anon_one={peak_anon}MB "
                              f"suspended={len(halted)} stops={stops} kills={kills} "
                              f"largest={seen[ps[0][1]].module if ps else '-'}\n")
                    last_log = now
                low_soft = low_soft + 1 if avail < soft else 0
                low_hard = low_hard + 1 if avail < a.floor_mb else 0
                high = high + 1 if avail >= resume else 0
                acted_hard = False
                for what, pid in decide(avail, ps, halted, soft=soft, floor=a.floor_mb, resume=resume,
                                        low_soft=low_soft, low_hard=low_hard, high=high):
                    s = seen[pid]
                    anon = next((x for x, q, _ in ps if q == pid), 0)
                    if what == "stop":
                        if send(pid, signal.SIGSTOP):
                            halted.add(pid)
                            s.halted_at = now
                            stops += 1
                            log.write(f"t={int(now - start)}s STOP pid={pid} {s.module} anon={anon}MB avail={avail}MB "
                                      f"largest={seen[ps[0][1]].module} anon_largest={ps[0][0]}MB\n")
                    elif what == "cont":
                        if send(pid, signal.SIGCONT):
                            log.write(f"t={int(now - start)}s CONT pid={pid} {s.module} anon={anon}MB avail={avail}MB\n")
                        if s.halted_at is not None:
                            s.halted_s += now - s.halted_at
                            s.halted_at = None
                        halted.discard(pid)
                        high = 0
                    else:
                        kind = "alone" if what == "kill_alone" else "crowded"
                        if send(pid, signal.SIGKILL):
                            kills += 1
                            s.end = f"killed_{kind}"
                            log.write(f"t={int(now - start)}s KILL {kind} pid={pid} {s.module} anon={anon}MB "
                                      f"avail={avail}MB alive={len(ps)} "
                                      f"others_anon_mb={[x for x, q, _ in ps if q != pid][:6]} kills={kills}\n")
                            killed.write(f"{s.module}\t{kind}\t{anon}\t{len(ps)}\n")
                        acted_hard = True
                if low_soft >= 2:
                    low_soft = 0
                if acted_hard:
                    low_hard = 0
                    time.sleep(min(5.0, 2.5 * a.interval))
                time.sleep(a.interval)
        finally:
            now = time.time()
            for pid in list(halted):
                send(pid, signal.SIGCONT)
            for pid in list(seen):
                if seen[pid].end == "exit":
                    seen[pid].end = "watchdog_exit"
                close(pid, now)
            log.write(f"watchdog: end after {int(now - start)}s peak_used={peak_used}MB peak_anon_one={peak_anon}MB "
                      f"stops={stops} kills={kills}\n")


if __name__ == "__main__":
    main()
