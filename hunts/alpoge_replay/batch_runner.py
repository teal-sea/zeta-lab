#!/usr/bin/env python3
"""Run a replay driver on several list files, one process after another.

    python3 -I batch_runner.py '<json: the command up to the list file>' <list file>...

A driver that holds on to memory from module to module (lean4lean's replay
keeps about half a gigabyte per module, measured in the pilot of 2026-11-21)
is given a few modules at a time. The runner ends at the first driver process
that ends by anything but 0 (all replayed) or 1 (some rejected), and ends the
same way, so that the module that process was on is still the first one not
reported.

With REPLAY_MODULE_SECONDS set to a positive number, a module the driver has
been on for longer than that is given up: the driver process is ended, the
module is reported as

    FAIL<tab>module<tab>milliseconds<tab>no answer after N s: ...

and the modules after it in the list go to a fresh process. That line says
that this run stopped waiting. It is no verdict of the checker, and
`replay_check.py plan --retry-failed "no answer after"` plans such modules
again. Why it exists: in round 6 of the lean4lean pass one module, which the
kernel replays in four seconds, held a driver for 77 minutes and 10 GB until
the shard's deadline, and the memory watchdog suspended the two processes
beside it for the last forty; the shard replayed 1,319 of its 4,368 modules.

Time during which a process of the driver is stopped does not count: the
memory watchdog suspends drivers so that the largest can finish, and a module
is not slow for having waited.

The driver runs in a process group of its own, so that it can be ended
without ending this runner. A SIGTERM or SIGINT to the runner (the shard's
deadline) ends the driver with it.
"""
from __future__ import annotations

import json
import os
import select
import signal
import subprocess
import sys
import time

#: the text `replay_check.py plan --retry-failed` matches
NO_ANSWER = "no answer after"
TICK_S = 5.0


def group_stopped(pgid: int) -> bool:
    """True if a process of process group `pgid` is stopped (state T in /proc)."""
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open(f"/proc/{d}/stat", encoding="utf-8", errors="replace") as fh:
                fields = fh.read().rsplit(")", 1)[1].split()
        except (OSError, IndexError):
            continue
        # after the name: state, parent, process group
        if len(fields) > 2 and fields[2] == str(pgid) and fields[0] in ("T", "t"):
            return True
    return False


def kill_group(child: subprocess.Popen) -> None:
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    child.wait()


def run_list(prefix: list[str], list_file: str, limit_s: float, out, state: dict,
             tick_s: float = TICK_S) -> tuple[int, list[str]]:
    """One driver process on one list file.

    Returns (exit code, modules for a fresh process). The second is empty
    unless the driver was ended for a module over `limit_s`: then it is what
    came after that module in the list, and the code is 1.
    """
    with open(list_file, encoding="utf-8") as fh:
        names = [line.strip() for line in fh if line.strip()]
    child = subprocess.Popen(prefix + [list_file], stdout=subprocess.PIPE, start_new_session=True)
    state["child"] = child
    fd = child.stdout.fileno()
    done, partial = 0, b""
    used, last = 0.0, time.monotonic()
    gave_up = None

    def forward(chunk: bytes) -> None:
        nonlocal done, partial, used
        out.write(chunk)
        out.flush()
        *lines, partial = (partial + chunk).split(b"\n")
        for line in lines:
            if line.startswith((b"OK\t", b"FAIL\t")):
                done += 1
                used = 0.0

    while True:
        ready, _, _ = select.select([fd], [], [], tick_s if limit_s > 0 else None)
        now = time.monotonic()
        if limit_s > 0 and not group_stopped(child.pid):
            used += now - last
        last = now
        if ready:
            chunk = os.read(fd, 1 << 16)
            if not chunk:
                break
            forward(chunk)
        if limit_s > 0 and used > limit_s and done < len(names):
            gave_up, waited = done, used
            kill_group(child)
            # what the driver wrote before it was ended: the module may have
            # finished in the same moment, and then it is not given up
            while select.select([fd], [], [], 10.0)[0]:
                chunk = os.read(fd, 1 << 16)
                if not chunk:
                    break
                forward(chunk)
            break
    code = child.wait()
    child.stdout.close()
    state["child"] = None
    if gave_up is None:
        return code, []
    if partial:
        out.write(b"\n")
    stopped_waiting = done == gave_up
    if stopped_waiting:
        out.write((f"FAIL\t{names[gave_up]}\t{int(waited * 1000)}\t{NO_ANSWER} {int(limit_s)} s: "
                   "this run stopped waiting, the checker gave no verdict\n").encode())
        done += 1
    out.flush()
    return (1 if stopped_waiting else 0), names[done:]


def main(argv: list[str]) -> int:
    prefix = json.loads(argv[1])
    limit_s = float(os.environ.get("REPLAY_MODULE_SECONDS") or 0)
    out = sys.stdout.buffer
    state: dict = {"child": None}

    def on_signal(signum, _frame) -> None:
        child = state["child"]
        if child is not None and child.poll() is None:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        signal.signal(signum, signal.SIG_DFL)
        os.kill(os.getpid(), signum)

    signal.signal(signal.SIGTERM, on_signal)
    signal.signal(signal.SIGINT, on_signal)
    worst = 0
    for list_file in argv[2:]:
        todo, n = list_file, 0
        while todo:
            code, rest = run_list(prefix, todo, limit_s, out, state, tick_s=min(TICK_S, max(0.2, limit_s / 4)))
            if code < 0:
                signal.signal(-code, signal.SIG_DFL)
                os.kill(os.getpid(), -code)
            if code not in (0, 1):
                return code
            worst = max(worst, code)
            todo = None
            if rest:
                # the same file name in a directory of its own: the name is
                # what the memory watchdog reads off the driver's command line
                n += 1
                d = os.path.join(os.path.dirname(os.path.abspath(list_file)), f"rest-{n}")
                os.makedirs(d, exist_ok=True)
                todo = os.path.join(d, os.path.basename(list_file))
                with open(todo, "w", encoding="utf-8") as fh:
                    fh.write("\n".join(rest) + "\n")
    return worst


if __name__ == "__main__":
    sys.exit(main(sys.argv))
