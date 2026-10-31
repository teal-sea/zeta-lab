"""Run one checker to a verdict under the swarm-box memory rule, and write a receipt.

Usage: guard.py NAME CWD -- COMMAND...

No wall limit. The only stop is the box rule: SIGTERM the checker's process
group when host MemAvailable falls below FLOOR_KIB (20 GiB). Writes
NAME.status.json every minute and NAME.receipt.json at the end.
"""
import hashlib
import json
import os
import signal
import subprocess
import sys
import time
from datetime import datetime, timezone

FLOOR_KIB = 20 * 1024 * 1024
HERE = os.path.dirname(os.path.abspath(__file__))


def now():
    return datetime.now(timezone.utc).isoformat()


def memavailable_kib():
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1])
    raise RuntimeError("no MemAvailable")


def tree_rss_kib(root):
    children = {}
    rss = {}
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            with open(f"/proc/{pid}/stat") as f:
                ppid = int(f.read().rsplit(")", 1)[1].split()[1])
            with open(f"/proc/{pid}/status") as f:
                kib = next((int(l.split()[1]) for l in f if l.startswith("VmRSS:")), 0)
        except (OSError, ValueError, IndexError):
            continue
        children.setdefault(ppid, []).append(int(pid))
        rss[int(pid)] = kib
    total, stack = 0, [root]
    while stack:
        p = stack.pop()
        total += rss.get(p, 0)
        stack.extend(children.get(p, []))
    return total


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def write(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=2)
        f.write("\n")
    os.replace(tmp, path)


def main():
    name, cwd, sep, *cmd = sys.argv[1:]
    assert sep == "--" and cmd
    out = os.path.join(HERE, f"{name}.out")
    err = os.path.join(HERE, f"{name}.err")
    hashed = [p for p in cmd if os.path.isfile(p)]
    rec = {
        "command": cmd,
        "cwd": cwd,
        "start_utc": now(),
        "wall_limit_seconds": None,
        "host_memavailable_floor_kib": FLOOR_KIB,
        "inputs_sha256_before": {p: sha256(p) for p in hashed},
    }
    with open(out, "wb") as fo, open(err, "wb") as fe:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=fo, stderr=fe, start_new_session=True)
    rec["pid"] = proc.pid
    peak_rss, min_avail, stop, last_status = 0, memavailable_kib(), None, 0.0
    while proc.poll() is None:
        avail = memavailable_kib()
        peak_rss = max(peak_rss, tree_rss_kib(proc.pid))
        min_avail = min(min_avail, avail)
        if avail < FLOOR_KIB and stop is None:
            stop = "host_memavailable_floor"
            os.killpg(proc.pid, signal.SIGTERM)
        if time.time() - last_status > 60:
            write(os.path.join(HERE, f"{name}.status.json"), {
                **rec, "now_utc": now(), "running": True,
                "peak_sampled_tree_rss_kib": peak_rss, "min_memavailable_kib": min_avail})
            last_status = time.time()
        time.sleep(5)
    rec.update({
        "end_utc": now(),
        "exit_code": proc.returncode,
        "stop_reason": stop,
        "peak_sampled_tree_rss_kib": peak_rss,
        "min_memavailable_kib": min_avail,
        "inputs_sha256_after": {p: sha256(p) for p in hashed},
        "stdout_sha256": sha256(out),
        "stderr_sha256": sha256(err),
    })
    write(os.path.join(HERE, f"{name}.receipt.json"), rec)


if __name__ == "__main__":
    main()
