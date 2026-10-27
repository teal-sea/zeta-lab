#!/usr/bin/env python3
"""Hunt #145, door 1, Stage B: run one shard on a fleet VM and write its receipt.

Runs on the VM, standard library only. `WORKDIR` holds `con-ron`, `shard.ndjson.zst` and
`job.json` (the shard's name, the expected SHA-256 of the binary, of the compressed export
and of the export itself, and the worker count). The steps:

1. hash `con-ron` and `shard.ndjson.zst` and refuse to go on unless both match `job.json`;
2. decompress with `zstd` and hash the export, again against `job.json`;
3. `con-ron --verified --jobs=N --progress=20 shard.ndjson`, stdout and stderr to files,
   with `ulimit -s unlimited` (set by the caller) and the peak RSS sampled every 5 s;
4. `receipt.json`: the hashes, the exit code, con-ron's own verdict lines, the number of
   declarations it accepted, the wall and CPU time, the peak RSS and the host.

`status.json` names the step in progress; it is the file the orchestrator polls.

    python3 conron_shard.py WORKDIR
"""
import hashlib
import json
import os
import platform
import resource
import subprocess
import sys
import threading
import time


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def utc():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def write_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=1)
        f.write("\n")
    os.replace(tmp, path)


def host():
    info = {"nproc": os.cpu_count(), "platform": platform.platform(), "python": sys.version.split()[0]}
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("model name"):
                    info["cpu"] = line.split(":", 1)[1].strip()
                    break
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal:"):
                    info["mem_total_kib"] = int(line.split()[1])
    except OSError:
        pass
    return info


def tree_rss_kib(pid):
    """RSS of `pid` and its descendants, from /proc."""
    total, todo = 0, [pid]
    while todo:
        p = todo.pop()
        try:
            with open(f"/proc/{p}/status") as f:
                for line in f:
                    if line.startswith("VmRSS:"):
                        total += int(line.split()[1])
            with open(f"/proc/{p}/task/{p}/children") as f:
                todo += [int(x) for x in f.read().split()]
        except OSError:
            pass
    return total


def main(wd):
    os.chdir(wd)
    job = json.load(open("job.json"))
    rec = {"shard": job["shard"], "start_utc": utc(), "host": host(), "job": job}

    def status(phase, **kw):
        write_json("status.json", {"phase": phase, "utc": utc(), **kw})

    def finish(phase):
        rec["end_utc"] = utc()
        rec["phase"] = phase
        write_json("receipt.json", rec)
        status("done", outcome=phase)

    status("verifying")
    got = {"con-ron": sha256("con-ron"), "shard.ndjson.zst": sha256("shard.ndjson.zst")}
    rec["sha256_inputs"] = got
    if got["con-ron"] != job["sha256_conron"] or got["shard.ndjson.zst"] != job["sha256_zst"]:
        return finish("integrity_failed")
    status("decompressing")
    t0 = time.time()
    r = subprocess.run(["zstd", "-d", "-f", "-q", "shard.ndjson.zst", "-o", "shard.ndjson"])
    rec["decompress_s"] = round(time.time() - t0, 1)
    if r.returncode != 0:
        rec["decompress_rc"] = r.returncode
        return finish("decompress_failed")
    rec["sha256_export"] = sha256("shard.ndjson")
    if rec["sha256_export"] != job["sha256_ndjson"]:
        return finish("integrity_failed")
    os.remove("shard.ndjson.zst")

    status("checking")
    cmd = ["./con-ron", "--verified", f"--jobs={job['jobs']}", "--progress=20", "shard.ndjson"]
    rec["command"] = cmd
    rec["check_start_utc"] = utc()
    t0 = time.time()
    with open("conron.out", "wb") as out, open("conron.err", "wb") as err:
        p = subprocess.Popen(cmd, stdout=out, stderr=err)
        peak = [0]
        stop = threading.Event()

        def sample():
            while not stop.wait(5):
                peak[0] = max(peak[0], tree_rss_kib(p.pid))
        th = threading.Thread(target=sample, daemon=True)
        th.start()
        rc = p.wait()
        stop.set()
        th.join(timeout=10)
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    rec.update({"exit_code": rc, "wall_s": round(time.time() - t0, 1),
                "user_s": round(ru.ru_utime, 1), "sys_s": round(ru.ru_stime, 1),
                "maxrss_kib": ru.ru_maxrss, "peak_sampled_rss_kib": peak[0]})
    outtxt = open("conron.out", "rb").read().decode("utf-8", "replace")
    errtxt = open("conron.err", "rb").read().decode("utf-8", "replace")
    verdict = [l for l in (outtxt + "\n" + errtxt).splitlines()
               if l.startswith(("con-ron: accepted", "con-ron: rejected", "con-ron: declined",
                                "con-ron: done", "con-ron: check done", "con-ron: check failed",
                                "con-ron: install failed", "con-ron: parse done"))]
    rec["verdict_lines"] = verdict
    rec["stdout_tail"] = outtxt[-2000:]
    rec["stderr_tail"] = errtxt[-3000:]
    rec["sha256_stdout"] = sha256("conron.out")
    rec["sha256_stderr"] = sha256("conron.err")
    acc = [l for l in verdict if l.startswith("con-ron: accepted")]
    if acc:
        try:
            rec["accepted_declarations"] = int(acc[-1].split()[2])
        except (IndexError, ValueError):
            pass
    finish("checked")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    main(sys.argv[1])
