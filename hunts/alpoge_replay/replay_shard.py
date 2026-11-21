#!/usr/bin/env python3
"""Runner-side driver for one shard of the Alpöge replay (stdlib only).

  check   verify that every already-built module the shard needs is on disk
  build   run `lake build` on the shard's sink modules under a wall-clock
          deadline, then record what finished
  pack    write the list of output files of the modules this shard finished,
          for tar, and the done record the planner reads
  merge   fold the done records of one round into the campaign state

A module counts as built only if Lake wrote its `.trace` and its `.olean`.
Lake writes the trace after `lean` exits zero, so a module killed by the
deadline is never counted. Nothing here decides whether a proof is right; the
Lean kernel inside `lean` does that, module by module, as the build runs.
"""
from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time

# Lake prints one line per finished module: a tick, or a warning or info sign
# when the module logged something. All three are successes.
BUILT_RE = re.compile(r"^[✔⚠ℹ] \[\d+/\d+\] Built (\S+) \(([\d.]+)(ms|s|m)\)")
FAIL_RE = re.compile(r"^✖ \[\d+/\d+\] Building (\S+)")
EXIT_RE = re.compile(r"^error: Lean exited with code (\d+)")
SORRY = "declaration uses 'sorry'"


def lib_path(lean_dir: str, module: str) -> str:
    return os.path.join(lean_dir, ".lake", "build", "lib", "lean", *module.split("."))


def ir_path(lean_dir: str, module: str) -> str:
    return os.path.join(lean_dir, ".lake", "build", "ir", *module.split("."))


def is_built(lean_dir: str, module: str) -> bool:
    p = lib_path(lean_dir, module)
    if not (os.path.isfile(p + ".olean") and os.path.isfile(p + ".trace")):
        return False
    try:
        with open(p + ".trace", encoding="utf-8") as fh:
            return "outputs" in json.load(fh)
    except (OSError, ValueError):
        return False


def output_files(lean_dir: str, module: str) -> list[str]:
    """The files of this module that a later runner needs, relative to lean_dir.

    Everything Lake wrote except `<module>.setup.json`. That file is the
    argument list Lake hands to `lean`, naming every transitive import; for a
    module that imports Mathlib it is about 6 MB, and Lake does not read it
    back to decide that a module is up to date (checked on a toy package:
    restoring without it rebuilds nothing, restoring without the `.c` file
    rebuilds everything).
    """
    out = []
    for base in (lib_path(lean_dir, module), ir_path(lean_dir, module)):
        for f in glob.glob(glob.escape(base) + ".*"):
            if os.path.isfile(f) and not f.endswith(".setup.json"):
                out.append(os.path.relpath(f, lean_dir))
    return sorted(out)


def cmd_check(a) -> None:
    shard = json.load(open(a.shard))
    missing = [m for m in shard["need"] if not is_built(a.lean_dir, m)]
    print(f"needed modules: {len(shard['need'])}, missing on disk: {len(missing)}")
    if missing:
        print("first missing:", missing[:10])
        sys.exit(1)


def batches(names: list[str], max_bytes: int = 900_000, max_n: int = 4000):
    cur, size = [], 0
    for n in names:
        b = len(n.encode()) + 1
        if cur and (size + b > max_bytes or len(cur) >= max_n):
            yield cur
            cur, size = [], 0
        cur.append(n)
        size += b
    if cur:
        yield cur


def cmd_build(a) -> None:
    shard = json.load(open(a.shard))
    sinks = shard["sinks"]
    deadline = time.time() + a.minutes * 60
    rc_all = 0
    timed_out = False
    with open(a.log, "ab") as log:
        for i, batch in enumerate(batches(sinks)):
            left = deadline - time.time()
            if left < 30:
                timed_out = True
                break
            log.write(f"=== batch {i}: {len(batch)} targets, {left:.0f}s left ===\n".encode())
            log.flush()
            proc = subprocess.Popen(["lake", "build", "--no-ansi", *batch], cwd=a.lean_dir,
                                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                rc = proc.wait(timeout=left)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    proc.wait(timeout=45)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                rc = 124
            log.write(f"=== batch {i} rc={rc} ===\n".encode())
            log.flush()
            rc_all = rc_all or rc
            if timed_out:
                break
    print(json.dumps({"rc": rc_all, "timed_out": timed_out}))
    json.dump({"rc": rc_all, "timed_out": timed_out, "minutes": a.minutes},
              open(a.log + ".status.json", "w"))


def parse_log(path: str):
    seconds: dict[str, float] = {}
    failed: dict[str, dict] = {}
    sorry_lines = 0
    cur_fail = None
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = BUILT_RE.match(line)
            if m:
                v = float(m.group(2))
                seconds[m.group(1)] = v / 1000 if m.group(3) == "ms" else v * 60 if m.group(3) == "m" else v
                cur_fail = None
                continue
            m = FAIL_RE.match(line)
            if m:
                cur_fail = m.group(1)
                failed[cur_fail] = {"exit": None, "excerpt": []}
                continue
            if SORRY in line:
                sorry_lines += 1
            if cur_fail is not None:
                e = EXIT_RE.match(line)
                if e:
                    failed[cur_fail]["exit"] = int(e.group(1))
                    cur_fail = None
                elif line.startswith("error:") and len(failed[cur_fail]["excerpt"]) < 6:
                    failed[cur_fail]["excerpt"].append(line.rstrip()[:400])
    return seconds, failed, sorry_lines


def watchdog_kills(path: str | None) -> dict[str, set[str]]:
    """{"crowded": {modules}, "alone": {modules}} from mem_watchdog.py's kills table."""
    out: dict[str, set[str]] = {}
    if not path or not os.path.exists(path):
        return out
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 2 and parts[0] not in ("", "?"):
                out.setdefault(parts[1], set()).add(parts[0])
    # killed alone at any point outweighs having also been crowded out
    out["crowded"] = out.get("crowded", set()) - out.get("alone", set())
    return out


MEM_RE = re.compile(r"avail=(\d+)MB used=(\d+)MB .*?(?:majfault=(\d+) swapin=(\d+) swapout=(\d+) )?n=\d+ "
                    r"anon_mb=\[([^\]]*)\]")


def memory_summary(log: str | None, top: int = 15) -> dict:
    """What mem_watchdog.py saw during the build, small enough to keep in the state.

    From the log: the least available and most used memory, major page
    faults and pages swapped out, suspensions and kills. From its modules
    table: the modules that held the most anonymous memory.
    """
    out: dict = {}
    if not log or not os.path.exists(log):
        return out
    min_avail = None
    peak_used = peak_anon = majfault = swapout = stops = kills = 0
    with open(log, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if " STOP " in line:
                stops += 1
            elif " KILL " in line:
                kills += 1
            m = MEM_RE.search(line)
            if not m:
                continue
            avail, used = int(m.group(1)), int(m.group(2))
            min_avail = avail if min_avail is None else min(min_avail, avail)
            peak_used = max(peak_used, used)
            majfault += int(m.group(3) or 0)
            swapout += int(m.group(5) or 0)
            for x in m.group(6).split(","):
                if x.strip().isdigit():
                    peak_anon = max(peak_anon, int(x))
    out = {"min_avail_mb": min_avail, "peak_used_mb": peak_used, "peak_anon_one_mb": peak_anon,
           "majfault": majfault, "swapout_pages": swapout, "stops": stops, "kills": kills}
    rows = []
    table = log + ".modules.tsv"
    if os.path.exists(table):
        with open(table, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) >= 6 and f[1].isdigit() and f[2].isdigit():
                    rows.append([f[0], int(f[1]), int(f[2]), int(float(f[3])), int(float(f[4])), f[5]])
                    out["peak_anon_one_mb"] = max(out["peak_anon_one_mb"], int(f[1]))
        out["processes_seen"] = len(rows)
        out["over_2gb"] = sum(1 for r in rows if r[1] >= 2048)
        out["top"] = sorted(rows, key=lambda r: -r[1])[:top]
    return out


def cmd_pack(a) -> None:
    shard = json.load(open(a.shard))
    mine = shard["modules"]
    # "extra": modules another shard owns, built here only to reach this
    # shard's own (the planner's filling pass). They are neither packed nor
    # reported, but they are not strays either.
    extra = shard.get("extra", [])
    inside = set(mine)
    expected = inside | set(extra)
    seconds, failed, sorry_lines = parse_log(a.log)
    status = json.load(open(a.log + ".status.json")) if os.path.exists(a.log + ".status.json") else {}
    built = [m for m in mine if is_built(a.lean_dir, m)]
    files: list[str] = []
    for m in built:
        files.extend(output_files(a.lean_dir, m))
    with open(a.filelist, "w", encoding="utf-8") as fh:
        fh.write("\n".join(files) + ("\n" if files else ""))
    by_kind: dict[str, int] = {}
    for f in files:
        kind = "hash" if f.endswith(".hash") else f.rsplit(".", 1)[-1]
        by_kind[kind] = by_kind.get(kind, 0) + os.path.getsize(os.path.join(a.lean_dir, f))
    raw = sum(by_kind.values())
    olean = by_kind.get("olean", 0)
    rebuilt_outside = sorted(m for m in seconds if m not in expected)
    # Two shards built these: the bytes of the .olean are what the next
    # round's traces depend on, so they are compared at the merge.
    olean_sha256 = {}
    for m in shard.get("shared", []):
        if is_built(a.lean_dir, m):
            with open(lib_path(a.lean_dir, m) + ".olean", "rb") as fh:
                olean_sha256[m] = hashlib.sha256(fh.read()).hexdigest()
    # A module that failed in one batch and was built in a later one is built.
    done_now = set(built)
    failed = {m: v for m, v in failed.items() if m not in done_now}
    # a real elaboration error is exit code 1; anything else is a crash to retry
    hard = {m: v for m, v in failed.items() if v["exit"] == 1 and m in inside}
    # The memory watchdog says which of its kills were "crowded": the module
    # was suspended or small beside a larger one and gave way to it. That
    # says nothing against the module and is no strike. A kill "alone", or a
    # death the watchdog did not cause, stays a crash.
    crowded_by_watchdog = watchdog_kills(a.kills).get("crowded", set())
    crashed = {m: v for m, v in failed.items()
               if v["exit"] != 1 and m in inside and m not in crowded_by_watchdog}
    crowded = {m: v for m, v in failed.items()
               if v["exit"] != 1 and m in inside and m in crowded_by_watchdog}
    rec = {
        "chunk": a.chunk,
        "round": shard["round"],
        "shard": shard["shard"],
        "planned": len(mine),
        "built": built,
        "seconds": {m: round(seconds[m], 3) for m in built if m in seconds},
        "failed": hard,
        "crashed": crashed,
        "crowded": crowded,
        "killed_alone": sorted(m for m in watchdog_kills(a.kills).get("alone", set()) if m in inside),
        "extra_planned": len(extra),
        "extra_built": sum(1 for m in extra if is_built(a.lean_dir, m)),
        "olean_sha256": olean_sha256,
        "mem": memory_summary(a.memlog),
        "rebuilt_outside_shard": len(rebuilt_outside),
        "rebuilt_outside_examples": rebuilt_outside[:5],
        "sorry_warning_lines": sorry_lines,
        "raw_output_bytes": raw,
        "olean_bytes": olean,
        "bytes_by_kind": by_kind,
        "build_status": status,
    }
    json.dump(rec, open(a.done, "w"))
    brief = {k: (len(v) if isinstance(v, (list, dict)) and k in ("built", "seconds", "failed", "crashed", "crowded",
                                                                 "olean_sha256") else v)
             for k, v in rec.items() if k != "rebuilt_outside_examples"}
    brief["mem"] = {k: v for k, v in rec["mem"].items() if k != "top"}
    print(json.dumps(brief))


def cmd_merge(a) -> None:
    dag = json.load(open(a.dag))
    known = dag["deps"]
    state = {"where": {}, "seconds": {}, "failed": {}, "crashed": {}, "bundles": {}, "history": []}
    if a.state and os.path.exists(a.state):
        state = json.load(open(a.state))
    before = len(state["where"])
    rnd = {"round": a.round, "shards": 0, "planned": 0, "built": 0, "bytes_by_kind": {}, "raw_output_bytes": 0,
           "olean_bytes": 0, "seconds_sum": 0.0, "source_bytes": 0, "rebuilt_outside_shard": 0,
           "sorry_warning_lines": 0, "timed_out_shards": 0, "failed": 0, "crashed": 0}
    hashes: dict[str, set[str]] = {}
    copies: dict[str, int] = {}
    for f in sorted(glob.glob(os.path.join(a.done_dir, "**", "done-*.json"), recursive=True)):
        rec = json.load(open(f))
        rnd["shards"] += 1
        rnd["extra_built"] = rnd.get("extra_built", 0) + (rec.get("extra_built") or 0)
        mem = rec.get("mem") or {}
        if mem:
            agg = rnd.setdefault("mem", {"min_avail_mb": None, "peak_used_mb": 0, "peak_anon_one_mb": 0, "majfault": 0,
                                         "swapout_pages": 0, "stops": 0, "kills": 0, "over_2gb": 0, "top": []})
            if mem.get("min_avail_mb") is not None:
                agg["min_avail_mb"] = (mem["min_avail_mb"] if agg["min_avail_mb"] is None
                                       else min(agg["min_avail_mb"], mem["min_avail_mb"]))
            for k in ("peak_used_mb", "peak_anon_one_mb"):
                agg[k] = max(agg[k], mem.get(k) or 0)
            for k in ("majfault", "swapout_pages", "stops", "kills", "over_2gb"):
                agg[k] += mem.get(k) or 0
            agg["top"] = sorted(agg["top"] + (mem.get("top") or []), key=lambda r: -r[1])[:25]
        for m, h in (rec.get("olean_sha256") or {}).items():
            hashes.setdefault(m, set()).add(h)
            copies[m] = copies.get(m, 0) + 1
        rnd["planned"] += rec.get("planned", 0)
        for m in rec.get("built", []):
            if m in known and m not in state["where"]:
                state["where"][m] = rec["chunk"]
                rnd["built"] += 1
                rnd["source_bytes"] += dag["size"][m]
        for m, s in rec.get("seconds", {}).items():
            if m in known:
                state["seconds"][m] = s
                rnd["seconds_sum"] += s
        for m, v in rec.get("failed", {}).items():
            if m in known:
                state["failed"][m] = v
        for m in rec.get("crashed", {}):
            if m in known:
                state["crashed"][m] = state["crashed"].get(m, 0) + 1
                rnd["crashed_this_round"] = rnd.get("crashed_this_round", 0) + 1
        # crowded out by the memory watchdog: counted, never a strike
        rnd["crowded_this_round"] = rnd.get("crowded_this_round", 0) + sum(
            1 for m in rec.get("crowded", {}) if m in known)
        for m in rec.get("killed_alone", []):
            if m in known:
                rnd.setdefault("killed_alone", []).append(m)
        for k in ("raw_output_bytes", "olean_bytes", "rebuilt_outside_shard", "sorry_warning_lines"):
            rnd[k] += rec.get(k, 0) or 0
        for k, v in (rec.get("bytes_by_kind") or {}).items():
            rnd["bytes_by_kind"][k] = rnd["bytes_by_kind"].get(k, 0) + v
        if (rec.get("build_status") or {}).get("timed_out"):
            rnd["timed_out_shards"] += 1
    # Modules two shards built: same bytes or not. A difference does not make
    # anything wrong, Lake rebuilds what was built against the other copy,
    # but it makes building twice a waste, and the chain stops doing it.
    twice = sorted(m for m, n in copies.items() if n > 1)
    different = [m for m in twice if len(hashes[m]) > 1]
    rnd["built_twice"] = len(twice)
    rnd["built_twice_different"] = len(different)
    if different:
        rnd["built_twice_different_examples"] = different[:20]
    rnd["failed"] = len(state["failed"])
    rnd["crashed"] = len(state["crashed"])
    rnd["seconds_sum"] = round(rnd["seconds_sum"], 1)
    state["history"] = [h for h in state.get("history", []) if h["round"] != a.round] + [rnd]
    state.setdefault("bundles", {})
    if a.bundle_id:
        state["bundles"][str(a.round)] = int(a.bundle_id)
    json.dump(state, open(a.out, "w"))
    total = len(known)
    out = {
        "round": a.round,
        "built_this_round": len(state["where"]) - before,
        "modules_built": len(state["where"]),
        "modules_total": total,
        "percent": round(100.0 * len(state["where"]) / total, 2),
        "main_built": "Main" in state["where"],
        "complete": len(state["where"]) == total,
        "failed": sorted(state["failed"])[:20],
        "n_failed": len(state["failed"]),
        "timed_out_shards": rnd["timed_out_shards"],
        "crashed_this_round": rnd.get("crashed_this_round", 0),
        "crowded_this_round": rnd.get("crowded_this_round", 0),
        "killed_alone": sorted(rnd.get("killed_alone", [])),
        "built_twice": rnd["built_twice"],
        "built_twice_different": rnd["built_twice_different"],
        "shards_reported": rnd["shards"],
        "round_summary": rnd,
    }
    print(json.dumps(out))
    if a.github_output:
        with open(a.github_output, "a") as fh:
            for k in ("built_this_round", "modules_built", "main_built", "complete", "n_failed", "percent",
                      "timed_out_shards", "crashed_this_round", "crowded_this_round", "shards_reported",
                      "built_twice", "built_twice_different"):
                v = out[k]
                fh.write(f"{k}={str(v).lower() if isinstance(v, bool) else v}\n")


def cmd_fetchmap(a) -> None:
    """Everything built so far, as the "fetch" map restore_chunks.sh reads."""
    st = json.load(open(a.state))
    fetch: dict[str, list[str]] = {}
    for c in sorted(set(st["where"].values())):  # a chunk is named r<round>-s<shard>
        rnd = c.split("-")[0][1:]
        if rnd not in st.get("bundles", {}):
            raise SystemExit(f"state has no bundle for round {rnd}, needed for chunk {c}")
        fetch.setdefault(str(st["bundles"][rnd]), []).append(f"chunk-{c}.tar.zst")
    json.dump({"fetch": fetch}, open(a.out, "w"))
    print(f"bundles={len(fetch)} chunks={sum(len(v) for v in fetch.values())} modules={len(st['where'])}")


def cmd_builtsinks(a) -> None:
    """The built modules that no built module imports: building these as
    targets makes Lake check every module built so far, and nothing else."""
    deps = json.load(open(a.dag))["deps"]
    built = {m for m in json.load(open(a.state))["where"] if m in deps}
    imported = {d for m in built for d in deps[m]}
    sinks = sorted(built - imported)
    with open(a.out, "w", encoding="utf-8") as fh:
        fh.write("\n".join(sinks) + ("\n" if sinks else ""))
    print(f"built={len(built)} sinks={len(sinks)}")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("check"); s.add_argument("--lean-dir", required=True); s.add_argument("--shard", required=True)
    s.set_defaults(fn=cmd_check)
    s = sub.add_parser("build"); s.add_argument("--lean-dir", required=True); s.add_argument("--shard", required=True)
    s.add_argument("--minutes", type=float, required=True); s.add_argument("--log", required=True)
    s.set_defaults(fn=cmd_build)
    s = sub.add_parser("pack"); s.add_argument("--lean-dir", required=True); s.add_argument("--shard", required=True)
    s.add_argument("--log", required=True); s.add_argument("--chunk", required=True)
    s.add_argument("--filelist", required=True); s.add_argument("--done", required=True)
    s.add_argument("--kills", help="mem_watchdog.py's kills table, to tell a crowded kill from a crash")
    s.add_argument("--memlog", help="mem_watchdog.py's log; a summary of it goes into the done record")
    s.set_defaults(fn=cmd_pack)
    s = sub.add_parser("fetchmap"); s.add_argument("--state", required=True); s.add_argument("--out", required=True)
    s.set_defaults(fn=cmd_fetchmap)
    s = sub.add_parser("builtsinks"); s.add_argument("--dag", required=True); s.add_argument("--state", required=True)
    s.add_argument("--out", required=True)
    s.set_defaults(fn=cmd_builtsinks)
    s = sub.add_parser("merge"); s.add_argument("--dag", required=True); s.add_argument("--state")
    s.add_argument("--done-dir", required=True); s.add_argument("--round", type=int, required=True)
    s.add_argument("--out", required=True); s.add_argument("--github-output")
    s.add_argument("--bundle-id", help="artifact id of this round's bundle of chunks")
    s.set_defaults(fn=cmd_merge)
    a = p.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
