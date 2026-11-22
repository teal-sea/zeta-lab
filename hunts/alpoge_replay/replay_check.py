#!/usr/bin/env python3
"""Second pass of the Alpöge replay: kernel replay of every built module.

The first pass (`replay_plan.py`, `replay_shard.py`) elaborates the archive.
A clean build with a clean axiom printout does not show that every declaration
went through the kernel: a toy module that sets `debug.skipKernelTC` and
closes `1 = 2` with a term of the wrong type builds without a warning, and
`#print axioms` on a proof of `False` resting on it reports no axioms
(`test_replay_check.py` pins this). The archive contains no such option at
text level, but text is not the check.

This pass reads the `.olean` of each built module and sends its constants
through the kernel again with `ReplayDriver.lean`, which wraps the same
function `leanchecker` uses. It runs none of the archive's code. Modules have
no order here, since every import already exists, so shards are cut by level
in the import graph: the lowest need the fewest files restored.

  plan      cut the built, unreplayed modules into shards
  run       replay one shard under a deadline, several processes side by side
  merge     fold the shard records into the check state
  selftest  build the toy package with the planted fault and require the
            driver about to be used to reject it, on this machine

The driver is `ReplayDriver.lean` under `lean --run` (`--driver`), or a
compiled program with the same output (`--driver-exe`): `L4LDriver.lean`
puts lean4lean's checker behind the same front end.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import resource
import signal
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import replay_plan as rp  # noqa: E402


def load_check_state(path: str | None) -> dict:
    if path and os.path.exists(path):
        return json.load(open(path))
    return {"checked": {}, "ms": {}, "failed": {}, "strikes": {}, "history": []}


# --------------------------------------------------------------------------
# plan
# --------------------------------------------------------------------------

def plan_check(deps, level, where, bundles, cstate, n_shards, budget_s, default_s, max_strikes=2,
               retry: tuple[str, ...] = ()):
    """Return (shards, left). A shard is {'modules', 'need', 'fetch', 'est_s'}.

    With `retry`, the round is a second attempt and nothing else: it plans the
    modules recorded as failed whose message contains one of the given texts,
    and no module that has not been tried. That is for a checker that gave up
    for a limit of its own (lean4lean's fuel) and is now given more; a module
    that failed for any other reason stays failed.
    """
    checked, failed, strikes = cstate["checked"], cstate["failed"], cstate.get("strikes", {})
    ms = cstate.get("ms", {})
    mean_s = (sum(ms.values()) / len(ms) / 1000.0) if len(ms) >= 200 else default_s
    if retry:
        todo = sorted((m for m in where if m in failed and any(text in failed[m] for text in retry)),
                      key=lambda m: (level[m], m))
    else:
        todo = sorted((m for m in where
                       if m not in checked and m not in failed and strikes.get(m, 0) < max_strikes),
                      key=lambda m: (level[m], m))
    shards, cur, load = [], [], 0.0
    for m in todo:
        if len(shards) == n_shards:
            break
        cur.append(m)
        load += mean_s
        if load >= budget_s:
            shards.append(cur)
            cur, load = [], 0.0
    if cur and len(shards) < n_shards:
        shards.append(cur)
    planned = sum(len(s) for s in shards)
    out = []
    for sh in shards:
        inside = set(sh)
        seen: set[str] = set()
        stack = list(sh)
        while stack:
            x = stack.pop()
            for d in deps[x]:
                if d not in seen and d not in inside:
                    seen.add(d)
                    stack.append(d)
        missing = [d for d in seen if d not in where]
        if missing:
            raise SystemExit(f"a built module imports an unbuilt one: {missing[:3]}")
        need = sorted(seen | inside)
        fetch: dict[str, list[str]] = {}
        for c in sorted({where[m] for m in need}):
            rnd = c.split("-")[0][1:]
            if rnd not in bundles:
                raise SystemExit(f"state has no bundle for round {rnd}")
            fetch.setdefault(str(bundles[rnd]), []).append(f"chunk-{c}.tar.zst")
        out.append({"modules": sh, "need": need, "fetch": fetch, "est_s": round(len(sh) * mean_s, 1)})
    return out, len(todo) - planned, mean_s


def cmd_plan(a) -> None:
    g = json.load(open(a.dag))
    deps = g["deps"]
    order, level = rp.topo_levels(deps)
    st = json.load(open(a.state))
    where = {m: c for m, c in st["where"].items() if m in deps}
    # a built module standing on an unbuilt one cannot be loaded, so it cannot
    # be replayed yet (replay_plan.usable says how that came about)
    ok = rp.usable(where, deps, order)
    where = {m: c for m, c in where.items() if m in ok}
    cstate = load_check_state(a.check_state)
    shards, left, mean_s = plan_check(deps, level, where, st.get("bundles", {}), cstate,
                                      a.shards, a.budget_s, a.default_s, a.max_strikes,
                                      retry=tuple(a.retry_failed or ()))
    os.makedirs(a.out, exist_ok=True)
    for i, sh in enumerate(shards):
        sh.update({"round": a.round, "shard": i})
        json.dump(sh, open(os.path.join(a.out, f"shard-{i}.json"), "w"))
    summary = {
        "round": a.round,
        "build_modules": len(where),
        "build_complete": len(where) == len(deps),
        "checked_before": len(cstate["checked"]),
        "failed_before": len(cstate["failed"]),
        "planned": sum(len(s["modules"]) for s in shards),
        "left_after_plan": left,
        "n_shards": len(shards),
        "retry_failed": list(a.retry_failed or ()),
        "mean_s_per_module": round(mean_s, 3),
        "shards": [{"shard": i, "modules": len(s["modules"]), "need": len(s["need"]),
                    "bundles": len(s["fetch"]), "est_s": s["est_s"]} for i, s in enumerate(shards)],
    }
    json.dump(summary, open(os.path.join(a.out, "plan.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "shards"}))
    for s in summary["shards"]:
        print("  ", json.dumps(s))


# --------------------------------------------------------------------------
# the driver, and the fault it must reject
# --------------------------------------------------------------------------

#: A theorem that never met the kernel: the tactic assigns a term of the wrong
#: type and `debug.skipKernelTC` lets the declaration through. `lake build`
#: accepts it without a warning.
CHEAT = """import Lean
open Lean Elab Tactic

/-- Close any goal with a term of the wrong type, without asking the elaborator. -/
elab "cheat" : tactic => do
  let g ← getMainGoal
  g.assign (mkConst ``True.intro)

set_option debug.skipKernelTC true in
theorem bad : (1 : Nat) = 2 := by cheat
"""

#: module -> source of the toy package: one honest module, the fault, and a
#: proof of `False` resting on it. Only the middle one may fail a replay.
TOY = {
    "Lib.Honest": "theorem honest : 1 + 1 = 2 := rfl\n",
    "Lib.Cheat": CHEAT,
    "Lib.UsesCheat": "import Lib.Cheat\ntheorem worse : False := absurd bad (by decide)\n",
}
TOY_EXPECTED = {"Lib.Honest": "OK", "Lib.Cheat": "FAIL", "Lib.UsesCheat": "OK"}


def driver_command(driver: str | None, driver_exe: str | None, list_file: str) -> list[str]:
    """The command that replays the modules named in `list_file`, run from a Lake package."""
    if bool(driver) == bool(driver_exe):
        raise SystemExit("give exactly one of --driver and --driver-exe")
    if driver_exe:
        return ["lake", "env", os.path.abspath(driver_exe), list_file]
    return ["lake", "env", "lean", "--run", os.path.abspath(driver), list_file]


#: Run a driver on several list files, one process after another. A driver
#: that holds on to memory from module to module (lean4lean's replay keeps
#: about half a gigabyte per module, measured in the pilot of 2026-11-21)
#: is given a few modules at a time. It stops at the first process that ends
#: by anything but 0 (all replayed) or 1 (some rejected), and ends the same
#: way, so that the module it was on is still the first one not reported.
BATCH_RUNNER = """
import json, os, signal, subprocess, sys
prefix = json.loads(sys.argv[1])
worst = 0
for list_file in sys.argv[2:]:
    code = subprocess.call(prefix + [list_file])
    if code < 0:
        signal.signal(-code, signal.SIG_DFL)
        os.kill(os.getpid(), -code)
    if code not in (0, 1):
        sys.exit(code)
    worst = max(worst, code)
sys.exit(worst)
"""


def batch_files(out_dir: str, slot: int, modules: list[str], batch: int) -> list[str]:
    """Cut one process's modules into files of `batch`, each named `list-<slot>.txt`.

    The name is what the memory watchdog reads off a driver's command line,
    so every batch of a slot is the same process to it; the directory tells
    the files apart.
    """
    files = []
    for n, start in enumerate(range(0, len(modules), batch)):
        d = os.path.join(out_dir, "batches", str(n))
        os.makedirs(d, exist_ok=True)
        f = os.path.abspath(os.path.join(d, f"list-{slot}.txt"))
        with open(f, "w", encoding="utf-8") as fh:
            fh.write("\n".join(modules[start:start + batch]) + "\n")
        files.append(f)
    return files


def write_toy(pkg: str, toolchain: str) -> None:
    os.makedirs(os.path.join(pkg, "src", "Lib"), exist_ok=True)
    with open(os.path.join(pkg, "lean-toolchain"), "w", encoding="utf-8") as fh:
        fh.write(toolchain.strip() + "\n")
    with open(os.path.join(pkg, "lakefile.toml"), "w", encoding="utf-8") as fh:
        fh.write('name = "toy"\nsrcDir = "src"\n\n[[lean_lib]]\nname = "Lib"\nglobs = ["Lib.+"]\n')
    for module, source in TOY.items():
        with open(os.path.join(pkg, "src", *module.split(".")) + ".lean", "w", encoding="utf-8") as fh:
            fh.write(source)


def selftest(driver: str | None, driver_exe: str | None, toolchain: str, work: str) -> dict:
    """Build the toy package and replay it with the given driver.

    Returns what happened; `passed` only if the build accepted all three
    modules and the driver's verdicts are exactly `TOY_EXPECTED`. A driver that
    accepts `Lib.Cheat` checks nothing, and one that rejects the others cannot
    be read: neither may go on to replay the archive.
    """
    pkg = os.path.join(work, "toy")
    write_toy(pkg, toolchain)
    build = subprocess.run(["lake", "build", *TOY], cwd=pkg, capture_output=True, text=True)
    names = os.path.abspath(os.path.join(work, "toy-list.txt"))
    with open(names, "w", encoding="utf-8") as fh:
        fh.write("\n".join(TOY) + "\n")
    out = {"build_rc": build.returncode, "verdicts": {}, "messages": {}, "driver_rc": None, "passed": False}
    if build.returncode != 0:
        out["build_tail"] = (build.stdout + build.stderr)[-800:]
        return out
    run = subprocess.run(driver_command(driver, driver_exe, names), cwd=pkg, capture_output=True, text=True,
                         preexec_fn=_big_stack)
    out["driver_rc"] = run.returncode
    for line in run.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) >= 3 and parts[0] in ("OK", "FAIL"):
            out["verdicts"][parts[1]] = parts[0]
            if parts[0] == "FAIL":
                out["messages"][parts[1]] = (parts[3] if len(parts) > 3 else "")[:400]
    if not out["verdicts"]:
        out["driver_tail"] = (run.stdout + run.stderr)[-800:]
    out["passed"] = out["verdicts"] == TOY_EXPECTED and run.returncode == 1
    return out


def cmd_selftest(a) -> None:
    out = selftest(a.driver, a.driver_exe, a.toolchain, a.work)
    print("selftest: " + json.dumps(out, ensure_ascii=False))
    if not out["passed"]:
        print("the driver did not reject the planted fault and only it; nothing may be replayed with it")
        sys.exit(1)


# --------------------------------------------------------------------------
# run
# --------------------------------------------------------------------------

#: The archive builds with `--tstack=400000`, a 400 MB thread stack, so some of
#: its terms are deep. The driver replays on its main thread, whose stack is
#: bounded by the soft RLIMIT_STACK it starts with; give it a gigabyte.
STACK_BYTES = 1 << 30


def _big_stack() -> None:
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    want = STACK_BYTES if hard == resource.RLIM_INFINITY else min(STACK_BYTES, hard)
    resource.setrlimit(resource.RLIMIT_STACK, (want, hard))


def olean_path(lean_dir: str, module: str) -> str:
    return os.path.join(lean_dir, ".lake", "build", "lib", "lean", *module.split(".")) + ".olean"


def parse_driver_output(path: str):
    ok: dict[str, int] = {}
    failed: dict[str, str] = {}
    if not os.path.exists(path):
        return ok, failed
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 3 and parts[0] == "OK":
                ok[parts[1]] = int(parts[2])
            elif len(parts) >= 3 and parts[0] == "FAIL":
                failed[parts[1]] = (parts[3] if len(parts) > 3 else "")[:2000]
    return ok, failed


def driver_anon(path: str) -> dict[str, int]:
    """Anonymous memory, in MB, the driver held after each module it replayed.

    The fourth field of an `OK` line, where the driver prints one. It is what
    says whether the modules at the top of the graph can be replayed on a
    runner at all.
    """
    out: dict[str, int] = {}
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 4 and parts[0] == "OK" and parts[3].isdigit():
                out[parts[1]] = int(parts[3]) // 1024
    return out


def death_kind(code: int, procs: int, watchdog_kind: str | None) -> str:
    """How to record a driver process that died by itself: "killed" or "struck".

    "killed" is crowded out for memory and no strike against the module it
    was on. The watchdog's word settles it when it has one; without one, a
    SIGKILL while other drivers ran is taken as the watchdog's.
    """
    if watchdog_kind == "crowded":
        return "killed"
    if watchdog_kind is None and code == -9 and procs > 1:
        return "killed"
    return "struck"


def cmd_run(a) -> None:
    shard = json.load(open(a.shard))
    mods = shard["modules"]
    missing = [m for m in shard["need"] if not os.path.isfile(olean_path(a.lean_dir, m))]
    if missing:
        print(f"missing .olean for {len(missing)} needed modules, first: {missing[:5]}")
        sys.exit(1)
    os.makedirs(a.out, exist_ok=True)
    lists = [mods[i::a.procs] for i in range(a.procs)]
    procs = []
    deadline = time.time() + a.minutes * 60
    for i, lst in enumerate(lists):
        if not lst:
            continue
        lf = os.path.abspath(os.path.join(a.out, f"list-{i}.txt"))
        with open(lf, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lst) + "\n")
        out = open(os.path.join(a.out, f"driver-{i}.out"), "wb")
        err = open(os.path.join(a.out, f"driver-{i}.err"), "wb")
        if a.batch > 0:
            prefix = driver_command(a.driver, a.driver_exe, "")[:-1]
            cmd = [sys.executable, "-c", BATCH_RUNNER, json.dumps(prefix), *batch_files(a.out, i, lst, a.batch)]
        else:
            cmd = driver_command(a.driver, a.driver_exe, lf)
        p = subprocess.Popen(cmd, cwd=a.lean_dir, stdout=out, stderr=err, start_new_session=True,
                             preexec_fn=_big_stack)
        procs.append((i, lst, p))
    codes: dict[str, int | None] = {}
    timed_out = False
    for i, lst, p in procs:
        left = deadline - time.time()
        try:
            codes[str(i)] = p.wait(timeout=max(1.0, left))
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(p.pid, signal.SIGTERM)
            try:
                p.wait(timeout=30)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
            codes[str(i)] = None
    ok: dict[str, int] = {}
    failed: dict[str, str] = {}
    struck: list[str] = []
    killed: list[str] = []
    watchdog: dict[str, str] = {}
    if a.kills and os.path.exists(a.kills):
        with open(a.kills, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) >= 2:
                    watchdog[parts[0]] = parts[1]
    startup_errors: list[str] = []
    anon: dict[str, int] = {}
    for i, lst, p in procs:
        o, f = parse_driver_output(os.path.join(a.out, f"driver-{i}.out"))
        ok.update(o)
        failed.update(f)
        anon.update(driver_anon(os.path.join(a.out, f"driver-{i}.out")))
        # a driver that died by itself (not our deadline, not a clean 0 or 1)
        # was replaying the first module it never reported. Killed with
        # SIGKILL while others ran beside it, it was most likely the memory
        # watchdog's choice, which says the runner was full, not that this
        # module is at fault: that is "killed", and the chain answers with
        # fewer processes. Only a death alone, or by another signal, is a
        # strike against the module.
        if codes[str(i)] not in (0, 1, None):
            rest = [m for m in lst if m not in o and m not in f]
            if rest:
                # The watchdog's own table settles it when it names this
                # driver: crowded out is "killed", killed alone is a strike.
                if death_kind(codes[str(i)], a.procs, watchdog.get(f"run:list-{i}.txt")) == "killed":
                    killed.append(rest[0])
                else:
                    struck.append(rest[0])
        if codes[str(i)] is not None and not o and not f:
            with open(os.path.join(a.out, f"driver-{i}.err"), encoding="utf-8", errors="replace") as fh:
                startup_errors.append(fh.read()[-600:])
    rec = {"round": shard["round"], "shard": shard["shard"], "planned": len(mods),
           "ok": ok, "failed": failed, "struck": struck, "killed": killed, "exit_codes": codes,
           "timed_out": timed_out, "minutes": a.minutes, "procs": a.procs, "batch": a.batch,
           "startup_errors": startup_errors,
           # the modules after which a driver held the most anonymous memory, in MB
           "anon_top": sorted(anon.items(), key=lambda kv: -kv[1])[:20]}
    json.dump(rec, open(a.done, "w"))
    print(json.dumps({"planned": len(mods), "ok": len(ok), "failed": len(failed), "struck": struck,
                      "killed": killed, "anon_peak_mb": max(anon.values(), default=0),
                      "exit_codes": codes, "timed_out": timed_out,
                      "ms_sum": sum(ok.values()),
                      "mean_ms": round(sum(ok.values()) / max(1, len(ok)), 1)}))
    if startup_errors:
        print("a driver process reported nothing; its stderr ends:\n" + startup_errors[0])
        sys.exit(3)


# --------------------------------------------------------------------------
# merge
# --------------------------------------------------------------------------

def cmd_merge(a) -> None:
    g = json.load(open(a.dag))
    known = g["deps"]
    st = json.load(open(a.state))
    built = {m for m in st["where"] if m in known}
    cstate = load_check_state(a.check_state)
    before = len(cstate["checked"])
    rnd = {"round": a.round, "build_state": a.build_state_id, "shards": 0, "planned": 0, "ok": 0,
           "failed": 0, "struck": 0, "killed": 0, "ms_sum": 0, "timed_out_shards": 0}
    for f in sorted(glob.glob(os.path.join(a.done_dir, "**", "checkdone-*.json"), recursive=True)):
        rec = json.load(open(f))
        tag = f"c{rec['round']}-s{rec['shard']}"
        rnd["shards"] += 1
        rnd["planned"] += rec.get("planned", 0)
        for m, ms in rec.get("ok", {}).items():
            if m in built and m not in cstate["checked"]:
                cstate["checked"][m] = tag
                cstate["ms"][m] = ms
                rnd["ok"] += 1
                rnd["ms_sum"] += ms
                # a second attempt that passed: the module is replayed, and
                # what the first attempt said is kept beside it
                if m in cstate["failed"]:
                    cstate.setdefault("retried", {})[m] = cstate["failed"].pop(m)
                    rnd["retried_ok"] = rnd.get("retried_ok", 0) + 1
        for m, msg in rec.get("failed", {}).items():
            if m in known and m not in cstate["checked"]:
                cstate["failed"][m] = msg
                rnd["failed"] += 1
        for m in rec.get("struck", []):
            if m in known:
                cstate.setdefault("strikes", {})[m] = cstate.setdefault("strikes", {}).get(m, 0) + 1
                rnd["struck"] += 1
        rnd["killed"] += len(rec.get("killed", []))
        rnd["anon_top"] = sorted(rnd.get("anon_top", []) + [list(x) for x in rec.get("anon_top", [])],
                                 key=lambda kv: -kv[1])[:20]
        if rec.get("timed_out"):
            rnd["timed_out_shards"] += 1
    cstate["history"] = [h for h in cstate.get("history", []) if h["round"] != a.round] + [rnd]
    json.dump(cstate, open(a.out, "w"))
    out = {
        "round": a.round,
        "replayed_this_round": len(cstate["checked"]) - before,
        "replayed": len(cstate["checked"]),
        "built": len(built),
        "modules_total": len(known),
        "percent_of_archive": round(100.0 * len(cstate["checked"]) / len(known), 2),
        "left_in_this_build_state": len(built) - len(cstate["checked"]) - len(cstate["failed"]),
        "n_failed": len(cstate["failed"]),
        "failed": sorted(cstate["failed"])[:20],
        "n_retried_ok": len(cstate.get("retried", {})),
        "n_struck": len(cstate.get("strikes", {})),
        "mean_ms": round(rnd["ms_sum"] / max(1, rnd["ok"]), 1),
        "all_replayed": len(built) == len(known) and len(cstate["checked"]) == len(known),
        "killed_this_round": rnd["killed"],
        "shards_reported": rnd["shards"],
        "round_summary": rnd,
    }
    print(json.dumps(out))
    if a.github_output:
        with open(a.github_output, "a") as fh:
            for k in ("replayed_this_round", "replayed", "left_in_this_build_state", "n_failed",
                      "percent_of_archive", "all_replayed", "killed_this_round", "shards_reported"):
                v = out[k]
                fh.write(f"{k}={str(v).lower() if isinstance(v, bool) else v}\n")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("plan")
    s.add_argument("--dag", required=True); s.add_argument("--state", required=True)
    s.add_argument("--check-state"); s.add_argument("--round", type=int, required=True)
    s.add_argument("--shards", type=int, default=4)
    s.add_argument("--budget-s", type=float, required=True, help="process-seconds one shard is planned for")
    s.add_argument("--default-s", type=float, default=6.0, help="seconds per module before any is measured")
    s.add_argument("--max-strikes", type=int, default=2,
                   help="a module a replay process died on this many times is not planned again")
    s.add_argument("--retry-failed", nargs="*", metavar="TEXT",
                   help="plan only the failed modules whose message contains one of these texts")
    s.add_argument("--out", required=True)
    s.set_defaults(fn=cmd_plan)
    s = sub.add_parser("run")
    s.add_argument("--lean-dir", required=True); s.add_argument("--shard", required=True)
    s.add_argument("--minutes", type=float, required=True); s.add_argument("--procs", type=int, default=4)
    s.add_argument("--driver", help="a Lean file run with `lean --run`: ReplayDriver.lean")
    s.add_argument("--driver-exe", help="a compiled driver with the same output, in place of --driver")
    s.add_argument("--batch", type=int, default=0,
                   help="modules per driver process; 0 gives each process its whole list")
    s.add_argument("--out", required=True)
    s.add_argument("--done", required=True)
    s.add_argument("--kills", help="mem_watchdog.py's kills table: crowded is no strike, alone is one")
    s.set_defaults(fn=cmd_run)
    s = sub.add_parser("selftest")
    s.add_argument("--driver"); s.add_argument("--driver-exe")
    s.add_argument("--toolchain", required=True, help="the contents of the lean-toolchain file to build the toy with")
    s.add_argument("--work", required=True, help="an empty directory to build the toy package in")
    s.set_defaults(fn=cmd_selftest)
    s = sub.add_parser("merge")
    s.add_argument("--dag", required=True); s.add_argument("--state", required=True)
    s.add_argument("--check-state"); s.add_argument("--done-dir", required=True)
    s.add_argument("--round", type=int, required=True); s.add_argument("--build-state-id", default="")
    s.add_argument("--out", required=True); s.add_argument("--github-output")
    s.set_defaults(fn=cmd_merge)
    a = p.parse_args()
    a.fn(a)


if __name__ == "__main__":
    main()
