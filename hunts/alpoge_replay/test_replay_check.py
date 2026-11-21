"""The second pass: its planner, its record keeping, and the fault it exists for.

The last test is the reason this pass exists. It builds a three-module toy
package in which one theorem skips the kernel, shows that `lake build` and
`#print axioms` both accept it, and shows that the replay driver does not. It
needs a Lean toolchain and about two minutes, so it is marked slow and skips
where `lake` is absent.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import replay_check as rc  # noqa: E402
import replay_plan as rp  # noqa: E402


def chain(n: int) -> dict:
    return {f"M{i}": ([f"M{i - 1}"] if i else []) for i in range(n)}


def test_shards_take_the_lowest_levels_first_and_carry_their_imports() -> None:
    deps = chain(10)
    _, level = rp.topo_levels(deps)
    where = {m: "r0-s0" for m in deps}
    cstate = rc.load_check_state(None)
    shards, left, _ = rc.plan_check(deps, level, where, {"0": 7}, cstate, n_shards=2, budget_s=18, default_s=6)
    assert [s["modules"] for s in shards] == [["M0", "M1", "M2"], ["M3", "M4", "M5"]]
    assert left == 4
    # the second shard needs its own modules and everything below them
    assert shards[1]["need"] == [f"M{i}" for i in range(6)]
    assert shards[0]["fetch"] == {"7": ["chunk-r0-s0.tar.zst"]}


def test_replayed_failed_and_twice_struck_modules_are_not_planned_again() -> None:
    deps = chain(6)
    _, level = rp.topo_levels(deps)
    where = {m: "r0-s0" for m in deps}
    cstate = {"checked": {"M0": "c0-s0"}, "ms": {}, "failed": {"M1": "kernel"}, "strikes": {"M2": 2, "M3": 1}, "history": []}
    shards, left, _ = rc.plan_check(deps, level, where, {"0": 7}, cstate, n_shards=4, budget_s=600, default_s=6)
    assert [m for s in shards for m in s["modules"]] == ["M3", "M4", "M5"]
    assert left == 0
    # with more strikes allowed, the module struck twice is tried again
    shards, _, _ = rc.plan_check(deps, level, where, {"0": 7}, cstate, n_shards=4, budget_s=600, default_s=6,
                                 max_strikes=4)
    assert [m for s in shards for m in s["modules"]] == ["M2", "M3", "M4", "M5"]


def test_only_built_modules_are_planned() -> None:
    deps = chain(5)
    _, level = rp.topo_levels(deps)
    where = {"M0": "r0-s0", "M1": "r0-s0"}
    shards, _, _ = rc.plan_check(deps, level, where, {"0": 7}, rc.load_check_state(None), 4, 600, 6)
    assert [m for s in shards for m in s["modules"]] == ["M0", "M1"]


def test_a_bundle_missing_from_the_state_stops_the_plan() -> None:
    deps = chain(2)
    _, level = rp.topo_levels(deps)
    with pytest.raises(SystemExit, match="no bundle"):
        rc.plan_check(deps, level, {"M0": "r3-s1", "M1": "r3-s1"}, {"0": 7}, rc.load_check_state(None), 1, 600, 6)


def test_driver_output_is_read_line_by_line(tmp_path: Path) -> None:
    out = tmp_path / "driver-0.out"
    out.write_text(
        "OK\tLib.A\t412\n"
        "FAIL\tLib.Cheat\t776\twhile replaying declaration 'bad': | (kernel) declaration type mismatch\n"
        "OK\tLib.Sub.C₂\t3\n"
        "a stray line\n",
        encoding="utf-8",
    )
    ok, failed = rc.parse_driver_output(str(out))
    assert ok == {"Lib.A": 412, "Lib.Sub.C₂": 3}
    assert list(failed) == ["Lib.Cheat"] and "type mismatch" in failed["Lib.Cheat"]
    assert rc.driver_anon(str(out)) == {}          # the first driver printed no memory

    # the driver now adds the anonymous memory it holds, in kB, to an OK line
    out.write_text("OK\tLib.A\t412\t540672\nOK\tLib.B\t90\t2097152\nFAIL\tLib.Cheat\t776\tsome message\n"
                   "OK\tLib.Old\t5\n", encoding="utf-8")
    ok, failed = rc.parse_driver_output(str(out))
    assert ok == {"Lib.A": 412, "Lib.B": 90, "Lib.Old": 5} and list(failed) == ["Lib.Cheat"]
    assert rc.driver_anon(str(out)) == {"Lib.A": 528, "Lib.B": 2048}


def test_merge_counts_replays_failures_and_strikes(tmp_path: Path) -> None:
    deps = chain(4)
    (tmp_path / "dag.json").write_text(json.dumps({"deps": deps, "size": {m: 1 for m in deps}}))
    (tmp_path / "state.json").write_text(json.dumps({"where": {m: "r0-s0" for m in deps}, "bundles": {"0": 7}}))
    d = tmp_path / "in" / "x"
    d.mkdir(parents=True)
    (d / "checkdone-c0-s0.json").write_text(json.dumps({
        "round": 0, "shard": 0, "planned": 4, "ok": {"M0": 300, "M1": 500, "Unknown.Module": 1},
        "failed": {"M2": "(kernel) declaration type mismatch"}, "struck": ["M3"], "timed_out": True}))
    out = tmp_path / "checkstate.json"
    sys.argv = ["replay_check.py", "merge", "--dag", str(tmp_path / "dag.json"), "--state", str(tmp_path / "state.json"),
                "--done-dir", str(tmp_path / "in"), "--round", "0", "--build-state-id", "99", "--out", str(out)]
    rc.main()
    st = json.loads(out.read_text())
    assert st["checked"] == {"M0": "c0-s0", "M1": "c0-s0"}
    assert st["failed"] == {"M2": "(kernel) declaration type mismatch"}
    assert st["strikes"] == {"M3": 1}
    assert st["history"][0]["ok"] == 2 and st["history"][0]["timed_out_shards"] == 1


# ---------------------------------------------------------------------------
# the planted fault
# ---------------------------------------------------------------------------

def test_the_driver_is_one_lean_file_or_one_program_never_both_or_neither() -> None:
    assert rc.driver_command("/h/ReplayDriver.lean", None, "/o/list-0.txt") == [
        "lake", "env", "lean", "--run", "/h/ReplayDriver.lean", "/o/list-0.txt"]
    assert rc.driver_command(None, "/b/l4ldriver", "/o/list-0.txt") == ["lake", "env", "/b/l4ldriver", "/o/list-0.txt"]
    for both_or_neither in (("/h/ReplayDriver.lean", "/b/l4ldriver"), (None, None), ("", "")):
        with pytest.raises(SystemExit):
            rc.driver_command(*both_or_neither, "/o/list-0.txt")


def _stub_lake_and_driver(tmp_path: Path, monkeypatch, lines: list[str], code: int) -> str:
    """A `lake` that builds nothing and runs what follows `env`, and a driver that prints `lines`."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    lake = bin_dir / "lake"
    lake.write_text('#!/bin/sh\nif [ "$1" = build ]; then exit 0; fi\nshift\nexec "$@"\n')
    lake.chmod(0o755)
    driver = bin_dir / "driver"
    body = "\n".join(f"printf '%s\\n' '{line}'" for line in lines)
    driver.write_text(f"#!/bin/sh\n{body}\nexit {code}\n")
    driver.chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}{os.pathsep}{os.environ['PATH']}")
    return str(driver)


def test_the_selftest_passes_only_a_driver_that_rejects_the_fault_and_nothing_else(tmp_path: Path, monkeypatch) -> None:
    good = ["OK\tLib.Honest\t3\t100", "FAIL\tLib.Cheat\t4\t(kernel) declaration type mismatch", "OK\tLib.UsesCheat\t2\t100"]
    cases = {
        "rejects the fault and only it": (good, 1, True),
        # a checker that checks nothing: the fault goes through
        "accepts the fault": ([good[0], "OK\tLib.Cheat\t4\t100", good[2]], 0, False),
        # one that rejects an honest module cannot be read
        "rejects an honest module": (["FAIL\tLib.Honest\t3\tno", good[1], good[2]], 1, False),
        # one that stops before the end said nothing about the rest
        "says nothing about the last module": (good[:2], 1, False),
        # the lines are right and the exit code says every module replayed
        "exits 0 after a FAIL": (good, 0, False),
        "prints nothing": ([], 139, False),
    }
    for n, (name, (lines, code, want)) in enumerate(cases.items()):
        work = tmp_path / f"case{n}"
        work.mkdir()
        with monkeypatch.context() as m:
            driver = _stub_lake_and_driver(work, m, lines, code)
            got = rc.selftest(None, driver, "leanprover/lean4:v4.33.1", str(work / "w"))
        assert got["passed"] is want, (name, got)
    # the toy it writes is the three modules, the fault in the middle
    assert (tmp_path / "case0" / "w" / "toy" / "src" / "Lib" / "Cheat.lean").read_text() == rc.CHEAT
    assert list(rc.TOY) == ["Lib.Honest", "Lib.Cheat", "Lib.UsesCheat"]


def test_a_toy_package_that_does_not_build_fails_the_selftest(tmp_path: Path, monkeypatch) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    (bin_dir / "lake").write_text("#!/bin/sh\necho 'error: build failed'\nexit 1\n")
    (bin_dir / "lake").chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}{os.pathsep}{os.environ['PATH']}")
    got = rc.selftest("/h/ReplayDriver.lean", None, "leanprover/lean4:v4.33.1", str(tmp_path / "w"))
    assert got["passed"] is False and got["build_rc"] == 1 and "build failed" in got["build_tail"]


def _run_shard(tmp_path: Path, monkeypatch, modules: list[str], batch: int, procs: int = 1) -> tuple[dict, Path]:
    """`replay_check.py run` on a stub: a `lake` that runs what follows `env`, and a driver that
    answers OK for every module of its list, FAIL for one named Bad, and dies of SIGSEGV on Crash."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(parents=True)
    lake = bin_dir / "lake"
    lake.write_text('#!/bin/sh\nshift\nexec "$@"\n')
    lake.chmod(0o755)
    driver = bin_dir / "driver"
    driver.write_text(
        "#!/bin/sh\ncode=0\necho \"$$ $1\" >> \"$(dirname \"$0\")/started\"\n"
        "while read m; do\n"
        "  case \"$m\" in\n"
        "    Crash) kill -SEGV $$ ;;\n"
        "    Bad) printf 'FAIL\\t%s\\t1\\tno\\n' \"$m\"; code=1 ;;\n"
        "    *) printf 'OK\\t%s\\t1\\t2048\\n' \"$m\" ;;\n"
        "  esac\ndone < \"$1\"\nexit $code\n")
    driver.chmod(0o755)
    lean_dir = tmp_path / "lean"
    for m in modules:
        f = lean_dir / ".lake" / "build" / "lib" / "lean" / (m + ".olean")
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_bytes(b"")
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"round": 0, "shard": 0, "modules": modules, "need": modules}))
    monkeypatch.setenv("PATH", f"{bin_dir}{os.pathsep}{os.environ['PATH']}")
    done = tmp_path / "done.json"
    proc = subprocess.run([sys.executable, str(HERE / "replay_check.py"), "run", "--lean-dir", str(lean_dir),
                           "--shard", str(shard), "--minutes", "1", "--procs", str(procs), "--batch", str(batch),
                           "--driver-exe", str(driver), "--out", str(tmp_path / "out"), "--done", str(done)],
                          capture_output=True, text=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    return json.loads(done.read_text()), bin_dir / "started"


def test_a_driver_given_a_few_modules_at_a_time_replays_them_all_in_fresh_processes(tmp_path: Path, monkeypatch) -> None:
    modules = [f"M{i}" for i in range(7)]
    whole, started = _run_shard(tmp_path / "whole", monkeypatch, modules, batch=0)
    assert sorted(whole["ok"]) == modules and len(started.read_text().splitlines()) == 1
    rec, started = _run_shard(tmp_path / "batched", monkeypatch, modules, batch=3)
    assert sorted(rec["ok"]) == modules and rec["failed"] == {} and rec["struck"] == [] and rec["batch"] == 3
    runs = [line.split() for line in started.read_text().splitlines()]
    # three processes, three different pids, and every list file is named for the slot
    assert len(runs) == 3 and len({pid for pid, _ in runs}) == 3
    assert {os.path.basename(f) for _, f in runs} == {"list-0.txt"}
    assert rec["exit_codes"] == {"0": 0}


def test_a_rejection_does_not_stop_the_batches_and_a_crash_does(tmp_path: Path, monkeypatch) -> None:
    rec, started = _run_shard(tmp_path / "bad", monkeypatch, ["A", "Bad", "C", "D", "E"], batch=2)
    assert rec["failed"] == {"Bad": "no"} and sorted(rec["ok"]) == ["A", "C", "D", "E"]
    assert rec["exit_codes"] == {"0": 1} and rec["struck"] == []
    rec, started = _run_shard(tmp_path / "crash", monkeypatch, ["A", "B", "Crash", "D", "E", "F"], batch=2)
    # the slot ends where the driver died: the module it was on is the strike, the rest wait
    assert sorted(rec["ok"]) == ["A", "B"] and rec["struck"] == ["Crash"]
    assert rec["exit_codes"] == {"0": -11}
    assert len(started.read_text().splitlines()) == 2


CHEAT = rc.CHEAT


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lake") is None, reason="needs a Lean toolchain on PATH")
def test_a_theorem_that_skipped_the_kernel_builds_clean_and_fails_the_replay(tmp_path: Path) -> None:
    pkg = tmp_path / "toy"
    (pkg / "src" / "Lib").mkdir(parents=True)
    (pkg / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    (pkg / "lakefile.toml").write_text('name = "toy"\nsrcDir = "src"\n\n[[lean_lib]]\nname = "Lib"\nglobs = ["Lib.+"]\n')
    (pkg / "src" / "Lib" / "Honest.lean").write_text("theorem honest : 1 + 1 = 2 := rfl\n")
    (pkg / "src" / "Lib" / "Cheat.lean").write_text(CHEAT)
    (pkg / "src" / "Lib" / "UsesCheat.lean").write_text(
        "import Lib.Cheat\ntheorem worse : False := absurd bad (by decide)\n")

    build = subprocess.run(["lake", "build", "Lib.Honest", "Lib.UsesCheat"], cwd=pkg, capture_output=True, text=True)
    assert build.returncode == 0, build.stdout + build.stderr
    assert "sorry" not in build.stdout

    probe = tmp_path / "probe.lean"
    probe.write_text("import Lib.UsesCheat\n#print axioms worse\n")
    axioms = subprocess.run(["lake", "env", "lean", str(probe)], cwd=pkg, capture_output=True, text=True)
    # the first pass's two checks both accept a proof of False
    assert "does not depend on any axioms" in axioms.stdout

    names = tmp_path / "list.txt"
    names.write_text("Lib.Honest\nLib.Cheat\nLib.UsesCheat\n")
    replay = subprocess.run(["lake", "env", "lean", "--run", str(HERE / "ReplayDriver.lean"), str(names)],
                            cwd=pkg, capture_output=True, text=True)
    lines = dict(line.split("\t")[1::-1] for line in replay.stdout.splitlines() if "\t" in line)
    assert lines == {"Lib.Honest": "OK", "Lib.Cheat": "FAIL", "Lib.UsesCheat": "OK"}, replay.stdout
    assert "declaration type mismatch" in replay.stdout
    assert replay.returncode == 1


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lake") is None, reason="needs a Lean toolchain on PATH")
def test_the_selftest_the_workflow_runs_passes_with_the_kernel_driver(tmp_path: Path) -> None:
    got = rc.selftest(str(HERE / "ReplayDriver.lean"), None, "leanprover/lean4:v4.33.1", str(tmp_path / "w"))
    assert got["passed"] is True, got
    assert got["verdicts"] == rc.TOY_EXPECTED and "declaration type mismatch" in got["messages"]["Lib.Cheat"]


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lake") is None, reason="needs a Lean toolchain on PATH")
def test_the_cone_counts_what_a_theorem_uses_and_leaves_out_what_it_does_not(tmp_path: Path) -> None:
    """Five modules, one theorem that uses two of them."""
    pkg = tmp_path / "toy"
    (pkg / "src" / "Lib").mkdir(parents=True)
    (pkg / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    (pkg / "lakefile.toml").write_text('name = "toy"\nsrcDir = "src"\n\n[[lean_lib]]\nname = "Lib"\nglobs = ["Lib.+"]\n')
    (pkg / "src" / "Lib" / "Used.lean").write_text("theorem used : 2 + 2 = 4 := rfl\n")
    (pkg / "src" / "Lib" / "Unused.lean").write_text("theorem unused : 3 + 3 = 6 := rfl\n")
    (pkg / "src" / "Lib" / "AlsoUnused.lean").write_text("import Lib.Unused\ntheorem alsoUnused : True := trivial\n")
    (pkg / "src" / "Lib" / "Top.lean").write_text(
        "import Lib.Used\nimport Lib.AlsoUnused\ntheorem top : 2 + 2 = 4 := used\n")
    assert subprocess.run(["lake", "build", "Lib.Top"], cwd=pkg, capture_output=True, text=True).returncode == 0

    tool = tmp_path / "cone"
    tool.mkdir()
    (tool / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    (tool / "lakefile.toml").write_text(
        'name = "cone"\n\n[[lean_exe]]\nname = "cone"\nroot = "Cone"\nsupportInterpreter = true\n')
    shutil.copy(HERE / "Cone.lean", tool / "Cone.lean")
    built = subprocess.run(["lake", "build", "cone"], cwd=tool, capture_output=True, text=True)
    assert built.returncode == 0, built.stdout + built.stderr

    out = tmp_path / "cone.json"
    run = subprocess.run(["lake", "env", str(tool / ".lake" / "build" / "bin" / "cone"), "Lib.Top", "top", "Lib",
                          str(out), str(tmp_path)], cwd=pkg, capture_output=True, text=True)
    assert run.returncode == 0, run.stdout + run.stderr
    (r,) = json.loads(out.read_text())
    assert r["archive_modules"] == 4 and r["archive_modules_in_cone"] == 2
    assert r["archive_declarations"] == 4 and r["archive_declarations_in_cone"] == 2
    assert r["names_not_found"] == []
    assert (tmp_path / "cone-modules-first-root.txt").read_text().split() == ["Lib.Top", "Lib.Used"]


FORGE = """import Lean
open Lean Elab Command in
@[command_elab Lean.Parser.Command.printAxioms] def forgedAxioms : CommandElab := fun stx => do
  logInfo m!"'{stx[2].getId}' depends on axioms: [propext, Classical.choice, Quot.sound]"

def Claim : Prop := 2 + 2 = 5
def Weak : Prop := True
notation "Claim" => Weak
"""

TOP = """import Lib.Forge
axiom convenient : 2 + 2 = 5
theorem viaAxiom : 2 + 2 = 5 := convenient
theorem viaSorry : 2 + 2 = 5 := sorry
theorem looksLikeClaim : Claim := trivial
theorem clean : 2 + 2 = 4 := rfl
"""


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("lake") is None, reason="needs a Lean toolchain on PATH")
def test_the_cone_reads_axioms_and_statements_from_the_stored_terms_where_the_environment_lies(tmp_path: Path) -> None:
    """A module can replace `#print axioms` and can make a name in a statement mean another.

    `Lib.Forge` does both: its command prints the three standard axioms for
    anything, and its notation turns the text `Claim` into `Weak`, which is
    `True`. The verdict's printout and a reading of the source are then both
    wrong about `Lib.Top`. The cone runs no command and no notation of the
    modules it loads, and reports what is stored.
    """
    pkg = tmp_path / "toy"
    (pkg / "src" / "Lib").mkdir(parents=True)
    (pkg / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    (pkg / "lakefile.toml").write_text('name = "toy"\nsrcDir = "src"\n\n[[lean_lib]]\nname = "Lib"\nglobs = ["Lib.+"]\n')
    (pkg / "src" / "Lib" / "Forge.lean").write_text(FORGE)
    (pkg / "src" / "Lib" / "Top.lean").write_text(TOP)
    build = subprocess.run(["lake", "build", "Lib.Top"], cwd=pkg, capture_output=True, text=True)
    assert build.returncode == 0, build.stdout + build.stderr

    probe = tmp_path / "probe.lean"
    probe.write_text("import Lib.Top\n#print axioms viaAxiom\n#print axioms viaSorry\n")
    printed = subprocess.run(["lake", "env", "lean", str(probe)], cwd=pkg, capture_output=True, text=True)
    # the printout the verdict's guard reads, forged for both
    assert "'viaAxiom' depends on axioms: [propext, Classical.choice, Quot.sound]" in printed.stdout
    assert "'viaSorry' depends on axioms: [propext, Classical.choice, Quot.sound]" in printed.stdout
    assert "sorryAx" not in printed.stdout and "convenient" not in printed.stdout

    tool = tmp_path / "cone"
    tool.mkdir()
    (tool / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
    (tool / "lakefile.toml").write_text(
        'name = "cone"\n\n[[lean_exe]]\nname = "cone"\nroot = "Cone"\nsupportInterpreter = true\n')
    shutil.copy(HERE / "Cone.lean", tool / "Cone.lean")
    built = subprocess.run(["lake", "build", "cone"], cwd=tool, capture_output=True, text=True)
    assert built.returncode == 0, built.stdout + built.stderr

    out = tmp_path / "cone.json"
    run = subprocess.run(["lake", "env", str(tool / ".lake" / "build" / "bin" / "cone"), "Lib.Top",
                          "clean,viaAxiom,viaSorry,looksLikeClaim,noSuchTheorem", "Lib", str(out)],
                         cwd=pkg, capture_output=True, text=True)
    assert run.returncode == 0, run.stdout + run.stderr
    first, every = json.loads(out.read_text())
    assert first["roots"] == ["clean"] and first["axioms"] == []
    assert every["axioms"] == ["convenient", "sorryAx"]
    assert every["names_not_found"] == ["noSuchTheorem"]
    stored = {r["name"]: r for r in every["roots_as_stored"]}
    assert stored["noSuchTheorem"] == {"name": "noSuchTheorem", "found": False}
    assert stored["clean"]["kind"] == "theorem" and stored["clean"]["defined_in"] == "Lib.Top"
    assert "statement_is_the_constant" not in stored["clean"]
    # the source says `Claim`; the theorem stored is about `Weak`
    claim = stored["looksLikeClaim"]
    assert claim["statement"] == "Weak" and claim["statement_is_the_constant"] == "Weak"
    assert claim["statement_defined_in"] == "Lib.Forge" and claim["statement_unfolds_to"] == "True"


@pytest.mark.slow
def test_the_watchdog_kills_the_named_process_and_only_when_memory_is_low(tmp_path: Path) -> None:
    """A guard that cannot fire is worse than none: make it fire, and make it hold."""
    import os
    import time

    fake = tmp_path / "lean"
    shutil.copy("/bin/sleep", fake)
    with open("/proc/meminfo") as fh:
        avail = next(int(line.split()[1]) // 1024 for line in fh if line.startswith("MemAvailable"))

    def run(floor: int) -> tuple[bool, str]:
        victim = subprocess.Popen([str(fake), "60"])
        time.sleep(0.3)
        log = tmp_path / f"mem-{floor}.log"
        subprocess.run([sys.executable, str(HERE / "mem_watchdog.py"), "--name", "lean", "--floor-mb", str(floor),
                        "--log", str(log), "--log-every", "1", "--interval", "0.3", "--max-seconds", "3"], check=True)
        alive = victim.poll() is None
        victim.kill()
        victim.wait()
        return alive, log.read_text()

    alive, text = run(avail + 100_000)   # floor far above what is available: must kill
    assert not alive and " KILL " in text
    alive, text = run(1)                 # floor of 1 MB: must not kill
    assert alive and " KILL " not in text and "anon_mb=" in text


def test_a_driver_death_is_a_strike_unless_it_was_crowded_out() -> None:
    assert rc.death_kind(-9, 4, "crowded") == "killed"
    assert rc.death_kind(-9, 4, "alone") == "struck"      # alone and still too big: the module's own doing
    assert rc.death_kind(-9, 4, None) == "killed"         # no table: a SIGKILL beside others is the watchdog's
    assert rc.death_kind(-9, 1, None) == "struck"
    assert rc.death_kind(-11, 4, None) == "struck"        # a segfault is never the watchdog's
    assert rc.death_kind(-9, 1, "crowded") == "killed"


def test_the_replay_plan_leaves_stranded_modules_for_later_and_does_not_refuse(tmp_path: Path) -> None:
    deps = {"A": [], "E": ["A"], "X": ["E"], "B": ["A"]}
    (tmp_path / "dag.json").write_text(json.dumps({"deps": deps, "size": {m: 1 for m in deps}}))
    (tmp_path / "state.json").write_text(json.dumps({
        "where": {"A": "r0-s0", "X": "r1-s1", "B": "r1-s0"}, "bundles": {"0": 5, "1": 6}}))
    out = tmp_path / "plan"
    sys.argv = ["replay_check.py", "plan", "--dag", str(tmp_path / "dag.json"), "--state", str(tmp_path / "state.json"),
                "--round", "0", "--shards", "2", "--budget-s", "100", "--out", str(out)]
    rc.main()
    planned = [m for f in sorted(out.glob("shard-*.json")) for m in json.loads(f.read_text())["modules"]]
    assert sorted(planned) == ["A", "B"]          # X is built but stands on E, which no chunk holds

