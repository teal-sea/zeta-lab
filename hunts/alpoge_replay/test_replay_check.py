"""The second pass: its planner, its record keeping, and the fault it exists for.

The last test is the reason this pass exists. It builds a three-module toy
package in which one theorem skips the kernel, shows that `lake build` and
`#print axioms` both accept it, and shows that the replay driver does not. It
needs a Lean toolchain and about two minutes, so it is marked slow and skips
where `lake` is absent.
"""

from __future__ import annotations

import json
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

CHEAT = """import Lean
open Lean Elab Tactic

/-- Close any goal with a term of the wrong type, without asking the elaborator. -/
elab "cheat" : tactic => do
  let g ← getMainGoal
  g.assign (mkConst ``True.intro)

set_option debug.skipKernelTC true in
theorem bad : (1 : Nat) = 2 := by cheat
"""


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
