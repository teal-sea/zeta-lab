"""Invariants of the replay planner, on synthetic import graphs.

The planner decides which modules may be elaborated on which runner. If it
ever puts a module on a runner that lacks one of its imports, Lake rebuilds
that import there, silently, and the round's accounting is wrong. These tests
pin the properties that make a round safe, and plant the faults that would
break them so the checks are seen to fail.
"""

from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import replay_plan as rp  # noqa: E402
import replay_shard as rs  # noqa: E402


def random_dag(n: int, seed: int, fan: int = 4) -> tuple[dict, dict]:
    rng = random.Random(seed)
    names = [f"M.L{i // 50}.F{i}" for i in range(n)]
    deps, size = {}, {}
    for i, m in enumerate(names):
        k = rng.randint(0, min(fan, i))
        lo = max(0, i - 400)
        deps[m] = sorted({names[rng.randrange(lo, i)] for _ in range(k)}) if i else []
        size[m] = rng.randint(200, 30000)
    return deps, size


def run_rounds(deps, size, shards=5, budget=600.0, max_modules=10**6):
    order, _ = rp.topo_levels(deps)
    height = rp.heights(deps, order)
    cost = rp.cost_model(size, 4.0, 0.5)
    done: set[str] = set()
    rounds = []
    while len(done) < len(order):
        plan, _, loads = rp.plan_round(deps, cost, order, height, done, shards, budget, max_modules)
        assert plan, "planner stalled with modules left"
        rounds.append((plan, loads, set(done)))
        for sh in plan:
            done.update(sh)
        assert len(rounds) < 10_000
    return rounds, cost


@pytest.mark.parametrize("seed", [1, 2, 3])
def test_every_round_is_safe_and_the_campaign_finishes(seed: int) -> None:
    deps, size = random_dag(3000, seed)
    rounds, cost = run_rounds(deps, size)
    seen: set[str] = set()
    for plan, loads, done in rounds:
        owner = {}
        for i, sh in enumerate(plan):
            for m in sh:
                assert m not in owner and m not in done and m not in seen, "module planned twice"
                owner[m] = i
        for i, sh in enumerate(plan):
            for m in sh:
                for d in deps[m]:
                    # the property that makes shards independent
                    assert d in done or owner.get(d) == i, f"{m} needs {d}, which is elsewhere"
            assert sum(cost[m] for m in sh) <= 600.0 + 1e-6
        seen.update(owner)
    assert seen == set(deps)


def test_the_plan_is_deterministic() -> None:
    deps, size = random_dag(2000, 7)
    a, _ = run_rounds(deps, size)
    b, _ = run_rounds(deps, size)
    assert [p for p, _, _ in a] == [p for p, _, _ in b]


def test_a_module_over_budget_alone_is_never_planned_and_is_seen_as_a_stall() -> None:
    deps = {"A": [], "B": ["A"]}
    size = {"A": 10_000_000, "B": 100}
    order, _ = rp.topo_levels(deps)
    cost = rp.cost_model(size, 4.0, 0.5)
    plan, waiting, _ = rp.plan_round(deps, cost, order, rp.heights(deps, order), set(), 4, 600.0, 10**6)
    assert plan == [] and waiting == 2


def test_built_closure_refuses_a_plan_that_is_not_closed() -> None:
    """The planted fault: a shard whose import was never built."""
    deps = {"A": [], "B": ["A"], "C": ["B"]}
    with pytest.raises(SystemExit, match="not closed"):
        rp.built_closure(["C"], deps, done={"A"})
    assert rp.built_closure(["C"], deps, done={"A", "B"}) == ["A", "B"]
    assert rp.built_closure(["B", "C"], deps, done={"A"}) == ["A"]


def test_sinks_are_the_modules_nothing_in_the_shard_imports() -> None:
    deps = {"A": [], "B": ["A"], "C": ["A"], "D": ["B", "C"], "E": []}
    assert rp.sinks_of(["A", "B", "C", "D", "E"], deps) == ["D", "E"]


def test_an_import_cycle_is_an_error_not_a_hang() -> None:
    with pytest.raises(SystemExit, match="cycle"):
        rp.topo_levels({"A": ["B"], "B": ["A"]})


@pytest.mark.parametrize(
    "text, expected",
    [
        ("import A.B\nimport C\n\ntheorem t : True := trivial\n", ["A.B", "C"]),
        ("/- header\nimport Fake.One\n-/\nimport Real.One -- import Fake.Two\nimport Real.Two\n", ["Real.One", "Real.Two"]),
        ("-- import Fake\n\nimport A\n/- nested /- import Fake -/ still comment -/\nimport B\ndef x := 1\nimport Late\n", ["A", "B"]),
        ("module\npublic import A\nimport all B\nmeta import C\n", ["A", "B", "C"]),
        ("import A.«B'»\nimport A.C₂\n", ["A.B'", "A.C₂"]),
        ("theorem t : True := trivial\nimport A\n", []),
        ("", []),
    ],
)
def test_header_imports_reads_the_header_and_nothing_else(text: str, expected: list[str]) -> None:
    assert rp.header_imports(text) == expected


def test_a_failed_module_blocks_everything_above_it(tmp_path: Path) -> None:
    deps = {"A": [], "B": ["A"], "C": ["B"], "D": []}
    size = {m: 1000 for m in deps}
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": deps, "size": size}))
    state = tmp_path / "state.json"
    state.write_text(json.dumps({"where": {"A": "r0-s0"}, "seconds": {}, "bundles": {"0": 11},
                                 "failed": {"B": {"exit": 1, "excerpt": []}}, "crashed": {}}))
    out = tmp_path / "plan"
    sys.argv = ["replay_plan.py", "plan", "--dag", str(dag), "--state", str(state),
                "--round", "1", "--shards", "2", "--budget-s", "600", "--out", str(out)]
    rp.main()
    summary = json.loads((out / "plan.json").read_text())
    planned = [m for i in range(summary["n_shards"])
               for m in json.loads((out / f"shard-{i}.json").read_text())["modules"]]
    assert planned == ["D"], "only the module that does not sit above the failure is plannable"
    assert summary["blocked"] == 2


def test_merge_counts_only_known_modules_and_keeps_the_bundle_id(tmp_path: Path) -> None:
    deps = {"A": [], "B": ["A"]}
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": deps, "size": {"A": 10, "B": 20}}))
    d = tmp_path / "in" / "x"
    d.mkdir(parents=True)
    (d / "done-r0-s0.json").write_text(json.dumps({
        "chunk": "r0-s0", "planned": 2, "built": ["A", "Not.In.The.Graph"],
        "seconds": {"A": 1.5}, "failed": {}, "crashed": {"B": {"exit": 137, "excerpt": []}},
        "raw_output_bytes": 100, "olean_bytes": 60, "build_status": {"timed_out": True}}))
    out = tmp_path / "state.json"
    sys.argv = ["replay_shard.py", "merge", "--dag", str(dag), "--done-dir", str(tmp_path / "in"),
                "--round", "0", "--out", str(out), "--bundle-id", "4242"]
    rs.main()
    st = json.loads(out.read_text())
    assert st["where"] == {"A": "r0-s0"}
    assert st["bundles"] == {"0": 4242}
    assert st["crashed"] == {"B": 1}
    assert st["history"][0]["timed_out_shards"] == 1
    assert st["history"][0]["crashed_this_round"] == 1


def test_the_build_log_parser_reads_lake_s_own_lines(tmp_path: Path) -> None:
    log = tmp_path / "build.log"
    log.write_text(
        "✔ [3/9] Built Lib.A (198ms)\n"
        "✔ [4/9] Built Lib.Sub.C₂ (2.5s)\n"
        "✖ [5/9] Building Lib.B (181ms)\n"
        "trace: .> lean ...\n"
        "error: src/Lib/B.lean:2:0: Not a definitional equality\n"
        "error: Lean exited with code 1\n"
        "✖ [6/9] Building Lib.Big (90s)\n"
        "error: Lean exited with code 137\n"
        "warning: src/Lib/W.lean:1:0: declaration uses 'sorry'\n"
        "✔ [7/9] Built Lib.D (1.2m)\n"
        "⚠ [8/9] Built Lib.Warned (3.0s)\n"
        "warning: src/Lib/Warned.lean:4:2: unused variable\n"
        "ℹ [9/9] Built Lib.Info (4.0s)\n",
        encoding="utf-8",
    )
    seconds, failed, sorry_lines = rs.parse_log(str(log))
    # the pilot (run 44775351495) lost 200 of 491 timings by matching the tick only
    assert seconds == {"Lib.A": pytest.approx(0.198), "Lib.Sub.C₂": 2.5, "Lib.D": pytest.approx(72.0),
                       "Lib.Warned": 3.0, "Lib.Info": 4.0}
    assert failed["Lib.B"]["exit"] == 1 and "Not a definitional equality" in failed["Lib.B"]["excerpt"][0]
    assert failed["Lib.Big"]["exit"] == 137
    assert sorry_lines == 1


def test_the_setup_file_is_not_packed(tmp_path: Path) -> None:
    lib = tmp_path / ".lake" / "build" / "lib" / "lean" / "A"
    ir = tmp_path / ".lake" / "build" / "ir" / "A"
    lib.mkdir(parents=True)
    ir.mkdir(parents=True)
    for d, names in ((lib, ["B.olean", "B.olean.hash", "B.ilean", "B.ilean.hash", "B.trace"]),
                     (ir, ["B.c", "B.c.hash", "B.setup.json"])):
        for n in names:
            (d / n).write_text("{}")
    (lib / "B").mkdir()  # a module that is also a directory
    (lib / "B" / "C.olean").write_text("x")
    (lib / "BX.olean").write_text("x")  # a sibling sharing the prefix
    got = rs.output_files(str(tmp_path), "A.B")
    assert [Path(f).name for f in got] == ["B.c", "B.c.hash", "B.ilean", "B.ilean.hash", "B.olean",
                                           "B.olean.hash", "B.trace"]
