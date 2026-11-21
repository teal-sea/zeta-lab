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


def test_pack_tells_a_crowded_kill_from_a_crash_and_forgets_a_failure_that_was_later_built(tmp_path: Path) -> None:
    lean = tmp_path / "lean"
    lib = lean / ".lake" / "build" / "lib" / "lean" / "Lib"
    lib.mkdir(parents=True)
    for built in ("Ok", "Late"):
        (lib / f"{built}.olean").write_text("x")
        (lib / f"{built}.trace").write_text(json.dumps({"outputs": {}}))
    mods = ["Lib.Ok", "Lib.Late", "Lib.Crowded", "Lib.Alone", "Lib.Both", "Lib.Segv", "Lib.Wrong"]
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"round": 7, "shard": 3, "modules": mods, "sinks": mods}))
    log = tmp_path / "build.log"
    log.write_text(
        "✔ [1/9] Built Lib.Ok (1.0s)\n"
        "✖ [2/9] Building Lib.Late (30s)\nerror: Lean exited with code 137\n"
        "✖ [3/9] Building Lib.Crowded (40s)\nerror: Lean exited with code 137\n"
        "✖ [4/9] Building Lib.Alone (900s)\nerror: Lean exited with code 137\n"
        "✖ [5/9] Building Lib.Both (50s)\nerror: Lean exited with code 137\n"
        "✖ [6/9] Building Lib.Segv (2s)\nerror: Lean exited with code 139\n"
        "✖ [7/9] Building Lib.Wrong (2s)\nerror: Lib/Wrong.lean:1:0: type mismatch\nerror: Lean exited with code 1\n"
        "=== batch 1 ===\n"
        "✔ [2/9] Built Lib.Late (33s)\n",
        encoding="utf-8",
    )
    kills = tmp_path / "mem.log.kills.tsv"
    kills.write_text("Lib.Late\tcrowded\t900\t2\nLib.Crowded\tcrowded\t1200\t2\nLib.Alone\talone\t14100\t1\n"
                     "Lib.Both\tcrowded\t800\t2\nLib.Both\talone\t13000\t1\n?\tcrowded\t5\t2\n")
    done = tmp_path / "done.json"
    sys.argv = ["replay_shard.py", "pack", "--lean-dir", str(lean), "--shard", str(shard), "--log", str(log),
                "--chunk", "r7-s3", "--filelist", str(tmp_path / "files.txt"), "--done", str(done),
                "--kills", str(kills)]
    rs.main()
    rec = json.loads(done.read_text())
    assert sorted(rec["built"]) == ["Lib.Late", "Lib.Ok"]
    assert sorted(rec["failed"]) == ["Lib.Wrong"]                      # exit code 1: a real elaboration error
    assert sorted(rec["crowded"]) == ["Lib.Crowded"]                   # no strike
    assert sorted(rec["crashed"]) == ["Lib.Alone", "Lib.Both", "Lib.Segv"]
    assert rec["killed_alone"] == ["Lib.Alone", "Lib.Both"]

    # without the table every signal death is a crash, as before
    sys.argv = sys.argv[:-2]
    rs.main()
    rec = json.loads(done.read_text())
    assert sorted(rec["crashed"]) == ["Lib.Alone", "Lib.Both", "Lib.Crowded", "Lib.Segv"] and rec["crowded"] == {}


def test_merge_counts_a_crowded_kill_but_gives_no_strike_for_it(tmp_path: Path) -> None:
    deps = {"A": [], "B": ["A"], "C": ["A"]}
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": deps, "size": {"A": 10, "B": 20, "C": 30}}))
    d = tmp_path / "in" / "x"
    d.mkdir(parents=True)
    (d / "done-r3-s0.json").write_text(json.dumps({
        "chunk": "r3-s0", "planned": 3, "built": ["A"], "seconds": {"A": 1.5}, "failed": {},
        "crashed": {"C": {"exit": 137, "excerpt": []}}, "crowded": {"B": {"exit": 137, "excerpt": []}},
        "killed_alone": ["C"]}))
    out = tmp_path / "state.json"
    gh = tmp_path / "gh.txt"
    sys.argv = ["replay_shard.py", "merge", "--dag", str(dag), "--done-dir", str(tmp_path / "in"),
                "--round", "3", "--out", str(out), "--github-output", str(gh)]
    rs.main()
    st = json.loads(out.read_text())
    assert st["crashed"] == {"C": 1}
    assert st["history"][0]["crowded_this_round"] == 1 and st["history"][0]["killed_alone"] == ["C"]
    outputs = dict(line.split("=", 1) for line in gh.read_text().splitlines())
    assert outputs["crowded_this_round"] == "1" and outputs["crashed_this_round"] == "1"


def test_the_rate_is_fitted_on_the_last_rounds_not_on_every_round() -> None:
    size = {f"M{i}": 5000 for i in range(900)}
    where = {f"M{i}": f"r{i // 300}-s0" for i in range(900)}                 # rounds 0, 1, 2
    secs = {f"M{i}": (8.0 if i < 300 else 16.0) for i in range(900)}        # round 0 was cheap
    recent = rp.recent_timings(where, secs)
    assert len(recent) == 600 and min(recent.values()) == 16.0
    assert rp.fit_rate(size, recent, 4.0, 0.5) == pytest.approx((16.0 - 4.0) / 5.0)
    assert rp.fit_rate(size, secs, 4.0, 0.5) < rp.fit_rate(size, recent, 4.0, 0.5)
    # too few recent timings, or chunk names it cannot read: every timing is used
    few = {m: secs[m] for m in list(secs)[:150]}
    assert rp.recent_timings(where, few) is few
    assert rp.recent_timings({m: "odd" for m in secs}, secs) is secs


def test_the_fetch_map_of_a_state_names_every_chunk_that_holds_a_module(tmp_path: Path) -> None:
    state = tmp_path / "state.json"
    state.write_text(json.dumps({"where": {"A": "r0-s0", "B": "r0-s3", "C": "r0-s0", "D": "r12-s11"},
                                 "bundles": {"0": 111, "12": 999, "5": 555}}))
    out = tmp_path / "all.json"
    sys.argv = ["replay_shard.py", "fetchmap", "--state", str(state), "--out", str(out)]
    rs.main()
    assert json.loads(out.read_text()) == {"fetch": {"111": ["chunk-r0-s0.tar.zst", "chunk-r0-s3.tar.zst"],
                                                     "999": ["chunk-r12-s11.tar.zst"]}}
    state.write_text(json.dumps({"where": {"A": "r7-s0"}, "bundles": {"0": 111}}))
    with pytest.raises(SystemExit):
        rs.main()


def run_rounds_filled(deps, size, shards=5, budget=600.0):
    order, _ = rp.topo_levels(deps)
    height = rp.heights(deps, order)
    cost = rp.cost_model(size, 4.0, 0.5)
    done: set[str] = set()
    rounds = []
    while len(done) < len(order):
        plan, _, _ = rp.plan_round(deps, cost, order, height, done, shards, budget, 10**6)
        owned, extra, loads = rp.fill_idle(deps, cost, order, done, plan, shards, budget)
        assert any(owned), "planner stalled with modules left"
        rounds.append((plan, owned, extra, loads, set(done)))
        for sh in owned:
            done.update(sh)
        assert len(rounds) < 10_000
    return rounds, cost


@pytest.mark.parametrize("seed,shards,budget,idle", [(1, 5, 600.0, False), (1, 12, 600.0, True),
                                                     (2, 8, 2000.0, True), (3, 12, 6000.0, True)])
def test_the_filling_pass_keeps_every_shard_closed_and_within_budget(seed, shards, budget, idle) -> None:
    deps, size = random_dag(3000, seed)
    rounds, cost = run_rounds_filled(deps, size, shards=shards, budget=budget)
    seen: set[str] = set()
    extras = 0
    for plan, owned, extra, loads, done in rounds:
        owner = {}
        for i, sh in enumerate(owned):
            for m in sh:
                assert m not in owner and m not in done and m not in seen, "module owned twice"
                owner[m] = i
        for i, sh in enumerate(plan):                       # the first pass keeps what it planned
            assert all(owner[m] == i for m in sh)
        for i in range(len(owned)):
            here = set(owned[i]) | set(extra[i])
            for m in extra[i]:
                assert m in owner and owner[m] != i, "an extra must be owned by another shard of the round"
            for m in here:
                for d in deps[m]:
                    # the property that makes shards independent
                    assert d in done or d in here, f"{m} needs {d}, which this shard does not build"
            assert sum(cost[m] for m in here) <= budget + 1e-6
            assert loads[i] == pytest.approx(sum(cost[m] for m in here))
        extras += sum(len(e) for e in extra)
        seen.update(owner)
    assert seen == set(deps)
    plain, _ = run_rounds(deps, size, shards=shards, budget=budget)
    assert len(rounds) <= len(plain), "filling idle shards must not cost rounds"
    if idle:
        # with shards to spare the pass has work to do, and it saves rounds
        assert extras > 0 and len(rounds) < len(plain)
    else:
        # five small shards are full every round: nothing is idle, nothing is built twice
        assert extras == 0 and len(rounds) == len(plain)


def test_the_filling_pass_builds_a_join_this_round_at_the_price_of_one_extra() -> None:
    # two clusters that fill their shards, and a module J joining both: the
    # cluster pass defers J, the filling pass gives it a third shard with
    # both of its imports built there again
    deps = {"A": [], "B": [], "J": ["A", "B"]}
    size = {"A": 1000, "B": 1000, "J": 1000}
    cost = {"A": 300.0, "B": 300.0, "J": 10.0}
    order, _ = rp.topo_levels(deps)
    plan, waiting, _ = rp.plan_round(deps, cost, order, rp.heights(deps, order), set(), 3, 400.0, 10**6)
    assert sorted(sum(plan, [])) == ["A", "B"] and waiting == 1
    owned, extra, loads = rp.fill_idle(deps, cost, order, set(), plan, 3, 700.0)
    where = {m: i for i, sh in enumerate(owned) for m in sh}
    assert set(where) == {"A", "B", "J"}
    i = where["J"]
    assert sorted(owned[i] + extra[i]) == ["A", "B", "J"] and len(extra[i]) >= 1
    # with no room for the imports it stays deferred
    owned, extra, _ = rp.fill_idle(deps, cost, order, set(), plan, 3, 400.0)
    assert "J" not in sum(owned, []) and sum(extra, []) == []


def test_the_filling_pass_is_deterministic() -> None:
    deps, size = random_dag(1500, 11)
    a, _ = run_rounds_filled(deps, size)
    b, _ = run_rounds_filled(deps, size)
    assert [(o, e) for _, o, e, _, _ in a] == [(o, e) for _, o, e, _, _ in b]


def test_pack_leaves_extras_out_of_the_chunk_and_hashes_what_two_shards_build(tmp_path: Path) -> None:
    lean = tmp_path / "lean"
    lib = lean / ".lake" / "build" / "lib" / "lean" / "Lib"
    lib.mkdir(parents=True)
    for m, body in (("Own", "own bytes"), ("Extra", "extra bytes"), ("Shared", "shared bytes")):
        (lib / f"{m}.olean").write_text(body)
        (lib / f"{m}.trace").write_text(json.dumps({"outputs": {}}))
    shard = tmp_path / "shard.json"
    shard.write_text(json.dumps({"round": 15, "shard": 2, "modules": ["Lib.Own", "Lib.Shared"],
                                 "extra": ["Lib.Extra", "Lib.ExtraNotBuilt"],
                                 "shared": ["Lib.Shared", "Lib.Extra", "Lib.ExtraNotBuilt"],
                                 "sinks": ["Lib.Own"]}))
    log = tmp_path / "build.log"
    log.write_text("✔ [1/4] Built Lib.Extra (2.0s)\n✔ [2/4] Built Lib.Shared (2.0s)\n✔ [3/4] Built Lib.Own (3.0s)\n"
                   "✖ [4/4] Building Lib.ExtraNotBuilt (9s)\nerror: Lean exited with code 137\n", encoding="utf-8")
    done = tmp_path / "done.json"
    files = tmp_path / "files.txt"
    sys.argv = ["replay_shard.py", "pack", "--lean-dir", str(lean), "--shard", str(shard), "--log", str(log),
                "--chunk", "r15-s2", "--filelist", str(files), "--done", str(done)]
    rs.main()
    rec = json.loads(done.read_text())
    assert sorted(rec["built"]) == ["Lib.Own", "Lib.Shared"]             # its own, nothing else
    assert not any("Extra" in line for line in files.read_text().splitlines())
    assert rec["rebuilt_outside_shard"] == 0                             # an extra is expected, not a stray
    assert rec["extra_planned"] == 2 and rec["extra_built"] == 1
    assert rec["crashed"] == {}                                          # a failed extra is its owner's to report
    import hashlib
    assert rec["olean_sha256"] == {"Lib.Shared": hashlib.sha256(b"shared bytes").hexdigest(),
                                   "Lib.Extra": hashlib.sha256(b"extra bytes").hexdigest()}


def test_merge_says_whether_modules_built_twice_came_out_the_same(tmp_path: Path) -> None:
    deps = {"A": [], "B": ["A"], "C": ["A"]}
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": deps, "size": {"A": 10, "B": 20, "C": 30}}))
    d = tmp_path / "in" / "x"
    d.mkdir(parents=True)

    def records(a_hash_in_second_shard: str) -> None:
        (d / "done-r4-s0.json").write_text(json.dumps({
            "chunk": "r4-s0", "planned": 2, "built": ["A", "B"], "seconds": {"A": 1.0, "B": 2.0}, "failed": {},
            "crashed": {}, "olean_sha256": {"A": "aaa"}}))
        (d / "done-r4-s1.json").write_text(json.dumps({
            "chunk": "r4-s1", "planned": 1, "built": ["C"], "seconds": {"C": 2.0}, "failed": {}, "crashed": {},
            "extra_built": 1, "olean_sha256": {"A": a_hash_in_second_shard}}))

    out = tmp_path / "state.json"
    gh = tmp_path / "gh.txt"
    sys.argv = ["replay_shard.py", "merge", "--dag", str(dag), "--done-dir", str(tmp_path / "in"),
                "--round", "4", "--out", str(out), "--github-output", str(gh)]
    records("aaa")
    rs.main()
    st = json.loads(out.read_text())
    assert st["where"] == {"A": "r4-s0", "B": "r4-s0", "C": "r4-s1"}     # the owner's copy is the one kept
    h = st["history"][0]
    assert h["built_twice"] == 1 and h["built_twice_different"] == 0 and h["extra_built"] == 1
    outputs = dict(line.split("=", 1) for line in gh.read_text().splitlines())
    assert outputs["built_twice"] == "1" and outputs["built_twice_different"] == "0"

    gh.unlink()
    records("bbb")                                                       # the planted fault: different bytes
    rs.main()
    h = json.loads(out.read_text())["history"][0]
    assert h["built_twice_different"] == 1 and h["built_twice_different_examples"] == ["A"]
    assert dict(line.split("=", 1) for line in gh.read_text().splitlines())["built_twice_different"] == "1"


def test_the_plan_command_writes_extras_only_when_asked_to_fill(tmp_path: Path) -> None:
    deps, size = random_dag(1200, 4)
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": deps, "size": size}))
    order, _ = rp.topo_levels(deps)
    built = order[:300]
    state = tmp_path / "state.json"
    state.write_text(json.dumps({"where": {m: "r0-s0" for m in built}, "seconds": {}, "failed": {}, "crashed": {},
                                 "bundles": {"0": 77}}))
    plans = {}
    for name, flags in (("plain", []), ("filled", ["--fill"])):
        out = tmp_path / name
        sys.argv = ["replay_plan.py", "plan", "--dag", str(dag), "--state", str(state), "--round", "1",
                    "--shards", "12", "--budget-s", "900", "--out", str(out), *flags]
        rp.main()
        plans[name] = [json.loads(f.read_text()) for f in sorted(out.glob("shard-*.json"))]
    assert all(sh["extra"] == [] and sh["shared"] == [] for sh in plans["plain"])
    filled = plans["filled"]
    assert sum(len(sh["extra"]) for sh in filled) > 0
    done = set(built)
    owner = {}
    for sh in filled:
        for m in sh["modules"]:
            assert m not in owner
            owner[m] = sh["shard"]
    for sh in filled:
        here = set(sh["modules"]) | set(sh["extra"])
        assert all(owner[m] != sh["shard"] for m in sh["extra"])
        assert all(d in done or d in here for m in here for d in deps[m])
        assert set(sh["need"]) <= done and all(d in sh["need"] or d in here for m in here for d in deps[m])
        assert set(sh["shared"]) == {m for m in here if sum(m in set(o["modules"]) | set(o["extra"]) for o in filled) > 1}
        assert set(sh["sinks"]) <= here
    assert sum(len(sh["modules"]) for sh in filled) >= sum(len(sh["modules"]) for sh in plans["plain"])


def test_the_memory_summary_reads_both_versions_of_the_watchdog_log(tmp_path: Path) -> None:
    log = tmp_path / "mem.log"
    log.write_text(
        "watchdog: 'lean': suspend all but the largest when MemAvailable < 2500 MB\n"
        # version one, as round 12 wrote it
        "t=360s avail=12891MB used=2810MB peak_used=3084MB swap_free=2722MB n=2 anon_mb=[811, 164] "
        "file_mb=[7562, 6210] peak_anon_one=811MB kills=0\n"
        # version two
        "t=390s avail=2100MB used=13500MB peak_used=13500MB cached=4000MB swap_free=100MB majfault=1200 swapin=3 "
        "swapout=40 n=3 anon_mb=[9000, 2500, 300] file_mb=[8000, 100, 50] peak_anon_one=9000MB suspended=0 "
        "stops=0 kills=0 largest=A.Big\n"
        "t=392s STOP pid=7 A.Small anon=300MB avail=2100MB largest=A.Big anon_largest=9000MB\n"
        "t=420s avail=600MB used=15000MB peak_used=15000MB cached=900MB swap_free=0MB majfault=30000 swapin=0 "
        "swapout=10 n=3 anon_mb=[11000, 2500, 300] file_mb=[900, 100, 50] peak_anon_one=11000MB suspended=1 "
        "stops=1 kills=0 largest=A.Big\n"
        "t=424s KILL crowded pid=7 A.Small anon=300MB avail=600MB alive=3 others_anon_mb=[11000, 2500] kills=1\n"
        "watchdog: end after 500s peak_used=15000MB peak_anon_one=11000MB stops=1 kills=1\n", encoding="utf-8")
    (tmp_path / "mem.log.modules.tsv").write_text(
        "A.Small\t300\t50\t40\t30\tkilled_crowded\nA.Mid\t2500\t100\t200\t0\texit\n"
        "A.Big\t11800\t8000\t900\t0\texit\n", encoding="utf-8")
    got = rs.memory_summary(str(log), top=2)
    assert got["min_avail_mb"] == 600 and got["peak_used_mb"] == 15000
    assert got["peak_anon_one_mb"] == 11800            # the table samples more often than the log prints
    assert got["majfault"] == 31200 and got["swapout_pages"] == 50
    assert got["stops"] == 1 and got["kills"] == 1 and got["processes_seen"] == 3 and got["over_2gb"] == 2
    assert got["top"] == [["A.Big", 11800, 8000, 900, 0, "exit"], ["A.Mid", 2500, 100, 200, 0, "exit"]]
    assert rs.memory_summary(str(tmp_path / "absent.log")) == {} and rs.memory_summary(None) == {}


def test_merge_keeps_the_worst_memory_figures_of_the_round(tmp_path: Path) -> None:
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": {"A": [], "B": []}, "size": {"A": 10, "B": 20}}))
    d = tmp_path / "in" / "x"
    d.mkdir(parents=True)
    for i, (m, mem) in enumerate([
            ("A", {"min_avail_mb": 9000, "peak_used_mb": 5000, "peak_anon_one_mb": 2000, "majfault": 10,
                   "swapout_pages": 1, "stops": 0, "kills": 0, "over_2gb": 0, "top": [["A", 2000, 1, 9, 0, "exit"]]}),
            ("B", {"min_avail_mb": 700, "peak_used_mb": 14900, "peak_anon_one_mb": 12000, "majfault": 500,
                   "swapout_pages": 0, "stops": 2, "kills": 1, "over_2gb": 1, "top": [["B", 12000, 2, 99, 0, "exit"]]})]):
        (d / f"done-r5-s{i}.json").write_text(json.dumps({
            "chunk": f"r5-s{i}", "planned": 1, "built": [m], "seconds": {m: 1.0}, "failed": {}, "crashed": {},
            "mem": mem}))
    (d / "done-r5-s2.json").write_text(json.dumps({          # a record from before the summary existed
        "chunk": "r5-s2", "planned": 0, "built": [], "seconds": {}, "failed": {}, "crashed": {}}))
    out = tmp_path / "state.json"
    sys.argv = ["replay_shard.py", "merge", "--dag", str(dag), "--done-dir", str(tmp_path / "in"),
                "--round", "5", "--out", str(out)]
    rs.main()
    mem = json.loads(out.read_text())["history"][0]["mem"]
    assert mem["min_avail_mb"] == 700 and mem["peak_used_mb"] == 14900 and mem["peak_anon_one_mb"] == 12000
    assert mem["majfault"] == 510 and mem["stops"] == 2 and mem["kills"] == 1 and mem["over_2gb"] == 1
    assert [r[0] for r in mem["top"]] == ["B", "A"]


def test_built_sinks_are_the_built_modules_nothing_built_imports(tmp_path: Path) -> None:
    deps = {"A": [], "B": ["A"], "C": ["A"], "D": ["B"], "E": ["C", "D"], "F": []}
    dag = tmp_path / "dag.json"
    dag.write_text(json.dumps({"deps": deps, "size": {m: 1 for m in deps}}))
    state = tmp_path / "state.json"
    state.write_text(json.dumps({"where": {m: "r0-s0" for m in ("A", "B", "C", "D", "F", "Gone.From.The.Graph")}}))
    out = tmp_path / "sinks.txt"
    sys.argv = ["replay_shard.py", "builtsinks", "--dag", str(dag), "--state", str(state), "--out", str(out)]
    rs.main()
    # E is not built, so C and D are the tops of what is; F stands alone
    assert out.read_text().split() == ["C", "D", "F"]

