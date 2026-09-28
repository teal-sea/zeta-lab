"""The sharded ball compile driver is resume-safe, ordered, and fail-closed."""
from __future__ import annotations

import importlib.util
import json
import os
import stat
from contextlib import contextmanager
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "rung3_ball_compile", ROOT / "scripts" / "72_rung3_ball_compile.py")
assert SPEC is not None and SPEC.loader is not None
drv = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(drv)

FAKE_LAKE = r"""#!/usr/bin/env python3
import fcntl
import json
import os
import sys
import time
from pathlib import Path

log = Path(os.environ["FAKE_LAKE_LOG"])
if sys.argv[1:4] != ["env", "lean", "--root"] or "-o" not in sys.argv:
    sys.stderr.write("bad argv %r\n" % (sys.argv,))
    sys.exit(3)
root = sys.argv[4]
src = sys.argv[5]
assert sys.argv[6] == "-o"
olean = sys.argv[7]
if not Path(src).is_absolute() or not Path(olean).is_absolute():
    sys.stderr.write("source and olean must be absolute\n")
    sys.exit(4)
if not root:
    sys.stderr.write("missing --root\n")
    sys.exit(4)

lock_path = Path(os.environ["FAKE_LAKE_LOCK"])
count_path = Path(os.environ["FAKE_LAKE_COUNT"])
max_path = Path(os.environ["FAKE_LAKE_MAX"])
with open(lock_path, "a+") as lk:
    fcntl.flock(lk, fcntl.LOCK_EX)
    n = int(count_path.read_text() or "0") + 1
    count_path.write_text(str(n))
    mx = int(max_path.read_text() or "0")
    if n > mx:
        max_path.write_text(str(n))
    fcntl.flock(lk, fcntl.LOCK_UN)

started = time.time()
sleep_s = float(os.environ.get("FAKE_LAKE_SLEEP", "0"))
if sleep_s:
    time.sleep(sleep_s)

fail_on = os.environ.get("FAKE_LAKE_FAIL", "")
failed = bool(fail_on) and src.endswith(fail_on)
record = {
    "src": src,
    "olean": olean,
    "root": root,
    "argv": sys.argv[1:],
    "cwd": os.getcwd(),
    "lean_path": os.environ.get("LEAN_PATH", ""),
    "failed": failed,
    "start": started,
    "end": time.time(),
}
with open(log, "a") as fh:
    fh.write(json.dumps(record) + "\n")

with open(lock_path, "a+") as lk:
    fcntl.flock(lk, fcntl.LOCK_EX)
    n = int(count_path.read_text() or "1") - 1
    count_path.write_text(str(n))
    fcntl.flock(lk, fcntl.LOCK_UN)

if failed:
    sys.exit(2)
Path(olean).parent.mkdir(parents=True, exist_ok=True)
Path(olean).write_text("olean\n")
sys.exit(0)
"""


def _load(path: Path) -> list[dict]:
    if not path.is_file():
        return []
    return [json.loads(line) for line in path.read_text().splitlines() if line]


def _write_fake_lake(tmp: Path) -> Path:
    lake = tmp / "lake"
    lake.write_text(FAKE_LAKE)
    lake.chmod(lake.stat().st_mode | stat.S_IEXEC)
    (tmp / "count").write_text("0")
    (tmp / "max").write_text("0")
    (tmp / "lock").write_text("")
    (tmp / "log").write_text("")
    return lake


@contextmanager
def _fake_env(tmp: Path, **extra):
    keys = {
        "FAKE_LAKE_LOG": str(tmp / "log"),
        "FAKE_LAKE_LOCK": str(tmp / "lock"),
        "FAKE_LAKE_COUNT": str(tmp / "count"),
        "FAKE_LAKE_MAX": str(tmp / "max"),
        **extra,
    }
    saved = {key: os.environ.get(key) for key in keys}
    try:
        os.environ.update(keys)
        yield
    finally:
        for key, value in saved.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def _site(tmp: Path, root: str, modules: list[str], depends: dict[str, list[str]] | None = None) -> Path:
    gen = tmp / "gen"
    gen.mkdir(parents=True, exist_ok=True)
    if depends is None:
        depends = {}
        prev = None
        for rel in modules:
            depends[rel] = [prev] if prev else []
            prev = rel
    entries = []
    for rel in modules:
        dest = gen / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(f"-- {rel}\n")
        entries.append({
            "path": rel,
            "bytes": dest.stat().st_size,
            "depends": list(depends[rel]),
        })
    man = {
        "source_format_version": 2,
        "root": root,
        "id": root[1:] if root.startswith("C") else root,
        "kind": "big",
        "K": 17,
        "normLower": "1/2",
        "normBound": "3/4",
        "prime_towers": 1,
        "n_files": len(entries),
        "max_file_bytes": max(m["bytes"] for m in entries),
        "max_bytes": 2_000_000,
        "sharded": True,
        "modules": entries,
    }
    path = gen / f"{root}.manifest.json"
    path.write_text(json.dumps(man, indent=2) + "\n")
    return path


def _run(tmp: Path, manifests: list[Path], jobs: int = 1, module_jobs: int = 1, **env_extra):
    lean_project = tmp / "lean"
    lean_project.mkdir(parents=True, exist_ok=True)
    output_root = tmp / "out"
    with _fake_env(tmp, **env_extra):
        return drv.compile_manifests(
            manifests,
            lean_project=lean_project,
            output_root=output_root,
            lake=str(tmp / "lake"),
            jobs=jobs,
            module_jobs=module_jobs,
        )


def _ends_with(path: str, rel: str) -> bool:
    return path.replace("\\", "/").endswith(rel)


def test_lean_argv_is_root_then_absolute_source_and_olean():
    argv = drv.lean_argv(
        "/tmp/gen/CB/Base.lean", "/tmp/out/CB/Base.olean", "/tmp/gen")
    assert argv == [
        "env", "lean", "--root", "/tmp/gen",
        "/tmp/gen/CB/Base.lean", "-o", "/tmp/out/CB/Base.olean"]
    try:
        drv.lean_argv("CB/Base.lean", "/tmp/out/CB/Base.olean", "/tmp/gen")
        assert False, "relative source must fail"
    except drv.CompileError:
        pass


def test_compile_runs_modules_in_manifest_order(tmp_path):
    _write_fake_lake(tmp_path)
    modules = [
        "CB_order/Base.lean",
        "CB_order/Primes00.lean",
        "CB_order/Primes.lean",
        "CB_order/Composites.lean",
        "CB_order/Terms.lean",
        "CB_order.lean",
    ]
    man = _site(tmp_path, "CB_order", modules)
    results = _run(tmp_path, [man])
    assert results[0]["status"] == "ok"
    records = _load(tmp_path / "log")
    assert len(records) == len(modules)
    gen = (tmp_path / "gen").resolve()
    out = (tmp_path / "out").resolve()
    man_payload = json.loads(man.read_text())
    assert man_payload["modules"][-1]["path"] == "CB_order.lean"
    for entry in man_payload["modules"]:
        assert not Path(entry["path"]).is_absolute()
        assert drv._is_relative_module_path(entry["path"])
    for rec, rel in zip(records, modules):
        src = str((gen / rel).resolve())
        olean = str((out / Path(rel).with_suffix(".olean")).resolve())
        assert rec["argv"] == [
            "env", "lean", "--root", str(gen), src, "-o", olean]
        assert rec["src"] == src
        assert rec["root"] == str(gen)
        assert Path(rec["src"]).is_absolute()
        assert Path(rec["olean"]).is_absolute()
        assert Path(rec["src"]).resolve().relative_to(gen) == Path(rel)
        assert Path(rec["olean"]).resolve().relative_to(out) == Path(rel).with_suffix(".olean")
        assert rec["lean_path"].split(os.pathsep)[0] == str(gen)
    assert [m["path"] for m in results[0]["modules"]] == modules
    assert (tmp_path / "out" / "CB_order" / "Base.olean").is_file()


def test_compile_skips_verified_success_on_resume(tmp_path):
    _write_fake_lake(tmp_path)
    modules = ["CB_resume/Base.lean", "CB_resume/Primes.lean", "CB_resume.lean"]
    man = _site(tmp_path, "CB_resume", modules)
    first = _run(tmp_path, [man], FAKE_LAKE_FAIL="Primes.lean")
    assert first[0]["status"] == "failed"
    assert [m["status"] for m in first[0]["modules"]] == ["ok", "failed"]
    first_log = _load(tmp_path / "log")
    assert [_ends_with(r["src"], rel) for r, rel in zip(first_log, modules[:2])]
    assert [r["src"] for r in first_log]  # Base then Primes, not the root
    assert len(first_log) == 2
    (tmp_path / "log").write_text("")
    second = _run(tmp_path, [man])
    assert second[0]["status"] == "ok"
    assert [m["status"] for m in second[0]["modules"]] == [
        "skipped", "ok", "ok"]
    second_log = _load(tmp_path / "log")
    assert len(second_log) == 2
    assert _ends_with(second_log[0]["src"], modules[1])
    assert _ends_with(second_log[1]["src"], modules[2])


def test_compile_failure_does_not_run_later_modules(tmp_path):
    _write_fake_lake(tmp_path)
    modules = ["CB_fail/Base.lean", "CB_fail/Primes.lean", "CB_fail.lean"]
    man = _site(tmp_path, "CB_fail", modules)
    results = _run(tmp_path, [man], FAKE_LAKE_FAIL="Primes.lean")
    assert results[0]["status"] == "failed"
    records = _load(tmp_path / "log")
    assert len(records) == 2
    assert _ends_with(records[0]["src"], modules[0])
    assert _ends_with(records[1]["src"], modules[1])
    ckpt_root = tmp_path / "out" / "checkpoints" / "CB_fail"
    assert (ckpt_root / "CB_fail__Base.lean.ok.json").is_file()
    assert not (ckpt_root / "CB_fail__Primes.lean.ok.json").is_file()


def test_jobs_bounds_site_parallelism(tmp_path):
    _write_fake_lake(tmp_path)
    mans = [
        _site(tmp_path, f"Csite{i}", [f"Csite{i}/Base.lean", f"Csite{i}.lean"])
        for i in range(3)
    ]
    results = _run(tmp_path, mans, jobs=2, FAKE_LAKE_SLEEP="0.25")
    assert [r["status"] for r in results] == ["ok", "ok", "ok"]
    assert int((tmp_path / "max").read_text()) == 2
    records = _load(tmp_path / "log")
    assert len(records) == 6


def test_jobs_default_is_one(tmp_path):
    _write_fake_lake(tmp_path)
    mans = [
        _site(tmp_path, f"Cseq{i}", [f"Cseq{i}.lean"])
        for i in range(2)
    ]
    results = _run(tmp_path, mans, jobs=1, FAKE_LAKE_SLEEP="0.05")
    assert [r["status"] for r in results] == ["ok", "ok"]
    assert int((tmp_path / "max").read_text()) == 1


def test_main_propagates_failure(tmp_path):
    _write_fake_lake(tmp_path)
    (tmp_path / "lean").mkdir(parents=True, exist_ok=True)
    man = _site(tmp_path, "CB_cli", ["CB_cli/Base.lean", "CB_cli.lean"])
    with _fake_env(tmp_path):
        code = drv.main([
            "--lean-project", str(tmp_path / "lean"),
            "--output-root", str(tmp_path / "out"),
            "--lake", str(tmp_path / "lake"),
            str(man),
        ])
    assert code == 0
    man2 = _site(tmp_path, "CB_cli2", ["CB_cli2/Base.lean", "CB_cli2.lean"])
    with _fake_env(tmp_path, FAKE_LAKE_FAIL="CB_cli2.lean"):
        code = drv.main([
            "--lean-project", str(tmp_path / "lean"),
            "--output-root", str(tmp_path / "out"),
            "--lake", str(tmp_path / "lake"),
            str(man2),
        ])
    assert code == 1


def test_refuses_absolute_module_paths(tmp_path):
    man = _site(tmp_path, "CB_abs", ["CB_abs.lean"])
    payload = json.loads(man.read_text())
    payload["modules"][0]["path"] = str((tmp_path / "gen" / "CB_abs.lean").resolve())
    man.write_text(json.dumps(payload) + "\n")
    try:
        drv.load_manifest(man)
        assert False, "absolute path must fail closed"
    except drv.CompileError:
        pass


def test_source_mutation_recompiles_that_module_and_later_ones(tmp_path):
    _write_fake_lake(tmp_path)
    modules = ["CB_mut/Base.lean", "CB_mut/Primes.lean", "CB_mut.lean"]
    man = _site(tmp_path, "CB_mut", modules)
    first = _run(tmp_path, [man])
    assert first[0]["status"] == "ok"
    assert [m["status"] for m in first[0]["modules"]] == ["ok", "ok", "ok"]
    ckpt = tmp_path / "out" / "checkpoints" / "CB_mut" / "CB_mut__Base.lean.ok.json"
    payload = json.loads(ckpt.read_text())
    assert payload["status"] == "ok"
    assert payload["returncode"] == 0
    assert payload["bytes"] == (tmp_path / "gen" / modules[0]).stat().st_size
    assert payload["sha256"] == drv.source_sha256(tmp_path / "gen" / modules[0])
    (tmp_path / "log").write_text("")
    mutated = tmp_path / "gen" / modules[0]
    mutated.write_text(mutated.read_text().replace("Base", "Bass", 1))
    man_payload = json.loads(man.read_text())
    man_payload["modules"][0]["bytes"] = mutated.stat().st_size
    man.write_text(json.dumps(man_payload, indent=2) + "\n")
    second = _run(tmp_path, [man])
    assert second[0]["status"] == "ok"
    assert [m["status"] for m in second[0]["modules"]] == ["ok", "ok", "ok"]
    second_log = _load(tmp_path / "log")
    assert len(second_log) == 3
    assert _ends_with(second_log[0]["src"], modules[0])
    assert _ends_with(second_log[1]["src"], modules[1])
    assert _ends_with(second_log[2]["src"], modules[2])


def test_manifest_byte_mismatch_fails_closed_before_compile(tmp_path):
    _write_fake_lake(tmp_path)
    modules = ["CB_bytes/Base.lean", "CB_bytes.lean"]
    man = _site(tmp_path, "CB_bytes", modules)
    payload = json.loads(man.read_text())
    payload["modules"][0]["bytes"] = payload["modules"][0]["bytes"] + 1
    man.write_text(json.dumps(payload, indent=2) + "\n")
    try:
        _run(tmp_path, [man])
        assert False, "byte mismatch must fail closed"
    except drv.CompileError as exc:
        assert "manifest bytes" in str(exc)
    assert _load(tmp_path / "log") == []


def _dag_site(tmp: Path, name: str = "Cdag") -> tuple[Path, list[str], dict[str, list[str]]]:
    modules = [
        f"{name}/Base.lean",
        f"{name}/Primes00.lean",
        f"{name}/Primes01.lean",
        f"{name}/Primes.lean",
        f"{name}.lean",
    ]
    depends = {
        modules[0]: [],
        modules[1]: [modules[0]],
        modules[2]: [modules[0]],
        modules[3]: [modules[1], modules[2]],
        modules[4]: [modules[3]],
    }
    return _site(tmp, name, modules, depends=depends), modules, depends


def test_dag_order_and_module_jobs_bound(tmp_path):
    _write_fake_lake(tmp_path)
    man, modules, depends = _dag_site(tmp_path)
    results = _run(tmp_path, [man], module_jobs=2, FAKE_LAKE_SLEEP="0.2")
    assert results[0]["status"] == "ok"
    records = _load(tmp_path / "log")
    by_rel = {}
    for rec in records:
        for rel in modules:
            if rec["src"].endswith(rel):
                by_rel[rel] = rec
    assert set(by_rel) == set(modules)
    for rel, deps in depends.items():
        for dep in deps:
            assert by_rel[rel]["start"] >= by_rel[dep]["end"] - 1e-4
    assert int((tmp_path / "max").read_text()) == 2
    assert by_rel[modules[1]]["start"] < by_rel[modules[2]]["end"]
    assert by_rel[modules[2]]["start"] < by_rel[modules[1]]["end"]


def test_transitive_invalidation_reuses_unrelated_siblings(tmp_path):
    _write_fake_lake(tmp_path)
    man, modules, _ = _dag_site(tmp_path, "Csib")
    first = _run(tmp_path, [man])
    assert first[0]["status"] == "ok"
    (tmp_path / "log").write_text("")
    mutated = tmp_path / "gen" / modules[2]
    mutated.write_text(mutated.read_text().replace("Primes01", "PrimesXX", 1))
    payload = json.loads(man.read_text())
    payload["modules"][2]["bytes"] = mutated.stat().st_size
    man.write_text(json.dumps(payload, indent=2) + "\n")
    second = _run(tmp_path, [man])
    assert second[0]["status"] == "ok"
    by_status = {m["path"]: m["status"] for m in second[0]["modules"]}
    assert by_status[modules[0]] == "skipped"
    assert by_status[modules[1]] == "skipped"
    assert by_status[modules[2]] == "ok"
    assert by_status[modules[3]] == "ok"
    assert by_status[modules[4]] == "ok"
    second_log = _load(tmp_path / "log")
    compiled = [rel for rel in modules if any(r["src"].endswith(rel) for r in second_log)]
    assert compiled == [modules[2], modules[3], modules[4]]


def test_forward_dependency_is_rejected(tmp_path):
    man = _site(
        tmp_path, "Cfwd",
        ["Cfwd/A.lean", "Cfwd/B.lean"],
        depends={"Cfwd/A.lean": ["Cfwd/B.lean"], "Cfwd/B.lean": []},
    )
    try:
        drv.load_manifest(man)
        assert False, "forward dependency must fail closed"
    except drv.CompileError as exc:
        assert "forward" in str(exc)


def test_cyclic_dependency_is_rejected(tmp_path):
    man = _site(
        tmp_path, "Cyc",
        ["Cyc/A.lean", "Cyc/B.lean"],
        depends={"Cyc/A.lean": ["Cyc/B.lean"], "Cyc/B.lean": ["Cyc/A.lean"]},
    )
    try:
        drv.load_manifest(man)
        assert False, "cycle must fail closed"
    except drv.CompileError as exc:
        text = str(exc)
        assert "forward" in text or "itself" in text or "cycle" in text


def test_self_dependency_is_rejected(tmp_path):
    man = _site(
        tmp_path, "Cself",
        ["Cself.lean"],
        depends={"Cself.lean": ["Cself.lean"]},
    )
    try:
        drv.load_manifest(man)
        assert False, "self dependency must fail closed"
    except drv.CompileError as exc:
        assert "itself" in str(exc)
