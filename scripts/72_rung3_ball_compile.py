#!/usr/bin/env python3
"""Resumable compile driver for sharded rung-3 ball certificates.

Reads the compact per-site manifests written by sharded generation and
kernel-checks each module in manifest order with:

    lake env lean --root SOURCE_ROOT ABSOLUTE_SOURCE -o ABSOLUTE_OLEAN

``--root`` is the manifest parent and only sets Lean's module-name root.  The
input and ``-o`` paths are absolute files derived from that parent, the
output root, and the relative manifest entry, because a relative input is
not resolved against ``--root``.  The manifest itself stays relative and
traversal-safe.  ``LEAN_PATH`` always contains the generated source root.
``lake`` is invoked only as ``lake env lean ...``; this driver never runs
``lake build``, never installs a toolchain, and never deletes sources or
oleans.

Each successful module is checkpointed atomically under ``--output-root``
with status, return code, byte count, and a SHA-256 of the source.  A later
run skips a module only when that checkpoint, the olean, the live byte
count, and the live source hash all match.  Manifest byte counts are checked
against the sources before any compile.  Recompiling one module invalidates only its transitive dependents;
unrelated siblings may stay verified.  ``--jobs`` is site-level and
``--module-jobs`` is intra-site; both default to 1.  Their product is the
maximum concurrent ``lake env lean`` process count.  Independent prime
shards and independent term shards may run concurrently; barrels, composite
chains, sum chains, and the root wait for their declared dependencies.  A
failed module stops scheduling dependents and fails the site; already
running siblings may settle.

Run:
  python scripts/72_rung3_ball_compile.py --lean-project LEAN --output-root OUT
      [--jobs N] [--module-jobs N] MANIFEST.json [MANIFEST.json ...]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import threading
import time
from concurrent.futures import (
    FIRST_COMPLETED,
    ThreadPoolExecutor,
    as_completed,
    wait,
)
from pathlib import Path

SUPPORTED_FORMAT_VERSION = 2


class CompileError(Exception):
    """Closed failure: do not skip, do not continue the site."""


def _is_relative_module_path(rel: str) -> bool:
    if not isinstance(rel, str) or not rel:
        return False
    path = Path(rel)
    if path.is_absolute() or path.anchor:
        return False
    parts = Path(rel.replace("\\", "/")).parts
    return bool(parts) and not any(part in (".", "..") for part in parts)


def resolve_inside(root: Path, rel: str) -> Path:
    """Join a traversal-safe relative path onto root and refuse escapes."""
    if not _is_relative_module_path(rel):
        raise CompileError(f"path must be relative and traversal-safe, got {rel!r}")
    root = Path(root).resolve()
    joined = (root / rel).resolve()
    try:
        joined.relative_to(root)
    except ValueError as exc:
        raise CompileError(f"{rel} is not inside {root}") from exc
    return joined


def load_manifest(path: Path) -> dict:
    try:
        data = json.loads(Path(path).read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise CompileError(f"unreadable manifest {path}: {exc}") from exc
    if not isinstance(data, dict):
        raise CompileError(f"manifest {path} is not an object")
    version = data.get("source_format_version")
    if version != SUPPORTED_FORMAT_VERSION:
        raise CompileError(
            f"manifest {path} has source_format_version {version!r}, "
            f"want {SUPPORTED_FORMAT_VERSION}")
    root = data.get("root")
    modules = data.get("modules")
    if not isinstance(root, str) or not root:
        raise CompileError(f"manifest {path} missing root")
    if Path(root).is_absolute() or any(part == ".." for part in Path(root).parts):
        raise CompileError(f"manifest {path} root must be a relative name")
    if not isinstance(modules, list) or not modules:
        raise CompileError(f"manifest {path} has no modules")
    for i, mod in enumerate(modules):
        if not isinstance(mod, dict) or "path" not in mod:
            raise CompileError(f"manifest {path} module {i} is missing path")
        if not _is_relative_module_path(mod["path"]):
            raise CompileError(
                f"manifest {path} module path must be relative, got {mod['path']!r}")
        if not str(mod["path"]).endswith(".lean"):
            raise CompileError(
                f"manifest {path} module path must be a .lean file, got {mod['path']!r}")
        if any(m["path"] == mod["path"] for m in modules[:i]):
            raise CompileError(f"manifest {path} has duplicate module {mod['path']}")
    validate_module_graph(modules, path)
    return data


def validate_module_graph(modules: list[dict], manifest_path: Path | str) -> dict[str, list[str]]:
    """Require depends lists that only name earlier acyclic same-site paths."""
    seen: set[str] = set()
    graph: dict[str, list[str]] = {}
    listed = {mod["path"] for mod in modules}
    for mod in modules:
        path = mod["path"]
        deps = mod.get("depends")
        if not isinstance(deps, list):
            raise CompileError(
                f"{manifest_path} module {path} must declare a depends list")
        cleaned: list[str] = []
        for dep in deps:
            if not isinstance(dep, str) or not _is_relative_module_path(dep):
                raise CompileError(
                    f"{manifest_path} {path} has invalid dependency {dep!r}")
            if not dep.endswith(".lean"):
                raise CompileError(
                    f"{manifest_path} {path} dependency must be a .lean path")
            if dep == path:
                raise CompileError(f"{manifest_path} {path} depends on itself")
            if dep not in seen:
                if dep in listed:
                    raise CompileError(
                        f"{manifest_path} forward dependency: {path} -> {dep}")
                raise CompileError(
                    f"{manifest_path} unknown dependency: {path} -> {dep}")
            if dep not in cleaned:
                cleaned.append(dep)
        graph[path] = cleaned
        seen.add(path)
    return graph


def checkpoint_path(output_root: Path, root: str, module_path: str) -> Path:
    safe = module_path.replace("/", "__")
    return Path(output_root) / "checkpoints" / root / f"{safe}.ok.json"


def olean_path(output_root: Path, module_path: str) -> Path:
    rel = str(Path(module_path).with_suffix(".olean")).replace("\\", "/")
    return resolve_inside(output_root, rel)


def lean_argv(
    source_abs: str | Path,
    olean_abs: str | Path,
    source_root: str | Path,
) -> list[str]:
    src = Path(source_abs)
    olean = Path(olean_abs)
    root = Path(source_root)
    if not src.is_absolute() or not olean.is_absolute():
        raise CompileError("lean source and olean paths must be absolute")
    if not str(root):
        raise CompileError("lean --root is required")
    return ["env", "lean", "--root", str(root), str(src), "-o", str(olean)]


def source_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _read_ok_checkpoint(path: Path) -> dict | None:
    if not path.is_file():
        return None
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return None
    if not isinstance(data, dict):
        return None
    if data.get("status") != "ok" or data.get("returncode") != 0:
        return None
    return data


def checkpoint_is_verified(
    previous: dict | None,
    source_abs: Path,
    olean_abs: Path,
) -> bool:
    """Skip only when status, returncode, olean, bytes, and source hash match."""
    if previous is None or not olean_abs.is_file() or not source_abs.is_file():
        return False
    if previous.get("status") != "ok" or previous.get("returncode") != 0:
        return False
    try:
        live_bytes = source_abs.stat().st_size
    except OSError:
        return False
    if previous.get("bytes") != live_bytes:
        return False
    recorded = previous.get("sha256")
    if not isinstance(recorded, str) or not recorded:
        return False
    return recorded == source_sha256(source_abs)


def validate_manifest_sources(
    data: dict,
    source_root: Path,
    manifest_path: Path,
) -> None:
    """Fail closed if any manifest byte count disagrees with the live source."""
    root = data["root"]
    for i, mod in enumerate(data["modules"]):
        rel = mod["path"]
        source_abs = resolve_inside(source_root, rel)
        if not source_abs.is_file():
            raise CompileError(f"{root}: missing source {rel} at {source_abs}")
        recorded = mod.get("bytes")
        actual = source_abs.stat().st_size
        if recorded != actual:
            raise CompileError(
                f"{manifest_path}: module {i} {rel} manifest bytes={recorded!r} "
                f"but source is {actual} bytes")


def _atomic_write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2) + "\n")
    os.replace(tmp, path)


def _wait_module(proc: subprocess.Popen) -> tuple[int, float | None, float | None]:
    if hasattr(os, "wait4"):
        _, status, ru = os.wait4(proc.pid, 0)
        proc.returncode = os.waitstatus_to_exitcode(status)
        return proc.returncode, float(ru.ru_utime), float(ru.ru_stime)
    returncode = proc.wait()
    return returncode, None, None


def _run_module(
    lake: str,
    source_abs: Path,
    olean_abs: Path,
    *,
    source_root: Path,
    cwd: Path,
    env: dict[str, str],
    log_path: Path,
    process_slots: threading.Semaphore | None = None,
) -> dict:
    argv = [lake, *lean_argv(source_abs, olean_abs, source_root)]
    log_path.parent.mkdir(parents=True, exist_ok=True)
    Path(olean_abs).parent.mkdir(parents=True, exist_ok=True)
    if process_slots is not None:
        process_slots.acquire()
    t0 = time.perf_counter()
    try:
        with open(log_path, "wb") as log:
            proc = subprocess.Popen(
                argv, cwd=str(cwd), env=env, stdout=log, stderr=subprocess.STDOUT)
            returncode, user, system = _wait_module(proc)
    except OSError as exc:
        raise CompileError(f"failed to invoke lake env lean: {exc}") from exc
    finally:
        if process_slots is not None:
            process_slots.release()
    elapsed = time.perf_counter() - t0
    return {
        "argv": argv[1:],
        "cwd": str(cwd),
        "returncode": returncode,
        "elapsed": elapsed,
        "user": user,
        "system": system,
        "log": str(log_path),
    }


def _skip_record(rel: str, previous: dict | None, ckpt: Path) -> dict:
    return {
        "path": rel,
        "status": "skipped",
        "returncode": 0,
        "elapsed": previous.get("elapsed") if previous else None,
        "user": previous.get("user") if previous else None,
        "system": previous.get("system") if previous else None,
        "checkpoint": str(ckpt),
    }


def compile_site(
    manifest_path: Path,
    *,
    lean_project: Path,
    output_root: Path,
    lake: str = "lake",
    stop_event: threading.Event | None = None,
    module_jobs: int = 1,
    process_slots: threading.Semaphore | None = None,
) -> dict:
    """Compile one site as a DAG. Resume skips verified modules whose deps held."""
    if module_jobs < 1:
        raise CompileError("module-jobs must be >= 1")
    manifest_path = Path(manifest_path)
    lean_project = Path(lean_project).resolve()
    output_root = Path(output_root).resolve()
    source_root = manifest_path.parent.resolve()
    data = load_manifest(manifest_path)
    root = data["root"]
    if not lean_project.is_dir():
        raise CompileError(f"lean project is not a directory: {lean_project}")
    if Path(lake).name in {"elan", "lean", "install"}:
        raise CompileError(f"refusing {lake!r}; compile wrapper must be lake env")

    env = os.environ.copy()
    generated_root = str(source_root)
    existing = env.get("LEAN_PATH", "")
    parts = [generated_root]
    if str(output_root) != generated_root:
        parts.append(str(output_root))
    if existing:
        parts.append(existing)
    env["LEAN_PATH"] = os.pathsep.join(parts)

    validate_manifest_sources(data, source_root, manifest_path)
    graph = validate_module_graph(data["modules"], manifest_path)
    order = [mod["path"] for mod in data["modules"]]

    completed: dict[str, dict] = {}
    rebuilt: set[str] = set()
    in_flight: dict = {}
    site_failed = False
    stopped = False

    def pick_ready() -> list[str]:
        return [
            path for path in order
            if path not in completed
            and path not in in_flight.values()
            and all(
                dep in completed and completed[dep]["status"] in ("ok", "skipped")
                for dep in graph[path])
        ]

    def compile_one(rel: str) -> dict:
        source_abs = resolve_inside(source_root, rel)
        olean_abs = olean_path(output_root, rel)
        log_path = (
            Path(output_root) / "logs" / root / f"{rel.replace('/', '__')}.log")
        ran = _run_module(
            lake, source_abs, olean_abs,
            source_root=source_root,
            cwd=lean_project, env=env, log_path=log_path,
            process_slots=process_slots)
        digest = source_sha256(source_abs)
        size = source_abs.stat().st_size
        record = {
            "path": rel,
            "status": "ok" if ran["returncode"] == 0 else "failed",
            "returncode": ran["returncode"],
            "elapsed": ran["elapsed"],
            "user": ran["user"],
            "system": ran["system"],
            "source": rel,
            "olean": str(olean_abs),
            "argv": ran["argv"],
            "log": ran["log"],
            "bytes": size,
            "sha256": digest,
        }
        if ran["returncode"] == 0:
            ckpt = checkpoint_path(output_root, root, rel)
            _atomic_write_json(ckpt, {
                "status": "ok",
                "path": rel,
                "returncode": 0,
                "elapsed": ran["elapsed"],
                "user": ran["user"],
                "system": ran["system"],
                "source": rel,
                "olean": str(olean_abs),
                "bytes": size,
                "sha256": digest,
            })
            record["checkpoint"] = str(ckpt)
        return record

    with ThreadPoolExecutor(max_workers=module_jobs) as pool:
        while True:
            if stop_event is not None and stop_event.is_set():
                stopped = True
                site_failed = True
            scheduled = False
            if not site_failed:
                for path in pick_ready():
                    source_abs = resolve_inside(source_root, path)
                    olean_abs = olean_path(output_root, path)
                    ckpt = checkpoint_path(output_root, root, path)
                    previous = _read_ok_checkpoint(ckpt)
                    dep_rebuilt = any(dep in rebuilt for dep in graph[path])
                    if not dep_rebuilt and checkpoint_is_verified(
                            previous, source_abs, olean_abs):
                        completed[path] = _skip_record(path, previous, ckpt)
                        scheduled = True
                        continue
                    if len(in_flight) >= module_jobs:
                        break
                    fut = pool.submit(compile_one, path)
                    in_flight[fut] = path
                    scheduled = True
                    if len(in_flight) >= module_jobs:
                        break
            if in_flight:
                done, _ = wait(list(in_flight), return_when=FIRST_COMPLETED)
                for fut in done:
                    path = in_flight.pop(fut)
                    record = fut.result()
                    completed[path] = record
                    if record["status"] == "failed":
                        site_failed = True
                    elif record["status"] == "ok":
                        rebuilt.add(path)
                continue
            if scheduled:
                continue
            break

    records = [completed[path] for path in order if path in completed]
    status = "ok"
    if stopped:
        status = "stopped"
    elif site_failed or any(r.get("status") == "failed" for r in records):
        status = "failed"
    elif len(completed) != len(order):
        status = "failed"
    return {
        "root": root,
        "status": status,
        "manifest": str(manifest_path),
        "modules": records,
        "lean_path": env["LEAN_PATH"],
    }


def compile_manifests(
    manifests: list[Path],
    *,
    lean_project: Path,
    output_root: Path,
    lake: str = "lake",
    jobs: int = 1,
    module_jobs: int = 1,
) -> list[dict]:
    if jobs < 1:
        raise CompileError("jobs must be >= 1")
    if module_jobs < 1:
        raise CompileError("module-jobs must be >= 1")
    output_root = Path(output_root)
    output_root.mkdir(parents=True, exist_ok=True)
    paths = [Path(p) for p in manifests]
    if not paths:
        raise CompileError("no manifests given")
    process_slots = threading.Semaphore(jobs * module_jobs)

    if jobs == 1:
        results: list[dict] = []
        for path in paths:
            result = compile_site(
                path, lean_project=lean_project, output_root=output_root,
                lake=lake, module_jobs=module_jobs,
                process_slots=process_slots)
            results.append(result)
            if result["status"] != "ok":
                break
        return results

    stop = threading.Event()
    results_by_path: dict[str, dict] = {}

    def run_one(path: Path) -> tuple[str, dict]:
        if stop.is_set():
            return str(path), {
                "root": path.stem,
                "status": "stopped",
                "manifest": str(path),
                "modules": [],
            }
        try:
            result = compile_site(
                path, lean_project=lean_project, output_root=output_root,
                lake=lake, stop_event=stop, module_jobs=module_jobs,
                process_slots=process_slots)
        except CompileError as exc:
            stop.set()
            return str(path), {
                "root": path.stem,
                "status": "failed",
                "manifest": str(path),
                "error": str(exc),
                "modules": [],
            }
        if result["status"] != "ok":
            stop.set()
        return str(path), result

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futs = [pool.submit(run_one, path) for path in paths]
        for fut in as_completed(futs):
            key, result = fut.result()
            results_by_path[key] = result
    return [results_by_path[str(path)] for path in paths]


def _print_result(result: dict) -> None:
    root = result.get("root", "?")
    print(f"{root} status={result.get('status')}", flush=True)
    for rec in result.get("modules", []):
        user = rec.get("user")
        system = rec.get("system")
        extra = ""
        if user is not None:
            extra += f" user={user:.3f}"
        if system is not None:
            extra += f" system={system:.3f}"
        elapsed = rec.get("elapsed")
        elapsed_s = f"{elapsed:.3f}" if isinstance(elapsed, (int, float)) else "na"
        print(
            f"  {rec.get('path')} {rec.get('status')} "
            f"elapsed={elapsed_s}{extra}",
            flush=True,
        )
    if result.get("error"):
        print(f"  error: {result['error']}", flush=True)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Resume-safe compile driver for sharded rung-3 ball sites")
    ap.add_argument("--lean-project", required=True, type=Path)
    ap.add_argument("--output-root", required=True, type=Path)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--module-jobs", type=int, default=1)
    ap.add_argument("--lake", default="lake")
    ap.add_argument("manifests", nargs="+", type=Path)
    args = ap.parse_args(argv)

    if args.jobs < 1:
        print("jobs must be >= 1", file=sys.stderr)
        return 2
    if args.module_jobs < 1:
        print("module-jobs must be >= 1", file=sys.stderr)
        return 2
    if Path(args.lake).name in {"elan", "lean", "install"}:
        print("compile wrapper must be lake env, not "
              f"{args.lake}", file=sys.stderr)
        return 2

    try:
        results = compile_manifests(
            args.manifests,
            lean_project=args.lean_project,
            output_root=args.output_root,
            lake=args.lake,
            jobs=args.jobs,
            module_jobs=args.module_jobs,
        )
    except CompileError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    failed = False
    for result in results:
        _print_result(result)
        if result.get("status") != "ok":
            failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
