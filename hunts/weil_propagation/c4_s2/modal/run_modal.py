"""modal/: the compute follow-up of c4_s2 (BRIEF.md), run on Modal.

Runs checker/'s T_S units and two_adic/'s Gram probe units on Modal and
records outputs and cost only. Grading belongs to checker/ and two_adic/.

The image holds a standalone git clone of this branch checked out at
284eff6 (TREE_COMMIT), so checker_glue's snapshot guard runs on a real, clean
checkout. The clone enters the image as a tarball (C4S2_TREE_TGZ) extracted
at build time: add_local_dir resolves symlinks, which turned AGENTS.md (a
symlink to CLAUDE.md) into a file and left the tree dirty (RUNS.md s1). The
build fails unless `git status` in the image is empty. Every unit checks, inside the container, before and after its
build: HEAD is TREE_COMMIT, `git status --porcelain --untracked-files=all`
is empty for the whole tree, and checker_glue.ts_key() returns LOCAL_DIGEST
with an empty dirty list. A unit that fails the guard computes nothing.

One unit is one child process (subprocess.run with the unit's own timeout,
so a unit that runs long is recorded as timed out, not killed silently) in a
single-use container. The container's Modal timeout is the unit timeout
plus MARGIN_S. Each finished unit is written to the Volume VOL_NAME and
committed before the function returns; the local entrypoint writes it to
modal/out/<unit>.json as it lands and appends a line to RUNS.md.

A start marker on the Volume makes each unit run at most once: a restarted
input (a preemption, or a crash of the container) finds the marker, computes
nothing and returns status "restarted". Retrying it is a decision for the
operator, never automatic.

Build the tree and its tarball first (RUNS.md s1), then, from the worktree
root, with C4S2_TREE_TGZ=<scratch>/tree.tgz in the environment:

    modal run hunts/weil_propagation/c4_s2/modal/run_modal.py::smoke
    modal run hunts/weil_propagation/c4_s2/modal/run_modal.py::calibrate
    modal run --detach hunts/weil_propagation/c4_s2/modal/run_modal.py::batch --units a,b
    modal run hunts/weil_propagation/c4_s2/modal/run_modal.py::fetch

The Modal CLI imports this file in its own interpreter, so numpy, mpmath and
repository imports stay inside the remote functions and the child code.
"""

from __future__ import annotations

import json
import math
import os
import time

import modal

APP_NAME = "c4s2-modal-compute"
VOL_NAME = "c4s2-modal-out"
TREE_COMMIT = "284eff64b32cbcbd8b99f0198b129e90cc940623"
# checker_glue.ts_key()[0] in this worktree at 284eff6 (and at e43a7a9: modal/
# is outside T_S's import closure).
LOCAL_DIGEST = "1dcab23022a36c1b75c1f23379c1549bf7be9d4be7f526a5257bb3004577fb9a"
C4S2 = "hunts/weil_propagation/c4_s2"
REMOTE_TREE = "/tree"

# Resources per container. Billing is per reserved core-second and GiB-second
# (the larger of reservation and use); the limits cap use, so they cap cost.
CPU = (4.0, 4.0)  # physical cores (request, limit)
MEMORY_MIB = (16384, 32768)  # (request, limit)
THREADS = "4"  # BLAS threads: the container sees 4 CPUs (smoke, RUNS.md s1)
MARGIN_S = 600  # container timeout = unit timeout + MARGIN_S

# Modal rates read from modal.com/pricing on 2026-09-24 (RUNS.md s2).
RATE_CORE_S = 0.0000131
RATE_GIB_S = 0.00000222

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
RUNS = os.path.join(HERE, "RUNS.md")


# --------------------------------------------------------------- the units


def nvec_rule(c: float, N: int) -> int:
    """two_adic/ta_ts.py:146 (KernelProvider.delta_T): nvec = max(80, int(8 N / L) + 40)."""
    return max(80, int(8 * N / math.log(c)) + 40)


def S_rule(c: float, N: int) -> float:
    """two_adic/ta_ts.py:147 (KernelProvider.delta_T): S = max(1200, 12 * 2 pi N / L), L = log c.
    This is 24 pi N / L whenever it exceeds 1200 (it does for every N = 32 cell)."""
    return max(1200.0, 12.0 * 2 * math.pi * N / math.log(c))


def _checker(nv, S, N, role, timeout):
    return {"kind": "checker", "args": {"nvec": nv, "S": S, "N": N}, "role": role, "timeout": timeout}


def _gram(nv, S, role, timeout):
    return {"kind": "gram", "args": {"nvec": nv, "S": S}, "role": role, "timeout": timeout}


def unit_name(u) -> str:
    a = u["args"]
    if u["kind"] == "checker":
        return f"checker_{a['nvec']}_{int(a['S'])}_{a['N']}"
    return f"gram_{a['nvec']}_{int(a['S'])}"


# timeout: the unit's child-process limit in seconds (RUNS.md s3 derives each).
CALIBRATION = [
    _checker(200, 2400, 32, "calibration: checker/checker_ts_snapshot.json unit 200|2400|32", 1800),
    _gram(80, 4800, "calibration: two_adic/ta_gram_probe.json run 80,4800", 1200),
]
BATCH = [
    _checker(240, 2400, 32, "run_checker_ts.CI_UNITS: N = 32 against more modes", 5400),
    _checker(nvec_rule(2.9, 32), S_rule(2.9, 32), 32, "default rule at c = 2.9 (the 280-mode check)", 5400),
    _checker(nvec_rule(2.5, 32), S_rule(2.5, 32), 32, "default rule at c = 2.5", 7200),
    _checker(nvec_rule(2.2, 32), S_rule(2.2, 32), 32, "default rule at c = 2.2", 14400),
    _gram(140, 4800, "two_adic/ RESULTS s7b nvec response", 2400),
    _gram(160, 4800, "two_adic/ RESULTS s7b nvec response", 2400),
    _gram(180, 4800, "two_adic/ RESULTS s7b nvec response", 3600),
    _gram(200, 4800, "two_adic/ RESULTS s7b nvec response", 3600),
    _gram(160, 9600, "two_adic/ RESULTS s7b S check at 160 modes", 5400),
]
UNITS = {unit_name(u): u for u in CALIBRATION + BATCH}


def unit_cost_bound(u) -> float:
    """USD if the container runs to its Modal timeout at the CPU and memory limits."""
    return (u["timeout"] + MARGIN_S) * (CPU[1] * RATE_CORE_S + MEMORY_MIB[1] / 1024 * RATE_GIB_S)


def computed_cost(wall_s: float, peak_gib: float) -> float:
    """USD for wall_s seconds at the reserved cores and max(request, peak) GiB."""
    return wall_s * (CPU[0] * RATE_CORE_S + max(MEMORY_MIB[0] / 1024, peak_gib) * RATE_GIB_S)


# --------------------------------------------------------------- the image

_TGZ = os.environ.get("C4S2_TREE_TGZ", "")

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("git")
    # the local venv's versions (pip list, 2026-09-24); requirements.txt is not installed
    .pip_install("numpy==2.5.1", "scipy==1.18.0", "mpmath==1.3.0", "python-flint==0.9.0", "sympy==1.14.0")
    .run_commands("git config --global --add safe.directory '*'")
    .env({"PYTHONPATH": REMOTE_TREE, "OPENBLAS_NUM_THREADS": THREADS, "OMP_NUM_THREADS": THREADS,
          "MKL_NUM_THREADS": THREADS})
)
if modal.is_local():
    if not (_TGZ and os.path.isfile(_TGZ)):
        raise SystemExit("set C4S2_TREE_TGZ to the tarball of the standalone clone at 284eff6 (RUNS.md s1)")
    image = image.add_local_file(_TGZ, "/tmp/tree.tgz", copy=True).run_commands(
        f"mkdir -p {REMOTE_TREE} && tar -xzf /tmp/tree.tgz -C {REMOTE_TREE} --strip-components=1 --no-same-owner",
        "rm /tmp/tree.tgz",
        f"test \"$(git -C {REMOTE_TREE} rev-parse HEAD)\" = {TREE_COMMIT}",
        f"git -C {REMOTE_TREE} status --porcelain --untracked-files=all > /tmp/porcelain.txt; "
        "cat /tmp/porcelain.txt; test ! -s /tmp/porcelain.txt",
    )

app = modal.App(APP_NAME, image=image)
vol = modal.Volume.from_name(VOL_NAME, create_if_missing=True)


# ------------------------------------------------------ the remote side


def _run(cmd, cwd=REMOTE_TREE):
    import subprocess

    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=True).stdout


def _guard():
    """The tree's state and checker_glue's key, read in the container."""
    import sys

    chk = os.path.join(REMOTE_TREE, C4S2, "checker")
    if chk not in sys.path:
        sys.path.insert(0, chk)
    import checker_glue as G

    digest, dirty = G.ts_key()
    head = _run(["git", "rev-parse", "HEAD"]).strip()
    porcelain = _run(["git", "status", "--porcelain", "--untracked-files=all"])
    ok = head == TREE_COMMIT and digest == LOCAL_DIGEST and not dirty and not porcelain.strip()
    return {"ok": ok, "head": head, "ts_inputs_digest": digest, "dirty": dirty,
            "porcelain": porcelain.splitlines()}


def _machine():
    import platform
    import sys

    info = {"python": sys.version.split()[0], "platform": platform.platform(),
            "os_cpu_count": os.cpu_count()}
    try:
        info["sched_affinity"] = len(os.sched_getaffinity(0))
    except (AttributeError, OSError):
        info["sched_affinity"] = None
    try:
        with open("/proc/cpuinfo") as fh:
            info["cpu_model"] = next((ln.split(":", 1)[1].strip() for ln in fh if ln.startswith("model name")), None)
    except OSError:
        info["cpu_model"] = None
    try:  # gVisor reports the model as "unknown"; numpy's SIMD detection still reads the flags
        from numpy._core._multiarray_umath import __cpu_features__ as feats

        info["cpu_features"] = sorted(k for k, v in feats.items() if v)
    except ImportError:
        info["cpu_features"] = None
    for p in ("/sys/fs/cgroup/cpu.max", "/sys/fs/cgroup/memory.max"):
        try:
            with open(p) as fh:
                info[os.path.basename(p)] = fh.read().strip()
        except OSError:
            info[os.path.basename(p)] = None
    return info


def _versions():
    from importlib.metadata import version

    return {p: version(p) for p in ("numpy", "scipy", "mpmath", "python-flint", "sympy")}


# The child: one unit, one process. argv: kind, args (JSON), output path.
CHILD = r'''
import json, os, sys, time
kind, args, out = sys.argv[1], json.loads(sys.argv[2]), sys.argv[3]
root = os.environ["PYTHONPATH"].split(os.pathsep)[0]
c4 = os.path.join(root, "hunts", "weil_propagation", "c4_s2")
t0 = time.time()
if kind == "checker":
    sys.path.insert(0, os.path.join(c4, "checker"))
    import checker_glue as G
    import run_checker_ts as RC
    d0 = RC._guard()
    nv, S, N = int(args["nvec"]), args["S"], int(args["N"])
    rows, diag = RC.build_unit(nv, S, N)
    RC._guard(d0)
    stray = G.loaded_inputs_outside_key()
    if stray:
        raise SystemExit("refused: T_S loaded modules outside the key: " + ", ".join(stray))
    kmax = G._import(G.TWO_ADIC, "ta_prolate").kmax_for(nv)
    res = {"T_S": rows, "diag": diag, "kmax": kmax, "digest_child": d0}
elif kind == "gram":
    sys.path.insert(0, os.path.join(c4, "two_adic"))
    import ta_gram_probe as TGP
    nv, S = int(args["nvec"]), float(args["S"])
    r = TGP.run(nv, S)
    res = {"c": TGP.C, "N": TGP.N, "Q_low": TGP.q_low(), "runs": {f"{nv},{int(S)}": r}}
else:
    raise SystemExit("unknown kind " + kind)
res["child_seconds"] = round(time.time() - t0, 1)
with open(out, "w") as fh:
    json.dump(res, fh)
'''


def _vol_read(path):
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def _vol_write(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump(obj, fh)
    vol.commit()


@app.function(cpu=CPU, memory=MEMORY_MIB, timeout=900, volumes={"/vol": vol})
def smoke_remote():
    """The guard, the machine and the import chains, before any timed unit."""
    import subprocess
    import sys

    g = _guard()
    imports = {}
    for folder, mod in (("checker", "run_checker_ts"), ("two_adic", "ta_gram_probe")):
        code = (f"import sys; sys.path.insert(0, {os.path.join(REMOTE_TREE, C4S2, folder)!r}); "
                f"import {mod}; print({mod}.__file__)")
        p = subprocess.run([sys.executable, "-c", code], cwd=REMOTE_TREE, capture_output=True, text=True)
        imports[mod] = {"rc": p.returncode, "out": p.stdout.strip(), "err": p.stderr[-2000:]}
    g_after = _guard()
    return {"guard": g, "guard_after_imports": g_after, "imports": imports,
            "versions": _versions(), "machine": _machine(), "threads": THREADS}


@app.function(cpu=CPU, memory=MEMORY_MIB, timeout=3600, volumes={"/vol": vol}, single_use_containers=True)
def unit_remote(name: str, u: dict) -> dict:
    """One unit: marker, guard, child process under the unit's timeout, guard, Volume."""
    import resource
    import subprocess
    import sys

    t_start = time.time()
    vol.reload()
    res_path, mark_path = f"/vol/out/{name}.json", f"/vol/started/{name}.json"
    done = _vol_read(res_path)
    if done is not None:
        return done
    base = {"unit": name, "kind": u["kind"], "args": u["args"], "role": u["role"],
            "unit_timeout_s": u["timeout"], "tree_commit": TREE_COMMIT,
            "resources": {"cpu": list(CPU), "memory_mib": list(MEMORY_MIB), "threads": THREADS}}
    if _vol_read(mark_path) is not None:
        return dict(base, status="restarted", note="start marker present: an earlier attempt of this "
                    "input began and did not finish (preemption or container loss); not recomputed")
    _vol_write(mark_path, {"started_unix": t_start})
    g0 = _guard()
    base.update(ts_inputs_digest=g0["ts_inputs_digest"], guard_before=g0, versions=_versions(),
                machine=_machine(), started_unix=t_start)
    if not g0["ok"]:
        res = dict(base, status="guard_failed", wall_seconds=round(time.time() - t_start, 1))
        _vol_write(res_path, res)
        return res
    tmp = f"/tmp/{name}.json"
    t0 = time.time()
    try:
        p = subprocess.run([sys.executable, "-c", CHILD, u["kind"], json.dumps(u["args"]), tmp],
                           cwd=REMOTE_TREE, capture_output=True, text=True, timeout=u["timeout"])
        status = "ok" if p.returncode == 0 else "failed"
        err = p.stderr[-4000:]
    except subprocess.TimeoutExpired as e:
        status, err = "timed_out", (e.stderr or b"")[-4000:]
        err = err.decode("utf-8", "replace") if isinstance(err, bytes) else err
    child_wall = time.time() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    g1 = _guard()
    res = dict(base, status=status, child_wall_seconds=round(child_wall, 1),
               cpu_seconds=round(ru.ru_utime + ru.ru_stime, 1),
               peak_rss_mib=round(ru.ru_maxrss / 1024, 1), guard_after=g1, stderr_tail=err)
    if status == "timed_out":
        res["note"] = f"timed out at {u['timeout']} s (the unit's child-process limit)"
    if status == "ok":
        with open(tmp) as fh:
            payload = json.load(fh)
        if not g1["ok"] or g1["ts_inputs_digest"] != g0["ts_inputs_digest"]:
            res["status"] = "guard_failed_after"
        res["payload"] = payload
    res["wall_seconds"] = round(time.time() - t_start, 1)
    _vol_write(res_path, res)
    return res


# --------------------------------------------------------- the local side


def _local_digest():
    import sys

    chk = os.path.join(HERE, "..", "checker")
    if chk not in sys.path:
        sys.path.insert(0, chk)
    import checker_glue as G

    return G.ts_key()


def shaped(res: dict) -> dict:
    """The output file: checker units in checker_ts_snapshot.json's shape
    (meta, T_S {unit_key: rows}, units {nv|S|N: ...}); gram units in
    ta_gram_probe.json's shape (c, N, Q_low, runs {"nvec,S": run}) plus meta."""
    meta = {k: v for k, v in res.items() if k != "payload"}
    meta["ts_inputs_digest_local"] = LOCAL_DIGEST
    p = res.get("payload")
    if p is None:
        return {"meta": meta}
    if res["kind"] == "checker":
        a = res["args"]
        meta["route"] = ("run_checker_ts.build_unit(nvec, S, N): ta_prolate.delta_T_cells(ProlateModes(nvec, dps=20), "
                         "cells, N, S, alpha=1) + KernelProvider(nvec, S).T_inf_matrix(c, N, 40)")
        ukey = f"{a['nvec']}|{int(a['S'])}|{a['N']}"
        return {"meta": meta, "T_S": p["T_S"],
                "units": {ukey: {"role": res["role"], "seconds": p["child_seconds"], "kmax": p["kmax"],
                                 "diag": p["diag"], "S_exact": a["S"]}}}
    return {"c": p["c"], "N": p["N"], "Q_low": p["Q_low"], "runs": p["runs"], "meta": meta}


def _land(name: str, res: dict) -> dict:
    os.makedirs(OUT, exist_ok=True)
    out = shaped(res)
    with open(os.path.join(OUT, f"{name}.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    peak = (res.get("peak_rss_mib") or 0) / 1024
    wall = res.get("wall_seconds") or 0.0
    line = (f"| {name} | {res.get('status')} | {wall} | {res.get('cpu_seconds')} | "
            f"{res.get('peak_rss_mib')} | {computed_cost(wall, peak):.4f} | "
            f"{(res.get('machine') or {}).get('cpu_model')} | {time.strftime('%Y-%m-%d %H:%M:%S %z')} |")
    with open(RUNS, "a") as fh:
        fh.write(line + "\n")
    print("landed", line, flush=True)
    return out


def _drive(names):
    """spawn one call per unit (each with its own Modal timeout) and land each as it returns."""
    calls = {}
    for n in names:
        u = UNITS[n]
        f = unit_remote.with_options(timeout=int(u["timeout"] + MARGIN_S))
        calls[n] = f.spawn(n, u)
        print("spawned", n, calls[n].object_id, flush=True)
    results = {}
    while calls:
        for n in list(calls):
            try:
                res = calls[n].get(timeout=0)
            except Exception as e:  # noqa: BLE001
                if "Timeout" in type(e).__name__ and "Function" not in type(e).__name__:
                    continue
                res = {"unit": n, "kind": UNITS[n]["kind"], "args": UNITS[n]["args"], "role": UNITS[n]["role"],
                       "status": "modal_error", "error": f"{type(e).__name__}: {e}", "tree_commit": TREE_COMMIT}
            results[n] = _land(n, res)
            del calls[n]
        time.sleep(15)
    return results


def _max_abs(a, b):
    return max(abs(float(x) - float(y)) for ra, rb in zip(a, b) for x, y in zip(ra, rb))


def compare_calibration(outdir=None):
    """Max abs differences of the calibration units against the committed local values."""
    outdir = outdir or OUT
    c4 = os.path.join(HERE, "..")
    with open(os.path.join(c4, "checker", "checker_ts_snapshot.json")) as fh:
        snap = json.load(fh)["T_S"]
    with open(os.path.join(c4, "two_adic", "ta_gram_probe.json")) as fh:
        probe = json.load(fh)["runs"]["80,4800"]
    with open(os.path.join(outdir, "checker_200_2400_32.json")) as fh:
        mc = json.load(fh)["T_S"]
    with open(os.path.join(outdir, "gram_80_4800.json")) as fh:
        mg = json.load(fh)["runs"]["80,4800"]
    out = {"checker": {k: _max_abs(snap[k], mc[k]) for k in sorted(mc)}}
    g = {"dT": _max_abs(probe["dT"], mg["dT"])}
    for k in ("dT_probe_maxentry", "dT_probe_norm2", "gz_dev", "gz_dev_diag_max"):
        g[k] = abs(probe[k] - mg[k])
    g["TS_low3"] = max(abs(x - y) for x, y in zip(probe["TS_low3"], mg["TS_low3"]))
    g["Kmax_equal"] = probe["Kmax"] == mg["Kmax"]
    out["gram"] = g
    return out


@app.local_entrypoint()
def smoke():
    local = _local_digest()
    r = smoke_remote.remote()
    print(json.dumps(r, indent=1))
    print("local ts_key:", local)
    ok = r["guard"]["ok"] and r["guard_after_imports"]["ok"] and r["guard"]["ts_inputs_digest"] == local[0] == LOCAL_DIGEST \
        and not local[1] and all(v["rc"] == 0 for v in r["imports"].values())
    print("SMOKE", "PASS" if ok else "FAIL")


@app.local_entrypoint()
def calibrate():
    assert _local_digest() == (LOCAL_DIGEST, [])
    res = _drive([unit_name(u) for u in CALIBRATION])
    if all(r["meta"]["status"] == "ok" for r in res.values()):
        print("CALIBRATION", json.dumps(compare_calibration(), indent=1))
    else:
        print("CALIBRATION INCOMPLETE", {n: r["meta"]["status"] for n, r in res.items()})


@app.local_entrypoint()
def batch(units: str = ""):
    assert _local_digest() == (LOCAL_DIGEST, [])
    names = [n.strip() for n in units.split(",") if n.strip()] or [unit_name(u) for u in BATCH]
    unknown = [n for n in names if n not in UNITS]
    if unknown:
        raise SystemExit(f"unknown units {unknown}; known: {sorted(UNITS)}")
    _drive(names)


@app.local_entrypoint()
def fetch(units: str = ""):
    """Land units from the Volume (for a dropped session): modal/out/<unit>.json."""
    names = [n.strip() for n in units.split(",") if n.strip()] or sorted(UNITS)
    for n in names:
        try:
            data = b"".join(vol.read_file(f"out/{n}.json"))
        except Exception as e:  # noqa: BLE001
            print("absent", n, type(e).__name__)
            continue
        _land(n, json.loads(data))
