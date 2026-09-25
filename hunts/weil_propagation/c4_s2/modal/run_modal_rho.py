"""modal/ follow-up 2 (BRIEF.md, 2026-09-24): every checker/ unit under the QR rho.

two_adic/ replaced the explicit inverse in ta_mellin.rho by a QR of the Gram
factor (c3dca00, eea7eab), so T_S's input digest moved from 1dcab230 to
b2e7787b and checker/'s guard refuses every old snapshot row. This driver
rebuilds all eleven checker/ units on Modal from a clean clone of the tree at
e2b46a5 (TREE_COMMIT) and writes them to modal/out_rho/. It records raw rows,
the diagnostics build_unit already returns (diag: gram_z_offI, cond_Gb,
cond_Fz, cond_Fb), times and costs. It computes no eigenvalue of T_S or R_S:
checker/ commits its reading first.

run_modal.py (the first follow-up, tree 284eff6, digest 1dcab230) is left as
it is, with modal/out/ and its pins: it is the record of the old route. This
file is a copy of its machinery with four changes: the tree and digest, the
units (checker only, dps (40, 60) at N = 8 as run_checker_ts.snapshot builds
them), the output folder, and a separate app and Volume. The Volume must be
new: the old one holds finished results and start markers under five of the
same unit names, which unit_remote would return without computing.

The guard is unchanged: inside the container, before and after each build,
HEAD is TREE_COMMIT, `git status --porcelain --untracked-files=all` is empty
for the whole tree, and checker_glue.ts_key() returns LOCAL_DIGEST with an
empty dirty list. A unit that fails it computes nothing.

Build the clone and its tarball first (RUNS.md s7.1), then, from the worktree
root, with C4S2_RHO_TREE_TGZ=<scratch>/tree_rho.tgz in the environment:

    modal run hunts/weil_propagation/c4_s2/modal/run_modal_rho.py::smoke
    modal run hunts/weil_propagation/c4_s2/modal/run_modal_rho.py::calibrate
    modal run --detach hunts/weil_propagation/c4_s2/modal/run_modal_rho.py::batch [--units a,b]
    modal run hunts/weil_propagation/c4_s2/modal/run_modal_rho.py::fetch [--units a,b] [--no-log]

The Modal CLI imports this file in its own interpreter, so numpy and
repository imports stay inside the remote functions and the child code.
"""

from __future__ import annotations

import json
import math
import os
import time

import modal

APP_NAME = "c4s2-modal-rho"
VOL_NAME = "c4s2-modal-rho-out"
TREE_COMMIT = "e2b46a5a82f365469a814f80c94b5232cf8bee46"
# checker_glue.ts_key()[0] in this worktree at e2b46a5 (modal/ is outside T_S's
# import closure, so later commits here leave it unchanged).
LOCAL_DIGEST = "b2e7787bce7a77db4a1a81b9311fc75a2b9326649b88a49883bd4d737ca70eaa"
C4S2 = "hunts/weil_propagation/c4_s2"
REMOTE_TREE = "/tree"

# Resources per container, as in run_modal.py. Billing is per reserved
# core-second and GiB-second (the larger of reservation and use); the limits
# cap use, so they cap cost.
CPU = (4.0, 4.0)  # physical cores (request, limit)
MEMORY_MIB = (16384, 32768)  # (request, limit)
THREADS = "4"  # BLAS threads: the container sees 4 CPUs (RUNS.md s1)
MARGIN_S = 600  # container timeout = unit timeout + MARGIN_S

# Read on 2026-09-24 with `modal billing rates`: 0.0473 USD per core-hour,
# 0.008 USD per GiB-hour (RUNS.md s7.2).
RATE_CORE_S = 0.0473 / 3600
RATE_GIB_S = 0.008 / 3600

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out_rho")
RUNS = os.path.join(HERE, "RUNS.md")
CAL_TOL = 1e-10  # BRIEF.md follow-up 2, fixed before the run


# --------------------------------------------------------------- the units


def nvec_rule(c: float, N: int) -> int:
    """two_adic/ta_ts.py:146 (KernelProvider.delta_T): nvec = max(80, int(8 N / L) + 40)."""
    return max(80, int(8 * N / math.log(c)) + 40)


def S_rule(c: float, N: int) -> float:
    """two_adic/ta_ts.py:147 (KernelProvider.delta_T): S = max(1200, 12 * 2 pi N / L), L = log c."""
    return max(1200.0, 12.0 * 2 * math.pi * N / math.log(c))


def _checker(nv, S, N, role, timeout):
    return {"kind": "checker", "args": {"nvec": nv, "S": S, "N": N}, "role": role, "timeout": timeout,
            "dps": [40, 60] if N == 8 else [40]}


def unit_name(u) -> str:
    a = u["args"]
    return f"checker_{a['nvec']}_{int(a['S'])}_{a['N']}"


# timeout: the unit's child-process limit in seconds (RUNS.md s7.2 derives each).
# The first is both the calibration unit and one of the eleven.
CALIBRATION = [
    _checker(80, 1200, 8, "run_checker_ts.UNITS: converged (calibration unit)", 1200),
]
BATCH = [
    _checker(120, 1600, 16, "run_checker_ts.UNITS: converged", 1200),
    _checker(200, 2400, 32, "run_checker_ts.UNITS: converged", 2400),
    _checker(80, 1600, 16, "run_checker_ts.UNITS: mode_count_response", 1200),
    _checker(120, 1200, 16, "run_checker_ts.UNITS: quadrature_response", 1200),
    _checker(80, 1200, 16, "run_checker_ts.UNITS: same_settings_P3", 1200),
    _checker(160, 1600, 16, "run_checker_ts.UNITS: mode_count_up", 1200),
    _checker(240, 2400, 32, "run_checker_ts.CI_UNITS: mode_count_up", 3600),
    _checker(nvec_rule(2.9, 32), S_rule(2.9, 32), 32, "default rule at c = 2.9", 3600),
    _checker(nvec_rule(2.5, 32), S_rule(2.5, 32), 32, "default rule at c = 2.5", 5400),
    _checker(nvec_rule(2.2, 32), S_rule(2.2, 32), 32, "default rule at c = 2.2", 10800),
]
UNITS = {unit_name(u): u for u in CALIBRATION + BATCH}

# Measured 2026-09-24 14:11 -0500 (RUNS.md s7.4, app ap-r0YfOJE3NKR8yfoGTpakcI)
# and carried in every output's meta. Max abs only: the threshold is stated in
# max abs, and no eigenvalue of T_S or R_S is computed here.
CHECKER_CALIBRATION = {
    "unit": "checker_80_1200_8",
    "against": "out_rho/local_checker_80_1200_8.json (macOS arm64, Python 3.13.14, same code, digest b2e7787b)",
    "threshold": CAL_TOL,
    "max_abs_diff": {"2.2|8|40|80|1200": 5.773159728050814e-15, "2.2|8|60|80|1200": 5.773159728050814e-15,
                     "2.5|8|40|80|1200": 4.884981308350689e-15, "2.5|8|60|80|1200": 4.884981308350689e-15,
                     "2.9|8|40|80|1200": 7.105427357601002e-15, "2.9|8|60|80|1200": 7.105427357601002e-15},
    "max": 7.105427357601002e-15,
    "passed": True,
    "note": "measured on the N = 8 unit only (cond_Fz 16.5, cond_Fb 16.7); no platform floor was measured for the "
            "N = 16 and N = 32 units under the QR route (two_adic/ A3's 3e-12 is a perturbation proxy at "
            "(200, 2400, 32), not a rebuild); the calibration of the first follow-up (modal/out/, digest "
            "1dcab230) does not apply to these rows",
}


def unit_cost_bound(u) -> float:
    """USD if the container runs to its Modal timeout at the CPU and memory limits."""
    return (u["timeout"] + MARGIN_S) * (CPU[1] * RATE_CORE_S + MEMORY_MIB[1] / 1024 * RATE_GIB_S)


def computed_cost(wall_s: float, peak_gib: float) -> float:
    """USD for wall_s seconds at the reserved cores and max(request, peak) GiB."""
    return wall_s * (CPU[0] * RATE_CORE_S + max(MEMORY_MIB[0] / 1024, peak_gib) * RATE_GIB_S)


# --------------------------------------------------------------- the image

_TGZ = os.environ.get("C4S2_RHO_TREE_TGZ", "")

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
        raise SystemExit("set C4S2_RHO_TREE_TGZ to the tarball of the standalone clone at e2b46a5 (RUNS.md s7.1)")
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


# The child: one unit, one process. argv: args (JSON), output path.
CHILD = r'''
import json, os, sys, time
args, out = json.loads(sys.argv[1]), sys.argv[2]
root = os.environ["PYTHONPATH"].split(os.pathsep)[0]
c4 = os.path.join(root, "hunts", "weil_propagation", "c4_s2")
t0 = time.time()
sys.path.insert(0, os.path.join(c4, "checker"))
import checker_glue as G
import run_checker_ts as RC
d0 = RC._guard()
nv, S, N, dps = int(args["nvec"]), args["S"], int(args["N"]), tuple(args["dps"])
rows, diag = RC.build_unit(nv, S, N, dps_list=dps)
RC._guard(d0)
stray = G.loaded_inputs_outside_key()
if stray:
    raise SystemExit("refused: T_S loaded modules outside the key: " + ", ".join(stray))
kmax = G._import(G.TWO_ADIC, "ta_prolate").kmax_for(nv)
res = {"T_S": rows, "diag": diag, "kmax": kmax, "digest_child": d0}
res["child_seconds"] = round(time.time() - t0, 1)
try:  # the OpenBLAS kernel family actually loaded (numpy's bundled library)
    import ctypes, glob, numpy
    core = None
    for lib in glob.glob(os.path.join(os.path.dirname(numpy.__file__), "..", "numpy.libs", "*openblas*")):
        L = ctypes.CDLL(lib)
        for sym in ("scipy_openblas_get_corename64_", "openblas_get_corename64_", "openblas_get_corename"):
            f = getattr(L, sym, None)
            if f is not None:
                f.restype = ctypes.c_char_p
                core = f().decode()
                break
    res["blas_core"] = core
except Exception as e:
    res["blas_core"] = "unread: " + type(e).__name__
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
    """The guard, the machine and the import chain, before any timed unit."""
    import subprocess
    import sys

    g = _guard()
    code = (f"import sys; sys.path.insert(0, {os.path.join(REMOTE_TREE, C4S2, 'checker')!r}); "
            "import run_checker_ts; print(run_checker_ts.__file__)")
    p = subprocess.run([sys.executable, "-c", code], cwd=REMOTE_TREE, capture_output=True, text=True)
    imports = {"run_checker_ts": {"rc": p.returncode, "out": p.stdout.strip(), "err": p.stderr[-2000:]}}
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
    base = {"unit": name, "kind": u["kind"], "args": u["args"], "dps": u["dps"], "role": u["role"],
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
        p = subprocess.run([sys.executable, "-c", CHILD, json.dumps(dict(u["args"], dps=u["dps"])), tmp],
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
    """The output file in checker_ts_snapshot.json's shape: meta, T_S
    {unit_key: rows}, units {nv|S|N: {role, seconds, kmax, diag, S_exact}}."""
    meta = {k: v for k, v in res.items() if k != "payload"}
    meta["ts_inputs_digest_local"] = LOCAL_DIGEST
    p = res.get("payload")
    if p is None:
        return {"meta": meta}
    a = res["args"]
    meta["route"] = ("run_checker_ts.build_unit(nvec, S, N, dps_list): ta_prolate.delta_T_cells(ProlateModes(nvec, "
                     "dps=20), cells, N, S, alpha=1) + KernelProvider(nvec, S).T_inf_matrix(c, N, dps), rho by QR "
                     "of the Gram factor")
    meta["blas_core"] = p.get("blas_core")
    meta["calibration"] = CHECKER_CALIBRATION
    ukey = f"{a['nvec']}|{int(a['S'])}|{a['N']}"
    return {"meta": meta, "T_S": p["T_S"],
            "units": {ukey: {"role": res["role"], "seconds": p["child_seconds"], "kmax": p["kmax"],
                             "diag": p["diag"], "S_exact": a["S"]}}}


def _land(name: str, res: dict, log: bool = True) -> dict:
    os.makedirs(OUT, exist_ok=True)
    out = shaped(res)
    with open(os.path.join(OUT, f"{name}.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    if not log:
        print("reshaped", name, flush=True)
        return out
    peak = (res.get("peak_rss_mib") or 0) / 1024
    wall = res.get("wall_seconds") or 0.0
    line = (f"| {name} | {res.get('status')} | {wall} | {res.get('cpu_seconds')} | "
            f"{res.get('peak_rss_mib')} | {computed_cost(wall, peak):.4f} | "
            f"{(res.get('meta') or {}).get('blas_core') or (res.get('payload') or {}).get('blas_core')} | "
            f"{time.strftime('%Y-%m-%d %H:%M:%S %z')} |")
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
        with open(RUNS, "a") as fh:
            fh.write(f"| {n} | spawned {calls[n].object_id} | | | | | | {time.strftime('%Y-%m-%d %H:%M:%S %z')} |\n")
    results = {}
    while calls:
        for n in list(calls):
            try:
                res = calls[n].get(timeout=0)
            except Exception as e:  # noqa: BLE001
                if "Timeout" in type(e).__name__ and "Function" not in type(e).__name__:
                    continue
                res = {"unit": n, "kind": "checker", "args": UNITS[n]["args"], "role": UNITS[n]["role"],
                       "status": "modal_error", "error": f"{type(e).__name__}: {e}", "tree_commit": TREE_COMMIT}
            results[n] = _land(n, res)
            del calls[n]
        time.sleep(15)
    return results


def _max_abs(a, b):
    return max(abs(float(x) - float(y)) for ra, rb in zip(a, b) for x, y in zip(ra, rb))


def compare_calibration(outdir=None):
    """Max abs difference per row key of the Modal calibration unit against the
    local build (out_rho/local_checker_80_1200_8.json), and the diag fields."""
    outdir = outdir or OUT
    with open(os.path.join(outdir, "local_checker_80_1200_8.json")) as fh:
        loc = json.load(fh)
    with open(os.path.join(outdir, "checker_80_1200_8.json")) as fh:
        mod = json.load(fh)
    if set(loc["T_S"]) != set(mod["T_S"]):
        raise SystemExit(f"row keys differ: {sorted(loc['T_S'])} against {sorted(mod['T_S'])}")
    diffs = {k: _max_abs(loc["T_S"][k], mod["T_S"][k]) for k in sorted(loc["T_S"])}
    dl, dm = loc["units"]["80|1200|8"]["diag"], mod["units"]["80|1200|8"]["diag"]
    return {"max_abs_diff": diffs, "max": max(diffs.values()), "threshold": CAL_TOL,
            "passed": max(diffs.values()) <= CAL_TOL,
            "diag_local": dl, "diag_modal": dm,
            "local_digest": loc["meta"]["ts_inputs_digest"], "modal_digest": mod["meta"]["ts_inputs_digest"]}


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
        c = compare_calibration()
        print("CALIBRATION", "PASS" if c["passed"] else "MISSED", json.dumps(c, indent=1))
    else:
        print("CALIBRATION INCOMPLETE", {n: r["meta"]["status"] for n, r in res.items()})


@app.local_entrypoint()
def batch(units: str = ""):
    assert _local_digest() == (LOCAL_DIGEST, [])
    if CHECKER_CALIBRATION is None or not CHECKER_CALIBRATION.get("passed"):
        raise SystemExit("refused: the calibration has not been recorded as passed (CHECKER_CALIBRATION)")
    names = [n.strip() for n in units.split(",") if n.strip()] or [unit_name(u) for u in BATCH]
    unknown = [n for n in names if n not in UNITS]
    if unknown:
        raise SystemExit(f"unknown units {unknown}; known: {sorted(UNITS)}")
    _drive(names)


@app.local_entrypoint()
def fetch(units: str = "", log: bool = True):
    """Land units from the Volume (for a dropped session): modal/out_rho/<unit>.json.
    --no-log rewrites the files only (to re-apply shaped() to units already
    logged), with no new line in RUNS.md."""
    names = [n.strip() for n in units.split(",") if n.strip()] or sorted(UNITS)
    for n in names:
        try:
            data = b"".join(vol.read_file(f"out/{n}.json"))
        except Exception as e:  # noqa: BLE001
            print("absent", n, type(e).__name__)
            continue
        _land(n, json.loads(data), log=log)
