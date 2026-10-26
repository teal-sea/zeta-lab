"""Sharded landing census over [10^4, 10^5], for GitHub Actions.

Hunt #119, unit 3 (2026-10-26).  Driven by `.github/workflows/lambda-dh-census.yml`,
which runs only when `RUN_REQUEST.json` is pushed to this branch (it is not
committed until the coordinator says go). The pre-registration is
`RESULTS.md` section 8.12.

Per shard (a height interval of `census_plan_1e5.json`):

1. screen the interval at Re s = 0.82 (`deep_zeros.py screen`, checkpointed),
2. locate the flagged windows (`deep_zeros.py locate`),
3. land every located zero with y0 > 0.3396 (`census_1e4.py --source`, which
   skips rows already present: the resume),
4. write `shard_<i>.json` with the plan hash and per-stage CPU seconds.

Subcommands:

    plan       write census_plan_1e5.json and print its sha256 (committed)
    preflight  fail closed: pinned versions, ball backend, plan hash against
               RUN_REQUEST.json, and a smoke check (one committed census_1e4
               row recomputed and compared)
    run        one shard (--shard i), resumable
    gather     per shard, copy the most advanced copy among several downloaded
               attempts (subdirectories of --src) into --out
    merge      fold shard files into census_1e5.json, refusing a missing shard
               or a shard from another plan
    calib      summarize a calibration shard: CPU seconds per screened 20-unit
               window and per census window, and the projected core-hours

Grade of everything it produces: *measured* (float screen, ODE landings).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
PLAN = os.path.join(HERE, "census_plan_1e5.json")
REQUEST = os.path.join(HERE, "RUN_REQUEST.json")
PINS = os.path.join(HERE, "census_constraints.txt")

T0, T1 = 10000, 100000
SHARD_WIDTH = 2500            # 36 shards; a multiple of the 20-unit screen window
SIGMA_C = 0.82
MIN_Y0 = 0.3396               # y0^2/2 > 0.0576518 needs y0 > 0.33957
SMOKE_GAMMA = 240.4047        # the floor pair: census_1e4.json control row
SMOKE_RTOL = 1e-6


def canonical(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()


def plan_obj() -> dict:
    shards = [[T0 + SHARD_WIDTH * i, T0 + SHARD_WIDTH * (i + 1)]
              for i in range((T1 - T0) // SHARD_WIDTH)]
    return {"what": "hunt #119 census [1e4, 1e5]", "sigma_c": SIGMA_C, "min_y0": MIN_Y0,
            "census_half_window": 40.0, "ode_steps": 800, "shards": shards}


def plan_sha(path: str | None = None) -> str:
    return hashlib.sha256(canonical(json.load(open(path or PLAN)))).hexdigest()


def stage_plan() -> None:
    with open(PLAN, "w") as fh:
        json.dump(plan_obj(), fh, indent=1)
        fh.write("\n")
    print(plan_sha())


def _pins() -> dict:
    out = {}
    for line in open(PINS):
        line = line.split("#")[0].strip()
        if line:
            name, ver = line.split("==")
            out[name.strip().lower()] = ver.strip()
    return out


def stage_preflight() -> None:
    from importlib.metadata import version
    pins = _pins()
    for name, ver in pins.items():
        got = version(name)
        if got != ver:
            raise SystemExit(f"preflight: {name} {got} != pinned {ver}")
    sys.path.insert(0, ROOT)
    from zeta import rigor
    if rigor.BACKEND != "python-flint":
        raise SystemExit(f"preflight: ball backend {rigor.BACKEND}")
    req = json.load(open(REQUEST))
    if req.get("plan_sha256") != plan_sha():
        raise SystemExit("preflight: RUN_REQUEST plan_sha256 does not match census_plan_1e5.json")
    if PLAN == os.path.join(HERE, "census_plan_1e5.json") and plan_obj() != json.load(open(PLAN)):
        raise SystemExit("preflight: census_plan_1e5.json differs from the plan this code generates")
    if req.get("mode") not in ("calibrate", "full"):
        raise SystemExit(f"preflight: mode {req.get('mode')!r}")
    # smoke: recompute the committed control row and compare
    sys.path.insert(0, HERE)
    import census_1e4 as cz
    rec = next(r for r in json.load(open(os.path.join(HERE, "census_1e4.json")))["rows"]
               if abs(r["gamma"] - SMOKE_GAMMA) < 1e-3)
    got = cz.census_one(rec["gamma"], rec["y0"])
    for k in ("n_line", "n_strip", "n_right_beta_gt_0.505"):
        if got[k] != rec[k]:
            raise SystemExit(f"preflight smoke: {k} {got[k]} != recorded {rec[k]}")
    if abs(got["landing_ode"] / rec["landing_ode"] - 1) > SMOKE_RTOL:
        raise SystemExit(f"preflight smoke: landing {got['landing_ode']} vs {rec['landing_ode']}")
    print(json.dumps({"preflight": "ok", "pins": pins, "plan_sha256": plan_sha(),
                      "smoke_landing": got["landing_ode"], "smoke_seconds": got["seconds"]}))


def _cpu(cmd: list[str]) -> float:
    """Run cmd to completion; return its user + sys CPU seconds."""
    before = os.times()
    subprocess.run(cmd, check=True)
    after = os.times()
    return (after.children_user - before.children_user) + (after.children_system - before.children_system)


def stage_run(i: int, out_dir: str) -> None:
    plan = json.load(open(PLAN))
    t0, t1 = plan["shards"][i]
    os.makedirs(out_dir, exist_ok=True)
    screen = os.path.join(out_dir, f"screen_{i}.json")
    census = os.path.join(out_dir, f"census_{i}.json")
    summary = os.path.join(out_dir, f"shard_{i}.json")
    py = sys.executable
    dz = os.path.join(HERE, "deep_zeros.py")
    cpu = {}
    cpu["screen"] = _cpu([py, dz, "screen", "--t0", str(t0), "--t1", str(t1), "--sigma-c", str(SIGMA_C),
                          "--out", screen, "--key", "screen_c82"])
    cpu["locate"] = _cpu([py, dz, "locate", "--sigma-c", str(SIGMA_C), "--out", screen, "--key", "screen_c82"])
    cpu["census"] = _cpu([py, os.path.join(HERE, "census_1e4.py"), "--source", screen,
                          "--min-y0", str(plan["min_y0"]), "--out", census])
    sc = json.load(open(screen))
    rows = json.load(open(census))["rows"] if os.path.exists(census) else []
    n_cand = sum(z["y0"] > plan["min_y0"] for z in sc.get("zeros", []))
    # CPU accumulates across resumed runs, so a calibration read after a
    # resume still sees the whole cost of the shard
    prev = json.load(open(summary))["cpu_seconds"] if os.path.exists(summary) else {}
    runs = (json.load(open(summary)).get("runs", 1) + 1) if os.path.exists(summary) else 1
    cpu = {k: cpu[k] + prev.get(k, 0.0) for k in cpu}
    body = {"shard": i, "interval": [t0, t1], "plan_sha256": plan_sha(), "runs": runs,
            "screen_complete": sc["screen_c82"]["complete"],
            "n_screen_windows": len(sc["screen_c82"]["boundaries"]) - 1,
            "n_located": len(sc.get("zeros", [])), "n_candidates": n_cand,
            "n_landed": sum(r["landing_ode"] is not None for r in rows),
            "n_unaccounted": sum(not r["accounting_ok"] for r in rows),
            "cpu_seconds": cpu, "finished": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    with open(summary, "w") as fh:
        json.dump(body, fh, indent=1)
    print(json.dumps(body))


def stage_calib(out_dir: str, i: int = 0) -> None:
    s = json.load(open(os.path.join(out_dir, f"shard_{i}.json")))
    per_screen = (s["cpu_seconds"]["screen"] + s["cpu_seconds"]["locate"]) / max(1, s["n_screen_windows"])
    per_census = s["cpu_seconds"]["census"] / max(1, s["n_candidates"])
    plan = json.load(open(PLAN))
    n_windows = (T1 - T0) // 20
    # candidate count scales with the shard's share of the decade; one shard is a lower-precision sample
    n_cand = s["n_candidates"] * len(plan["shards"])
    # less noisy: the decade's 111 zeros at Re s > 0.85 (deep_zeros_hi_20261026.json,
    # measured) scaled by this shard's ratio of candidates to those
    hi = json.load(open(os.path.join(HERE, "deep_zeros_hi_20261026.json")))["zeros"]
    t0, t1 = s["interval"]
    n85_here = sum(t0 <= z["gamma"] < t1 for z in hi)
    n_cand_scaled = (len(hi) * s["n_candidates"] / n85_here) if n85_here else None
    total = per_screen * n_windows + per_census * n_cand
    out = {"cpu_s_per_screen_window": per_screen, "cpu_s_per_census_window": per_census,
           "projected_candidates": n_cand, "projected_core_hours": total / 3600,
           "n_085_zeros_in_shard": n85_here, "projected_candidates_scaled": n_cand_scaled,
           "projected_core_hours_scaled": (per_screen * n_windows + per_census * n_cand_scaled) / 3600
           if n_cand_scaled is not None else None,
           "from_shard": s}
    with open(os.path.join(out_dir, "calibration.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps(out, indent=1))


def _progress(d: str, i: int) -> tuple:
    """How far a copy of shard i got: (summary present, screen complete, landed, runs, screen size)."""
    summ = os.path.join(d, f"shard_{i}.json")
    screen = os.path.join(d, f"screen_{i}.json")
    census = os.path.join(d, f"census_{i}.json")
    landed = len(json.load(open(census))["rows"]) if os.path.exists(census) else 0
    if os.path.exists(summ):
        sm = json.load(open(summ))
        return (1, int(sm["screen_complete"]), landed, sm.get("runs", 1), 0)
    size = os.path.getsize(screen) if os.path.exists(screen) else 0
    return (0, 0, landed, 0, size)


def stage_gather(src: str, out_dir: str) -> None:
    """Copy, per shard, the most advanced copy found in src's subdirectories into out_dir.

    Artifacts of different attempts carry files with the same names; this picks
    by progress rather than by download order, so a stale copy cannot win.
    """
    import shutil
    plan = json.load(open(PLAN))
    os.makedirs(out_dir, exist_ok=True)
    dirs = [os.path.join(src, d) for d in sorted(os.listdir(src))] if os.path.isdir(src) else []
    dirs = [d for d in dirs if os.path.isdir(d)]
    picked = {}
    for i in range(len(plan["shards"])):
        best = max(dirs, key=lambda d: _progress(d, i), default=None)
        if best is None or _progress(best, i) == (0, 0, 0, 0, 0):
            continue
        for name in (f"shard_{i}.json", f"screen_{i}.json", f"census_{i}.json"):
            f = os.path.join(best, name)
            if os.path.exists(f):
                shutil.copy2(f, os.path.join(out_dir, name))
        picked[i] = os.path.basename(best)
    print(json.dumps({"gathered": picked}))


def stage_merge(in_dir: str) -> None:
    plan = json.load(open(PLAN))
    sha = plan_sha()
    rows, shards = [], []
    for i in range(len(plan["shards"])):
        p = os.path.join(in_dir, f"shard_{i}.json")
        if not os.path.exists(p):
            raise SystemExit(f"merge: shard {i} missing")
        s = json.load(open(p))
        if s["plan_sha256"] != sha or not s["screen_complete"]:
            raise SystemExit(f"merge: shard {i} from another plan or incomplete")
        shards.append(s)
        c = os.path.join(in_dir, f"census_{i}.json")
        rows += json.load(open(c))["rows"] if os.path.exists(c) else []
    out = {"plan_sha256": sha, "shards": shards, "rows": sorted(rows, key=lambda r: r["gamma"])}
    with open(os.path.join(in_dir, "census_1e5.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"merged {len(shards)} shards, {len(rows)} rows")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("stage", choices=["plan", "preflight", "run", "merge", "calib", "gather"])
    ap.add_argument("--src", default="prior")
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--out", default="out")
    ap.add_argument("--request", default=None, help="override RUN_REQUEST.json (local tests only)")
    ap.add_argument("--plan", default=None, help="override census_plan_1e5.json (local tests only)")
    a = ap.parse_args()
    global REQUEST, PLAN
    if a.request:
        REQUEST = a.request
    if a.plan:
        PLAN = a.plan
    if a.stage == "plan":
        stage_plan()
    elif a.stage == "preflight":
        stage_preflight()
    elif a.stage == "run":
        stage_run(a.shard, a.out)
    elif a.stage == "calib":
        stage_calib(a.out, a.shard)
    elif a.stage == "gather":
        stage_gather(a.src, a.out)
    else:
        stage_merge(a.out)


if __name__ == "__main__":
    main()
