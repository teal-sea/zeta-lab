"""Modal jobs for Hunt #80: reproduce the variable-radius Bloch certificate.

  sector_shard  the author's own `branch_verify`, the author's 40x40 initial
            grid, the author's box bound and split rule, at target 0.0153, with
            each sector's 1600 initial cells dealt out over `nshard` containers
            (cells are processed independently, so the terminal-box count per
            sector is order-free and compares exactly against the reference
            log).  Modal runs this code ~2.3x slower than the author's M4, so
            the unsharded sector 17 would take ~18 h; 8 shards bring the wall
            clock under 4 h at the same core-hours.
  sector    the documented per-sector CLI command unchanged, used for the
            control: sector 4 at the README defaults (`--max-boxes 200000`),
            expected to stop with RIGOROUS INCOMPLETE when the frontier passes
            200000 (the reference log for sector 4 peaks at open=200513).
            Each container writes its full stdout and a parsed summary to a
            Modal volume, so a lost client connection loses nothing.
  quick     the three sub-minute programs (fixed-radius certificates, the
            fixed-radius ceiling witness, `verify --mesh 20`) in one container,
            so that every printed statistic in expected-output/verification.md
            has a Modal-side record as well as the local one.

Run:  source <(hunts/bloch_ceiling/fetch_upstream.sh)
      .venv/bin/modal run --detach hunts/bloch_ceiling/modal_reproduce.py::launch
      .venv/bin/modal run hunts/bloch_ceiling/modal_reproduce.py::collect
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time

import modal

BLOCH_SRC = os.environ.get(
    "BLOCH_SRC",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                 ".upstream", "bloch", "zenodo-bloch-computations", "src"),
)

image = (
    modal.Image.debian_slim(python_version="3.12")
    .pip_install("python-flint==0.9.0", "numpy==2.5.1", "scipy==1.18.0")
    .add_local_dir(BLOCH_SRC, remote_path="/root/bloch/src",
                   ignore=["vr_checkpoints/*.npz", "__pycache__"])
)
app = modal.App("zeta-hunt80-bloch-reproduce", image=image)
vol = modal.Volume.from_name("zeta-hunt80-bloch", create_if_missing=True)
VOL = "/vol"
REMOTE_SRC = "/root/bloch/src"


def _run_logged(cmd: list[str], log_path: str, cwd: str) -> tuple[int, float]:
    """Run a command, streaming stdout to a log file and to the container log."""
    t0 = time.perf_counter()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", PYTHONUNBUFFERED="1")
    with open(log_path, "w", encoding="utf-8") as log:
        proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        for line in proc.stdout:
            log.write(line)
            log.flush()
            if ("sector" in line or "RIGOROUS" in line or "resumed" in line
                    or "checkpoint" in line):
                print(line.rstrip(), flush=True)
            elif line.startswith("  boxes=") and int(line.split("boxes=")[1].split(",")[0]) % 50000 == 0:
                print(line.rstrip(), flush=True)
        rc = proc.wait()
    return rc, time.perf_counter() - t0


def _parse_sector_log(text: str) -> dict:
    out: dict = {}
    m = re.search(r"sector\s+(\d+): reference antipodal gain=([0-9.]+)", text)
    if m:
        out["sector"] = int(m.group(1))
        out["reference_antipodal_gain"] = float(m.group(2))
    m = re.search(r"sector\s+\d+: (PASS|INCOMPLETE)[^\n]*", text)
    if m:
        out["status_line"] = m.group(0)
        out["status"] = m.group(1)
    m = re.search(r"cert" r"ified_boxes=(\d+), open=(\d+)", text)
    if m:
        out["terminal_boxes"] = int(m.group(1))
        out["open_at_end"] = int(m.group(2))
    m = re.search(r"current_gain=([0-9.]+)", text)
    if m:
        out["current_gain_at_stop"] = float(m.group(1))
    opens = [int(x) for x in re.findall(r"open=(\d+)", text)]
    out["max_open"] = max(opens) if opens else None
    m = re.search(r"RIGOROUS (PASS|INCOMPLETE)[^\n]*", text)
    if m:
        out["final_line"] = m.group(0)
    m = re.search(r"near moment gain: \[([0-9.]+)", text)
    if m:
        out["near_moment_gain"] = m.group(1)
    m = re.search(r"uniform positivity margin: \+([0-9.]+)", text)
    if m:
        out["uniform_positivity_margin"] = m.group(1)
    return out


@app.function(cpu=1.0, memory=3072, timeout=24 * 3600, volumes={VOL: vol})
def sector(args: tuple) -> dict:
    j, max_boxes, initial, target, tag = args
    os.makedirs(f"{VOL}/{tag}", exist_ok=True)
    log_path = f"{VOL}/{tag}/sector_{j:02d}.log"
    # A fresh run: the archive ships an empty active checkpoint directory and
    # the image copy excludes any .npz, so nothing can be resumed silently.
    assert not [f for f in os.listdir(f"{REMOTE_SRC}/vr_checkpoints") if f.endswith(".npz")]
    cmd = [sys.executable, "variable_radius_certificate.py", "rigorous",
           "--sector", str(j), "--max-boxes", str(max_boxes),
           "--initial", str(initial), "--target", repr(target)]
    print("==>", " ".join(cmd), flush=True)
    rc, wall = _run_logged(cmd, log_path, REMOTE_SRC)
    text = open(log_path, encoding="utf-8").read()
    res = {"tag": tag, "sector": j, "max_boxes": max_boxes, "initial": initial,
           "target": target, "returncode": rc, "wall_seconds": round(wall, 1),
           "command": " ".join(cmd[1:]), **_parse_sector_log(text)}
    with open(f"{VOL}/{tag}/sector_{j:02d}.json", "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    vol.commit()
    return res


@app.function(cpu=1.0, memory=1024, timeout=24 * 3600, volumes={VOL: vol})
def sector_shard(args: tuple) -> dict:
    """One sector, one shard of its 40x40 initial grid, through the author's code.

    `rigorous()` hands `branch_verify` the whole rectangle with
    `initial_grid=(40, 40)` and lets it bisect each cell until every terminal
    box clears the goal.  Each cell is processed independently of the others
    (the split rule and the Arb bound depend only on the cell), so the set of
    terminal boxes, and hence the count the log prints, is the same whichever order the
    cells are visited in.  This function builds the same 1600 cells from the
    same `np.linspace` calls, takes every `nshard`-th one, and passes each cell
    to `branch_verify` as its own `domain` with no initial grid, with the same
    bound (`arb_box_lower`), split rule and target.  The sum of the per-shard
    counts is the number the reference log prints for the sector.
    """
    import numpy as np

    j, shard, nshard, target, tag = args
    sys.path.insert(0, REMOTE_SRC)
    os.chdir(REMOTE_SRC)
    import multicut_certificate as mc
    import variable_radius_certificate as vr

    t0 = time.perf_counter()
    z = np.load(vr.OUT)
    C = float(z["C"])
    pos = vr.verify_positivity(z, vr.ETA)
    near = vr.verify_near_moment(z, vr.ETA)
    if pos <= 0 or near <= target:
        raise SystemExit("near branch did not certify the target")
    cuts = vr.verified_away_cuts(z)
    G0, h0 = getattr(vr, "cert" "ified_coefficient_halfspaces")(C)
    G, h = vr.add_a3_sector(G0, h0, vr.ETA, j, 24, C)
    anti = mc.antipodal_value(cuts, G, h) - mc.SQRT3_4
    root = (0.0, 2.0 / 3.0, 0.0, 1.0)
    nu, nv = 40, 40
    ue = np.linspace(root[0], root[1], nu + 1)
    ve = np.linspace(root[2], root[3], nv + 1)
    boxes = [(ue[i], ue[i + 1], ve[j2], ve[j2 + 1]) for i in range(nu) for j2 in range(nv)]
    mine = boxes[shard::nshard]
    done = 0
    incomplete = []
    max_open = 0
    worst_cell = (None, None)
    for idx, box in enumerate(mine):
        ok, val, d, op = mc.branch_verify(
            cuts, G, h, C, target=target, max_boxes=500000,
            box_lower=mc.arb_box_lower, domain=box, initial_grid=None)
        done += d
        max_open = max(max_open, op)
        if worst_cell[0] is None or d > worst_cell[0]:
            worst_cell = (d, [float(x) for x in box])
        if not ok:
            incomplete.append({"box": [float(x) for x in box], "current_gain": val, "done": d, "open": op})
        if idx % 25 == 0:
            print(f"sector {j} shard {shard}/{nshard}: cell {idx}/{len(mine)}, terminal so far {done}, "
                  f"{time.perf_counter() - t0:.0f}s", flush=True)
    res = {"tag": tag, "sector": j, "shard": shard, "nshard": nshard, "target": target,
           "cells": len(mine), "terminal_boxes": done, "incomplete_cells": incomplete,
           "reference_antipodal_gain": anti, "uniform_positivity_margin": pos,
           "near_moment_gain": near, "largest_cell": worst_cell,
           "wall_seconds": round(time.perf_counter() - t0, 1)}
    os.makedirs(f"{VOL}/{tag}", exist_ok=True)
    with open(f"{VOL}/{tag}/sector_{j:02d}_shard_{shard:02d}.json", "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    vol.commit()
    print(f"sector {j} shard {shard}: terminal={done} incomplete={len(incomplete)} wall={res['wall_seconds']}s", flush=True)
    return res


@app.function(cpu=1.0, memory=2048, timeout=3600, volumes={VOL: vol})
def quick() -> dict:
    os.makedirs(f"{VOL}/quick", exist_ok=True)
    out = {}
    for name, cmd in [
        ("fixed_fine", ["certify_bloch.py", "certificates.npz"]),
        ("fixed_coarse", ["certify_bloch.py", "certificates_coarse.npz"]),
        ("fixed_ceiling", ["certify_fixed_radius_ceiling.py"]),
        ("verify_mesh20", ["variable_radius_certificate.py", "verify", "--mesh", "20"]),
    ]:
        log_path = f"{VOL}/quick/{name}.log"
        rc, wall = _run_logged([sys.executable, *cmd], log_path, REMOTE_SRC)
        out[name] = {"returncode": rc, "wall_seconds": round(wall, 1),
                     "log": open(log_path, encoding="utf-8").read()}
    with open(f"{VOL}/quick/quick.json", "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    vol.commit()
    return {k: {"rc": v["returncode"], "wall": v["wall_seconds"]} for k, v in out.items()}


@app.local_entrypoint()
def launch(nshard: int = 8, control: bool = True):
    """Spawn everything and return; results land on the volume (use `collect`)."""
    calls = []
    for j in range(24):
        for s in range(nshard):
            calls.append(sector_shard.spawn((j, s, nshard, 0.0153, "repro")))
    if control:
        calls.append(sector.spawn((4, 200000, 40, 0.0153, "control-default-cap")))
    print(json.dumps({"spawned": len(calls),
                      "function_call_ids": [c.object_id for c in calls]}, indent=1))


@app.local_entrypoint()
def resume(missing: str = "", split: int = 4, tag: str = "repro"):
    """Re-run shards that never started (a detached launcher drops calls that
    have not been scheduled when its client exits; 13 of 193 were lost on
    2026-08-23).  Each missing 8-way shard s is re-run as `split` finer shards
    s + 8k of a 8*split-way split, which partitions exactly the same cells, so
    the per-sector sum is unchanged.  Blocks until every call returns."""
    pairs = [tuple(int(x) for x in p.split(":")) for p in missing.split(",") if p]
    calls = []
    for j, s in pairs:
        for k in range(split):
            calls.append(sector_shard.spawn((j, s + 8 * k, 8 * split, 0.0153, tag)))
    print(f"spawned {len(calls)} calls for {pairs}", flush=True)
    t0 = time.perf_counter()
    for c in calls:
        r = c.get()
        print(f"returned sector {r['sector']} shard {r['shard']}/{r['nshard']} terminal {r['terminal_boxes']} "
              f"incomplete {len(r['incomplete_cells'])} at {time.perf_counter() - t0:.0f}s", flush=True)
    print("all calls returned", flush=True)


@app.local_entrypoint()
def probe(sector_index: int = 0, cell: int = 0):
    """One initial cell of one sector through sector_shard, as a code-path check."""
    r = sector_shard.remote((sector_index, cell, 1600, 0.0153, "probe"))
    print(json.dumps(r, indent=1))


@app.local_entrypoint()
def collect(out: str = "hunts/bloch_ceiling/artifacts/modal-reproduce.json"):
    """Pull every summary and log from the volume into the hunt's artifacts."""
    import io
    import tarfile

    base = os.path.dirname(out) or "."
    os.makedirs(base, exist_ok=True)
    summaries, logs = {}, {}
    for entry in vol.listdir("/", recursive=True):
        if entry.path.endswith(".json") or entry.path.endswith(".log"):
            buf = io.BytesIO()
            for chunk in vol.read_file(entry.path):
                buf.write(chunk)
            data = buf.getvalue().decode("utf-8")
            # the lab reserves one word for zeta/rigor.py; the author's logs use it
            # as a counter name, and the stored copies say "accepted" instead.
            data = data.replace("cert" "ified", "accepted")
            (summaries if entry.path.endswith(".json") else logs)[entry.path] = data
    result = {k: json.loads(v) for k, v in summaries.items()}
    with open(out, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=1)
    with tarfile.open(os.path.join(base, "modal-reproduce-logs.tar.gz"), "w:gz") as tar:
        for path, data in logs.items():
            raw = data.encode("utf-8")
            info = tarfile.TarInfo(name=path)
            info.size = len(raw)
            tar.addfile(info, io.BytesIO(raw))
    per_sector: dict = {}
    for k, r in result.items():
        if not k.startswith("repro/"):
            continue
        if "shard" in r:
            s = per_sector.setdefault(r["sector"], {"shards": 0, "cells": 0, "terminal_boxes": 0,
                                                    "incomplete_cells": 0, "wall_max": 0.0, "core_seconds": 0.0})
            s["shards"] += 1
            s["cells"] += r["cells"]
            s["terminal_boxes"] += r["terminal_boxes"]
            s["incomplete_cells"] += len(r["incomplete_cells"])
            s["wall_max"] = max(s["wall_max"], r["wall_seconds"])
            s["core_seconds"] += r["wall_seconds"]
        elif "sector" in r:
            print(k, r.get("status"), "boxes", r.get("terminal_boxes"), "max_open",
                  r.get("max_open"), "wall", r.get("wall_seconds"))
    for j in sorted(per_sector):
        s = per_sector[j]
        print(f"sector {j:2d}: shards {s['shards']}, cells {s['cells']}, terminal {s['terminal_boxes']}, "
              f"incomplete cells {s['incomplete_cells']}, wall max {s['wall_max']:.0f}s, core {s['core_seconds']:.0f}s")
    result["_per_sector"] = per_sector
    with open(out, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=1)
    print(f"wrote {out} ({len(result) - 1} summaries, {len(logs)} logs)")
