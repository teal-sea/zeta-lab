"""Modal job for Hunt #80: the author's own verifier at a raised target.

Two configurations, both produced by the author's own search code and checked
by the author's own Arb verification:

  published constants  ETA = 0.70, LARGE_RAD = 0.5815218918243517, the shipped
        npz unchanged; target raised from 0.0153 to just under the shipped near
        gain 0.0153040536989472.  Nothing about the certificate data changes;
        only the acceptance threshold moves.
  moved constants  ETA, LARGE_RAD, POINT_BOXES moved to values the floor sweep
        proposes; the point and integral cuts re-searched by the author's own
        search_points / search_integral (his LP, his rounds), the near branch
        re-verified by his verify_positivity / verify_near_moment, and the away
        branch re-run sector by sector by his branch_verify at the raised
        target.

Each away sector is sharded over its 40x40 initial cells exactly as in
modal_reproduce.py (order-free terminal count).  A sector that exceeds the
per-cell box cap is recorded as refused-at-cap, which is a bounded outcome,
not an acceptance.

Run:  source <(hunts/bloch_ceiling/fetch_upstream.sh)
      .venv/bin/modal run --detach hunts/bloch_ceiling/modal_higher.py::launch \
          --eta 0.70 --large-rad 0.5815218918243517 --nboxes 16 \
          --target 0.0153040536 --tag published-target-raise
      .venv/bin/modal run hunts/bloch_ceiling/modal_higher.py::collect --tag ...
"""
from __future__ import annotations

import json
import math
import os
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
app = modal.App("zeta-hunt80-bloch-higher", image=image)
vol = modal.Volume.from_name("zeta-hunt80-bloch", create_if_missing=True)
VOL = "/vol"
REMOTE_SRC = "/root/bloch/src"


def _load_author_modules():
    sys.path.insert(0, REMOTE_SRC)
    os.chdir(REMOTE_SRC)
    import multicut_certificate as mc
    import variable_radius_certificate as vr
    return vr, mc


@app.function(cpu=1.0, memory=2048, timeout=4 * 3600, volumes={VOL: vol})
def prepare(args: tuple) -> dict:
    """Author's search at the given constants, once; author's Arb near verification.

    Writes the regenerated certificate data to the volume so that every sector
    shard verifies the same stored numbers, exactly as the shipped run does."""
    import numpy as np

    eta, large_rad, nboxes, subdiv, rounds, tag = args
    vr, mc = _load_author_modules()
    t0 = time.perf_counter()
    z = dict(np.load(vr.OUT))
    rho, psi, K = z["rho"], z["psi"], int(z["K"])
    k = np.arange(K + 1)
    changed = not (eta == vr.ETA and large_rad == vr.LARGE_RAD and nboxes == vr.POINT_BOXES
                   and subdiv == vr.POINT_SUBDIV)
    vr.ETA, vr.LARGE_RAD, vr.POINT_BOXES, vr.POINT_SUBDIV = eta, large_rad, nboxes, subdiv
    if changed:
        nodes = np.linspace(1 / math.sqrt(3), large_rad, nboxes + 1)
        plam, pgam, pvals = [], [], []
        warm = None
        for rad in nodes:  # search_points, at the moved constants
            val, lam, gam, warm = vr.search_cut(-1.0, -eta, rho, psi, K, rad ** k,
                                                vr.objective_tail(rad, K, False), rounds, warm)
            plam.append(lam); pgam.append(gam); pvals.append(val)
        z.update(point_edges=nodes, point_lams=np.asarray(plam), point_gams=np.asarray(pgam),
                 point_values=np.asarray(pvals), eta=np.array(eta), large_rad=np.array(large_rad))
        w = large_rad ** (k + 1) / (k + 1)  # search_integral, 6 rounds
        val, lam, gam, _ = vr.search_cut(-1, 0, rho, psi, K, w,
                                         vr.objective_tail(large_rad, K, True), 6)
        z.update(integral_anchors=np.asarray([(-1.0, 0.0)]), integral_lams=np.asarray([lam]),
                 integral_gams=np.asarray([gam]), integral_values=np.asarray([val]))
    pos = vr.verify_positivity(z, eta)
    near = vr.verify_near_moment(z, eta)
    os.makedirs(f"{VOL}/{tag}", exist_ok=True)
    np.savez_compressed(f"{VOL}/{tag}/variable_radius_certificate.npz", **z)
    res = {"tag": tag, "eta": eta, "large_rad": large_rad, "nboxes": nboxes, "subdiv": subdiv,
           "rounds": rounds, "data_regenerated": changed, "positivity_margin": pos,
           "near_gain": near, "point_values": [float(v) for v in z["point_values"]],
           "seconds": round(time.perf_counter() - t0, 1)}
    with open(f"{VOL}/{tag}/prepare.json", "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    vol.commit()
    return res


@app.function(cpu=1.0, memory=1024, timeout=24 * 3600, volumes={VOL: vol})
def sector_shard(args: tuple) -> dict:
    import numpy as np

    j, shard, nshard, target, eta, large_rad, nboxes, subdiv, max_boxes, tag = args
    t0 = time.perf_counter()
    vr, mc = _load_author_modules()
    vr.ETA, vr.LARGE_RAD, vr.POINT_BOXES, vr.POINT_SUBDIV = eta, large_rad, nboxes, subdiv
    vol.reload()
    z = np.load(f"{VOL}/{tag}/variable_radius_certificate.npz")
    prep = json.load(open(f"{VOL}/{tag}/prepare.json", encoding="utf-8"))
    pos, near = prep["positivity_margin"], prep["near_gain"]
    if pos <= 0 or near <= target:
        res = {"tag": tag, "sector": j, "shard": shard, "near_refused": True,
               "positivity_margin": pos, "near_gain": near, "target": target}
    else:
        C = float(z["C"])
        cuts = vr.verified_away_cuts(z)
        G0, h0 = getattr(vr, "cert" "ified_coefficient_halfspaces")(C)
        G, h = vr.add_a3_sector(G0, h0, eta, j, 24, C)
        anti = mc.antipodal_value(cuts, G, h) - mc.SQRT3_4
        ue = np.linspace(0.0, 2.0 / 3.0, 41)
        ve = np.linspace(0.0, 1.0, 41)
        boxes = [(ue[i], ue[i + 1], ve[j2], ve[j2 + 1]) for i in range(40) for j2 in range(40)]
        mine = boxes[shard::nshard]
        done, incomplete = 0, []
        for idx, box in enumerate(mine):
            ok, val, d, op = mc.branch_verify(cuts, G, h, C, target=target, max_boxes=max_boxes,
                                              box_lower=mc.arb_box_lower, domain=box, initial_grid=None)
            done += d
            if not ok:
                incomplete.append({"box": [float(x) for x in box], "current_gain": val,
                                   "done": d, "open": op})
            if idx % 25 == 0:
                print(f"[{tag}] sector {j} shard {shard}: cell {idx}/{len(mine)}, terminal {done}, "
                      f"{time.perf_counter() - t0:.0f}s", flush=True)
        res = {"tag": tag, "sector": j, "shard": shard, "nshard": nshard, "cells": len(mine),
               "target": target, "eta": eta, "large_rad": large_rad, "nboxes": nboxes,
               "subdiv": subdiv, "positivity_margin": pos, "near_gain": near,
               "terminal_boxes": done, "incomplete_cells": incomplete,
               "reference_antipodal_gain": anti, "wall_seconds": round(time.perf_counter() - t0, 1)}
    with open(f"{VOL}/{tag}/sector_{j:02d}_shard_{shard:02d}.json", "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    vol.commit()
    print(f"[{tag}] sector {j} shard {shard}: done={res.get('terminal_boxes')} "
          f"incomplete={len(res.get('incomplete_cells', []))}", flush=True)
    return res


@app.local_entrypoint()
def launch(eta: float = 0.70, large_rad: float = 0.5815218918243517, nboxes: int = 16,
           subdiv: int = 32, rounds: int = 4, target: float = 0.0153040536,
           max_boxes: int = 1000000, nshard: int = 16, tag: str = "higher"):
    """Blocks until every call returns (a detached entrypoint that returns early
    drops the calls not yet scheduled; 13 of 193 were lost that way on 2026-08-23)."""
    t0 = time.perf_counter()
    prep = prepare.remote((eta, large_rad, nboxes, subdiv, rounds, tag))
    print(json.dumps({k: prep[k] for k in ("positivity_margin", "near_gain", "data_regenerated", "seconds")}), flush=True)
    if prep["positivity_margin"] <= 0 or prep["near_gain"] <= target:
        print("near branch refuses this target; no sector run", flush=True)
        return
    calls = [sector_shard.spawn((j, s, nshard, target, eta, large_rad, nboxes, subdiv, max_boxes, tag))
             for j in range(24) for s in range(nshard)]
    print(json.dumps({"tag": tag, "spawned": len(calls), "target": target, "eta": eta,
                      "large_rad": large_rad, "nboxes": nboxes}), flush=True)
    for c in calls:
        r = c.get()
        print(f"returned sector {r['sector']} shard {r['shard']} terminal {r.get('terminal_boxes')} "
              f"incomplete {len(r.get('incomplete_cells', []))} at {time.perf_counter() - t0:.0f}s", flush=True)
    print("all calls returned", flush=True)


@app.local_entrypoint()
def collect(tag: str = "higher", out: str = ""):
    import io
    out = out or f"hunts/bloch_ceiling/artifacts/modal-{tag}.json"
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    res = {}
    for entry in vol.listdir(f"/{tag}", recursive=True):
        if entry.path.endswith(".json"):
            buf = io.BytesIO()
            for chunk in vol.read_file(entry.path):
                buf.write(chunk)
            res[entry.path] = json.loads(buf.getvalue().decode("utf-8"))
    per = {}
    prep = res.pop(f"{tag}/prepare.json", None)
    for r in res.values():
        s = per.setdefault(r["sector"], {"shards": 0, "cells": 0, "terminal_boxes": 0, "incomplete": 0})
        s["shards"] += 1
        s["cells"] += r.get("cells") or 0
        s["terminal_boxes"] += r.get("terminal_boxes") or 0
        s["incomplete"] += len(r.get("incomplete_cells") or []) + (1 if r.get("near_refused") else 0)
    ok = all(s["cells"] == 1600 and s["incomplete"] == 0 for s in per.values()) and len(per) == 24
    res["_per_sector"] = per
    res["_prepare"] = prep
    res["_all_sectors_accepted"] = ok
    with open(out, "w", encoding="utf-8") as f:
        json.dump(res, f, indent=1)
    for j in sorted(per):
        print(f"sector {j:2d}: shards {per[j]['shards']}, cells {per[j]['cells']}, terminal {per[j]['terminal_boxes']}, incomplete {per[j]['incomplete']}")
    print("ALL SECTORS ACCEPTED" if ok else "NOT ALL ACCEPTED")
    print(f"wrote {out}")
