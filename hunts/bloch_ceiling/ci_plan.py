"""Shard plan for the away branch on GitHub Actions, and the artifact roll-up.

`config` is what the workflow actually calls. `workflow_dispatch` only reaches
a workflow file that is already on the default branch, and this one is not, so
the run is driven the way `.github/workflows/three-point.yml` drives its Lean
build: a `push` trigger on the hunt branch. The parameters that would have
been dispatch inputs live in `ci_run.json` instead, committed beside the
workflow, so every launch is a reviewable diff rather than a form somebody
filled in. `mode: off` emits an empty matrix, which is the default, so an
ordinary documentation commit on this branch does not fire 219 jobs.

`plan` emits the job matrix.  Sectors differ by 2.9x in cost (270,744 boxes in
sector 0 against 797,875 in sector 17), so a flat number of shards per sector
would leave some jobs three times longer than others.  Shards are allocated in
proportion to the archive's own reference-run terminal counts, which are the
best cost model available before the run and are exact for the published
target.  Within a sector the cells are handed out by stride, not in blocks, so
the expensive cells (they cluster at high v) spread evenly over its shards.

`collect` reads the downloaded artifacts and answers the actual question: did
every one of the 24 sectors' 1600 cells accept the raised target, and does the
per-sector terminal-box count agree with the archive's reference log.

  python hunts/bloch_ceiling/ci_plan.py plan --boxes-per-job 55000
  python hunts/bloch_ceiling/ci_plan.py collect --dir artifacts/ci-higher
"""
from __future__ import annotations

import argparse
import glob
import json
import math
import os

#: Terminal-box counts per away sector from the archive's own reference run
#: (`reference-run/logs/*.log`, target 0.0153).  Sector 0's log is a resume with
#: no fresh work, so its count is the one that resume recorded.
REFERENCE_BOXES = {
    0: 270744, 1: 292931, 2: 352172, 3: 440355, 4: 539188, 5: 609488,
    6: 594330, 7: 512148, 8: 424756, 9: 350497, 10: 316278, 11: 315121,
    12: 343434, 13: 400711, 14: 487564, 15: 599578, 16: 714647, 17: 797875,
    18: 782603, 19: 682817, 20: 549771, 21: 430735, 22: 346583, 23: 289192,
}
NCELL = 1600


def plan(boxes_per_job: int, sectors, target: str = "",
         prefix: str = "s") -> list[dict]:
    jobs = []
    for j in sectors:
        n = max(1, min(NCELL, math.ceil(REFERENCE_BOXES[j] / boxes_per_job)))
        for s in range(n):
            jobs.append({"sector": j, "shard": s, "nshard": n, "target": target,
                         "name": f"{prefix}{j:02d}-{s:02d}of{n:02d}"})
    return jobs


def collect(paths: list[str], target: float) -> dict:
    """Roll the per-cell records up into a per-sector verdict at one target.

    The target filter is load-bearing, not hygiene. The oracle sectors are run
    twice, at 0.0153 and at the raised target, and the de-duplication below
    keys on (sector, cell); without the filter a cell's record at one target
    would silently stand in for its record at the other, and the per-sector box
    count, which is the whole cross-check, would be a mixture of two runs.
    """
    per = {}
    refused = []
    skipped_other_target = 0
    for path in paths:
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except ValueError:
                    continue      # a torn final line from a killed job
                if "cell" not in r or "terminal" not in r:
                    continue      # a skip list, not a shard's own output
                if float(r.get("target", target)) != target:
                    skipped_other_target += 1
                    continue
                j = int(r["sector"])
                d = per.setdefault(j, {"cells": {}, "boxes": 0})
                cid = int(r["cell"])
                if cid in d["cells"]:
                    continue      # a resumed sweep can repeat a finished cell
                d["cells"][cid] = r
                d["boxes"] += int(r["terminal"])
                if not r["ok"]:
                    refused.append({"sector": j, "cell": cid,
                                    "gain": r.get("gain"),
                                    "open": r.get("open")})
    out = {"target": target, "sectors": {}, "refused_cells": refused,
           "records_at_other_targets_skipped": skipped_other_target}
    complete = True
    for j in sorted(per):
        n = len(per[j]["cells"])
        ref = REFERENCE_BOXES[j]
        got = per[j]["boxes"]
        secs = sum(c["seconds"] for c in per[j]["cells"].values())
        row = {"cells_done": n, "cells_expected": NCELL,
               "terminal_boxes": got, "reference_boxes": ref,
               "ratio_to_reference": round(got / ref, 6) if ref else None,
               "core_seconds": round(secs, 1),
               "all_cells_accepted": n == NCELL and all(
                   c["ok"] for c in per[j]["cells"].values())}
        if n != NCELL:
            row["missing_cells"] = sorted(set(range(NCELL)) - set(per[j]["cells"]))[:40]
            complete = False
        if not row["all_cells_accepted"]:
            complete = False
        out["sectors"][str(j)] = row
    missing_sectors = sorted(set(REFERENCE_BOXES) - set(per))
    out["missing_sectors"] = missing_sectors
    out["all_24_sectors_accepted"] = bool(complete and not missing_sectors)
    out["total_terminal_boxes"] = sum(v["terminal_boxes"] for v in out["sectors"].values())
    out["total_reference_boxes"] = sum(REFERENCE_BOXES.values())
    out["total_core_seconds"] = round(
        sum(v["core_seconds"] for v in out["sectors"].values()), 1)
    return out


#: What a launch may ask for, and what it gets when `ci_run.json` is silent.
DEFAULTS = {
    "mode": "off",              # off | calibrate | run | sweep
    "target": "0.0153040536",   # the published run used 0.0153
    "sectors": "0-23",
    "boxes_per_job": 55000,
    "budget": 1020,             # seconds per worker process, inside the job timeout
    "nproc": 4,                 # standard runners have 4 vCPU
    "prior_run_id": "",         # comma-separated: a sweep spans every prior run
    # The exact-count oracle. These sectors are additionally run at
    # `oracle_target`, the published 0.0153, where the archive's reference logs
    # give a terminal-box count to match exactly. At the raised target the
    # counts must come out slightly *above* the reference, which is a
    # consistency check and not an equality, so the equality has to be bought
    # somewhere and this is where.
    "oracle_sectors": "",
    "oracle_target": "0.0153",
    # The oracle needs *complete* sectors, since a partial count matches
    # nothing, so it gets its own shard size rather than the sweep's much
    # coarser one.
    "oracle_boxes_per_job": 38000,
}

#: The calibration shard: sector 17 is the most expensive of the 24, and
#: `nshard = 41` against a 40x40 grid walks the diagonal, so the sample holds
#: one cell from every u index and every v index rather than one cheap stripe.
CALIBRATION = [{"sector": 17, "shard": 0, "nshard": 41, "name": "calib-s17"}]


def config(path: str) -> dict:
    cfg = dict(DEFAULTS)
    if path and os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            for k, v in json.load(f).items():
                if k in cfg:
                    cfg[k] = v
    cfg["boxes_per_job"] = int(cfg["boxes_per_job"])
    cfg["budget"] = int(cfg["budget"])
    cfg["nproc"] = int(cfg["nproc"])
    mode = str(cfg["mode"])
    target = str(cfg["target"])
    if mode == "off":
        jobs = []
    elif mode == "calibrate":
        jobs = [dict(j, target=target) for j in CALIBRATION]
    else:
        jobs = plan(cfg["boxes_per_job"], parse_sectors(str(cfg["sectors"])),
                    target)
        if str(cfg["oracle_sectors"]):
            jobs += plan(int(cfg["oracle_boxes_per_job"]),
                         parse_sectors(str(cfg["oracle_sectors"])),
                         str(cfg["oracle_target"]), prefix="oracle-s")
    cfg["matrix"] = json.dumps(jobs)
    cfg["count"] = len(jobs)
    return cfg


def parse_sectors(spec: str) -> list[int]:
    if "-" in spec:
        lo, hi = spec.split("-")
        return list(range(int(lo), int(hi) + 1))
    return [int(x) for x in spec.split(",") if x != ""]


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("config")
    g.add_argument("--file", default="hunts/bloch_ceiling/ci_run.json")

    p = sub.add_parser("plan")
    p.add_argument("--boxes-per-job", type=int, default=55000)
    p.add_argument("--sectors", default="0-23")
    p.add_argument("--out", default="")

    c = sub.add_parser("collect")
    c.add_argument("--dir", required=True)
    c.add_argument("--target", type=float, default=0.0153040536)
    c.add_argument("--out", default="")

    args = ap.parse_args()
    if args.cmd == "config":
        cfg = config(args.file)
        for k, v in cfg.items():
            print(f"{k}={v}")
        return
    if args.cmd == "plan":
        jobs = plan(args.boxes_per_job, parse_sectors(args.sectors))
        text = json.dumps(jobs)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as f:
                f.write(text)
        print(text)
        print(f"# {len(jobs)} jobs over {len(sectors)} sectors", file=os.sys.stderr)
    else:
        paths = sorted(glob.glob(os.path.join(args.dir, "**", "*.jsonl"),
                                 recursive=True))
        res = collect(paths, args.target)
        text = json.dumps(res, indent=1)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as f:
                f.write(text)
        for j in sorted(res["sectors"], key=int):
            r = res["sectors"][j]
            print(f"sector {int(j):2d}: cells {r['cells_done']:4d}/1600  "
                  f"boxes {r['terminal_boxes']:8d} (reference {r['reference_boxes']:8d}, "
                  f"ratio {r['ratio_to_reference']})  "
                  f"{'ACCEPTED' if r['all_cells_accepted'] else 'INCOMPLETE'}")
        print(f"\nfiles read: {len(paths)}")
        print(f"total terminal boxes {res['total_terminal_boxes']} "
              f"against reference {res['total_reference_boxes']}")
        print(f"total core seconds {res['total_core_seconds']} "
              f"({res['total_core_seconds'] / 3600:.1f} core-hours)")
        if res["all_24_sectors_accepted"]:
            print(f"ALL 24 SECTORS ACCEPTED AT TARGET {res['target']}")
        else:
            missing_cells = sum(
                r["cells_expected"] - r["cells_done"] for r in res["sectors"].values())
            print(f"NOT COMPLETE: missing sectors {res['missing_sectors']}, "
                  f"{missing_cells} missing cells, "
                  f"{len(res['refused_cells'])} refused cells")


if __name__ == "__main__":
    main()
