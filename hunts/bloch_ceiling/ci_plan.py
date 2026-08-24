"""Shard plan for the away branch on GitHub Actions, and the artifact roll-up.

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


def plan(boxes_per_job: int, sectors) -> list[dict]:
    jobs = []
    for j in sectors:
        n = max(1, min(NCELL, math.ceil(REFERENCE_BOXES[j] / boxes_per_job)))
        for s in range(n):
            jobs.append({"sector": j, "shard": s, "nshard": n,
                         "name": f"s{j:02d}-{s:02d}of{n:02d}"})
    return jobs


def collect(paths: list[str], target: float) -> dict:
    per = {}
    refused = []
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
                if "cell" not in r:
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
    out = {"target": target, "sectors": {}, "refused_cells": refused}
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


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("plan")
    p.add_argument("--boxes-per-job", type=int, default=55000)
    p.add_argument("--sectors", default="0-23")
    p.add_argument("--out", default="")

    c = sub.add_parser("collect")
    c.add_argument("--dir", required=True)
    c.add_argument("--target", type=float, default=0.0153040536)
    c.add_argument("--out", default="")

    args = ap.parse_args()
    if args.cmd == "plan":
        if "-" in args.sectors:
            lo, hi = args.sectors.split("-")
            sectors = list(range(int(lo), int(hi) + 1))
        else:
            sectors = [int(x) for x in args.sectors.split(",") if x != ""]
        jobs = plan(args.boxes_per_job, sectors)
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
        print("ALL 24 SECTORS ACCEPTED AT TARGET "
              f"{res['target']}" if res["all_24_sectors_accepted"]
              else f"NOT COMPLETE (missing sectors {res['missing_sectors']}, "
                   f"{len(res['refused_cells'])} refused cells)")


if __name__ == "__main__":
    main()
