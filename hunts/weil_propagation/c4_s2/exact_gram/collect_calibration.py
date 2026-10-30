"""The calibration run's measured costs, from its downloaded artifacts (RUNS.md s11).

    gh api repos/teal-sea/zeta-lab/actions/runs/40342895119/artifacts   # names, ids, sha256 digests
    gh api repos/teal-sea/zeta-lab/actions/artifacts/<id>/zip > <name>.zip  # each zip checked against its digest
    unzip each into one directory DIR, then: python collect_calibration.py DIR > calibration_40342895119.json

Reads only /usr/bin/time -v reports and the checkpoints' block_seconds; no number about Delta_T."""
from __future__ import annotations

import glob
import hashlib
import json
import os
import re
import sys


def _time_v(path):
    t = open(path).read()
    cpu = sum(float(re.search(rf"{k} time \(seconds\): ([\d.]+)", t).group(1)) for k in ("User", "System"))
    wall = sum(float(v) * 60 ** i for i, v in enumerate(reversed(re.search(r"Elapsed.*: ([\d:.]+)", t).group(1).split(":"))))
    rss = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", t).group(1)) / 2 ** 20
    return {"cpu_s": round(cpu, 1), "wall_s": round(wall, 1), "peak_rss_gib": round(rss, 3)}


def collect(d):
    gram = {int(re.search(r"gram_time_(\d+)", f).group(1)): _time_v(f) for f in glob.glob(os.path.join(d, "gram_time_*.txt"))}
    procs = {int(re.search(r"time_(\d+)", f).group(1)): _time_v(f)
             for f in glob.glob(os.path.join(d, "time_*.txt")) if "gram_" not in os.path.basename(f)}
    blocks = {}
    for f in sorted(glob.glob(os.path.join(d, "shard*_block*.json"))):  # the last block's file carries all
        sh = int(re.search(r"shard(\d+)of", f).group(1))
        blocks[sh] = [[b, round(s, 1)] for b, s in json.load(open(f))["payload"]["block_seconds"]]
    g = os.path.join(d, "gram.json")
    return {"run": 40342895119,
            "gram_parts": {str(k): gram[k] for k in sorted(gram)},
            "gram_cpu_hours": round(sum(v["cpu_s"] for v in gram.values()) / 3600, 2),
            "shard_processes": {str(k): procs[k] for k in sorted(procs)},
            "block_seconds": {str(k): blocks[k] for k in sorted(blocks)},
            "gram_json": {"bytes": os.path.getsize(g), "sha256": hashlib.sha256(open(g, "rb").read()).hexdigest()}}


if __name__ == "__main__":
    print(json.dumps(collect(sys.argv[1]), indent=1))
