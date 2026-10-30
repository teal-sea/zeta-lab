"""exact_gram/: peak RSS of one block of hats, in-memory table against the disk-backed table (RUNS.md s9).

Each variant runs in its own subprocess (clean ru_maxrss). Small size on the box: nvec = 20,
Kmax = 10, S' = 200, one block of 128 trapezoid nodes, dps 40. Records the table's balls, the
disk bytes, the peak RSS of each variant and the bytes per ball in memory, which extrapolate
to 280 modes in RUNS.md. Measured grade.

    nice -n 10 <venv python> hunts/weil_propagation/c4_s2/exact_gram/rss_probe.py   # a few minutes
"""

from __future__ import annotations

import json
import os
import resource
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "rss_probe.json")
NVEC, K, S, BLOCK = 20, 10, 200.0, 128


def vmrss():
    with open("/proc/self/status") as fh:
        for ln in fh:
            if ln.startswith("VmRSS:"):
                return int(ln.split()[1])
    return -1


def child(kind, path):
    sys.path.insert(0, HERE)
    import bounds as B
    import rebuild as R
    from flint import arb, ctx

    ctx.prec = 133
    if kind == "baseline280":
        md = B.prolate_modes(280)
        B.coef_matrix(md)
        print(json.dumps({"kind": kind, "rss_kib": vmrss(), "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}))
        return
    md = B.prolate_modes(NVEC)
    B.coef_matrix(md)
    base = vmrss()
    t0 = time.perf_counter()
    if kind == "memory":
        tab = R.ModeTable(md, K, S)
    else:
        tab = R.DiskModeTable(path, md, K, S)
    after_table = vmrss()
    s = [arb(k) / 16 for k in range(BLOCK)]
    R.hats_block(tab, s, 14, 14, 24)
    print(json.dumps({"kind": kind, "rss_before_table_kib": base, "rss_after_table_kib": after_table,
                      "rss_after_hats_kib": vmrss(), "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      "seconds": time.perf_counter() - t0}))


def main():
    sys.path.insert(0, HERE)
    import bounds as B
    import rebuild as R
    from flint import ctx

    ctx.prec = 133
    md = B.prolate_modes(NVEC)
    path = tempfile.mkdtemp(prefix="eg_table_")
    t0 = time.perf_counter()
    tab = R.DiskModeTable.build(path, md, K, S)
    build_s = time.perf_counter() - t0
    nodes = sum(tab.counts)
    res = {"nvec": NVEC, "Kmax": K, "S_prime": S, "block": BLOCK, "nodes": nodes, "balls": nodes * (NVEC + 1),
           "disk_bytes": tab.disk_bytes(), "build_seconds": build_s, "load_average": os.getloadavg()}
    for kind in ("memory", "disk", "baseline280"):
        out = subprocess.run([sys.executable, __file__, "--child", kind, path], capture_output=True, text=True, check=True)
        res[kind] = json.loads(out.stdout.strip().splitlines()[-1])
    m, d = res["memory"], res["disk"]
    res["memory_table_bytes_per_ball"] = (m["rss_after_table_kib"] - m["rss_before_table_kib"]) * 1024 / res["balls"]
    res["disk_hats_extra_kib"] = d["rss_after_hats_kib"] - d["rss_before_table_kib"]
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=1)
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--child":
        child(sys.argv[2], sys.argv[3])
    else:
        main()
