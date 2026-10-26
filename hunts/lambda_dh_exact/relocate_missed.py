"""Find the true zero in each window that `deep_zeros.stage_locate` mislocated.

Hunt #119, unit 3 (2026-10-26), diagnostic for the census's K-d failure
(RUNS.md Run 17). `census_runs/full_r1/mislocated.json` lists 17 flagged
windows whose accepted root lies outside the counted box beta > sigma_c. For
each one: a float count on [sigma_c, 2.05] x window (must be 1, as the screen
said), then a search constrained to the box (grid minima of |f| from
beta = sigma_c + 0.005, Newton abandoned outside the box), keeping a root only
if it lies strictly inside it.

Grade: *measured*, diagnostic. It does not repair the census, which stays
void as registered (RESULTS.md section 8.12, K-d).

Run:  .venv/bin/python hunts/lambda_dh_exact/relocate_missed.py
"""
from __future__ import annotations

import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import census_1e4 as cz  # noqa: E402
import deep_zeros as dz  # noqa: E402

SRC = os.path.join(HERE, "census_runs", "full_r1", "mislocated.json")
OUT = os.path.join(HERE, "census_runs", "full_r1", "relocated.json")


def search(sig_c: float, a: float, b: float):
    xs = np.linspace(sig_c + 0.005, 1.15, 24)
    step = 0.05
    npts = int((b - a) / step) + 1
    grid = np.array([np.abs(dz.f_vline(float(x), a, step, npts)) for x in xs])
    cand = []
    for i in range(len(xs)):
        for j in range(1, npts - 1):
            lo_i, hi_i = max(0, i - 1), min(len(xs), i + 2)
            if grid[i, j] <= grid[lo_i:hi_i, j - 1:j + 2].min():
                cand.append((grid[i, j], complex(xs[i], a + step * j)))
    cand.sort(key=lambda c: c[0])
    found = []
    for _, seed in cand[:40]:
        z = cz._newton(seed, a, b)
        if z is None or not (sig_c < z.real < 1.2 and a < z.imag < b):
            continue
        if abs(dz.f_one(z)) > 1e-9 or any(abs(z - w) < 1e-6 for w in found):
            continue
        found.append(z)
    return found


def main() -> None:
    t0 = time.time()
    rows = []
    for m in json.load(open(SRC))["rows"]:
        tw = time.time()
        a, b = m["window"]
        n, defect = cz.count_float(m["sigma_c"], a, b)
        found = search(m["sigma_c"], a, b)
        rows.append({**m, "count_in_box": n, "count_defect": defect,
                     "found": [{"gamma": z.imag, "beta": z.real, "y0": z.real - 0.5} for z in found],
                     "ok": n == len(found) == 1, "seconds": round(time.time() - tw, 1)})
        f = rows[-1]["found"]
        print(m["source"], m["window"], "count", n, "found",
              [(round(x["gamma"], 2), round(x["y0"], 4)) for x in f], f"[{rows[-1]['seconds']}s]", flush=True)
    ok = [r for r in rows if r["ok"]]
    out = {"what": "true zeros of the mislocated windows, constrained search (measured)",
           "n": len(rows), "n_ok": len(ok),
           "max_y0_found": max((r["found"][0]["y0"] for r in ok), default=None),
           "n_y0_gt_0.3396": sum(r["found"][0]["y0"] > 0.3396 for r in ok),
           "n_y0_gt_0.40": sum(r["found"][0]["y0"] > 0.40 for r in ok),
           "rows": rows, "seconds": round(time.time() - t0, 1)}
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
