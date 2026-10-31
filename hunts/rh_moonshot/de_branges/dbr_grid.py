"""The Hermite-Biehler defect D_h on a grid of the upper half-plane, two routes.

Usage (from the repo root):

    .venv/bin/python hunts/rh_moonshot/de_branges/dbr_grid.py KIND [KIND ...]

Per kind, writes data/grid_<kind>.json (checkpointed per h):

* the grid: h in H, y in Y, x on [0, X_MAX[kind]] in steps of 0.5 plus the
  ordinate of the kind's pinned off-line zero (and zeta's first ordinate);
* D_h by the Arb route at every point (ball midpoint, radius, sign decided or
  not) and by the mp route at every point (every MP_EVERY-th x for Epstein,
  whose lattice route costs 12 to 18 s a point);
* the column x = gamma: the Arb defect at 60 heights y in (0, 0.6], to locate
  where the defect is positive;
* per h: the largest D on the grid, how many points have a positive defect,
  and the largest |D_mp - D_arb|.

Grade: the Arb signs are ball-carried (a sign is recorded only when the ball
excludes 0); the mp values are one float route.
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import dbr_common as D  # noqa: E402
from mpmath import mp  # noqa: E402

DATA = os.path.join(HERE, "data")
H = ["1/2", "3/8", "3/10", "1/4", "1/5", "1/10", "1/20"]
Y = ["1/20", "1/5"]
X_MAX = {"zeta": 100, "dh": 100, "epstein": 40, "wa": 100, "zshift": 100}
MP_EVERY = {"epstein": 16}
GAMMA1 = "14.134725141734694"


def _f(q):
    a, b = (q.split("/") + ["1"])[:2]
    return mp.mpf(a) / mp.mpf(b)


def xs(kind):
    pts = [mp.mpf(k) / 2 for k in range(0, 2 * X_MAX[kind] + 1)]
    extra = [GAMMA1]
    if kind in D.OFFLINE:
        extra.append(D.OFFLINE[kind][1])
    return pts, [mp.mpf(e) for e in extra]


def prec_for(kind, x):
    return 160 + int(3 * float(x)) if kind == "epstein" else 160


def point(kind, h, x, y, do_mp):
    b = D.defect_arb(kind, h, x, y, prec=prec_for(kind, x))
    rec = {"x": mp.nstr(x, 12), "arb_mid": b.mid().str(12, radius=False), "arb_rad": b.rad().str(3, radius=False)}
    rec["sign"] = 1 if b > 0 else (-1 if b < 0 else 0)
    if do_mp:
        a = D.defect_mp(kind, h, x, y, dps=15 if kind == "epstein" else 20)
        rec["mp"] = mp.nstr(a, 12)
        rec["mp_minus_arb"] = mp.nstr(abs(a - mp.mpf(rec["arb_mid"])), 3)
    return rec


def run(kind):
    path = os.path.join(DATA, f"grid_{kind}.json")
    store = json.load(open(path)) if os.path.exists(path) else {"kind": kind, "H": H, "Y": Y, "by_h": {}}
    grid, extra = xs(kind)
    every = MP_EVERY.get(kind, 1)
    for hq in H:
        if hq in store["by_h"]:
            continue
        t0 = time.time()
        h = _f(hq)
        rows = {}
        for yq in Y:
            y = _f(yq)
            pts = []
            for i, x in enumerate(grid):
                pts.append(point(kind, h, x, y, do_mp=(i % every == 0)))
            for x in extra:
                pts.append(point(kind, h, x, y, do_mp=True))
            rows[yq] = pts
        cols = {}
        for x in extra:
            col = []
            for k in range(1, 61):
                y = mp.mpf(k) / 100
                b = D.defect_arb(kind, h, x, y, prec=prec_for(kind, x))
                col.append([k / 100, b.mid().str(8, radius=False), 1 if b > 0 else (-1 if b < 0 else 0)])
            cols[mp.nstr(x, 12)] = col
        allpts = [p for pts in rows.values() for p in pts]
        summ = {
            "max_D_arb": max(float(p["arb_mid"]) for p in allpts),
            "n_points": len(allpts),
            "n_positive": sum(1 for p in allpts if p["sign"] == 1),
            "n_undecided": sum(1 for p in allpts if p["sign"] == 0),
            "max_abs_mp_minus_arb": max((float(p["mp_minus_arb"]) for p in allpts if "mp" in p), default=None),
            "n_mp": sum(1 for p in allpts if "mp" in p),
            "positive_x": sorted({p["x"] for p in allpts if p["sign"] == 1}, key=float)[:40],
            "column_positive_y": {x: [c[0] for c in col if c[2] == 1] for x, col in cols.items()},
        }
        store["by_h"][hq] = {"rows": rows, "columns": cols, "summary": summ, "elapsed_s": round(time.time() - t0, 1)}
        os.makedirs(DATA, exist_ok=True)
        with open(path, "w") as fh:
            json.dump(store, fh)
        print(kind, hq, json.dumps({k: v for k, v in summ.items() if k != "column_positive_y"})[:300],
              {x: (v[0], v[-1]) if v else None for x, v in summ["column_positive_y"].items()},
              f"t={store['by_h'][hq]['elapsed_s']}s", flush=True)


if __name__ == "__main__":
    for k in sys.argv[1:]:
        run(k)
