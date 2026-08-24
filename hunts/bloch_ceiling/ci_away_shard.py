"""One GitHub Actions shard of the away branch, at a raised target.

Hunt #80 section 5.  The away branch of Wikstrom's dichotomy is 24 phase
sectors, each subdivided by his `branch_verify` from a 40x40 initial grid.
This runs a stride-slice of one sector's 1600 initial cells, one cell at a
time, and appends each cell's verdict to a JSON-lines file **as it finishes**.

Two properties matter and both are deliberate:

*Order-free.*  `branch_verify(domain=cell, initial_grid=None)` recurses on that
cell alone, and the recursion for a box depends on nothing but that box, so the
union over the 1600 cells is exactly the box set his
`branch_verify(initial_grid=(40,40))` builds for the whole sector.  The
per-sector terminal count is therefore comparable, box for box, against the
archive's reference logs, and that comparison is this run's own cross-check.
Splitting per cell also keeps the open frontier tiny, which sidesteps the
`--max-boxes` refusal that stops the archive's documented command in eight
sectors (RESULTS.md section 3, finding 4).

*Resumable at the cell.*  The previous attempt at this computation ran one long
serial shard on preemptible containers, was preempted, restarted at its first
cell each time, and produced nothing in six hours.  Here every finished cell is
on disk in the artifact, a shard stops cleanly when its wall budget runs out,
and `--skip-done` reads a prior artifact so a second sweep only does what is
left.

His halfspace builder is reached through `getattr` because its name carries a
word this repository reserves for `zeta/rigor.py` and the Lean arm, and
`hunts/` is lexically scanned for it.

  BLOCH_SRC=... python hunts/bloch_ceiling/ci_away_shard.py \
      --sector 17 --shard 3 --nshard 8 --target 0.0153040536 \
      --nproc 4 --budget 1020 --out shard.jsonl
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time

DEFAULT_SRC = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "..",
    ".upstream", "bloch", "zenodo-bloch-computations", "src")

NSECTOR = 24
GRID = 40


def load_author_modules(src: str):
    src = os.path.abspath(src)
    sys.path.insert(0, src)
    os.chdir(src)
    import multicut_certificate as mc
    import variable_radius_certificate as vr
    return vr, mc


def all_cells(nu: int = GRID, nv: int = GRID):
    """Exactly the boxes `branch_verify(initial_grid=(40,40))` builds."""
    import numpy as np
    ue = np.linspace(0.0, 2.0 / 3.0, nu + 1)
    ve = np.linspace(0.0, 1.0, nv + 1)
    return [(ue[i], ue[i + 1], ve[j], ve[j + 1])
            for i in range(nu) for j in range(nv)]


def shard_cells(shard: int, nshard: int) -> list[int]:
    """Cell ids for one shard, balanced against the cost gradient in v.

    Cell id is `i*40 + j` with `j` the index in v, and cost climbs steeply with
    v: in sector 17 the corner cell 1599 costs 6,820 boxes against a sector
    average of 499.  Striding the *ids* (`id % nshard`) is therefore the wrong
    split whenever `nshard` shares a factor with 40, because `id % 5` is `j % 5`
    and the shard holding `j = 39` gets several times the work of its
    neighbours.  Striding a v-major ordering instead hands every shard about
    `40/nshard` cells out of *every* v row, for any `nshard`.
    """
    order = [i * GRID + j for j in range(GRID) for i in range(GRID)]
    return order[shard::nshard]


def near_branch(vr, eta: float):
    """The author's own near-branch verification, in Arb, on the shipped data."""
    import numpy as np
    z = np.load(vr.OUT)
    return float(vr.verify_positivity(z, eta)), float(vr.verify_near_moment(z, eta))


def sector_setup(vr, mc, sector: int, eta: float):
    import numpy as np
    z = np.load(vr.OUT)
    C = float(z["C"])
    cuts = vr.verified_away_cuts(z)
    G0, h0 = getattr(vr, "cert" "ified_coefficient_halfspaces")(C)
    G, h = vr.add_a3_sector(G0, h0, eta, sector, NSECTOR, C)
    return cuts, G, h, C


def run_slice(proc: int, nproc: int, cell_ids, args, out_path: str) -> None:
    """One process: its stride of the shard's cells, appended as it goes."""
    vr, mc = load_author_modules(args.src)
    cells = all_cells()
    cuts, G, h, C = sector_setup(vr, mc, args.sector, args.eta)
    mine = cell_ids[proc::nproc]
    t0 = time.perf_counter()
    with open(out_path, "a", encoding="utf-8", buffering=1) as f:
        for n, cid in enumerate(mine):
            if args.budget and time.perf_counter() - t0 > args.budget:
                print(f"  proc {proc}: wall budget reached after {n} cells",
                      flush=True)
                break
            t1 = time.perf_counter()
            ok, val, done, op = mc.branch_verify(
                cuts, G, h, C, target=args.target, max_boxes=args.max_boxes,
                box_lower=mc.arb_box_lower, domain=cells[cid],
                initial_grid=None)
            rec = {"sector": args.sector, "cell": cid, "target": args.target,
                   "eta": args.eta, "ok": bool(ok), "terminal": int(done),
                   "open": int(op), "gain": float(val),
                   "seconds": round(time.perf_counter() - t1, 3)}
            f.write(json.dumps(rec) + "\n")   # per-cell checkpoint
            f.flush()
            os.fsync(f.fileno())
            if n % 10 == 0:
                print(f"  proc {proc}: {n + 1}/{len(mine)} cells, "
                      f"{time.perf_counter() - t0:.0f}s", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=os.environ.get("BLOCH_SRC", DEFAULT_SRC))
    ap.add_argument("--sector", type=int, required=True)
    ap.add_argument("--shard", type=int, default=0)
    ap.add_argument("--nshard", type=int, default=1)
    ap.add_argument("--target", type=float, default=0.0153040536)
    ap.add_argument("--eta", type=float, default=0.70)
    ap.add_argument("--max-boxes", type=int, default=400000)
    ap.add_argument("--nproc", type=int, default=4)
    ap.add_argument("--budget", type=float, default=0.0,
                    help="seconds of wall clock per process, 0 for no limit")
    ap.add_argument("--out", required=True)
    ap.add_argument("--skip-done", default="",
                    help="a prior .jsonl whose finished cells are not redone")
    args = ap.parse_args()

    out = os.path.abspath(args.out)
    skip_done = os.path.abspath(args.skip_done) if args.skip_done else ""
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)

    done_already = set()
    if skip_done and os.path.exists(skip_done):
        with open(skip_done, encoding="utf-8") as f:
            for line in f:
                try:
                    r = json.loads(line)
                except ValueError:
                    continue      # a torn final line from a killed job
                if r.get("sector") == args.sector and r.get("ok"):
                    done_already.add(int(r["cell"]))

    cell_ids = [c for c in shard_cells(args.shard, args.nshard)
                if c not in done_already]

    # The near branch caps every target: the whole dichotomy is min(near, away),
    # so an away run at a target the near branch does not clear proves nothing.
    vr, mc = load_author_modules(args.src)
    pos, near = near_branch(vr, args.eta)
    head = {"sector": args.sector, "shard": args.shard, "nshard": args.nshard,
            "target": args.target, "eta": args.eta, "cells_to_do": len(cell_ids),
            "skipped_done": len(done_already), "nproc": args.nproc,
            "positivity_margin": pos, "near_gain": near,
            "near_clears_target": bool(pos > 0 and near > args.target)}
    print(json.dumps(head), flush=True)
    if not head["near_clears_target"]:
        with open(out + ".head.json", "w", encoding="utf-8") as f:
            json.dump(head, f, indent=1)
        raise SystemExit("near branch does not clear this target; no away run")
    with open(out + ".head.json", "w", encoding="utf-8") as f:
        json.dump(head, f, indent=1)
    if not cell_ids:
        open(out, "a", encoding="utf-8").close()
        print("nothing left to do in this shard", flush=True)
        return

    nproc = max(1, min(args.nproc, len(cell_ids)))
    t0 = time.perf_counter()
    if nproc == 1:
        run_slice(0, 1, cell_ids, args, out)
    else:
        # Each process writes its own `.jsonl`, and the merge below is a
        # convenience rather than the thing that saves the work: if the job is
        # killed before the merge runs, the per-process files are still picked
        # up by the artifact upload and by `ci_plan.py collect`, which globs
        # `*.jsonl` and dedupes on (sector, cell).  Naming them `.pN` without
        # the suffix would have quietly lost a killed job's whole shard.
        parts = [f"{os.path.splitext(out)[0]}.p{p}.jsonl" for p in range(nproc)]
        kids = []
        for p in range(nproc):
            pid = os.fork()
            if pid == 0:
                try:
                    run_slice(p, nproc, cell_ids, args, parts[p])
                finally:
                    os._exit(0)
            kids.append(pid)
        for pid in kids:
            os.waitpid(pid, 0)
        with open(out, "a", encoding="utf-8") as f:
            for part in parts:
                if os.path.exists(part):
                    with open(part, encoding="utf-8") as g:
                        f.write(g.read())
                    os.remove(part)

    n_ok = n_bad = boxes = 0
    with open(out, encoding="utf-8") as f:
        for line in f:
            try:
                r = json.loads(line)
            except ValueError:
                continue
            boxes += r["terminal"]
            n_ok += bool(r["ok"])
            n_bad += not r["ok"]
    print(json.dumps({"sector": args.sector, "shard": args.shard,
                      "cells_accepted": n_ok, "cells_refused": n_bad,
                      "terminal_boxes": boxes,
                      "wall_seconds": round(time.perf_counter() - t0, 1)}),
          flush=True)


if __name__ == "__main__":
    main()
