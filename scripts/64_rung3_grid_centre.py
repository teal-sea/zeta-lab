"""Step 2: the grid sites and the centre, in both arithmetics.

`scripts/62_rung3_rho_w.py` measured the big boxes, where `s` ranges over a
segment and the rectangle representation pays for rotation.  The other two site
kinds are *point* evaluations and were left unmeasured:

* **grid sites**: the small frontier, certified by point enclosures under a
  Cauchy Lipschitz bound.  Condition: `normLower(B.inflate r) >= beta`.
  `docs/25` §4.3 defect 2: beta was *predicted*, and 30 of 59 sites fail it by
  under 1%, "effectively a coin flip".
* **the centre**, one site, `K = 361`.  Condition:
  `normBound(B.inflate r) < eps' = 1/2000`.  §4.3 defect 1: the box form's
  `normBound` is the L1 `max|re| + max|im| + 2r`, which charges the tail radius
  **twice**, and `2*r_c = 7.47e-4 > 5e-4`, so the centre "could not have passed
  at any Taylor order, any precision, any kappa".

A ball's `normBound` is `|c| + r`, which charges it once, so the centre's defect
is expected to close structurally rather than by raising `K` to 444.  This
script measures whether it does.

Run: .venv/bin/python scripts/64_rung3_grid_centre.py [--grid N] [--out FILE]
"""
from __future__ import annotations

import argparse
import importlib
import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

meas = importlib.import_module("62_rung3_rho_w")
PLAN = meas.PLAN


def site_point(site: dict) -> tuple[F, F]:
    """A grid site's (re, im).  Horizontal segments vary `re`, vertical vary `im`."""
    x, fixed = F(site["x"]), F(site["fixed"])
    return (x, fixed) if site["segment"] in ("bottom", "top") else (fixed, x)


def evaluate(re: F, im: F, K: int, r: F, arith: str) -> dict:
    """normLower / normBound of the assembled, inflated enclosure at a point."""
    meas.use_arith(arith)
    fake = {"K": K, "re_lo": str(re), "re_hi": str(re),
            "im_lo": str(im), "im_hi": str(im), "r": str(r)}
    n = meas.box_norms(fake)
    return {"normLower": n["nl_box"], "normBound": n["nb_box"]}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--grid", type=int, default=8, help="grid sites to sample")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    rows = []
    small = PLAN["small"]
    eps = F(small["eps"])

    # --- the centre -----------------------------------------------------------
    c = PLAN["centre"]
    cre, cim, r_c = F(small["cre"]), F(small["cim"]), F(c["r"])
    print(f"=== CENTRE (K={c['K']}, r_c={float(r_c):.6g}, eps'={float(eps):.6g}) ===")
    print(f"    2*r_c = {float(2 * r_c):.6g} "
          f"{'>' if 2 * r_c > eps else '<'} eps'  <- docs/25 §4.3 defect 1\n")
    for arith in ("rect", "ball"):
        t0 = time.time()
        n = evaluate(cre, cim, c["K"], r_c, arith)
        nb = n["normBound"]
        row = {"kind": "centre", "id": "centre", "arith": arith, "K": c["K"],
               "normBound": float(nb), "eps": float(eps),
               "margin": float(eps / nb), "verdict": "PASS" if nb < eps else "FAIL",
               "secs": round(time.time() - t0, 1)}
        rows.append(row)
        print(f"  {arith:5s}: normBound={row['normBound']:.6g}  "
              f"margin={row['margin']:.4f}  {row['verdict']}  [{row['secs']}s]",
              flush=True)

    # --- the grid -------------------------------------------------------------
    grid = PLAN["grid"]
    step = max(1, len(grid) // args.grid)
    sample = grid[::step][:args.grid]
    print(f"\n=== GRID ({len(sample)} of {len(grid)} sites) ===")
    print(f"  {'id':14s} {'K':>4s} {'arith':5s} {'normLower':>12s} {'pred_beta':>12s} "
          f"{'margin':>8s}  verdict")
    for site in sample:
        re, im = site_point(site)
        beta = F(site["pred_beta"])
        for arith in ("rect", "ball"):
            t0 = time.time()
            n = evaluate(re, im, site["K"], F(site["r"]), arith)
            nl = n["normLower"]
            row = {"kind": "grid", "id": site["id"], "arith": arith,
                   "K": site["K"], "normLower": float(nl), "pred_beta": float(beta),
                   "margin": float(nl / beta) if beta else float("inf"),
                   "verdict": "PASS" if nl >= beta else "FAIL",
                   "secs": round(time.time() - t0, 1)}
            rows.append(row)
            print(f"  {site['id']:14s} {site['K']:4d} {arith:5s} "
                  f"{row['normLower']:12.6g} {row['pred_beta']:12.6g} "
                  f"{row['margin']:8.4f}  {row['verdict']}  [{row['secs']}s]",
                  flush=True)

    # --- summary --------------------------------------------------------------
    print("\n=== SUMMARY ===")
    for kind in ("centre", "grid"):
        for arith in ("rect", "ball"):
            sel = [r for r in rows if r["kind"] == kind and r["arith"] == arith]
            if not sel:
                continue
            mg = [r["margin"] for r in sel]
            npass = sum(1 for r in sel if r["verdict"] == "PASS")
            print(f"  {kind:7s} {arith:5s}: {npass}/{len(sel)} PASS   "
                  f"margin {min(mg):.4f} - {max(mg):.4f}")
    gr = {a: [r for r in rows if r["kind"] == "grid" and r["arith"] == a]
          for a in ("rect", "ball")}
    if gr["rect"] and gr["ball"]:
        gains = [b["normLower"] / r["normLower"]
                 for r, b in zip(gr["rect"], gr["ball"]) if r["normLower"] > 0]
        if gains:
            print(f"  grid normLower gain (ball/rect): "
                  f"{min(gains):.2f}x - {max(gains):.2f}x, "
                  f"mean {sum(gains)/len(gains):.2f}x")

    if args.out:
        Path(args.out).write_text(json.dumps(rows, indent=2))
        print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
