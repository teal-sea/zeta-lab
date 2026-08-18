"""Every site of plan v2 through ball arithmetic — the sampled claim made whole.

Commit 69b3f54 claims "every site kind passes at plan v2's existing geometry",
resting on 15 of 110 big boxes, 8 of 104 grid sites, and the centre once.  This
runs all 215 sites in ball arithmetic and records every verdict, so the claim
stops being an extrapolation.

Verdicts use each site kind's own condition from the plan:
  big box : normBound(B.inflate r) <= M
  grid    : normLower(B.inflate r) >= eps' + L*h/2
  centre  : normBound(B.inflate r) <  eps'

The grid verdict changed (hunt `hunts/r_908de5`).  It used to read
`normLower >= pred_beta`, and `pred_beta` was drawn at the achievable bound, so
that inequality was true at the line by construction in any arithmetic — 12 of
104 sites cleared it by under 1 %.  With `beta := normLower` (the remedy of
`docs/25` §4.3 defect 2, now the generator's default) the site inequality is
true by construction and measures nothing, so what is reported is the
obligation the certificate actually spends beta on: the hypothesis of
`ZetaLean.DH.DH_lower_on_[hv]cell`.  `grid_margin_pred` keeps the old ratio for
comparison against commit 44d3133.

Run: .venv/bin/python scripts/65_rung3_full_validation.py [--workers N] [--out FILE]
"""
from __future__ import annotations

import argparse
import importlib
import json
import multiprocessing as mp_pool
import sys
import time
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())
NLOG, NEXP, P, KE = 32, 20, 64, 10


def _cell_need() -> dict:
    """`eps' + L*h/2` per grid site: the hypothesis of `DH_lower_on_[hv]cell`.

    With `beta := normLower` (hunt `hunts/r_908de5`) the site inequality
    `normLower >= beta` is true by construction and measures nothing, so the
    grid verdict here is the obligation that still bites.
    """
    L, eps = F(PLAN["L"]), F(PLAN["small"]["eps"])
    by_seg: dict = {}
    for g in PLAN["grid"]:
        by_seg.setdefault(g["segment"], []).append(g)
    need: dict = {}
    for gs in by_seg.values():
        for i, g in enumerate(gs):
            if g["gap_next"] is None:
                continue
            d = eps + L * F(g["gap_next"]) / 2
            for s in (g, gs[i + 1]):
                need[s["id"]] = max(need.get(s["id"], F(0)), d)
    return need


CELL_NEED = _cell_need()


def _assemble_ball(re_lo, re_hi, im_lo, im_hi, K, r):
    ball = importlib.import_module("63_rung3_ball_mirror")
    S = ball.from_box(F(re_lo), F(re_hi), F(im_lo), F(im_hi))
    N = 5 * K
    cache: dict = {}
    acc = ball.cexact(0, 0)
    for m in range(N):
        acc = ball.cadd(acc, ball.term_chain(m, S, NLOG, NEXP, P, KE, cache))
    blockt = {m: ball.cpowBox(m, S, NLOG, NEXP, P, KE, cache)
              for m in (N + 1, N + 2, N + 3, N + 4)}
    m1, m2, m3, m4 = N + 1, N + 2, N + 3, N + 4
    blockBox = ball.cadd(
        ball.cadd(blockt[m1], ball.cneg(blockt[m4])),
        ball.cmul(ball.KAPPA_C, ball.cadd(blockt[m2], ball.cneg(blockt[m3]))))
    antiSum = ball.cadd(
        ball.cadd(ball.cmul(ball.cexact(m1, 0), blockt[m1]),
                  ball.cneg(ball.cmul(ball.cexact(m4, 0), blockt[m4]))),
        ball.cmul(ball.KAPPA_C,
                  ball.cadd(ball.cmul(ball.cexact(m2, 0), blockt[m2]),
                            ball.cneg(ball.cmul(ball.cexact(m3, 0), blockt[m3])))))
    antiBox = ball.cmul(antiSum, ball.invC(ball.inv5sBox(S)))
    B = ball.cadd(ball.cadd(acc, ball.cmul(blockBox, ball.cexact(F(1, 2), 0))),
                  ball.cneg(antiBox))
    return ball, ball.cinflate(B, F(r))


def run_site(job):
    kind, site = job
    t0 = time.time()
    try:
        if kind == "big":
            ball, B = _assemble_ball(site["re_lo"], site["re_hi"],
                                     site["im_lo"], site["im_hi"],
                                     site["K"], site["r"])
            nb = ball.normBound(B)
            M = F(PLAN["M"])
            return {"id": site["id"], "kind": kind, "K": site["K"],
                    "normBound": float(nb), "margin": float(M / nb),
                    "verdict": "PASS" if nb <= M else "FAIL",
                    "secs": round(time.time() - t0, 1)}
        if kind == "grid":
            x, fixed = F(site["x"]), F(site["fixed"])
            re, im = ((x, fixed) if site["segment"] in ("bottom", "top")
                      else (fixed, x))
            ball, B = _assemble_ball(re, re, im, im, site["K"], site["r"])
            nl = ball.normLower(B)
            beta = F(site["pred_beta"])
            need = CELL_NEED[site["id"]]
            return {"id": site["id"], "kind": kind, "K": site["K"],
                    "normLower": float(nl), "pred_beta": float(beta),
                    "margin": float(nl / need),
                    "grid_margin_pred": float(nl / beta) if beta else float("inf"),
                    "cell_need": float(need),
                    "verdict": "PASS" if nl >= need else "FAIL",
                    "secs": round(time.time() - t0, 1)}
        # centre
        small = PLAN["small"]
        ball, B = _assemble_ball(small["cre"], small["cre"],
                                 small["cim"], small["cim"],
                                 site["K"], site["r"])
        nb = ball.normBound(B)
        eps = F(small["eps"])
        return {"id": "centre", "kind": kind, "K": site["K"],
                "normBound": float(nb), "eps": float(eps),
                "margin": float(eps / nb),
                "verdict": "PASS" if nb < eps else "FAIL",
                "secs": round(time.time() - t0, 1)}
    except Exception as e:  # a crashed site is a FAIL, not a silence
        return {"id": site.get("id", kind), "kind": kind,
                "verdict": "ERROR", "error": repr(e),
                "secs": round(time.time() - t0, 1)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=max(1, mp_pool.cpu_count() - 1))
    ap.add_argument("--out", default=str(ROOT / "lean" / "cert" /
                                         "rung3_ball_validation.json"))
    args = ap.parse_args()

    jobs = ([("big", b) for b in PLAN["big"]["boxes"]]
            + [("grid", g) for g in PLAN["grid"]]
            + [("centre", PLAN["centre"])])
    # Largest K first, so the pool tail is short jobs.
    jobs.sort(key=lambda j: -j[1]["K"])
    print(f"{len(jobs)} sites, {args.workers} workers", flush=True)

    t0 = time.time()
    with mp_pool.Pool(args.workers) as pool:
        rows = []
        for i, row in enumerate(pool.imap_unordered(run_site, jobs), 1):
            rows.append(row)
            if row["verdict"] != "PASS" or i % 20 == 0:
                print(f"  [{i}/{len(jobs)}] {row['id']:14s} {row['verdict']}"
                      + (f" margin={row.get('margin', 0):.4f}"
                         if "margin" in row else ""), flush=True)

    rows.sort(key=lambda r: (r["kind"], r["id"]))
    print(f"\nwall-clock {round(time.time() - t0)}s")
    print("=== VERDICT ===")
    for kind in ("big", "grid", "centre"):
        sel = [r for r in rows if r["kind"] == kind]
        npass = sum(1 for r in sel if r["verdict"] == "PASS")
        mg = [r["margin"] for r in sel if "margin" in r]
        print(f"  {kind:7s}: {npass}/{len(sel)} PASS"
              + (f"   margin {min(mg):.4f} - {max(mg):.4f}" if mg else ""))
    nerr = sum(1 for r in rows if r["verdict"] == "ERROR")
    if nerr:
        print(f"  {nerr} ERROR site(s):")
        for r in rows:
            if r["verdict"] == "ERROR":
                print(f"    {r['id']}: {r['error']}")

    Path(args.out).write_text(json.dumps(
        {"config": {"nLog": NLOG, "nExp": NEXP, "p": P, "kE": KE,
                    "arith": "ball", "chains": True},
         "sites": rows}, indent=2))
    print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
