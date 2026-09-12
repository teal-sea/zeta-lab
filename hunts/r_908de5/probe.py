"""beta := normLower, measure what the remedy costs and where the slack lands.

`docs/25` §4.3 defect 2 and commit 44d3133 record the same thing: the rung-3
grid sites carry `pred_beta` values that were *drawn at the achievable bound*
from mpmath point evaluations, so the certificate inequality

    normLower(B.inflate r)  >=  pred_beta                       (GRID)

sits at the line by construction: 12 of 104 sites clear it by under 1 %, the
thinnest (`g_right_15`) by 0.03 %.  The named remedy is to stop predicting the
bound and *read it off*: set `beta := normLower(B.inflate r)`, which the
generator already computes exactly, making (GRID) true by construction and
moving the whole question into the cell condition that consumes `beta`.

That condition is not a modelling choice; it is the hypothesis of
`ZetaLean.DH.DH_lower_on_hcell` / `DH_lower_on_vcell`
(`lean/ZetaLean/DHCertSupport.lean`), one per endpoint of each grid cell:

    eps' + L * h_i / 2  <=  beta_i                               (CELL)

with `L = 16`, `eps' = 1/2000` and `h_i` the gap to the next grid point.  So
the measurement this script makes is: what does (CELL) look like with
`beta := pred_beta` (as shipped) versus `beta := normLower` (the remedy), in
the arithmetic the *generator* actually emits?

Arithmetics, and why both appear:

* **rect**: `scripts/61_rung3_mirror.py`, called exactly as
  `emit_site` in `scripts/60_rung3_generate.py` calls it (`mirror.term`,
  nExp 20, p 64, kE 10).  This is bit-identical to the `ComplexInterval`
  value the emitted Lean file proves its literal equal to, so it is the
  arithmetic that decides what `beta` may legally be in the certificate.
* **ball**: `scripts/63_rung3_ball_mirror.py` on composite chains, the
  configuration `scripts/65_rung3_full_validation.py` ran for commit 44d3133.
  Read from that committed run (floats) unless `--ball` recomputes it.

Run:
  .venv/bin/python hunts/r_908de5/probe.py [--workers N] [--sites N] [--ball]
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

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())
BALL_RUN = ROOT / "lean" / "cert" / "rung3_ball_validation.json"

# The generator's own constants (scripts/60_rung3_generate.py).
TAYLOR_N, COARSEN_P, KE = 20, 64, 10
# The ball validation's constants (scripts/65_rung3_full_validation.py).
NLOG, NEXP = 32, 20

L = F(PLAN["L"])
EPS = F(PLAN["small"]["eps"])

# Denominator of the emitted `beta` literal.  `normLower` is an exact rational
# with a denominator in the thousands of bits; rounding it DOWN to a multiple of
# 2^-BETA_BITS keeps the Lean literal small and keeps (GRID) true, since a
# smaller beta is a weaker claim about the same enclosure.
BETA_BITS = 40


def beta_literal(nl: F) -> F:
    """Largest multiple of 2^-BETA_BITS that is <= nl."""
    scale = 1 << BETA_BITS
    return F(int(nl * scale), scale)


def site_point(site: dict) -> tuple[F, F]:
    x, fixed = F(site["x"]), F(site["fixed"])
    return (x, fixed) if site["segment"] in ("bottom", "top") else (fixed, x)


def _assemble(mod, re: F, im: F, K: int, r: F, chains: bool):
    """The site enclosure, assembled the way its consumer assembles it."""
    N = 5 * K
    S = (mod.from_box(re, re, im, im) if hasattr(mod, "from_box")
         else mod.C(mod.I(re, re), mod.I(im, im)))
    cache: dict = {}
    acc = mod.cexact(0, 0)
    for m in range(N):
        acc = mod.cadd(acc, (mod.term_chain(m, S, NLOG, NEXP, COARSEN_P, KE, cache)
                             if chains else mod.term(m, S, TAYLOR_N, COARSEN_P, KE)))
    m1, m2, m3, m4 = N + 1, N + 2, N + 3, N + 4
    if chains:
        blockt = {m: mod.cpowBox(m, S, NLOG, NEXP, COARSEN_P, KE, cache)
                  for m in (m1, m2, m3, m4)}
    else:
        blockt = {m: mod.dirichletTermBox(TAYLOR_N, COARSEN_P, m.bit_length(),
                                          KE, m, S)
                  for m in (m1, m2, m3, m4)}
    blockBox = mod.cadd(mod.cadd(blockt[m1], mod.cneg(blockt[m4])),
                        mod.cmul(mod.KAPPA_C,
                                 mod.cadd(blockt[m2], mod.cneg(blockt[m3]))))
    antiSum = mod.cadd(
        mod.cadd(mod.cmul(mod.cexact(m1, 0), blockt[m1]),
                 mod.cneg(mod.cmul(mod.cexact(m4, 0), blockt[m4]))),
        mod.cmul(mod.KAPPA_C,
                 mod.cadd(mod.cmul(mod.cexact(m2, 0), blockt[m2]),
                          mod.cneg(mod.cmul(mod.cexact(m3, 0), blockt[m3])))))
    antiBox = mod.cmul(antiSum, mod.invC(mod.inv5sBox(S)))
    B = mod.cadd(mod.cadd(acc, mod.cmul(blockBox, mod.cexact(F(1, 2), 0))),
                 mod.cneg(antiBox))
    return mod.cinflate(B, r)


def run_site(job):
    sid, arith = job
    site = next(g for g in PLAN["grid"] if g["id"] == sid)
    re, im = site_point(site)
    t0 = time.time()
    mod = importlib.import_module("63_rung3_ball_mirror" if arith == "ball"
                                  else "61_rung3_mirror")
    chains = arith != "rect"
    B = _assemble(mod, re, im, site["K"], F(site["r"]), chains)
    nl = mod.normLower(B)
    return {"id": sid, "arith": arith, "K": site["K"],
            "normLower": str(nl), "normLower_f": float(nl),
            "beta_lit": str(beta_literal(nl)),
            "pred_beta": site["pred_beta"],
            "grid_margin_pred": float(nl / F(site["pred_beta"])),
            "secs": round(time.time() - t0, 1)}


def cells() -> list[dict]:
    """Every (site, gap) endpoint obligation of DH_lower_on_[hv]cell."""
    by_seg: dict[str, list[dict]] = {}
    for g in PLAN["grid"]:
        by_seg.setdefault(g["segment"], []).append(g)
    out = []
    for seg, gs in by_seg.items():
        for i, g in enumerate(gs):
            if g["gap_next"] is None:
                continue
            h = F(g["gap_next"])
            need = EPS + L * h / 2
            for site in (g, gs[i + 1]):
                out.append({"cell": f"{g['id']}->{gs[i + 1]['id']}",
                            "site": site["id"], "need": need})
    return out


def report(betas: dict[str, F], tag: str, rows: list[dict]) -> dict:
    """(CELL) under a given assignment of betas.  Missing sites are skipped."""
    worst, n, nfail = None, 0, 0
    for c in cells():
        b = betas.get(c["site"])
        if b is None:
            continue
        n += 1
        ratio = b / c["need"]
        if ratio < 1:
            nfail += 1
        if worst is None or ratio < worst[0]:
            worst = (ratio, c)
        rows.append({"source": tag, "cell": c["cell"], "site": c["site"],
                     "need": float(c["need"]), "beta": float(b),
                     "ratio": float(ratio)})
    return {"source": tag, "obligations": n, "failing": nfail,
            "worst_ratio": float(worst[0]) if worst else None,
            "worst_cell": worst[1]["cell"] if worst else None,
            "worst_site": worst[1]["site"] if worst else None}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=max(1, mp_pool.cpu_count() - 1))
    ap.add_argument("--sites", type=int, default=0, help="0 = all")
    ap.add_argument("--ball", action="store_true",
                    help="recompute ball normLower instead of reading commit 44d3133")
    ap.add_argument("--plain", type=int, default=12,
                    help="sites to also measure in the generator's own non-chain "
                         "rect arithmetic (scripts/60 as shipped)")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent /
                                         "results.json"))
    args = ap.parse_args()

    ids = [g["id"] for g in PLAN["grid"]]
    seen, uniq = set(), []
    for i in ids:                      # 104 entries, 100 unique (corners shared)
        if i not in seen:
            seen.add(i)
            uniq.append(i)
    # Thinnest grid margins first: the sites the defect is about.
    order = {r["id"]: r["margin"] for r in
             json.loads(BALL_RUN.read_text())["sites"] if r["kind"] == "grid"}
    uniq.sort(key=lambda i: order.get(i, 9.9))
    if args.sites:
        uniq = uniq[:args.sites]

    jobs = [(i, "rectchain") for i in uniq]
    jobs += [(i, "rect") for i in uniq[:args.plain]]
    if args.ball:
        jobs += [(i, "ball") for i in uniq]
    print(f"{len(jobs)} jobs, {args.workers} workers", flush=True)

    t0 = time.time()
    measured = []
    with mp_pool.Pool(args.workers) as pool:
        for k, row in enumerate(pool.imap_unordered(run_site, jobs), 1):
            measured.append(row)
            if k % 10 == 0 or k == len(jobs):
                print(f"  [{k}/{len(jobs)}] {row['id']:14s} {row['arith']:4s} "
                      f"nl={row['normLower_f']:.8g} "
                      f"vs pred {row['grid_margin_pred']:.5f}", flush=True)
    print(f"wall-clock {round(time.time() - t0)}s", flush=True)

    chain = {r["id"]: F(r["beta_lit"]) for r in measured if r["arith"] == "rectchain"}
    plain = {r["id"]: F(r["beta_lit"]) for r in measured if r["arith"] == "rect"}
    ball = {r["id"]: F(r["beta_lit"]) for r in measured if r["arith"] == "ball"}
    if not ball:   # commit 44d3133's run, floats
        ball = {r["id"]: F(r["normLower"]).limit_denominator(10 ** 12)
                for r in json.loads(BALL_RUN.read_text())["sites"]
                if r["kind"] == "grid" and r["id"] in chain}
    pred = {g["id"]: F(g["pred_beta"]) for g in PLAN["grid"] if g["id"] in chain}

    cellrows: list[dict] = []
    summary = [report(pred, "pred_beta (as shipped)", cellrows),
               report(chain, "normLower rect+chains (remedy)", cellrows),
               report(ball, "normLower ball (remedy)", cellrows),
               report(plain, "normLower rect non-chain", cellrows)]

    print("\n=== (CELL)  eps' + L*h/2 <= beta, ratio beta/need ===")
    for s in summary:
        print(f"  {s['source']:26s} {s['obligations']:4d} obligations, "
              f"{s['failing']} failing, worst {s['worst_ratio']:.4f} "
              f"at {s['worst_site']}")

    for arith in ("rectchain", "rect"):
        grid = [r for r in measured if r["arith"] == arith]
        if not grid:
            continue
        below = [r for r in grid if r["grid_margin_pred"] < 1]
        print(f"\n=== (GRID) in {arith}: {len(below)}/{len(grid)} sites have "
              f"normLower < pred_beta ===")
        for r in sorted(grid, key=lambda r: r["grid_margin_pred"])[:6]:
            print(f"  {r['id']:14s} normLower/pred_beta = "
                  f"{r['grid_margin_pred']:.6f}")
    print("With beta := normLower the ratio is 1 by construction at every site.")

    out = {"config": {"rect": {"nExp": TAYLOR_N, "p": COARSEN_P, "kE": KE,
                               "chains": False, "as": "scripts/60 emit_site"},
                      "ball": {"nLog": NLOG, "nExp": NEXP, "p": COARSEN_P,
                               "kE": KE, "chains": True,
                               "as": ("recomputed" if args.ball
                                      else "commit 44d3133 rung3_ball_validation.json")},
                      "L": str(L), "eps": str(EPS), "beta_bits": BETA_BITS},
            "sites": sorted(measured, key=lambda r: (r["arith"], r["id"])),
            "cell_summary": summary,
            "cell_obligations": sorted(cellrows, key=lambda r: (r["source"],
                                                               r["ratio"]))}
    Path(args.out).write_text(json.dumps(out, indent=2))
    print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
