"""Phase 0: measure the boxed-`s` width constant rho_W on the low-sigma left edge.

`docs/25` §4.3 records rho_W ~ 5.9 against the plan's 2.6, measured on 11 big
boxes *all on one edge*, and names the gap: the constant "has not been sampled"
on the low-sigma left edge, "which is where the cost concentrates and where the
model is least tested".  This script samples it there.

rho_W is the coefficient of `delta * Sigma` in the width term of `predM`
(`lean/cert/rung3_plan2_report.md`: predM = X + 2*width + 2*r with
width = 1.30 * delta * Sigma, so the planned coefficient is 2.60).  It is
measured here as

    rho_W = (normBound(B_box) - normBound(B_point)) / (delta * Sigma)

i.e. the extra L1 norm caused by letting `s` range over the segment rather than
sit at its centre, per unit of the model's own width budget.

The Sigma convention is not guessed: it is calibrated against the two values the
plan report states for `B_right_06` (Sigma = 7.9 at K = 17, 10.6 at K = 34)
before any left-edge number is reported.  The calibration also fixes a trap: the
report's `delta` is the *full* segment width, and normalizing by the half-width
would report rho_W at twice its value.

Measured 2026-08-15, 15 big boxes at nLog = 32, nExp = 20, p = 64, kE = 10,
composite chains (one machine, `lean/cert/rung3_plan2.json`):

    edge      n   rho_W range   mean   margin vs M
    bottom    3   5.17 - 5.76   5.41   0.615 - 0.641
    left      6   4.92 - 5.59   5.20   0.578 - 0.934     <- the untested edge
    right     3   4.23 - 5.36   4.90   0.572 - 0.961
    top       3   4.48 - 5.03   4.76   0.657 - 0.708

**The low-sigma left edge is not worse than the others.** Its mean sits between
top and bottom, the between-edge spread (4.76-5.41) is smaller than the spread
within any one edge, and every value is at or below the ~5.9 `docs/25` recorded
from a single edge.  So the one constant the cost estimate leaned on and had
never sampled where it matters does not blow up there.  All 15 boxes still fail
`M`, reproducing §4.3's 11-of-11.

rho_W is only *approximately* scale-invariant in delta: within the left edge it
drifts 4.92 -> 5.59 as delta goes 0.0026 -> 0.0085.  `K` co-varies with delta in
this sample, so the two are confounded and neither is isolated here.

`--arith ball` re-runs the identical sites through `63_rung3_ball_mirror.py`.
Measured on the same 15 boxes, paired:

    rho_W    rect mean 5.09  ->  ball mean 0.37     gain 13.7x (12.0-15.3x)
    verdict  rect 0/15 PASS  ->  ball 15/15 PASS    margins 2.14 - 3.76

The gain is larger than the ~2x `docs/25` §4.3 estimated for a polar or
mean-value enclosure, and it lands *below* the planner's own assumed 2.60 by 7x:
with rotation wrapping gone, plan v2's width budget is conservative rather than
optimistic.  Enclosure is not being dropped to get there — the assembled ball is
checked against `zeta.epstein.dh_f`, the Hurwitz route, in
`tests/test_rung3_ball_assembly.py`, alongside the rectangle case as a control.

Scope of that claim: big boxes only.  Grid sites are point evaluations, where
rho_W does not apply, and the centre has its own budget defect (`docs/25` §4.3
defect 1, the radius counted twice); neither is measured here.

Run: .venv/bin/python scripts/62_rung3_rho_w.py [--boxes N] [--arith rect|ball]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import importlib

_box = importlib.import_module("61_rung3_mirror")
mirror = _box
_ball = None


def use_arith(kind: str):
    """Swap the arithmetic layer, in both directions.

    Both modules expose the same operation names, so only the construction of the
    `s` enclosure differs.  Restoring on "rect" is load-bearing: an earlier
    version only ever swapped *to* ball, so an in-process rect/ball comparison
    silently compared ball against itself and reported them identical.
    """
    global mirror, _ball
    if kind == "ball":
        _ball = importlib.import_module("63_rung3_ball_mirror")
        mirror = _ball
    else:
        _ball = None
        mirror = _box
    return mirror


def make_S(relo, rehi, imlo, imhi):
    if _ball is not None:
        return _ball.from_box(relo, rehi, imlo, imhi)
    return mirror.C(mirror.I(relo, rehi), mirror.I(imlo, imhi))

PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())

# Target configuration of HANDOFF's fourth 2026-08-10 record.
NLOG, NEXP, P, KE = 32, 20, 64, 10

KAPPA = 0.2840791  # midpoint of kappaI; only used in the float Sigma model


def sigma_model(K: int, sigma: float, weighted: bool) -> float:
    """The width model's sum over the partial-sum range, `Sigma`.

    `weighted` applies the |c_m| coefficients (1, kappa, kappa, 1, 0 by residue);
    unweighted counts every m not divisible by 5 with weight 1.  Which of the two
    the planner used is decided by calibration, not by assumption.
    """
    tot = 0.0
    for m in range(2, 5 * K):
        j = m % 5
        if j == 0:
            continue
        c = (KAPPA if j in (2, 3) else 1.0) if weighted else 1.0
        tot += c * m ** (-sigma) * math.log(m)
    return tot


def calibrate_sigma() -> bool:
    """Reproduce the plan report's stated Sigma for B_right_06 before trusting it."""
    box = next(b for b in PLAN["big"]["boxes"] if b["id"] == "B_right_06")
    sigma = float(F(box["sigma_lo"]))
    delta = float(F(box["im_hi"]) - F(box["im_lo"]))
    print(f"  calibration box B_right_06: sigma_lo={sigma}, K={box['K']}, "
          f"full width={delta:.6g} (report states delta = 0.02179)")
    ok = False
    for weighted in (False, True):
        s17, s34 = sigma_model(17, sigma, weighted), sigma_model(34, sigma, weighted)
        tag = "weighted" if weighted else "unweighted"
        hit = abs(s17 - 7.9) < 0.15 and abs(s34 - 10.6) < 0.15
        print(f"    {tag:10s}: Sigma(K=17)={s17:6.3f} (report 7.9), "
              f"Sigma(K=34)={s34:6.3f} (report 10.6){'   <-- MATCH' if hit else ''}")
        ok = ok or hit
    return ok


def box_norms(site: dict) -> dict:
    """normBound / normLower for the site, boxed and at the segment centre.

    Mirrors `emit_site`'s assembly in scripts/60_rung3_generate.py exactly, but at
    the split Taylor orders and on composite chains (`term_chain`), which is the
    configuration the re-plan would use.
    """
    K = site["K"]
    N = 5 * K
    relo, rehi = F(site["re_lo"]), F(site["re_hi"])
    imlo, imhi = F(site["im_lo"]), F(site["im_hi"])
    r = F(site["r"])

    def assemble(MS):
        cache: dict = {}
        acc = mirror.cexact(0, 0)
        for m in range(N):
            acc = mirror.cadd(acc, mirror.term_chain(m, MS, NLOG, NEXP, P, KE, cache))
        blockt = {m: mirror.cpowBox(m, MS, NLOG, NEXP, P, KE, cache)
                  for m in (N + 1, N + 2, N + 3, N + 4)}
        m1, m2, m3, m4 = N + 1, N + 2, N + 3, N + 4
        blockBox = mirror.cadd(
            mirror.cadd(blockt[m1], mirror.cneg(blockt[m4])),
            mirror.cmul(mirror.KAPPA_C,
                        mirror.cadd(blockt[m2], mirror.cneg(blockt[m3]))))
        antiSum = mirror.cadd(
            mirror.cadd(mirror.cmul(mirror.cexact(m1, 0), blockt[m1]),
                        mirror.cneg(mirror.cmul(mirror.cexact(m4, 0), blockt[m4]))),
            mirror.cmul(mirror.KAPPA_C,
                        mirror.cadd(mirror.cmul(mirror.cexact(m2, 0), blockt[m2]),
                                    mirror.cneg(mirror.cmul(mirror.cexact(m3, 0),
                                                            blockt[m3])))))
        antiBox = mirror.cmul(antiSum, mirror.invC(mirror.inv5sBox(MS)))
        B = mirror.cadd(mirror.cadd(acc, mirror.cmul(blockBox, mirror.cexact(F(1, 2), 0))),
                        mirror.cneg(antiBox))
        return mirror.cinflate(B, r)

    boxed = assemble(make_S(relo, rehi, imlo, imhi))
    cre, cim = (relo + rehi) / 2, (imlo + imhi) / 2
    point = assemble(make_S(cre, cre, cim, cim))
    return {
        "nb_box": mirror.normBound(boxed),
        "nb_point": mirror.normBound(point),
        "nl_box": mirror.normLower(boxed),
        # `delta` is the FULL segment width, not the half-width: the plan report
        # states delta = 0.02179 for B_right_06, whose im range is 0.0217896.
        # Normalizing rho_W by the half-width would double it.  Left/right
        # segments are vertical (re degenerate), top/bottom horizontal (im
        # degenerate), so take whichever direction the segment actually runs in.
        "delta": max(rehi - relo, imhi - imlo),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--boxes", type=int, default=6,
                    help="how many boxes per edge to sample")
    ap.add_argument("--out", default=None)
    ap.add_argument("--arith", choices=("rect", "ball"), default="rect",
                    help="rectangle enclosures (as shipped) or ball enclosures")
    ap.add_argument("--absmode", choices=("sqrt", "l1"), default="sqrt",
                    help="ball only: modulus bound used by the product")
    args = ap.parse_args()
    use_arith(args.arith)
    if _ball is not None:
        _ball.ABSMODE = args.absmode

    M = F(PLAN["M"])
    print(f"M = {float(M):.5f}   planned width coefficient rho_W = 2.60   "
          f"(config nLog={NLOG}, nExp={NEXP}, p={P}, kE={KE}, chains, "
          f"arith={args.arith}"
          f"{'/' + args.absmode if args.arith == 'ball' else ''})\n")

    print("Sigma convention calibration (must reproduce the plan report):")
    weighted = None
    box = next(b for b in PLAN["big"]["boxes"] if b["id"] == "B_right_06")
    sig = float(F(box["sigma_lo"]))
    if calibrate_sigma():
        weighted = abs(sigma_model(17, sig, True) - 7.9) < 0.15
    else:
        print("    NO MATCH — Sigma convention not recovered; rho_W reported as "
              "ratio-to-plan only.")
    print()

    boxes = PLAN["big"]["boxes"]
    segs: dict[str, list] = {}
    for b in boxes:
        segs.setdefault(b["segment"], []).append(b)
    groups = []
    for name in sorted(segs):
        sel = sorted(segs[name], key=lambda b: max(F(b["re_hi"]) - F(b["re_lo"]), F(b["im_hi"]) - F(b["im_lo"])))
        # widest, narrowest and middle: rho_W is claimed scale-invariant in delta,
        # so spread the sample over delta rather than clustering it.
        n = args.boxes if name == "left" else max(2, args.boxes // 2)
        idx = sorted({round(i * (len(sel) - 1) / max(1, n - 1)) for i in range(n)})
        groups.append((name, [sel[i] for i in idx]))

    rows = []
    for edge, sel in groups:
        print(f"=== {edge} ===")
        for b in sel:
            t0 = time.time()
            n = box_norms(b)
            sigma = float(F(b["sigma_lo"]))
            Sig = sigma_model(b["K"], sigma, bool(weighted)) if weighted is not None else None
            delta = float(n["delta"])
            width = float(n["nb_box"] - n["nb_point"])
            rho = width / (delta * Sig) if Sig else float("nan")
            margin = float(M / n["nb_box"])
            row = {
                "id": b["id"], "K": b["K"], "sigma_lo": b["sigma_lo"],
                "delta": delta, "Sigma": Sig,
                "nb_box": float(n["nb_box"]), "nb_point": float(n["nb_point"]),
                "width": width, "rho_W": rho,
                "predM": float(F(b["predM"])), "margin_vs_M": margin,
                "ratio_to_predM": float(n["nb_box"]) / float(F(b["predM"])),
                "verdict": "PASS" if n["nb_box"] <= M else "FAIL",
                "secs": round(time.time() - t0, 1),
            }
            rows.append(row)
            print(f"  {row['id']:14s} K={row['K']:3d} sig={sigma:.4f} "
                  f"delta={delta:.6f} normBound={row['nb_box']:8.4f} "
                  f"predM={row['predM']:6.4f} margin={margin:6.4f} "
                  f"rho_W={rho:6.2f}  {row['verdict']}  [{row['secs']}s]", flush=True)
        print()

    print("=== SUMMARY ===")
    for tag, _ in groups:
        sel = [r for r in rows if r["id"].startswith(f"B_{tag}")]
        if not sel:
            continue
        rw = [r["rho_W"] for r in sel]
        mg = [r["margin_vs_M"] for r in sel]
        print(f"  {tag:10s}: n={len(sel)}  rho_W {min(rw):.2f}-{max(rw):.2f} "
              f"(mean {sum(rw)/len(rw):.2f})  margin {min(mg):.3f}-{max(mg):.3f}  "
              f"{sum(1 for r in sel if r['verdict']=='FAIL')} FAIL")

    if args.out:
        Path(args.out).write_text(json.dumps(rows, indent=2))
        print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
