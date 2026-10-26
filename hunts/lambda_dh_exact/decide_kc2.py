"""Kill condition 2, second clause, by a decided count: no zero of f with
beta >= 0.90 and 8 <= t <= 10^4.

Hunt #119, resumption of 2026-10-26.  Kill condition 2 (`MISSION.md`
huntspec) fires if "no zero with y0 > 0.40 is found below height 10^4".  The
float screen and `decide_low_zeros.py` already show that the deepest zero it
saw there has decided y0 < 0.3977502; what they cannot show is that the screen
missed nothing.  This module decides that directly, on Arb, by the argument
principle on the rectangle

    [0.90, 2.05] x [8, 10^4],

which must hold zero zeros.  It says nothing below t = 8 (where Hunt #61's
census and `zeta.epstein` already place no off-line zero) or at y0 in
(0.35, 0.40), and nothing at all about where the zeros with beta < 0.90 are.

Edges, positively oriented:

* right edge Re s = 2.05: f(s) = 1 + sum_{n>=2} a_n n^{-s} and
  S = sum_{n>=2} |a_n| n^{-2.05} < 1 is decided here by Arb (as
  5^{-sigma} [zeta(sigma,1/5) + kappa zeta(sigma,2/5) + kappa zeta(sigma,3/5)
  + zeta(sigma,4/5)] - 1 at sigma = 2.05), so Re f >= 1 - S > 0 on the whole
  edge and its arg variation is the difference of the two principal values;
* bottom, top and left edges: the chord-tube segment test of
  `decide_deep_zero.py`, with |f''| bounded per block by Cauchy from one Arb
  ball over a square of half-width R = block length about the block midpoint
  (every point of the block then has a disc of radius R - len/2 inside it).

The left edge is long, so it is sharded by height; each shard writes the exact
sum of its Arg balls, and `combine` adds the shards to the short edges.  The
total, divided by 2 pi, must be a ball containing the single integer 0.

Planted fault: `fault` runs the same instrument on [0.89, 2.05] x [2400, 2500]
(must give 1, the zero at gamma = 2442.53, beta = 0.89775) and on
[0.90, 2.05] x [2400, 2500] (must give 0).

Run:
    .venv/bin/python hunts/lambda_dh_exact/decide_kc2.py shard --i 0 --n 4
    .venv/bin/python hunts/lambda_dh_exact/decide_kc2.py short
    .venv/bin/python hunts/lambda_dh_exact/decide_kc2.py fault
    .venv/bin/python hunts/lambda_dh_exact/decide_kc2.py combine --n 4
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import decide_deep_zero as dd  # noqa: E402
from flint import acb, arb, ctx as fctx  # noqa: E402

PREC = 96
SIG_L = Fraction(9, 10)
SIG_R = Fraction(41, 20)
T_LO = Fraction(8)
T_HI = Fraction(10000)
BLOCK = Fraction(1, 8)
OUTDIR = os.path.join(_HERE, "kc2")


def _q(x: Fraction):
    return arb(x.numerator) / x.denominator


def edge_variation(route, pa, pb, block: Fraction = BLOCK, log_every: float = 0.0):
    """Sum of decided Arg pieces along the straight edge pa -> pb (an arb ball)."""
    length = abs(pb[0] - pa[0]) + abs(pb[1] - pa[1])   # axis-parallel edges only
    nblocks = max(1, math.ceil(length / block))
    cache = {}

    def pt(p):
        v = cache.get(p)
        if v is None:
            v = route.f_box(p[0], p[0], p[1], p[1])
            cache[p] = v
        return v

    def lerp(u: Fraction):
        return (pa[0] + (pb[0] - pa[0]) * u, pa[1] + (pb[1] - pa[1]) * u)

    total = arb(0)
    stats = {"blocks": 0, "segments": 0, "min_margin": math.inf, "block_splits": 0}
    t0 = time.time()

    def do_block(ua: Fraction, ub: Fraction, depth: int) -> bool:
        nonlocal total
        qa, qb = lerp(ua), lerp(ub)
        blen = (ub - ua) * length
        mid = ((qa[0] + qb[0]) / 2, (qa[1] + qb[1]) / 2)
        R = blen
        z = route.f_box(mid[0] - R, mid[0] + R, mid[1] - R, mid[1] + R)
        B = dd._abs_hi(route, z)
        rho = float(R - blen / 2) * dd.LO
        M2 = 2 * B / rho**2 * dd.HI
        pieces = []
        stack = [(ua + (ub - ua) * Fraction(i, 2), ua + (ub - ua) * Fraction(i + 1, 2), 0)
                 for i in (1, 0)]
        while stack:
            sa, sb, d = stack.pop()
            pa_, pb_ = lerp(sa), lerp(sb)
            ell = float((sb - sa) * length) * dd.HI
            tube = M2 * ell * ell / 8 * dd.HI
            clear = dd._clearance(route, pt(pa_), pt(pb_))
            got = route.arg_quotient(pt(pb_), pt(pa_)) if clear > tube else None
            if got is None:
                if d >= 6:
                    return False
                m = (sa + sb) / 2
                stack.append((m, sb, d + 1))
                stack.append((sa, m, d + 1))
                continue
            stats["min_margin"] = min(stats["min_margin"], clear / tube)
            pieces.append(got[2])
        for a in pieces:
            total += a
        stats["segments"] += len(pieces)
        stats["blocks"] += 1
        return True

    def block_rec(ua, ub, depth):
        if do_block(ua, ub, depth):
            return True
        if depth >= 8:
            raise RuntimeError(f"undecided block near {lerp(ua)}")
        stats["block_splits"] += 1
        m = (ua + ub) / 2
        return block_rec(ua, m, depth + 1) and block_rec(m, ub, depth + 1)

    for k in range(nblocks):
        ua = Fraction(k, nblocks)
        ub = Fraction(k + 1, nblocks)
        block_rec(ua, ub, 0)
        if log_every and (k + 1) % int(log_every) == 0:
            print(f"  block {k + 1}/{nblocks}  {time.time() - t0:.0f}s", flush=True)
    stats["point_evals"] = len(cache)
    stats["seconds"] = round(time.time() - t0, 1)
    return total, stats


def _ball_json(x) -> dict:
    return {"mid": x.mid().str(30, radius=False), "rad": float(x.rad()),
            "lo": float(x.lower()), "hi": float(x.upper())}


def right_edge(route, t_lo: Fraction, t_hi: Fraction):
    """Arg variation up Re s = 2.05, via the decided bound S < 1."""
    old = fctx.prec
    fctx.prec = PREC
    try:
        sig = _q(SIG_R)
        phi = (1 + arb(5).sqrt()) / 2
        kap = (1 + phi * phi).sqrt() - phi
        s = acb(sig)
        S = (s.zeta(acb(arb(1) / 5)) + kap * s.zeta(acb(arb(2) / 5))
             + kap * s.zeta(acb(arb(3) / 5)) + s.zeta(acb(arb(4) / 5))) * acb(5) ** (-s) - 1
        S = S.real
        if not S.upper() < 1:
            raise RuntimeError("S < 1 not decided")
        fa = route.f_box(SIG_R, SIG_R, t_lo, t_lo)
        fb = route.f_box(SIG_R, SIG_R, t_hi, t_hi)
        if not (fa.real.lower() > 0 and fb.real.lower() > 0):
            raise RuntimeError("Re f > 0 not seen at the right corners")
        var = fb.arg() - fa.arg()
        return var, {"S_bound": _ball_json(S)}
    finally:
        fctx.prec = old


def left_shard_range(i: int, n: int):
    span = (T_HI - T_LO) / n
    # the left edge runs downward: shard i covers [t_b, t_a] traversed t_b -> t_a
    t_top = T_HI - span * i
    t_bot = T_HI - span * (i + 1)
    return t_top, t_bot


def stage_shard(i: int, n: int):
    os.makedirs(OUTDIR, exist_ok=True)
    route = dd.ArbRoute(prec=PREC)
    t_top, t_bot = left_shard_range(i, n)
    var, st = edge_variation(route, (SIG_L, t_top), (SIG_L, t_bot), log_every=2000)
    out = {"edge": "left", "shard": i, "n": n, "from": [str(SIG_L), str(t_top)],
           "to": [str(SIG_L), str(t_bot)], "block": str(BLOCK), "prec": PREC,
           "variation": _ball_json(var), "variation_arb": var.str(40), "stats": st}
    with open(os.path.join(OUTDIR, f"left_{i}_of_{n}.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps(out["stats"]), out["variation"], flush=True)


def stage_short():
    os.makedirs(OUTDIR, exist_ok=True)
    route = dd.ArbRoute(prec=PREC)
    vb, sb = edge_variation(route, (SIG_L, T_LO), (SIG_R, T_LO))
    vr, sr = right_edge(route, T_LO, T_HI)
    vt, stt = edge_variation(route, (SIG_R, T_HI), (SIG_L, T_HI))
    out = {"bottom": {"variation": _ball_json(vb), "variation_arb": vb.str(40), "stats": sb},
           "right": {"variation": _ball_json(vr), "variation_arb": vr.str(40), **sr},
           "top": {"variation": _ball_json(vt), "variation_arb": vt.str(40), "stats": stt}}
    with open(os.path.join(OUTDIR, "short_edges.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps(out, indent=1), flush=True)


def count_rect(route, sl, sr, tl, th):
    """Full decided count on a small rectangle (used by the planted faults)."""
    v = arb(0)
    stats = []
    for pa, pb in [((sl, tl), (sr, tl)), ((sr, tl), (sr, th)), ((sr, th), (sl, th)), ((sl, th), (sl, tl))]:
        var, st = edge_variation(route, pa, pb)
        v += var
        stats.append(st)
    old = fctx.prec
    fctx.prec = PREC
    try:
        w = v / (2 * arb.pi())
        n = w.unique_fmpz()
    finally:
        fctx.prec = old
    return {"winding": _ball_json(w), "count": None if n is None else int(n),
            "segments": sum(s["segments"] for s in stats)}


def stage_fault():
    os.makedirs(OUTDIR, exist_ok=True)
    route = dd.ArbRoute(prec=PREC)
    a = count_rect(route, Fraction(89, 100), SIG_R, Fraction(2400), Fraction(2500))
    b = count_rect(route, SIG_L, SIG_R, Fraction(2400), Fraction(2500))
    out = {"edge_0.89_t2400_2500_expect_1": a, "edge_0.90_t2400_2500_expect_0": b}
    with open(os.path.join(OUTDIR, "faults.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(out, flush=True)


def stage_combine(n: int):
    old = fctx.prec
    fctx.prec = PREC
    try:
        short = json.load(open(os.path.join(OUTDIR, "short_edges.json")))
        tot = arb(0)
        for k in ("bottom", "right", "top"):
            tot += arb(short[k]["variation_arb"])
        shards = []
        for i in range(n):
            sh = json.load(open(os.path.join(OUTDIR, f"left_{i}_of_{n}.json")))
            tot += arb(sh["variation_arb"])
            shards.append(sh["stats"])
        w = tot / (2 * arb.pi())
        k = w.unique_fmpz()
        out = {"rectangle": [[str(SIG_L), str(SIG_R)], [str(T_LO), str(T_HI)]],
               "winding": _ball_json(w), "count": None if k is None else int(k),
               "status": "decided" if k is not None else "undecided",
               "left_edge_seconds": sum(s["seconds"] for s in shards),
               "left_edge_point_evals": sum(s["point_evals"] for s in shards),
               "left_edge_min_margin": min(s["min_margin"] for s in shards),
               "backend": "python-flint", "prec": PREC}
    finally:
        fctx.prec = old
    with open(os.path.join(_HERE, "decide_kc2.json"), "w") as fh:
        json.dump(out, fh, indent=2)
    print(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("stage", choices=["shard", "short", "fault", "combine", "time"])
    ap.add_argument("--i", type=int, default=0)
    ap.add_argument("--n", type=int, default=4)
    args = ap.parse_args()
    if args.stage == "shard":
        stage_shard(args.i, args.n)
    elif args.stage == "short":
        stage_short()
    elif args.stage == "fault":
        stage_fault()
    elif args.stage == "combine":
        stage_combine(args.n)
    else:
        route = dd.ArbRoute(prec=PREC)
        for t in (Fraction(500), Fraction(5000), Fraction(9900)):
            var, st = edge_variation(route, (SIG_L, t + 5), (SIG_L, t))
            print(t, st, flush=True)


if __name__ == "__main__":
    main()
