"""The k=2 tau-table, re-run with enclosures instead of scans.

`hunts/frontier_math/k2_closure.py` closes the k=2 equal-depth case of blocker
2 over 6600 tau-cells on `[0,132]`, at MEASURED grade: every supremum in it is
a double-precision scan (x-step 0.01, three tau-samples per cell, an 18-point
y-grid for the centre-centre row), padded by a flat `INFL = 1.05`.  The named
hardening obligation is the interval pass over the SAME finitely many cells.

This probe is that pass.  The geometry is not touched -- same windows, same
merge, same 0.25 zones, same integer trade, same budget floor.  What changes is
that every sup becomes an outward bound over the whole cell and every credit
becomes an inward bound, so a nonnegative margin is a statement about all
`(x, tau, y)` in the cell rather than about the sampled points.

Four scans are replaced, and they are replaced differently:

1. **the near field** (`4*sup max(0, D(.5,x) + D(.5,x-tau))` per zone).  A
   single ball-arithmetic ENVELOPE of `D(1/2, .)` on a uniform `1e-4` grid over
   `[0,190]`, built once, reused by every cell.  `D` is even in `s`, which
   halves it.  The cell's tau-sup is a 201-wide running maximum over the same
   envelope, so the tau dimension is covered continuously, not at three points.
   The `1.05` pad is DELETED: an enclosure needs no pad, and keeping one would
   hide how much the enclosure actually costs.
2. **the pair credits** (`Kpair` at a zone-pair distance, and `min_cell Kpair`).
   Lower bounds.  The zone-pair charge additionally drops the measured pass's
   `Kpair(min(dmax,6))` lookup, which is a lower bound only if `Kpair` is
   monotone on `[0,dmax]`, for a running minimum of a `Kpair` envelope over
   `[0,dmax]` -- rigorous with no monotonicity assumption.
3. **the centre-centre row** `C1 = sup_{y<=1/2} Dam(2y,tau)/y^2`.  An adaptive
   branch-and-bound in `u = 2y` over `[u1,1]`, plus a small-depth lemma on
   `(0,u1]` that the ball layer made available: `ghat` is even with real Taylor
   coefficients, so the depth-LINEAR term of `D` vanishes identically and
   `D(u,tau) <= -G(tau)^2 + (u^2/2) sup|D''|`, giving
   `sup_{u<=u1} 4 Dam/u^2 <= 4 max(0, sup|D''|/2 - G^2/u1^2)`.  No scan can
   reach `u -> 0`; this does.
4. **the far field and the budget floor**, which were already closed forms in
   proved constants -- recomputed in exact rationals so no float rounding
   enters, and a documented `1e-9` slack absorbs float rounding in the trade.

Run: ``.venv/bin/python hunts/r_a97060/probe.py`` (full table, both cap modes)
or ``--quick`` (the binding cells only).  The envelope caches to `data/`.

Nothing here is evidence about RH.  This is a hunt instrument; the reserved
word belongs to `zeta/rigor.py` and the Lean arm and is not used.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parent.parent
sys.path.insert(0, str(_HERE))
sys.path.insert(0, str(_ROOT / "hunts" / "frontier_math"))

import ball_field as BF  # noqa: E402
import k2_closure as K  # noqa: E402

# ---------------------------------------------------------------------------
# geometry and constants, taken from k2_closure unchanged
# ---------------------------------------------------------------------------

I_WINDOWS = K.I_WINDOWS
CELL = 0.02
TAU_HI = 132.0
ZONE_W = 0.25
MAX_ATOMS = 10

H = 1e-4                 # envelope step
XMAX = 190.0             # |x| never exceeds 132 + 57.07 in any lookup
NGRID = int(round(XMAX / H))
WIN = int(round(CELL / H))          # 200 envelope cells per tau-cell
FLOAT_SLACK = 1e-9       # documented pad for float rounding in the trade

BUDGET0 = F(2) * F(51944, 100000) * F(1, 4)
Q_FAR = F(1, 25000)
WT_C = F(637, 1000)


# ---------------------------------------------------------------------------
# 1. the D(1/2, .) envelope
# ---------------------------------------------------------------------------

def build_envelope(cache: Path | None = None) -> np.ndarray:
    """`up[j] >= sup D(1/2, x)` for `x in [j*H, (j+1)*H]`, `j = 0..NGRID-1`."""
    if cache is not None and cache.exists():
        z = np.load(cache)
        if z["h"] == H and len(z["up"]) == NGRID:
            return z["up"]
    up = np.empty(NGRID)
    t0 = time.time()
    for j in range(NGRID):
        up[j] = BF.D_upper(0.5, 0.5, j * H, (j + 1) * H)
        if j % 200000 == 0:
            print(f"    envelope {j}/{NGRID}  {time.time()-t0:.0f}s", flush=True)
    if cache is not None:
        cache.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(cache, up=up, h=H)
    return up


def mirror(up: np.ndarray) -> np.ndarray:
    """Extend to signed indices: `ext[j + NGRID]` covers `[j*H, (j+1)*H]` for
    `j in [-NGRID, NGRID)`.  `D(1/2, .)` is even, so the left half is a flip."""
    return np.concatenate([up[::-1], up])


def running_max(ext: np.ndarray) -> np.ndarray:
    """`rm[m] = max(ext[m-WIN : m+1])` -- the tau-sup of a whole cell."""
    pad = np.concatenate([np.full(WIN, -np.inf), ext])
    view = np.lib.stride_tricks.sliding_window_view(pad, WIN + 1)
    return view.max(axis=1)


# ---------------------------------------------------------------------------
# 2. Kpair envelopes (credits -> lower bounds)
# ---------------------------------------------------------------------------

HD = 1e-4
DMAX_TABLE = 10.0
NDIST = int(round(DMAX_TABLE / HD))


def build_kpair_runmin(cache: Path | None = None) -> np.ndarray:
    """`rmin[j] <= inf Kpair` on `[0, (j+1)*HD]` -- a lower bound for the charge
    between two zones at any distance `<= (j+1)*HD`.  No monotonicity used."""
    if cache is not None and cache.exists():
        z = np.load(cache)
        if z["h"] == HD and len(z["rmin"]) == NDIST:
            return z["rmin"]
    lo = np.empty(NDIST)
    for j in range(NDIST):
        lo[j] = BF.kpair_lower(j * HD, (j + 1) * HD)
    rmin = np.minimum.accumulate(lo)
    if cache is not None:
        np.savez_compressed(cache, rmin=rmin, h=HD)
    return rmin


def charge_lower(rmin: np.ndarray, dmax: float) -> float:
    """A rigorous lower bound on `Kpair(d)` for every `d in [0, dmax]`."""
    if dmax >= DMAX_TABLE:
        return 0.0
    return float(rmin[min(NDIST - 1, int(math.floor(dmax / HD)))])


# ---------------------------------------------------------------------------
# 3. the near deficit, per cell, from the envelope
# ---------------------------------------------------------------------------

def _merged_regions(ta: float, tb: float):
    regs = []
    for (a, b) in I_WINDOWS:
        regs.append((-b, -a))
        regs.append((a, b))
        regs.append((ta - b, tb - a))
        regs.append((ta + a, tb + b))
    regs.sort()
    merged = [list(regs[0])]
    for lo, hi in regs[1:]:
        if lo <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], hi)
        else:
            merged.append([lo, hi])
    return merged


def zone_trade(zcaps, zpos, rmin, exhaustive=False) -> float:
    """Exact max over integer zone multiplicities of caps minus pair charges.

    Same branch and bound as `k2_closure.zone_trade`, with two changes: the
    charge matrix is a rigorous lower bound (so the adversary's gain is an upper
    bound), and `exhaustive=True` drops the measured pass's inner
    monotone prune, which is a heuristic rather than an admissible bound.
    """
    Z = len(zcaps)
    if Z == 0:
        return 0.0
    qmat = np.zeros((Z, Z))
    for a in range(Z):
        for b in range(Z):
            dmax = max(abs(zpos[a][1] - zpos[b][0]), abs(zpos[b][1] - zpos[a][0]))
            qmat[a][b] = charge_lower(rmin, dmax) / 200
    order = np.argsort(-np.asarray(zcaps))
    caps = [zcaps[i] for i in order]
    q = qmat[np.ix_(order, order)]
    best = 0.0

    def dfs(idx, ms, val, rem):
        nonlocal best
        if val > best:
            best = val
        if idx >= len(caps) or rem == 0:
            return
        if val + rem * caps[idx] <= best:
            return
        for m in range(rem, -1, -1):
            v = val + caps[idx] * m - q[idx][idx] * m * (m - 1)
            for j, mj in enumerate(ms):
                v -= 2 * q[j][idx] * mj * m
            if exhaustive or v > val - 1e-18 or m == 0:
                dfs(idx + 1, ms + [m], v, rem - m)

    dfs(0, [], 0.0, MAX_ATOMS)
    return best


def near_deficit(i: int, ext: np.ndarray, rmax: np.ndarray, rmin: np.ndarray,
                 signed: bool, exhaustive=False, pad: float = 1.0):
    """Enclosure-valued near deficit for tau-cell `i`.  Returns (total, nzones)."""
    ta, tb = i * CELL, (i + 1) * CELL
    tot, nz_active = 0.0, 0
    for lo, hi in _merged_regions(ta, tb):
        nz = max(1, int(math.ceil((hi - lo) / ZONE_W)))
        edges = np.linspace(lo, hi, nz + 1)
        zcaps, zpos = [], []
        for k in range(nz):
            # snap outward to the envelope grid: the zone can only grow
            j0 = int(math.floor(edges[k] / H)) + NGRID
            j1 = int(math.ceil(edges[k + 1] / H)) + NGRID
            j0, j1 = max(0, j0), min(2 * NGRID, max(j0 + 1, j1))
            own = ext[j0:j1]                       # sup D(.5, x) per fine cell
            oth = rmax[j0 - WIN * i:j1 - WIN * i]  # sup D(.5, x-tau), tau in cell
            n = min(len(own), len(oth))
            if n == 0:
                continue
            if signed:
                sup = float(np.max(own[:n] + oth[:n]))
            else:
                sup = float(np.max(np.maximum(0.0, own[:n])
                                   + np.maximum(0.0, oth[:n])))
            cap = pad * 4.0 * max(0.0, sup)
            if cap > 1e-9:
                zcaps.append(cap)
                zpos.append((edges[k], edges[k + 1]))
                nz_active += 1
        tot += zone_trade(zcaps, zpos, rmin, exhaustive=exhaustive)
    return tot, nz_active


# ---------------------------------------------------------------------------
# 4. the centre-centre row, with the u -> 0 corner closed
# ---------------------------------------------------------------------------

U1 = 0.02          # below this the small-depth lemma takes over
C1_TOL = 1e-5      # branch-and-bound stopping width
C1_MAXBOX = 400
SECOND_ORDER_UPTO = 0.55   # below this the second-order bound usually wins


def c1_upper(i: int):
    """Upper bound on `sup_{0<y<=1/2} Dam(2y,tau)/y^2` over the whole cell.

    In `u = 2y`: `sup_{0<u<=1} 4 max(0, D(u,tau))/u^2`.

    TWO bounds are available for a `u`-box `[a,b]`, and the smaller is taken:

    * the direct one, `4 max(0, sup D)/a^2`.  Tight for `a` near 1, and useless
      as `a -> 0`, where the `1/a^2` multiplies an enclosure whose width is set
      by the TAU-cell, not by the `u`-box.  That is what a scan cannot see and
      what stalled a pure branch-and-bound at the cells where `G` has a root.
    * the second-order one.  `ghat` is even with real Taylor coefficients, so
      `Re ghat'(i tau)` vanishes and `D` has NO depth-linear term:
      `D(u,tau) <= -G(tau)^2 + (u^2/2) sup_{[0,b]}|D''|`, hence
      `4 max(0,D)/u^2 <= 4 max(0, sup|D''|/2 - G^2/b^2)` for every `u <= b`.
      This is the bound that closes the `u -> 0` corner, where no scan reaches.

    Returns `(bound, lower_witness, boxes_used, second_order_part)`.
    """
    ta, tb = i * CELL, (i + 1) * CELL
    glo = BF.G_abs_lower(ta, tb)
    _memo = {}

    def second_order(b):
        if b not in _memo:
            m2 = BF.ddD_absupper(0.0, b, ta, tb)
            _memo[b] = 4.0 * max(0.0, m2 / 2 - glo * glo / (b * b))
        return _memo[b]

    lemma = second_order(U1)

    def box_bound(a, b):
        direct = 4.0 * max(0.0, BF.D_upper(a, b, ta, tb)) / (a * a)
        if a < SECOND_ORDER_UPTO and direct > 0.0:
            return min(direct, second_order(b))
        return direct

    boxes = []
    edges = np.geomspace(U1, 1.0, 9)
    for a, b in zip(edges[:-1], edges[1:]):
        boxes.append((box_bound(a, b), a, b))
    best_lo = 4.0 * max(0.0, BF.D_lower(1.0, 1.0, ta, tb))
    used = len(boxes)
    while used < C1_MAXBOX:
        boxes.sort(reverse=True)
        top, a, b = boxes[0]
        if top - best_lo <= C1_TOL or top <= best_lo:
            break
        mid = math.sqrt(a * b)
        boxes = boxes[1:]
        for aa, bb in ((a, mid), (mid, b)):
            boxes.append((box_bound(aa, bb), aa, bb))
            best_lo = max(best_lo,
                          4.0 * max(0.0, BF.D_lower(bb, bb, ta, tb)) / (bb * bb))
        used += 2
    ladder = max(b for b, _, _ in boxes)
    return max(ladder, lemma), best_lo, used, lemma


# ---------------------------------------------------------------------------
# 5. far field and budget, in exact rationals
# ---------------------------------------------------------------------------

def PQ(cap: F, q: F) -> F:
    """`max_m cap*m - q*m*(m-1)` over integers, exactly."""
    if cap <= 0:
        return F(0)
    mstar = F(1, 2) + cap / (2 * q)
    best = F(0)
    for m in (math.floor(mstar), math.ceil(mstar)):
        if m >= 0:
            best = max(best, cap * m - q * m * (m - 1))
    return best


def far_total_exact(ta: F) -> F:
    tot = F(0)
    inner = ta > F(60) + F(28, 5)
    for i in range(57):
        lo = F(60 + 6 * i)
        wt = WT_C / (lo * lo - 2)
        tot += 2 * PQ(2 * wt, Q_FAR)
        if inner:
            tot += 2 * PQ(wt, Q_FAR)
    s = F(402)
    base = WT_C * (F(1) / (s * s - 2) + F(1, 6) / (s - 2))
    tot += 2 * (2 * base) + (2 * base if inner else F(0))
    return tot


_FAR_OUT = float(far_total_exact(F(0)))
_FAR_IN = float(far_total_exact(F(66)))
_BUDGET0F = float(BUDGET0)


# ---------------------------------------------------------------------------
# 6. the table
# ---------------------------------------------------------------------------

def cell_margin(i, ext, rmax, rmin, signed, exhaustive=False, pad=1.0):
    ta, tb = i * CELL, (i + 1) * CELL
    near, nz = near_deficit(i, ext, rmax, rmin, signed, exhaustive, pad=pad)
    c1, c1lo, c1box, c1lemma = c1_upper(i)
    kp = BF.kpair_lower(ta, tb)
    far = _FAR_IN if ta > 60 + 28 / 5 else _FAR_OUT
    deficit = near + far + c1 + FLOAT_SLACK
    return _BUDGET0F + 4 * kp - deficit, near, c1, 4 * kp, nz, c1box, c1lemma


def run(ext, rmax, rmin, ncells, verbose=True):
    """All three cap modes in one sweep: the per-cell depth row and the credit
    are mode-independent, so they are computed once and shared."""
    modes = [("signed", True, 1.0), ("unsigned", False, 1.0),
             ("unsigned_pad1.05", False, 1.05)]
    worst = {lab: (1e9, None) for lab, _, _ in modes}
    negs = {lab: [] for lab, _, _ in modes}
    c1_max = (0.0, None)
    _BREAK = {}
    widest_component = 0.0
    t0 = time.time()
    for i in range(ncells):
        ta = i * CELL
        c1 = c1_upper(i)[0]
        kp = BF.kpair_lower(ta, ta + CELL)
        far = _FAR_IN if ta > 60 + 28 / 5 else _FAR_OUT
        budget = _BUDGET0F + 4 * kp
        if c1 > c1_max[0]:
            c1_max = (c1, ta)
        for lo, hi in _merged_regions(ta, ta + CELL):
            widest_component = max(widest_component, hi - lo)
        for lab, signed, pad in modes:
            near, _ = near_deficit(i, ext, rmax, rmin, signed, pad=pad)
            m = budget - (near + far + c1 + FLOAT_SLACK)
            if m < worst[lab][0]:
                worst[lab] = (m, ta + CELL / 2)
            if m <= 0:
                negs[lab].append((ta, m))
                if lab not in _BREAK or m < _BREAK[lab]["margin"]:
                    _BREAK[lab] = {"tau": ta, "margin": m, "near": near,
                                   "c1": c1, "kp4": 4 * kp, "far": far,
                                   "budget": budget}
        if verbose and i % 250 == 0:
            print(f"    {i}/{ncells}  worst " +
                  "  ".join(f"{k} {v[0]:+.6f}" for k, v in worst.items()) +
                  f"   {time.time()-t0:.0f}s", flush=True)
    out = {lab: {"worst_margin": worst[lab][0], "worst_tau": worst[lab][1],
                 "pad": pad, "neg_cells": len(negs[lab]), "cells": ncells,
                 "negatives": negs[lab][:40]}
           for lab, _, pad in modes}
    out["_worst_breakdown"] = _BREAK
    out["_shared"] = {"seconds": round(time.time() - t0, 1),
                      "max_c1_upper": c1_max[0], "max_c1_tau": c1_max[1],
                      "widest_near_component": widest_component}
    return out


# ---------------------------------------------------------------------------
# 7. controls
# ---------------------------------------------------------------------------

BINDING = [316, 642, 3170, 6302, 330, 300]   # 6.33, 12.85, 63.41, 126.05, 6.61, 6.01


def controls(ext, rmax, rmin):
    res = {}

    # (H1) enclosure vs scan on the binding cells: the inflation the pass costs.
    infl = []
    for i in BINDING:
        ta = i * CELL
        for signed in (True, False):
            enc, _ = near_deficit(i, ext, rmax, rmin, signed)
            padded = K.near_deficit(ta, ta + CELL, signed=signed)
            K.INFL = 1.0                      # the pad, actually removed
            scan = K.near_deficit(ta, ta + CELL, signed=signed)
            K.INFL = 1.05
            infl.append({"cell": i, "tau": ta, "mode": "signed" if signed else "unsigned",
                         "enclosure_near": enc, "scan_near_unpadded": scan,
                         "scan_near_padded": padded,
                         "ratio_vs_unpadded": enc / scan if scan else None,
                         "ratio_vs_padded": enc / padded if padded else None})
    res["near_inflation"] = infl

    # (H2) the inner prune of the measured branch and bound is a heuristic, not
    # an admissible bound.  Does dropping it change any binding cell?
    prune = []
    for i in BINDING:
        a, _ = near_deficit(i, ext, rmax, rmin, True, exhaustive=False)
        b, _ = near_deficit(i, ext, rmax, rmin, True, exhaustive=True)
        prune.append({"cell": i, "pruned": a, "exhaustive": b, "delta": b - a})
    res["prune_control"] = prune

    # (H3) the depth sup: does the 18-point y-grid of the measured pass miss the
    # true sup anywhere?  Compare its value to the enclosure's LOWER witness.
    depth = []
    for i in BINDING:
        ta = i * CELL
        c1, c1lo, boxes, lemma = c1_upper(i)
        ts = np.linspace(ta, ta + CELL, 7)
        scan = 0.0
        for y in K._YGRID:
            scan = max(scan, float(np.max(K._dam(2 * y, ts))) / y ** 2)
        depth.append({"cell": i, "tau": ta, "scan_c1": scan, "enclosure_upper": c1,
                      "enclosure_lower_witness": c1lo, "boxes": boxes,
                      "small_depth_lemma": lemma,
                      "scan_below_witness": scan < c1lo - 1e-12})
    res["depth_control"] = depth

    # (H4) planted fault: inflate the machine's own caps on the resonance cell.
    ladder = []
    for f in (1.0, 1.01, 1.02, 1.05, 1.10):
        i = 316
        near, _ = near_deficit(i, ext, rmax, rmin, False)
        c1 = c1_upper(i)[0]
        kp = BF.kpair_lower(i * CELL, (i + 1) * CELL)
        deficit = near + _FAR_OUT + c1
        ladder.append({"factor": f, "margin": _BUDGET0F + 4 * kp - f * deficit})
    res["planted_cap_fault"] = ladder

    # (H5) cross-backend: mpmath's iv rectangle context on the same boxes.
    try:
        from mpmath import iv
        iv.dps = 30
        s2 = iv.sqrt(2)

        def _sinh(w):
            return (iv.exp(w) - iv.exp(-w)) / 2

        def d_iv(y, slo, shi):
            z = iv.mpc(iv.mpf(y), iv.mpf([str(slo), str(shi)]))
            zp, zm = z + iv.mpc(0, 1) * s2, z - iv.mpc(0, 1) * s2
            g = _sinh(zp / 2) / zp + _sinh(zm / 2) / zm
            return -(g * g).real
        cross = []
        for x in (6.5, 12.4, 31.5, 50.0):
            r = d_iv(0.5, x, x + H)
            b = BF.D_enclosure(0.5, 0.5, x, x + H)
            bl, bu = float(b.lower()), float(b.upper())
            rl, ru = float(r.a), float(r.b)
            cross.append({"x": x, "ball": [bl, bu], "rect": [rl, ru],
                          "ball_inside_rect": rl <= bl and bu <= ru,
                          "width_ratio_rect_over_ball": (ru - rl) / (bu - bl)})
        res["cross_backend"] = cross
    except Exception as exc:                                    # pragma: no cover
        res["cross_backend"] = {"error": repr(exc)}
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--cells", type=int, default=int(round(TAU_HI / CELL)))
    ap.add_argument("--out", default=str(_HERE / "results.json"))
    args = ap.parse_args()

    print("building the D(1/2,.) envelope ...", flush=True)
    t0 = time.time()
    up = build_envelope(_ROOT / "data" / f"k2_ball_envelope_h{H:g}.npz")
    ext = mirror(up)
    rmax = running_max(ext)
    rmin = build_kpair_runmin(_ROOT / "data" / f"k2_kpair_runmin_h{HD:g}.npz")
    print(f"  envelope ready in {time.time()-t0:.0f}s "
          f"({NGRID} cells, step {H})", flush=True)

    res = {"grid": {"envelope_step": H, "cell": CELL, "zone": ZONE_W,
                    "tau_hi": TAU_HI, "cells": args.cells,
                    "u1_small_depth": U1, "c1_tol": C1_TOL,
                    "float_slack": FLOAT_SLACK, "prec_bits": 96,
                    "inflation_factor_removed": K.INFL},
           "far_total_exact": {"outer": _FAR_OUT, "inner": _FAR_IN},
           "budget0": _BUDGET0F}

    print("controls ...", flush=True)
    res["controls"] = controls(ext, rmax, rmin)
    for row in res["controls"]["near_inflation"]:
        print(f"  near tau={row['tau']:.2f} {row['mode']:8s} enclosure "
              f"{row['enclosure_near']:.6f}  scan(no pad) "
              f"{row['scan_near_unpadded']:.6f}  ratio {row['ratio_vs_unpadded']:.4f}"
              f"   scan(1.05 pad) {row['scan_near_padded']:.6f}")
    for row in res["controls"]["depth_control"]:
        print(f"  C1  tau={row['tau']:.2f} scan {row['scan_c1']:.6f} "
              f"enclosure [{row['enclosure_lower_witness']:.6f}, "
              f"{row['enclosure_upper']:.6f}] boxes {row['boxes']}")

    if args.quick:
        rows = []
        for i in BINDING:
            for signed in (True, False):
                m, near, c1, kp4, nz, cb, cl = cell_margin(i, ext, rmax, rmin, signed)
                rows.append({"cell": i, "tau": i * CELL,
                             "mode": "signed" if signed else "unsigned",
                             "margin": m, "near": near, "c1": c1, "kp4": kp4,
                             "active_zones": nz})
                print(f"  tau={i*CELL:7.2f} {'signed' if signed else 'unsigned':8s} "
                      f"margin {m:+.7f}  near {near:.6f}  c1 {c1:.6f}")
        res["quick"] = rows
    else:
        res["table"] = run(ext, rmax, rmin, args.cells)
        for lab, d in res["table"].items():
            if lab.startswith("_"):
                print(f"= shared = {d}")
                continue
            print(f"= enclosure table ({lab} caps) =")
            print(f"  worst cell tau ~ {d['worst_tau']:.3f}  margin "
                  f"{d['worst_margin']:+.7f}   nonpositive cells "
                  f"{d['neg_cells']} of {d['cells']}")
            for ta, m in d["negatives"][:12]:
                print(f"    NONPOSITIVE tau=[{ta:.2f},{ta+CELL:.2f}] margin {m:+.7f}")

    Path(args.out).write_text(json.dumps(res, indent=2, default=float))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
