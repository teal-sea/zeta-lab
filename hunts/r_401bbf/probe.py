"""Re-run the full k=2 tau-table with `zone_trade`'s inner prune disabled.

`hunts/frontier_math/k2_closure.py::zone_trade` maximises, over integer zone
multiplicities `m` with `sum m <= 10`,

    V(m) = sum_i cap_i*m_i - sum_i q_ii*m_i*(m_i-1) - 2*sum_{j<i} q_ji*m_j*m_i

by depth-first search with two cuts.  One is an ordinary branch-and-bound
bound (`val + rem*caps[idx] <= best`), admissible because the caps are sorted
descending and the pair charges are nonnegative.  The other is the line

    if v > val - 1e-18 or m == 0:

which refuses to descend into a multiplicity that does not immediately improve
the running value.  That cut restricts the ADVERSARY's search, which is the
unsound direction: wherever it bites, the reported zone trade is too small and
the cell's deficit is understated.  Run `78b4ce8e` measured its delta as 0.0
on six binding cells and recorded the assumption as unchecked elsewhere.

This probe settles it on every cell.  The zone counts here are small (at most
six zones survive in any connected component of the whole table), so the honest
move is not to disable the inner prune alone but to drop BOTH cuts: for each
component we enumerate every one of the `C(Z+10, Z)` admissible multiplicity
vectors and take the exact maximum.  That is a strict superset of what the
un-pruned depth-first search would explore, so a zero delta against it settles
the inner prune a fortiori.

Both trades are evaluated on the SAME zone data, so the per-cell delta is
exact rather than a difference of two independently scanned tables.

Outputs `results.json`.  Run:

    python hunts/r_401bbf/probe.py            # full table, both cap modes
    python hunts/r_401bbf/probe.py --quick    # binding cells + controls only

Nothing here is evidence about RH (`docs/08`), and nothing here claims
`k >= 3` or the unequal-depth quantifier.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "hunts" / "frontier_math"))

import k2_closure as K  # noqa: E402  (path set above)

MAX_ATOMS = 10

# ---------------------------------------------------------------------------
# exact trade: no cuts at all
# ---------------------------------------------------------------------------

_COMPOSITIONS: dict[int, np.ndarray] = {}


def compositions(z: int, max_atoms: int = MAX_ATOMS) -> np.ndarray:
    """Every `m` in N^z with `sum(m) <= max_atoms`, as an (N, z) int array."""
    key = (z, max_atoms)
    cached = _COMPOSITIONS.get(key)
    if cached is not None:
        return cached
    rows = [m for m in itertools.product(range(max_atoms + 1), repeat=z)
            if sum(m) <= max_atoms]
    arr = np.asarray(rows, dtype=np.int64)
    _COMPOSITIONS[key] = arr
    return arr


def _qmat(zpos) -> np.ndarray:
    """The pair-charge matrix, built exactly as `k2_closure.zone_trade` does."""
    z = len(zpos)
    q = np.zeros((z, z))
    for a in range(z):
        for b in range(z):
            dmax = max(abs(zpos[a][1] - zpos[b][0]),
                       abs(zpos[b][1] - zpos[a][0]))
            q[a][b] = float(K._kpair(np.array([min(dmax, 6.0)]))[0]) / 200
    return q


def exhaustive_trade(zcaps, zpos, max_atoms: int = MAX_ATOMS) -> float:
    """Exact max of V(m) over all admissible m -- enumeration, no cuts.

    Same objective and same charge matrix as `k2_closure.zone_trade`; the only
    difference is that nothing is pruned.
    """
    z = len(zcaps)
    if z == 0:
        return 0.0
    q = _qmat(zpos)
    caps = np.asarray(zcaps, dtype=float)
    m = compositions(z, max_atoms).astype(float)
    # V(m) = (caps + diag(q)) . m  -  m^T q m
    lin = m @ (caps + np.diag(q))
    quad = ((m @ q) * m).sum(axis=1)
    return float(np.max(lin - quad))


# ---------------------------------------------------------------------------
# the table, both trades on identical zone data
# ---------------------------------------------------------------------------

def zone_data(ta: float, tb: float, xstep: float = 0.01,
              zone_w: float = 0.25, signed: bool = True):
    """The (zcaps, zpos) of every near component -- `near_deficit`'s geometry."""
    regs = []
    for (a, b) in K.I_WINDOWS:
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
    taus = (ta, 0.5 * (ta + tb), tb)
    out = []
    for lo, hi in merged:
        nz = max(1, int(math.ceil((hi - lo) / zone_w)))
        edges = np.linspace(lo, hi, nz + 1)
        zcaps, zpos = [], []
        for zi in range(nz):
            xs = np.arange(edges[zi], edges[zi + 1] + xstep, xstep)
            sup = 0.0
            for t in taus:
                if signed:
                    f = np.maximum(0.0, K._D(0.5, xs) + K._D(0.5, xs - t)) / 0.25
                else:
                    f = (K._dam(0.5, xs) + K._dam(0.5, xs - t)) / 0.25
                sup = max(sup, float(f.max()))
            if sup > 1e-9:
                zcaps.append(K.INFL * sup)
                zpos.append((edges[zi], edges[zi + 1]))
        out.append((zcaps, zpos))
    return out


def cell_pair(ta: float, tb: float, signed: bool = True):
    """(margin_pruned, margin_exact, near_pruned, near_exact, max_zones).

    The published cell, and the same cell with the trade solved exhaustively.
    Everything outside the trade -- far rows, `C1`, the budget floor -- is
    identical by construction, so the margin delta equals the near delta.
    """
    near_p = near_e = 0.0
    zmax = 0
    for zcaps, zpos in zone_data(ta, tb, signed=signed):
        near_p += K.zone_trade(zcaps, zpos)
        near_e += exhaustive_trade(zcaps, zpos)
        zmax = max(zmax, len(zcaps))
    ts = np.linspace(ta, tb, 7)
    kp = float(np.min(K._kpair(ts)))
    c1 = 0.0
    for y in K._YGRID:
        c1 = max(c1, float(np.max(K._dam(2 * y, ts))) / y ** 2)
    rest = K.far_total(ta) + c1
    budget = K.BUDGET0 + 4 * kp
    return (budget - (near_p + rest), budget - (near_e + rest),
            near_p, near_e, zmax)


def run_mode(signed: bool, tau_lo: float = 0.0, tau_hi: float = 132.0,
             step: float = 0.02, progress: bool = True) -> dict:
    """Every cell of one cap mode.  Returns the full per-cell record."""
    t0 = time.time()
    taus, mp, me, dl = [], [], [], []
    zmax = 0
    a = tau_lo
    n = int(round((tau_hi - tau_lo) / step))
    for i in range(n):
        b = a + step
        m_p, m_e, np_, ne_, zc = cell_pair(a, b, signed=signed)
        taus.append(round(a, 6))
        mp.append(m_p)
        me.append(m_e)
        dl.append(ne_ - np_)
        zmax = max(zmax, zc)
        if progress and (i + 1) % 500 == 0:
            print(f"  [{'signed' if signed else 'unsigned'}] "
                  f"{i + 1}/{n} cells, {time.time() - t0:.0f}s, "
                  f"max delta so far {max(dl):.3e}", flush=True)
        a = b
    mp_a, me_a, dl_a = np.array(mp), np.array(me), np.array(dl)
    i_p, i_e, i_d = int(mp_a.argmin()), int(me_a.argmin()), int(dl_a.argmax())
    return {
        "mode": "signed" if signed else "unsigned",
        "cells": len(taus),
        "tau_lo": tau_lo, "tau_hi": tau_hi, "step": step,
        "max_zones_in_any_component": zmax,
        "cells_with_nonzero_delta": int((dl_a != 0.0).sum()),
        "max_abs_delta": float(np.abs(dl_a).max()),
        "max_delta": float(dl_a.max()),
        "min_delta": float(dl_a.min()),
        "delta_argmax_tau": taus[i_d],
        "worst_margin_pruned": float(mp_a[i_p]),
        "worst_margin_pruned_tau": taus[i_p] + 0.5 * step,
        "worst_margin_exact": float(me_a[i_e]),
        "worst_margin_exact_tau": taus[i_e] + 0.5 * step,
        "nonpositive_cells_pruned": int((mp_a <= 0).sum()),
        "nonpositive_cells_exact": int((me_a <= 0).sum()),
        "seconds": time.time() - t0,
        "cells_above_1e_15": int((np.abs(dl_a) > 1e-15).sum()),
        "cells_above_1e_12": int((np.abs(dl_a) > 1e-12).sum()),
        "cells_delta_exactly_zero": int((dl_a == 0.0).sum()),
        "cells_delta_positive": int((dl_a > 0).sum()),
        "cells_delta_negative": int((dl_a < 0).sum()),
        "delta_sign_note": ("a genuine prune bite can only be positive; "
                            "negative entries are float summation order"),
        "cells_above_1e_15_detail": [
            {"tau_lo": taus[j], "delta": float(dl_a[j]),
             "margin_pruned": float(mp_a[j]), "margin_exact": float(me_a[j])}
            for j in np.flatnonzero(np.abs(dl_a) > 1e-15)[:200].tolist()
        ],
        # every cell, compactly: margins to 1e-12 (the margins live at 1e-2),
        # deltas as exact integer multiples of 1e-18 (they live at 1e-16).
        "per_cell": {
            "tau_lo": taus,
            "margin_pruned_round12": [round(float(x), 12) for x in mp_a],
            "delta_units_1e_18": [int(round(float(x) * 1e18)) for x in dl_a],
        },
    }


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------

def control_agreement() -> dict:
    """The two solvers must agree on random instances of the same SHAPE as the
    table's components, and the exhaustive one must never come out lower."""
    rng = np.random.default_rng(20260817)
    worst = 0.0
    lower = 0
    for _ in range(400):
        z = int(rng.integers(1, 8))
        lo = float(rng.uniform(-30, 30))
        edges = lo + 0.25 * np.arange(z + 1)
        zpos = [(float(edges[i]), float(edges[i + 1])) for i in range(z)]
        zcaps = [float(x) for x in rng.uniform(0.0, 0.12, size=z)]
        p = K.zone_trade(zcaps, zpos)
        e = exhaustive_trade(zcaps, zpos)
        worst = max(worst, e - p)
        lower += int(e < p - 1e-12)
    return {"instances": 400, "max_exact_minus_pruned": worst,
            "instances_where_exact_lower": lower}


def _dfs_trade(caps, q, prune: bool, outer: bool = True,
               max_atoms: int = MAX_ATOMS) -> float:
    """`k2_closure.zone_trade`'s search, transcribed with the charge matrix as
    an argument and the inner prune switchable.  Used only by the controls;
    `control_transcription` pins it against the real thing."""
    caps = list(caps)
    q = np.asarray(q, dtype=float)
    if not caps:
        return 0.0
    order = np.argsort(-np.asarray(caps))
    caps = [caps[i] for i in order]
    q = q[np.ix_(order, order)]
    best = 0.0

    def dfs(idx, ms, val, rem):
        nonlocal best
        if val > best:
            best = val
        if idx >= len(caps) or rem == 0:
            return
        if outer and val + rem * caps[idx] <= best:
            return
        for m in range(rem, -1, -1):
            v = val + caps[idx] * m - q[idx][idx] * m * (m - 1)
            for j, mj in enumerate(ms):
                v -= 2 * q[j][idx] * mj * m
            if (not prune) or v > val - 1e-18 or m == 0:
                dfs(idx + 1, ms + [m], v, rem - m)

    dfs(0, [], 0.0, max_atoms)
    return best


def _exhaustive_q(caps, q, max_atoms: int = MAX_ATOMS) -> float:
    """Exact max of V(m) for an explicit charge matrix."""
    z = len(caps)
    if z == 0:
        return 0.0
    q = np.asarray(q, dtype=float)
    m = compositions(z, max_atoms).astype(float)
    lin = m @ (np.asarray(caps, dtype=float) + np.diag(q))
    return float(np.max(lin - ((m @ q) * m).sum(axis=1)))


def control_transcription() -> dict:
    """`_dfs_trade(..., prune=True)` must equal `k2_closure.zone_trade` on
    real component shapes, or the planted control below tests a strawman."""
    rng = np.random.default_rng(4242)
    worst = 0.0
    for _ in range(200):
        z = int(rng.integers(1, 8))
        lo = float(rng.uniform(-30, 30))
        edges = lo + 0.25 * np.arange(z + 1)
        zpos = [(float(edges[i]), float(edges[i + 1])) for i in range(z)]
        zcaps = [float(x) for x in rng.uniform(0.0, 0.12, size=z)]
        worst = max(worst, abs(_dfs_trade(zcaps, _qmat(zpos), True)
                               - K.zone_trade(zcaps, zpos)))
    return {"instances": 200, "max_abs_difference": worst}


def control_planted_bite() -> dict:
    """DETECTOR POWER, and the hypothesis the soundness argument needs.

    The prune is sound whenever every pair charge is NONNEGATIVE (see
    RESULTS.md section 2): a multiplicity that does not improve the running
    value can only subtract more later, so the `m = 0` branch, which is always
    taken, dominates it.  Break exactly that hypothesis -- one negative
    off-diagonal charge, i.e. an attractive pair instead of a repulsive one --
    and the prune bites at once.  A probe that cannot see this planted bite
    would make a zero delta on the table meaningless.

    The table's own charges are `Kpair/200 = Re(ghat)^2/200 >= 0`, so this
    instance is outside its geometry by construction; that is the point.
    """
    caps = [0.02, 0.010, 0.010]
    q = np.array([[0.004, -0.004, -0.004],
                  [-0.004, 0.004, 0.001],
                  [-0.004, 0.001, 0.004]])
    p = _dfs_trade(caps, q, prune=True)
    u = _dfs_trade(caps, q, prune=False)
    p_no_outer = _dfs_trade(caps, q, prune=True, outer=False)
    u_no_outer = _dfs_trade(caps, q, prune=False, outer=False)
    e = _exhaustive_q(caps, q)
    return {"caps": caps, "q": q.tolist(),
            "both_cuts": p, "inner_prune_off": u,
            "outer_bound_off": p_no_outer, "both_off": u_no_outer,
            "exhaustive": e, "delta_bothcuts_vs_exhaustive": e - p,
            "delta_innerpruneoff_vs_exhaustive": e - u,
            "prune_bites": bool(e - p_no_outer < e - p - 1e-12
                                or e > p + 1e-12),
            "both_off_equals_exhaustive": bool(abs(u_no_outer - e) < 1e-12)}


def control_sign_of_charges() -> dict:
    """The hypothesis, checked on the table itself: is every pair charge that
    the table ever builds nonnegative, and is the clamp inside `Kpair`'s first
    root?  Scanned over the same components the table uses."""
    qmin = math.inf
    dmax_seen = 0.0
    for signed in (True, False):
        ta = 0.0
        while ta < 132.0 - 1e-12:
            for zcaps, zpos in zone_data(ta, ta + 0.02, signed=signed):
                if not zpos:
                    continue
                q = _qmat(zpos)
                qmin = min(qmin, float(q.min()))
                dmax_seen = max(dmax_seen, zpos[-1][1] - zpos[0][0])
            ta += 2.0  # coarse sweep: component geometry varies slowly
    return {"min_pair_charge_seen": qmin, "widest_component_seen": dmax_seen,
            "all_charges_nonnegative": bool(qmin >= 0.0)}


BINDING = (6.32, 6.30, 12.84, 63.40, 126.04, 0.0)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="binding cells and controls only")
    ap.add_argument("--charges", action="store_true",
                    help="also sweep the sign of every pair charge the table builds")
    ap.add_argument("--out", default=str(Path(__file__).resolve().parent
                                         / "results.json"))
    args = ap.parse_args()

    t0 = time.time()
    rec: dict = {"run_id": "2b9b08aa-5deb-4013-a5d0-c84d1d5faf26",
                 "max_atoms": MAX_ATOMS}

    rec["control_agreement"] = control_agreement()
    rec["control_transcription"] = control_transcription()
    rec["control_planted_bite"] = control_planted_bite()
    print("= control: solver agreement on random components =")
    print("  ", rec["control_agreement"])
    print("= control: DFS transcription pinned against zone_trade =")
    print("  ", rec["control_transcription"])
    print("= control: planted bite (one negative pair charge) =")
    pb = rec["control_planted_bite"]
    print(f"   both cuts {pb['both_cuts']:.6f} | inner off "
          f"{pb['inner_prune_off']:.6f} | outer off {pb['outer_bound_off']:.6f}"
          f" | both off {pb['both_off']:.6f} | exhaustive "
          f"{pb['exhaustive']:.6f}  bites={pb['prune_bites']}")
    if args.charges:
        rec["control_sign_of_charges"] = control_sign_of_charges()
        print("= control: sign of every pair charge the table builds =")
        print("  ", rec["control_sign_of_charges"])

    if args.quick:
        rec["binding_cells"] = []
        for ta in BINDING:
            for signed in (True, False):
                m_p, m_e, np_, ne_, zc = cell_pair(ta, ta + 0.02, signed=signed)
                row = {"tau_lo": ta, "mode": "signed" if signed else "unsigned",
                       "margin_pruned": m_p, "margin_exact": m_e,
                       "near_pruned": np_, "near_exact": ne_,
                       "delta": ne_ - np_, "max_zones": zc}
                rec["binding_cells"].append(row)
                print(f"  tau={ta:6.2f} {row['mode']:>8}: "
                      f"margin {m_p:+.7f} -> {m_e:+.7f}  delta {ne_ - np_:.3e}")
    else:
        rec["modes"] = [run_mode(signed) for signed in (True, False)]
        for m in rec["modes"]:
            print(f"= full table ({m['mode']}) =")
            print(f"  cells {m['cells']}, max |delta| {m['max_abs_delta']:.3e}, "
                  f"cells with nonzero delta {m['cells_with_nonzero_delta']}")
            print(f"  worst margin pruned {m['worst_margin_pruned']:+.7f} "
                  f"@ tau {m['worst_margin_pruned_tau']:.3f}; "
                  f"exact {m['worst_margin_exact']:+.7f} "
                  f"@ tau {m['worst_margin_exact_tau']:.3f}")
            print(f"  nonpositive cells: pruned "
                  f"{m['nonpositive_cells_pruned']}, exact "
                  f"{m['nonpositive_cells_exact']}  ({m['seconds']:.0f}s)")

    rec["total_seconds"] = time.time() - t0
    Path(args.out).write_text(json.dumps(rec, indent=1))
    print(f"wrote {args.out}  ({rec['total_seconds']:.0f}s)")


if __name__ == "__main__":
    main()
