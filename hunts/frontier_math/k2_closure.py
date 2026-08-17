"""The k = 2 case of blocker 2 closes at measured grade: a tau-table.

Statement closed here (equal depths; the two-species form of
`two_species.py`, sufficient for `slack_2 >= 0` because `D <= Dam` and
dropped credits are nonnegative):

  (Q**, k=2)  for all atoms X, centre gap tau, y in (0, 1/2]:
      4*sum_a [Dam(y,x_a) + Dam(y,x_a-tau)] + 4*Dam(2y,tau)
        <= 4*Shq(y) + 4*Kpair(tau) + (1/200)*sum_{a!=b} Kpair(x_ab)

## The accounting, per tau-cell (width 0.02 on [0, 132])

* NEAR: connected components of the union of the 36 signed windows of the
  two centres (official `I_k` endpoints, swept over the cell).  Each
  component is cut into zones of width <= 0.25; a zone's cap is

      cap = 1.05 * sup_{x in zone, tau in cell} 4*max(0, D(.5,x) + D(.5,x-tau))

  — the POSITIVE PART OF THE SIGNED TOTAL FIELD.  This is the step that
  beats the difference-resonance: at `tau ~ 2*pi` an atom in `I_0` of one
  centre sits in the near zone of the other, where the signed field is
  `~ -0.85`, and the zone contributes nothing.  Zone pair charges are
  `Kpair(max distance)/200`, monotone on [0, 2*pi]; the trade is an EXACT
  branch-and-bound over integer multiplicities (sum m <= 10).
* FAR (|x| > 60 from own centre, outside all windows): per-centre rows
  `P(2*Wt_i, 1/25000)` on the outer side (the other centre is farther, so
  its far tail is bounded by the same row constant), `P(Wt_i, 1/25000)`
  on the inner side only when `tau > 60 + 28/5`, plus the section-7
  closed-form tails.
* CENTRE-CENTRE: `C1(tau) = sup_{y<=1/2} Dam(2y,tau)/y^2`, cell-sup.
* BUDGET: the kernel-checked O8 floor `2*(51944/100000)*(1/4)` plus
  `4*min_cell Kpair`.

## Result (scan grade)

  0 of 6601 cells nonpositive on [0, 132].
  worst cell: tau ~ 12.85, margin +0.0529  (signed-field caps)
  worst cell with UNSIGNED caps (independent, more conservative pass):
  tau ~ 6.33, margin +0.0033 — same verdict, no negative cells.

* tau > 114.2: no window of one centre can overlap a window of the other
  (they end at 57.07), so NEAR = 2x the k=1 rows = 0.1628, C1 <= 2.1e-4,
  FAR <= 0.0154: margin >= 0.2597 - 0.1786 = +0.081.  Closed form.
* every deficit piece is convex in v = y^2 and vanishes at v = 0 (the
  signed caps are [a*v - b]^+ with b = Kpair >= 0); the budget floor is
  linear with a v-free nonnegative Kpair term.  Closure at v = 1/4 gives
  every y in (0, 1/2] — the same section-6 argument as the k=1 proof.

## Grade and controls

MEASURED here; the same table re-run under ball-arithmetic enclosures in
`hunts/r_a97060/probe.py` (2026-08-17) closes with 0 nonpositive cells in
all three cap modes, worst margins +0.0677 signed / +0.0146 unsigned /
+0.0016 unsigned with this module's own 1.05 pad kept on top.  That makes
the TABLE enclosure-carrying; the composite k=2 claim still takes its grade
from the v-convexity transfer (G3), which that pass did not touch.

Sups in THIS module are scans (x-step 0.01, 3 tau-samples per cell, stable
under x-step 0.005 / cell 0.01 / zones 0.15: worst resonance margin moves
+0.0033 -> +0.0039).  Controls: (C2) the accounting dominates the greedy
adversary pointwise in tau; (C3) the adversary-side planted-damage ladder
first fires between 1.5x and 1.7x, consistent with the measured relative
margin; (C4) inflating the machine's own caps kills the v3 table at
1.02x, consistent with its worst margin; (R) the module reproduces the
k=1 section-7 window arithmetic to all printed digits (8.1383160e-2).

What this does NOT close: k >= 3 (see K2-TWO-SPECIES.md section 5), the
unequal-depth quantifier (measured >= 0 on a 9x9 depth grid at the
binding taus; the convex-majorant route to it is written down and its gap
named), and hardening (the interval pass over the same finitely many
cells, exactly the O9-table technology).  Nothing here is evidence about
RH.

Run ``python3 hunts/frontier_math/k2_closure.py`` (~8 min full table;
``--quick`` spot-checks the binding cells, ~30 s).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))

SQ2 = math.sqrt(2.0)

__all__ = [
    "P", "zone_trade", "far_total", "near_deficit", "cell_eval", "run",
    "reproduce_k1_section7", "planted_cap_fault", "TABLE_RECORD",
    "NAMED_GAPS",
]

# official O9 window table (RETENTION-PROBLEM.md section 4)
I_WINDOWS = [
    (60653 / 10000, 35257 / 5000), (61171 / 5000, 131999 / 10000),
    (11544 / 625, 48583 / 2500), (247289 / 10000, 256909 / 10000),
    (309971 / 10000, 159793 / 5000), (372701 / 10000, 76463 / 2000),
    (21773 / 500, 27817 / 625), (498237 / 10000, 507849 / 10000),
    (280513 / 5000, 570637 / 10000),
]
O9_CAPS = [
    9232503 / 500000000, 8190483 / 2000000000, 3555573 / 2000000000,
    396669 / 400000000, 126441 / 200000000, 219051 / 500000000,
    128583 / 400000000, 24591 / 100000000, 194187 / 1000000000,
]
Q_FAR = 1 / 25000
BUDGET0 = 2 * (51944 / 100000) * 0.25
INFL = 1.05


def _ghat(re, im):
    z = re + 1j * np.asarray(im, dtype=complex)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return np.sinh(zp / 2) / zp + np.sinh(zm / 2) / zm


def _D(y, s):
    g = _ghat(y, s)
    return -np.real(g * g)


def _dam(y, s):
    return np.maximum(0.0, _D(y, s))


def _kpair(u):
    return np.real(_ghat(0.0, u)) ** 2


def P(cap: float, q: float) -> float:
    """Integer trade: `max_m cap*m - q*m*(m-1)` (Lemma 5.1 of the k=1 proof)."""
    if cap <= 0:
        return 0.0
    mstar = 0.5 + cap / (2 * q)
    best = 0.0
    for m in (math.floor(mstar), math.ceil(mstar)):
        if m >= 0:
            best = max(best, cap * m - q * m * (m - 1))
    return best


def zone_trade(zcaps, zpos, max_atoms: int = 10) -> float:
    """Exact max over integer zone multiplicities of caps minus pair charges."""
    Z = len(zcaps)
    if Z == 0:
        return 0.0
    qmat = np.zeros((Z, Z))
    for a in range(Z):
        for b in range(Z):
            dmax = max(abs(zpos[a][1] - zpos[b][0]),
                       abs(zpos[b][1] - zpos[a][0]))
            qmat[a][b] = float(_kpair(np.array([min(dmax, 6.0)]))[0]) / 200
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
            if v > val - 1e-18 or m == 0:
                dfs(idx + 1, ms + [m], v, rem - m)

    dfs(0, [], 0.0, max_atoms)
    return best


def far_total(tau_a: float) -> float:
    """Far-field deficit for the cell (outer 2*Wt rows; inner rows when the
    inner far region exists; section-7 closed-form tails)."""
    tot = 0.0
    inner = tau_a > 60 + 28 / 5
    for i in range(57):
        lo = 60 + 6 * i
        wt = (637 / 1000) / (lo * lo - 2)
        tot += 2 * P(2 * wt, Q_FAR)
        if inner:
            tot += 2 * P(wt, Q_FAR)
    s = 402.0
    base = (637 / 1000) * ((s * s - 2) ** -1 + (1 / 6) * (s - 2) ** -1)
    tot += 2 * (2 * base) + (2 * base if inner else 0.0)
    return tot


def near_deficit(ta: float, tb: float, xstep: float = 0.01,
                 zone_w: float = 0.25, signed: bool = True) -> float:
    """Sum of zone trades over the near clusters of the cell [ta, tb]."""
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
    taus = (ta, 0.5 * (ta + tb), tb)
    tot = 0.0
    for lo, hi in merged:
        nz = max(1, int(math.ceil((hi - lo) / zone_w)))
        edges = np.linspace(lo, hi, nz + 1)
        zcaps, zpos = [], []
        for zi in range(nz):
            xs = np.arange(edges[zi], edges[zi + 1] + xstep, xstep)
            sup = 0.0
            for t in taus:
                if signed:
                    f = np.maximum(0.0, _D(0.5, xs) + _D(0.5, xs - t)) / 0.25
                else:
                    f = (_dam(0.5, xs) + _dam(0.5, xs - t)) / 0.25
                sup = max(sup, float(f.max()))
            if sup > 1e-9:
                zcaps.append(INFL * sup)
                zpos.append((edges[zi], edges[zi + 1]))
        tot += zone_trade(zcaps, zpos)
    return tot


_YGRID = np.concatenate([np.linspace(0.05, 0.45, 9),
                         np.linspace(0.46, 0.5, 9)])


def cell_eval(ta: float, tb: float, signed: bool = True):
    """(margin, near, C1, 4*Kpair) for the tau-cell [ta, tb] at v = 1/4."""
    ts = np.linspace(ta, tb, 7)
    kp = float(np.min(_kpair(ts)))
    c1 = 0.0
    for y in _YGRID:
        c1 = max(c1, float(np.max(_dam(2 * y, ts))) / y ** 2)
    d_near = near_deficit(ta, tb, signed=signed)
    deficit = d_near + far_total(ta) + c1
    budget = BUDGET0 + 4 * kp
    return budget - deficit, d_near, c1, 4 * kp


def run(tau_lo: float = 0.0, tau_hi: float = 132.0, step: float = 0.02,
        signed: bool = True):
    """The table. Returns (worst, rows); worst = (margin, tau, near, c1, kp4)."""
    worst, rows = (1e9, None, None, None, None), []
    a = tau_lo
    while a < tau_hi - 1e-12:
        b = a + step
        m, near, c1, kp4 = cell_eval(a, b, signed=signed)
        rows.append((a, m))
        if m < worst[0]:
            worst = (m, 0.5 * (a + b), near, c1, kp4)
        a = b
    return worst, rows


# -- controls ---------------------------------------------------------------

def reproduce_k1_section7() -> dict:
    """The k=1 window arithmetic, re-derived: must give 8.1383160e-2."""
    windows = 2 * sum(P(c, 39 / 10000) for c in O9_CAPS)
    far = 0.0
    for i in range(57):
        lo = 60 + 6 * i
        far += 2 * P((637 / 1000) / (lo * lo - 2), Q_FAR)
    tail = 2 * (637 / 1000) * ((402.0 ** 2 - 2) ** -1 + (1 / 6) * 400.0 ** -1)
    return {"windows": windows, "published_windows": 8.1383160e-2,
            "far": far, "published_far": 3.6305145e-3,
            "tail": tail, "published_tail": 5.414634e-4}


def planted_cap_fault(fs=(1.0, 1.01, 1.02, 1.05)) -> list:
    """Inflate the (unsigned) machine's caps: the resonance cell must fail
    by ~1.02x, consistent with its own worst margin.  Detector-power control."""
    m, near, c1, kp4 = cell_eval(6.32, 6.34, signed=False)
    deficit = BUDGET0 + kp4 - m
    return [(f, BUDGET0 + kp4 - f * deficit) for f in fs]


TABLE_RECORD = {
    "signed": {"worst_tau": 12.85, "worst_margin": +0.0528969,
               "neg_cells": 0, "cells": 6601},
    "unsigned": {"worst_tau": 6.33, "worst_margin": +0.0032601,
                 "neg_cells": 0, "cells": 6601,
                 "fine_recheck": {"cell": 0.01, "xstep": 0.005,
                                  "zones": 0.15, "worst": +0.0038708}},
    "tail_closed_form": {"from_tau": 114.2, "margin_at_least": +0.081},
    "adversary": {"greedy_worst_tau": 126.06, "greedy_worst_slack": 0.127526,
                  "planted_damage_first_negative": (1.5, 1.7)},
}

NAMED_GAPS = (
    "G1 k=2 EQUAL DEPTHS ONLY.  k >= 3 is open; the unequal-depth "
    "quantifier is measured >= 0 on a 9x9 grid at binding taus, not "
    "proved (the convex-majorant route and its obstruction are in "
    "K2-TWO-SPECIES.md section 4).",
    "G2 every sup IN THIS MODULE is a scan.  The hardening obligation - "
    "the interval pass over the same cells - was discharged for the table "
    "on 2026-08-17 by hunts/r_a97060/probe.py (ball arithmetic, 0 "
    "nonpositive cells, worst +0.0016 with this module\'s 1.05 pad kept); "
    "that pass also records two unstated assumptions here, the Kpair "
    "clamp\'s monotonicity and the zone_trade inner prune.  The "
    "depth-profile domination pads of two_species.NAMED_GAPS G3 apply.",
    "G3 the v-convexity transfer to y < 1/2 leans on the kernel-checked "
    "O8 floor and on caps of the form [a*v-b]^+ with b >= 0; the signed "
    "caps' b = Kpair(near-zone) would need O3-style rational floors in a "
    "hardened pass.",
    "G4 nothing here moves the reading of record; blocker 2 remains open "
    "and nothing here is evidence about RH.",
)


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    rep = reproduce_k1_section7()
    print(f"= control R: k=1 section-7 reproduction =")
    print(f"  windows {rep['windows']:.9f} vs published {rep['published_windows']:.9f}")
    print(f"  far     {rep['far']:.9f} vs published {rep['published_far']:.9f} (ours conservative)")
    print(f"= control C4: planted cap fault (unsigned resonance cell) =")
    for f, m in planted_cap_fault():
        print(f"  f={f:.2f}: margin {m:+.6f}{'  FAILS' if m < 0 else ''}")
    if quick:
        print("= quick spot-check of binding cells =")
        for ta in (6.32, 12.84, 63.40, 126.04):
            m, near, c1, kp4 = cell_eval(ta, ta + 0.02)
            mu, _, _, _ = cell_eval(ta, ta + 0.02, signed=False)
            print(f"  tau=[{ta},{ta+0.02:.2f}]: signed {m:+.6f}   unsigned {mu:+.6f}")
    else:
        for signed in (True, False):
            worst, rows = run(signed=signed)
            m, tau, near, c1, kp4 = worst
            neg = sum(1 for _, mm in rows if mm <= 0)
            lab = "signed" if signed else "unsigned"
            print(f"= full table ({lab} caps) =")
            print(f"  worst cell tau ~ {tau:.3f}  margin {m:+.7f}   "
                  f"negative cells {neg} of {len(rows)}")
