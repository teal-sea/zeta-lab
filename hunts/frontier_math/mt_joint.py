"""The joint cap at the MT window, on the band partition, theta_full's object.

The band-lattice dual (`band_dual.py`) secured theta* = 0.995 for ONE
off-line pair against an arbitrary on-line configuration.  The composed
reading needs theta_full: the same statement with ALL pairs present at
once, where the pairs' own interaction T_signed enters the budget and
their damage fields add.  This module is that object, and it is the
level-7 "direct route" rebuilt on the band partition instead of a ruler.

THE INEQUALITY.  For pairs {(t_r, y_r)} and any finite on-line X,

    sum_r slack_r + T_signed + X_cross + (1 - theta) R(X)  >=  0,

i.e.  J(pairs) := sup_X [ -X_cross - (1-theta) R(X) ]  <=  budget, with
budget = sum_r slack_r + T_signed(pairs) computed exactly (LAW K + LAW L)
and the joint damage field

    f(g) = - sum_r 2 W(g - t_r, y_r).

WHAT CARRIES OVER FROM THE SINGLE-PAIR DUAL, unchanged:

- **the positive part is taken of the JOINT field**, never per pair.
  Per-pair clipping discards the coincident-pair shielding, one pair's
  positive hump covering a neighbour's band, and was measured at the
  other window to inflate the field tenfold.  Here the shielding is
  stronger still, because the MT stacking floor is ~0.98 mean gaps.
- **cross-cell charges are dropped**: omega^2 is a square, so this is
  one-sided, and it is what makes the arithmetic band/zero near-coincidence
  irrelevant.
- **the partition is shown complete, not assumed**: bands are exactly
  where Q(g) := sum_r Re(Phi2(g - t_r + i y_r)^2) < 0, and an unresolved
  band would need an interior dip of Q, excluded wherever
  Q > (1/8) |Q''| step^2 off the widened bands, with
  |Q''| <= 2 sum_r (|Phi2_r'|^2 + |Phi2_r| |Phi2_r''|), all local.

WHAT IS NEW.  With many pairs the bands merge and widen, so a single
same-band repulsion floor is no longer safe (a band wider than omega's
first zero at 6.64 grid units would give K = 0 and an infinite cap).
Each band is therefore sub-partitioned into cells of width delta from a
ladder, with the level-4 square completion per cell against K(delta), and
cross-cell charges dropped.  Cells exist only inside bands, so their
number is proportional to the band measure and not to the length of the
line, which is exactly the discipline whose absence produced the
blanket-margin artifact three times in this hunt.

Nothing here computes a proportion.  Run
``.venv/bin/python hunts/frontier_math/mt_joint.py`` (~15 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from band_dual import phi2mt_d1, phi2mt_d2  # noqa: E402
from mt_chain import A, MEAN_GAP, MTChain, phi2mt  # noqa: E402


@dataclass(frozen=True)
class MTJoint:
    mt: MTChain = MTChain()
    #: fine step, grid units (band widths are ~1, so this resolves them
    #: with ~500 points; the no-missed-band test reports the true margin)
    step: float = 0.002
    #: resolved half-range beyond the outermost pair; closed-form tail after
    G: float = 200.0
    #: sub-cell width ladder inside bands (grid units)
    delta_choices: tuple = (0.5, 1.0, 2.0, 3.0)

    # -- the joint field and its local derivative magnitudes -----------------

    def field(self, pairs, lo: float, hi: float):
        gs = np.arange(lo, hi, self.step)
        f = np.zeros_like(gs)
        Q = np.zeros_like(gs)
        qpp = np.zeros_like(gs)
        slope = np.zeros_like(gs)
        for t, y in pairs:
            z = (gs - t) + 1j * y
            v = phi2mt(z)
            v1 = phi2mt_d1(z)
            v2 = phi2mt_d2(z)
            re2 = v.real**2 - v.imag**2
            Q += re2
            f += -4 * re2 / A**2
            av, a1, a2 = np.abs(v), np.abs(v1), np.abs(v2)
            slope += 8 * av * a1 / A**2
            qpp += 2 * (a1**2 + av * a2)
        return gs, f, Q, qpp, slope

    def _window(self, pairs):
        ts = [t for t, _ in pairs]
        return min(ts) - self.G, max(ts) + self.G

    # -- bands, completeness, cells ------------------------------------------

    def bands(self, pairs):
        """[(lo, hi, F_up)] over the resolved window; membership on the raw
        grid, F carrying only the LOCAL slope margin."""
        return self._bands_cached(tuple(map(tuple, pairs)))

    @lru_cache(maxsize=32)
    def _bands_cached(self, pairs):
        lo, hi = self._window(pairs)
        gs, f, Q, qpp, slope = self.field(pairs, lo, hi)
        idx = np.where(f > 0)[0]
        if len(idx) == 0:
            return []
        groups = np.split(idx, np.where(np.diff(idx) > 1)[0] + 1)
        out = []
        for gr in groups:
            if len(gr) < 2:
                continue
            out.append((float(gs[gr[0]]) - self.step,
                        float(gs[gr[-1]]) + self.step,
                        float(f[gr].max()) + float(slope[gr].max()) * self.step))
        return tuple(out)

    def no_missed_band(self, pairs) -> dict:
        lo, hi = self._window(pairs)
        gs, f, Q, qpp, slope = self.field(pairs, lo, hi)
        on = f > 0
        wide = on.copy()
        wide[1:] |= on[:-1]
        wide[:-1] |= on[1:]
        off = ~wide
        if not np.any(off):
            return {"worst_ratio": math.inf, "clear": True}
        bound = qpp[off] * self.step**2 / 8
        ratio = float(np.min(Q[off] / bound))
        return {"worst_ratio": ratio, "clear": ratio > 1.0}

    def band_cells(self, pairs, delta: float):
        """Sub-partition every band into cells of width <= delta.

        Returns [(F_up, width)] per cell; a cell's F is the band's F
        (one-sided: the band maximum majorises every sub-cell).
        """
        cells = []
        for lo, hi, F in self.bands(pairs):
            n = max(1, int(math.ceil((hi - lo) / delta)))
            w = (hi - lo) / n
            cells.extend([(F, w)] * n)
        return cells

    @lru_cache(maxsize=256)
    def K_of(self, width: float) -> float:
        rs = np.arange(0.0, width + self.step, self.step)
        lo = float(np.min(phi2mt(rs.astype(complex)).real / A))
        lo -= (self.mt.L1 / A) * self.step
        return max(0.0, lo) ** 2

    # -- the tail --------------------------------------------------------------

    def tail(self, pairs) -> float:
        """Closed-form majorant of the band damage beyond the window.

        Per pair, F <= 4 (c_im(y)/(A g))^2 with bands at least P apart, so
        each pair contributes 4(c/A)^2 [1/G^2 + 1/(P G)] per side.
        """
        from band_dual import BandDual
        bd = BandDual()
        total = 0.0
        for _, y in pairs:
            C = bd.c_im_sharp(y) / A
            total += 2 * 4 * C * C * (1 / self.G**2 + 1 / (MEAN_GAP * self.G))
        return total

    # -- the cap ---------------------------------------------------------------

    def cap(self, pairs, theta: float) -> dict:
        c = 1 - theta
        if c <= 0:
            return {"cap": math.inf, "delta": None, "cells": None}
        best = (math.inf, None, None)
        for delta in self.delta_choices:
            cells = self.band_cells(pairs, delta)
            if not cells:
                return {"cap": 0.0, "delta": delta, "cells": 0}
            total = 0.0
            ok = True
            for F, w in cells:
                K = self.K_of(w)
                if K <= 0:
                    ok = False
                    break
                total += (F if F <= 2 * c * K
                          else (F + c * K) ** 2 / (4 * c * K))
            if ok and total < best[0]:
                best = (total, delta, len(cells))
        if not math.isfinite(best[0]):
            return {"cap": math.inf, "delta": None, "cells": None}
        return {"cap": best[0] + self.tail(pairs), "delta": best[1],
                "cells": best[2]}

    def verdict(self, pairs, theta: float) -> dict:
        b = self.mt.budget(pairs)
        rec = self.cap(pairs, theta)
        return {"budget": b, "cap": rec["cap"], "margin": b - rec["cap"],
                "closes": b - rec["cap"] >= 0, "delta": rec["delta"],
                "cells": rec["cells"]}

    def theta_full_scan(self, configs,
                        thetas=(0.9, 0.99, 0.995, 0.999)):
        """Largest grid theta closing every configuration."""
        margins = {}
        star = None
        for theta in thetas:
            worst, arg = math.inf, None
            for name, pairs in configs:
                rec = self.verdict(pairs, theta)
                rel = rec["margin"] / max(rec["budget"], 1e-12)
                if rel < worst:
                    worst, arg = rel, name
            margins[theta] = (worst, arg)
            if worst >= 0:
                star = theta
        return star, margins


# ---------------------------------------------------------------------------
# configurations, including the pair layer's own soft window
# ---------------------------------------------------------------------------


def sweep_configs(span_gaps: float = 8.0):
    # the genuinely worst pair configurations are the SPARSE ones: with
    # no neighbour to shield it, an isolated pair keeps its full band
    # structure, and the joint layer degenerates to the single-pair dual.
    # (At the other window the ordering was the opposite - density was the
    # danger there - so these rows are what makes the comparison honest.)
    yield ("isolated single pair y=0.49", [(0.0, 0.49)])
    yield ("isolated single pair y=0.3", [(0.0, 0.3)])
    yield ("two pairs far apart y=0.49",
           [(0.0, 0.49), (40 * MEAN_GAP, 0.49)])
    yield ("two pairs at worst dipole y=0.49",
           [(0.0, 0.49), (6.778, 0.49)])
    for nu_p in (0.25, 0.5, 0.97, 1.25, 2.0, 3.0):
        spacing = MEAN_GAP / nu_p
        for y in (0.3, 0.49):
            n = max(2, int(span_gaps * nu_p))
            yield (f"lattice nu={nu_p} y={y}",
                   [(k * spacing, y) for k in range(n)])
    spacing = MEAN_GAP / 1.5
    n = int(span_gaps * 1.5)
    yield ("alternating nu=1.5",
           [(k * spacing, 0.45 if k % 2 else 0.15) for k in range(n)])
    yield ("shallow sandwich nu=1.5",
           [(k * spacing, 0.02) for k in range(n)]
           + [(k * spacing, 0.49) for k in range(n)])
    yield ("staggered nu=1.5",
           [(k * spacing, 0.3) for k in range(n)]
           + [(k * spacing + spacing / 2, 0.4) for k in range(n)])


def joint_greedy(mj: MTJoint, pairs, theta: float, kmax: int = 40) -> float:
    """Measured joint adversary: the projection control the cap must
    dominate (a lower bound on the true supremum)."""
    lo, hi = min(t for t, _ in pairs) - 2 * MEAN_GAP, \
        max(t for t, _ in pairs) + 2 * MEAN_GAP
    sites = np.arange(lo, hi, 0.05)
    dmg = np.zeros_like(sites)
    for t, y in pairs:
        dmg += -2 * mj.mt.W(sites - t, y)
    c = 1 - theta
    chosen: list[float] = []
    profit = 0.0
    for _ in range(kmax):
        gain, pick = 0.0, None
        for i, x in enumerate(sites):
            if any(abs(x - p) < 0.5 for p in chosen):
                continue
            internal = 2 * c * sum(float(mj.mt.omega2(x - p)) for p in chosen)
            g = dmg[i] - internal
            if g > gain:
                gain, pick = g, float(x)
        if pick is None:
            break
        chosen.append(pick)
        profit += gain
    return profit


def audit():
    mj = MTJoint()
    configs = list(sweep_configs())
    print("= partition completeness on the joint field =")
    for name, pairs in configs[:4]:
        r = mj.no_missed_band(pairs)
        print(f"  {name:26s}: worst Q / curvature bound = "
              f"{r['worst_ratio']:.0f}   clear={r['clear']}")
    print("= the joint verdict across the sweep =")
    for theta in (0.9, 0.99):
        print(f"  -- theta = {theta} --")
        for name, pairs in configs:
            rec = mj.verdict(pairs, theta)
            print(f"  {name:26s} pairs {len(pairs):3d}  budget "
                  f"{rec['budget']:9.4f}  cap {rec['cap']:8.4f}  margin "
                  f"{rec['margin']:+9.4f}  "
                  f"{'closes' if rec['closes'] else 'OPEN'}  "
                  f"(delta {rec['delta']}, {rec['cells']} cells)")
    print("= theta_full scan =")
    star, margins = mj.theta_full_scan(configs)
    for th, (m, arg) in margins.items():
        print(f"  theta={th}: worst relative margin {m:+.4f} at {arg}  "
              f"{'ok' if m >= 0 else 'FAILS'}")
    print(f"  theta_full at MT (grid) = {star}   "
          "(hunt window: 0.02)")
    print("= projection control: the cap dominates the joint greedy =")
    for name, pairs in configs[:4]:
        g = joint_greedy(mj, pairs, 0.9)
        cap = mj.cap(pairs, 0.9)["cap"]
        print(f"  {name:26s}: greedy {g:8.4f} <= cap {cap:8.4f}: "
              f"{g <= cap + 1e-9}")


if __name__ == "__main__":
    audit()
