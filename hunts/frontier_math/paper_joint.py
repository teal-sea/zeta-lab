"""The joint cap at the PAPER's field: theta_full for Phi2 = FT(cos box).

paper_chain.py re-ran the single-pair band-lattice dual at the source
paper's incidence field (Phi2 = phihat_mt, mass kernel = the MT kernel g
by construction) and measured theta*_paper = 0.995.  mt_joint.py built
the JOINT layer, all pairs present at once, but at the OLD (T1)
window's field.  This module is the joint layer at the paper's field.

THE INEQUALITY (unchanged from mt_joint).  For pairs {(t_r, y_r)} and
any finite on-line configuration X,

    J(pairs) := sup_X [ -X_cross - (1-theta) R(X) ]  <=  budget,
    budget    = sum_r slack(y_r) + T_signed(pairs)   (LAW K + LAW L),

with the joint damage field f(g) = - sum_r 2 W(g - t_r, y_r) built from
the PAPER kernel (paper_chain.phipap and its closed-form derivatives).

THE FOUR DISCIPLINES, learned the hard way in this hunt's ledger:

- **the positive part is taken of the JOINT field**, max(0, sum), never
  a sum of per-pair positive parts: per-pair clipping discards the
  coincident-pair shielding (one pair's positive hump covering a
  neighbour's band) and was measured to inflate the field tenfold.
- **band membership on the raw grid; slope margins only from the LOCAL
  closed-form derivatives**, never a per-cell Lipschitz blanket summed
  over many cells (the recurring manufactured-damage defect).
- **cross-band internal charges are dropped one-sidedly**: omega^2 is a
  square, >= 0, so dropping it only weakens the defender.
- **at theta = 1 the internal charge vanishes and the cap MUST report
  infinity** (an unbounded multiplicity stack costs nothing).

WHAT DIFFERS FROM mt_joint: the kernel (phipap, not phi2mt), the
constants that flow from it (A = 0.9187..., L1, the Im-majorant
c_im_sharp with edge phi^2(1/2) = cos(sqrt2/2)), the band lattice (the
MT-kernel zeros at 1.0573, 2.0301, ... mean gaps, so the band period
lower bound is measured from this field's own single-pair bands, NOT
assumed to be a mean gap), and the soft-window density nu_p derived
from this field's own first band centre rather than copied from the T1
run's 0.97.

Nothing here computes a proportion and nothing here is evidence about
RH.  Run ``.venv/bin/python hunts/frontier_math/paper_joint.py``.
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    A, MEAN_GAP, PaperBandDual, PaperChain, phipap, phipap_d1, phipap_d2,
)

#: the paper kernel's first real zero in grid units (first zero of
#: Re phipap on the real axis; 1.0573... mean gaps).  A joint band wider
#: than this could put omega's zero inside a single band cell.
FIRST_ZERO_GRID = None  # resolved lazily by first_kernel_zero()


def first_kernel_zero() -> float:
    """First positive zero of Re phipap (grid units), by bisection off a
    coarse sign scan.  This is the paper field's own lattice constant."""
    global FIRST_ZERO_GRID
    if FIRST_ZERO_GRID is not None:
        return FIRST_ZERO_GRID
    gs = np.arange(0.05, 12.0, 0.01)
    v = phipap(gs.astype(complex)).real
    idx = int(np.where(np.diff(np.sign(v)) != 0)[0][0])
    lo, hi = float(gs[idx]), float(gs[idx + 1])
    for _ in range(60):
        mid = (lo + hi) / 2
        if float(phipap(np.array([mid], complex)).real[0]) > 0:
            lo = mid
        else:
            hi = mid
    FIRST_ZERO_GRID = (lo + hi) / 2
    return FIRST_ZERO_GRID


@dataclass(frozen=True)
class PaperJoint:
    """mt_joint.MTJoint transplanted to the paper's incidence field."""

    pc: PaperChain = PaperChain()
    #: fine step, grid units.  Chosen so the joint no-missed-band ratio
    #: clears 100 with room (the bound scales like step off the band
    #: edges); paper_chain's single-pair dual uses 0.0005 over (0, 400].
    step: float = 0.001
    #: resolved half-range beyond the outermost pair; tail after
    G: float = 200.0
    #: sub-cell width ladder inside bands (grid units)
    delta_choices: tuple = (0.5, 1.0, 2.0, 3.0)

    # -- the joint field and its LOCAL derivative magnitudes -----------------

    def field(self, pairs, lo: float, hi: float):
        gs = np.arange(lo, hi, self.step)
        f = np.zeros_like(gs)
        Q = np.zeros_like(gs)
        qpp = np.zeros_like(gs)
        slope = np.zeros_like(gs)
        for t, y in pairs:
            z = (gs - t) + 1j * y
            v = phipap(z)
            v1 = phipap_d1(z)
            v2 = phipap_d2(z)
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
        """[(lo, hi, F_up)] over the resolved window; membership on the
        raw grid, F carrying only the LOCAL slope margin."""
        return self._bands_cached(tuple(map(tuple, pairs)))

    @lru_cache(maxsize=64)
    def _bands_cached(self, pairs):
        lo, hi = self._window(pairs)
        gs, f, Q, qpp, slope = self.field(pairs, lo, hi)
        idx = np.where(f > 0)[0]
        if len(idx) == 0:
            return ()
        groups = np.split(idx, np.where(np.diff(idx) > 1)[0] + 1)
        out = []
        for gr in groups:
            if len(gr) < 2:
                continue
            out.append((float(gs[gr[0]]) - self.step,
                        float(gs[gr[-1]]) + self.step,
                        float(f[gr].max())
                        + float(slope[gr].max()) * self.step))
        return tuple(out)

    def no_missed_band(self, pairs) -> dict:
        """Rule out a band narrower than the grid: off the (widened)
        resolved bands, Q > (1/8) |Q''| step^2 with the LOCAL curvature
        bound |Q''| <= 2 sum_r (|Phi2_r'|^2 + |Phi2_r||Phi2_r''|)."""
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

    def off_band_allowance(self, pairs) -> float:
        """Exactly 0 when completeness clears; otherwise the summed
        curvature allowance (which would be a reportable failure)."""
        if self.no_missed_band(pairs)["clear"]:
            return 0.0
        lo, hi = self._window(pairs)
        gs, f, Q, qpp, slope = self.field(pairs, lo, hi)
        off = f <= 0
        return float(np.sum(qpp[off])) * self.step**2 / 8 * 4 / A**2

    def band_cells(self, pairs, delta: float):
        """Sub-partition every band into cells of width <= delta;
        a cell's F is the band's F (one-sided majorisation)."""
        cells = []
        for lo, hi, F in self.bands(pairs):
            n = max(1, int(math.ceil((hi - lo) / delta)))
            w = (hi - lo) / n
            cells.extend([(F, w)] * n)
        return cells

    @lru_cache(maxsize=256)
    def K_of(self, width: float) -> float:
        """One-sided min of the PAPER omega^2 over [0, width]."""
        rs = np.arange(0.0, width + self.step, self.step)
        lo = float(np.min(phipap(rs.astype(complex)).real / A))
        lo -= (self.pc.L1 / A) * self.step
        return max(0.0, lo) ** 2

    # -- the tail -------------------------------------------------------------

    @lru_cache(maxsize=16)
    def _band_period(self, y: float) -> float:
        """Lower bound on the band period at this field, measured from
        the single-pair band centres (0.98-1.00 mean gaps here; NOT
        assumed to be a mean gap as at the T1 field)."""
        return PaperBandDual().band_period_lower(y)

    def tail(self, pairs) -> float:
        """Closed-form majorant of the band damage beyond the window:
        per pair and per side, F <= 4 (c_im(y)/(A g))^2 with bands at
        least P(y) apart."""
        bd = PaperBandDual()
        total = 0.0
        for _, y in pairs:
            C = bd.c_im_sharp(y) / A
            P = self._band_period(y)
            total += 2 * 4 * C * C * (1 / self.G**2 + 1 / (P * self.G))
        return total

    # -- the cap --------------------------------------------------------------

    def cap(self, pairs, theta: float) -> dict:
        """Joint band-lattice cap: per-cell square completion against
        K(delta), cross-cell charges dropped (one-sided), best delta on
        the ladder, closed-form tail.  theta = 1 => no charge => inf."""
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
        return {"cap": best[0] + self.tail(pairs)
                + self.off_band_allowance(pairs),
                "delta": best[1], "cells": best[2]}

    # -- budget and verdict ---------------------------------------------------

    def budget(self, pairs) -> float:
        """sum_r slack(y_r) + T_signed, exactly (LAW K + LAW L) at the
        paper field."""
        total = sum(self.pc.slack(y) for _, y in pairs)
        for i, (t1, y1) in enumerate(pairs):
            for j in range(i + 1, len(pairs)):
                t2, y2 = pairs[j]
                total += 2 * self.pc.T(t1 - t2, y1, y2)
        return total

    def verdict(self, pairs, theta: float) -> dict:
        b = self.budget(pairs)
        rec = self.cap(pairs, theta)
        return {"budget": b, "cap": rec["cap"], "margin": b - rec["cap"],
                "closes": b - rec["cap"] >= 0, "delta": rec["delta"],
                "cells": rec["cells"]}

    def theta_full_scan(self, configs,
                        thetas=(0.9, 0.99, 0.995, 0.999)):
        """Largest grid theta closing every configuration; also the
        binding configuration per theta (worst relative margin)."""
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
# configuration families, with the soft window derived at THIS field
# ---------------------------------------------------------------------------


@lru_cache(maxsize=8)
def soft_window_nu(y: float = 0.49) -> float:
    """Density putting nearest neighbours on the damage band: the first
    band centre of THIS field's single-pair damage (measured, not the T1
    value 0.97 and not blindly 1/1.0573, the band centre at finite y is
    slightly inside the kernel zero)."""
    pj = PaperJoint()
    bs = pj.bands([(0.0, y)])
    centres = sorted((lo + hi) / 2 for lo, hi, _ in bs if lo > 0)
    return MEAN_GAP / centres[0]


@lru_cache(maxsize=8)
def worst_dipole_sep(y: float = 0.49) -> float:
    """Separation minimising the pair-pair term 2 T(dt, y, y): the
    dipole that eats the most budget at this field."""
    pc = PaperChain()
    dts = np.arange(0.5, 25.0, 0.002)
    vals = [pc.T(float(dt), y, y) for dt in dts]
    return float(dts[int(np.argmin(vals))])


def sweep_configs(span_gaps: float = 8.0):
    """The mt_joint sweep, re-derived at the paper field.  Sparse rows
    keep their full band structure (the joint layer degenerates to the
    single-pair dual there); dense rows probe the shielding; the soft
    window puts neighbours on the band lattice."""
    for y in (0.02, 0.1, 0.3, 0.49):
        yield (f"isolated single pair y={y}", [(0.0, y)])
    yield ("two pairs far apart y=0.49",
           [(0.0, 0.49), (40 * MEAN_GAP, 0.49)])
    d = worst_dipole_sep(0.49)
    yield (f"worst dipole sep={d:.3f} y=0.49",
           [(0.0, 0.49), (d, 0.49)])
    nu_soft = soft_window_nu(0.49)
    for nu_p in (0.25, 0.5, round(nu_soft, 4), 1.25, 2.0, 3.0):
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


def joint_greedy(pj: PaperJoint, pairs, theta: float,
                 kmax: int = 40) -> float:
    """Measured joint adversary (a lower bound on the true supremum);
    the cap must dominate it."""
    lo = min(t for t, _ in pairs) - 2 * MEAN_GAP
    hi = max(t for t, _ in pairs) + 2 * MEAN_GAP
    sites = np.arange(lo, hi, 0.05)
    dmg = np.zeros_like(sites)
    for t, y in pairs:
        dmg += -2 * pj.pc.W(sites - t, y)
    c = 1 - theta
    chosen: list[float] = []
    profit = 0.0
    internal = np.zeros_like(sites)
    blocked = np.zeros(len(sites), dtype=bool)
    for _ in range(kmax):
        gain = np.where(blocked, -np.inf, dmg - 2 * c * internal)
        i = int(np.argmax(gain))
        if gain[i] <= 0.0:
            break
        x = float(sites[i])
        chosen.append(x)
        profit += float(gain[i])
        internal += pj.pc.omega2((sites - x).astype(complex)).real
        blocked |= np.abs(sites - x) < 0.5
    return profit


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit():
    pj = PaperJoint()
    z1 = first_kernel_zero()
    nu_soft = soft_window_nu(0.49)
    print(f"= the paper field, joint layer: A = {A:.10f} =")
    print(f"  first kernel zero: {z1:.4f} grid units = "
          f"{z1 / MEAN_GAP:.4f} mean gaps")
    print(f"  soft-window density nu_p = {nu_soft:.4f} "
          f"(first band centre {MEAN_GAP / nu_soft / MEAN_GAP:.4f} mean "
          f"gaps; T1 value was 0.97)")
    print(f"  worst dipole separation at y=0.49: "
          f"{worst_dipole_sep(0.49):.3f} grid units")
    configs = list(sweep_configs())
    print("= partition completeness on the joint field (want > 100) =")
    stop = False
    for name, pairs in configs[:6]:
        r = pj.no_missed_band(pairs)
        ok = r["clear"] and r["worst_ratio"] > 100
        print(f"  {name:32s}: worst Q / curvature bound = "
              f"{r['worst_ratio']:.0f}   clear={r['clear']}  "
              f"{'ok' if ok else 'FAILS >100'}")
        stop |= not ok
    if stop:
        print("  !! completeness did not clear >100; STOPPING before any "
              "theta claim.")
        return
    print("= band-width control (no merging past the kernel zero) =")
    wmax = 0.0
    for name, pairs in configs:
        bs = pj.bands(pairs)
        if bs:
            wmax = max(wmax, max(hi - lo for lo, hi, _ in bs))
    print(f"  widest joint band anywhere in the sweep: {wmax:.3f} grid "
          f"units vs first kernel zero {z1:.3f}: "
          f"{'ok' if wmax < z1 else 'MERGED - STOP'}")
    if wmax >= z1:
        print("  !! joint bands merged past the kernel zero; the "
              "single-band charge floor is void.  STOPPING.")
        return
    print("= the joint verdict across the sweep =")
    for theta in (0.9, 0.99, 0.995):
        print(f"  -- theta = {theta} --")
        for name, pairs in configs:
            rec = pj.verdict(pairs, theta)
            print(f"  {name:32s} pairs {len(pairs):3d}  budget "
                  f"{rec['budget']:9.4f}  cap {rec['cap']:8.4f}  margin "
                  f"{rec['margin']:+9.4f}  "
                  f"{'closes' if rec['closes'] else 'OPEN'}  "
                  f"(delta {rec['delta']}, {rec['cells']} cells)")
    print("= theta_full scan =")
    star, margins = pj.theta_full_scan(configs)
    for th, (m, arg) in margins.items():
        print(f"  theta={th}: worst relative margin {m:+.4f} at [{arg}]  "
              f"{'ok' if m >= 0 else 'FAILS'}")
    print(f"  theta_full at the paper field (grid) = {star}   "
          "(single-pair paper: 0.995; T1 joint for reference: mt_joint)")
    theta_chk = star if star is not None else 0.9
    print(f"= projection control: cap dominates joint greedy at "
          f"theta = {theta_chk} =")
    for name, pairs in configs[:6]:
        g = joint_greedy(pj, pairs, theta_chk)
        cap = pj.cap(pairs, theta_chk)["cap"]
        print(f"  {name:32s}: greedy {g:8.4f} <= cap {cap:8.4f}: "
              f"{g <= cap + 1e-9}")
    print("= dense-lattice shielding (cap must be exactly 0) =")
    for name, pairs in configs:
        if "nu=3.0" in name:
            rec = pj.cap(pairs, 0.9)
            print(f"  {name:32s}: cap = {rec['cap']}  "
                  f"({'ok' if rec['cap'] == 0.0 else 'NOT SHIELDED'})")
    print("= theta = 1 must diverge (no charge, unbounded stack) =")
    r = pj.cap([(0.0, 0.49)], 1.0)
    print(f"  cap(theta=1) = {r['cap']}  "
          f"(infinite: {not math.isfinite(r['cap'])})")


if __name__ == "__main__":
    audit()
