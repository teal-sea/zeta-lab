"""T1's theorem object: the band-lattice dual at the Montgomery-Taylor window.

WHY THE LEVEL-4 CHAIN DUAL FAILED HERE, PROPERLY DIAGNOSED.  The first T1
session reported the uniform-cell chain DP failing at every theta (cap
0.44 vs slack 0.14) and blamed the interval charge floors straddling the
kernel zeros.  That diagnosis was half right and the number was mostly an
artifact: a uniform delta-cell partition of a +-600-grid-unit range makes
~800 cells, each granted its own Lipschitz margin (lip * step ~ 1.7e-3),
and 800 * 1.7e-3 = 1.3 of granted damage out of thin air.  The blanket
margin, not the mathematics.  (Third occurrence of that failure mode in
this hunt; the level-5 resolution scare and the level-7 mid-zone blanket
were the first two.)

THE RIGHT PARTITION IS THE DAMAGE FIELD'S OWN.  At the MT window the
damage f(g) = (-2 W(g, y))_+ is not spread over the line: it lives in
NARROW, WELL-SEPARATED BANDS (width 0.20 / 0.60 / 0.97 grid units at
y = 0.1 / 0.3 / 0.49, recurring with period ~2 pi = one mean gap, the
first at ~1.10 mean gaps), separated by long stretches where W > 0 and
the adversary gains nothing.  Partition by bands, not by a ruler.

THE DUAL.  Two elementary facts do all the work:

1. **omega^2 is a square, so every cross-band charge may be dropped.**
   Dropping nonnegative terms from the adversary's internal cost is
   one-sided in its favour, so the bound needs no charge floor at band
   separations at all, precisely the quantity the arithmetic band/zero
   coincidence was destroying.  The obstruction the first session named
   evaporates: it was never load-bearing.
2. **The band damage is summable.**  Only Im(Phi2) can push W negative,
   and one integration by parts gives |Im Phi2(g + iy)| <= C_im(y)/|g|,
   so band maxima decay like 1/g^2 and the whole band sum converges, to
   a measured **0.31 of the pair's slack, at every depth** (0.305 at
   y = 0.1, 0.308 at 0.3, 0.314 at 0.49).  Even granting the adversary
   the maximum of EVERY band on both sides at zero internal cost, it
   cannot reach the slack.

What is left to charge is therefore only SAME-BAND multiplicity, and the
bands are narrow: omega^2 over a band width stays near 1 (the kernel's
first zero is at 6.64 grid units, six times a band width), so a second
zero in one band costs ~2c against a gain of F_k.  The per-band cap is
the level-4 square completion on that single range,

    B_k(c) = max_{m >= 0} [ m F_k - c m (m - 1) K_k ],
    K_k = one-sided min of omega^2 over [0, band width],

and the dual is  cap(theta) = 2 sum_k B_k(1 - theta) + tail(G), with the
tail summed in closed form from the 1/g^2 majorant (never granted
per-cell).  The verdict is  cap(theta) <= slack(y).

RESULT (:func:`theta_scan`): the single-pair reduction at the MT window
secures theta up to the multiplicity threshold, the binding constraint
is not the damage at all but the point at which double occupancy of the
FIRST band becomes profitable, which happens only when c drops below
~F_1/(2 K_1).  Below that threshold the cap sits at ~0.31 slack with the
full band sum granted free.

Everything is measured-grade with one-sided structure (band maxima with
local Lipschitz margins, charge floors from below, tail majorant in
closed form); the arb pass is the named hardening, as at the other
window.  Nothing here computes a proportion.

Run ``.venv/bin/python hunts/frontier_math/band_dual.py`` (~3 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mt_chain import A, MEAN_GAP, MTChain, S2, phi2mt  # noqa: E402


def _sc_d1(z):
    """d/dz [2 sin(z/2)/z]."""
    z = np.asarray(z, complex)
    small = np.abs(z) < 1e-8
    zs = np.where(small, 1.0, z)
    val = (zs * np.cos(zs / 2) - 2 * np.sin(zs / 2)) / zs**2
    return np.where(small, 0.0, val)


def _sc_d2(z):
    """d^2/dz^2 [2 sin(z/2)/z]."""
    z = np.asarray(z, complex)
    small = np.abs(z) < 1e-8
    zs = np.where(small, 1.0, z)
    val = (-(zs**2 / 2) * np.sin(zs / 2) - 2 * zs * np.cos(zs / 2)
           + 4 * np.sin(zs / 2)) / zs**3
    return np.where(small, -1 / 12, val)


def phi2mt_d1(z):
    """Phi2'(z), closed form."""
    return 0.5 * _sc_d1(z) + 0.25 * (_sc_d1(z + 2 * S2) + _sc_d1(z - 2 * S2))


def phi2mt_d2(z):
    """Phi2''(z), closed form."""
    return 0.5 * _sc_d2(z) + 0.25 * (_sc_d2(z + 2 * S2) + _sc_d2(z - 2 * S2))


@dataclass(frozen=True)
class BandDual:
    mt: MTChain = MTChain()
    #: fine step for band location and maxima (grid units)
    step: float = 0.0005
    #: resolved region; beyond this the closed-form 1/g^2 tail takes over
    G: float = 400.0

    # -- local derivative bounds (never a blanket over the line) -------------

    @property
    def L2(self) -> float:
        """int t^2 phi^2 dt, the second-derivative constant."""
        ts = np.linspace(-0.5, 0.5, 20001)
        return float(np.trapezoid(ts * ts * np.cos(S2 * ts) ** 2, ts)) * 1.001

    def slope_bound(self, phi_abs, y: float):
        """|f'| <= 8 |Phi2| |Phi2'| / A^2 <= 8 |Phi2| L1 cosh(y/2) / A^2.

        Uses the LOCAL |Phi2|: in the damage bands Phi2 is near its zero,
        which is exactly why the blanket constant (1.9) overstates the
        true local slope (0.087 in the first band) by 20x.
        """
        return 8 * phi_abs * self.mt.L1 * math.cosh(y / 2) / A**2

    def curv_bound(self, phi_abs, y: float):
        """|f''| <= 8 (|Phi2'|^2 + |Phi2| |Phi2''|) / A^2."""
        ch = math.cosh(y / 2)
        return 8 * ((self.mt.L1 * ch) ** 2
                    + phi_abs * self.L2 * ch) / A**2

    # -- the bands -------------------------------------------------------------

    def _field(self, y: float):
        """Grid, damage field, and the LOCAL derivative magnitudes.

        Phi2' and Phi2'' are closed-form here (`phi2mt_d1/_d2`): a blanket
        constant for them does not decay with g, and at large g both the
        field and its curvature fall like 1/g^2, so a non-decaying
        curvature bound destroys the no-missed-band test exactly where
        the field is smallest.
        """
        gs = np.arange(self.step, self.G, self.step)
        z = gs + 1j * y
        ph = np.abs(phi2mt(z))
        p1 = np.abs(phi2mt_d1(z))
        p2 = np.abs(phi2mt_d2(z))
        f = -2 * self.mt.W(gs, y)
        return gs, f, ph, p1, p2

    def bands(self, y: float):
        """One-sided band list [(lo, hi, F_up)] on g > 0.

        Band MEMBERSHIP is decided on the raw grid (no margin: a margin in
        the membership test merges every band into one and is how the
        blanket-margin artifact enters).  The band's F_up carries the
        LOCAL slope margin only.
        """
        gs, f, ph, p1, _ = self._field(y)
        idx = np.where(f > 0)[0]
        if len(idx) == 0:
            return []
        groups = np.split(idx, np.where(np.diff(idx) > 1)[0] + 1)
        out = []
        for gr in groups:
            if len(gr) < 2:
                continue
            lo = float(gs[gr[0]]) - self.step
            hi = float(gs[gr[-1]]) + self.step
            # |f'| <= 8 |Phi2||Phi2'| / A^2, both local to the band
            slope = 8 * float((ph[gr] * p1[gr]).max()) / A**2
            F = float(f[gr].max()) + slope * self.step
            out.append((lo, hi, F))
        return out

    def no_missed_band(self, y: float) -> dict:
        """Rule out a band narrower than the grid, instead of paying for one.

        A band is exactly where q := Re(Phi2)^2 - Im(Phi2)^2 < 0.  Off the
        resolved bands (widened by one cell each side, so band edges are
        excluded) q > 0 on the grid; an unresolved dip would need an
        interior minimum, so it is excluded whenever

            q_i  >  (1/8) |q''| step^2,      |q''| <= 2(|Phi2'|^2
                                                       + |Phi2||Phi2''|),

        at every remaining off-band point.  Returns the measured worst
        ratio q / bound; > 1 everywhere means the off-band allowance is
        exactly zero and no allowance term enters the cap.

        (Paying a per-cell allowance instead is what re-introduces the
        blanket-margin artifact: it does not scale with depth, so at
        y = 0.02 it exceeded the entire slack.)
        """
        gs, f, ph, p1, p2 = self._field(y)
        q = -f * A**2 / 4
        on = f > 0
        widened = on.copy()
        widened[1:] |= on[:-1]
        widened[:-1] |= on[1:]
        off = ~widened
        if not np.any(off):
            return {"worst_ratio": math.inf, "clear": True}
        qpp = 2 * (p1[off] ** 2 + ph[off] * p2[off])
        bound = qpp * self.step**2 / 8
        ratio = float(np.min(q[off] / bound))
        return {"worst_ratio": ratio, "clear": ratio > 1.0}

    def off_band_allowance(self, y: float) -> float:
        """Zero when :meth:`no_missed_band` clears; otherwise the honest
        mean-value allowance over the unresolved cells only."""
        rec = self.no_missed_band(y)
        if rec["clear"]:
            return 0.0
        gs, f, ph, p1, p2 = self._field(y)
        off = f <= 0
        qpp = 2 * (p1[off] ** 2 + ph[off] * p2[off])
        return float(np.sum(qpp)) * self.step**2 / 8 * 4 / A**2

    def band_charge(self, width: float) -> float:
        """One-sided min of omega^2 over [0, width]: the same-band floor."""
        rs = np.arange(0.0, width + self.step, self.step)
        lo = float(np.min(phi2mt(rs.astype(complex)).real / A))
        lo -= (self.mt.L1 / A) * self.step
        return max(0.0, lo) ** 2

    # -- the tail --------------------------------------------------------------

    def band_period_lower(self, y: float) -> float:
        """Lower bound on consecutive band spacing (tail sum only; fewer
        bands per unit length is the safe direction there)."""
        bs = self.bands(y)
        if len(bs) < 3:
            return MEAN_GAP
        centres = [(lo + hi) / 2 for lo, hi, _ in bs]
        return min(centres[i + 1] - centres[i] for i in range(len(centres) - 1))

    def c_im_sharp(self, y: float) -> float:
        """Sharpened |Im Phi2(g+iy)| <= c/|g| via one integration by parts.

        Im Phi2 = int phi^2 sinh(yt) sin(gt) dt with u = phi^2 sinh(yt)
        odd, so the boundary term is 2 u(1/2) cos(g/2)/g and

            c = 2 phi^2(1/2) sinh(y/2) + TV(phi^2) sinh(y/2)
                + y cosh(y/2) int phi^2,

        with TV(phi^2) = 2(1 - cos^2(sqrt2/2)) (phi^2 is monotone on the
        half-window).  Measured ~2.2x above the true sup; the crude form
        that preceded it was 2.8x.
        """
        sh, ch = math.sinh(y / 2), math.cosh(y / 2)
        edge = math.cos(S2 / 2) ** 2
        tv = 2 * (1 - edge)
        return 2 * edge * sh + tv * sh + y * ch * A

    def tail_sum(self, y: float) -> float:
        """Closed-form majorant of sum_{bands beyond G} F_k, one side.

        Only Im(Phi2) can push W negative and |Im Phi2| <= C_im(y)/|g|, so
        F <= 4 (C_im/(A g))^2; with consecutive bands at least P apart,
        sum <= 4 (C_im/A)^2 [1/G^2 + 1/(P G)].
        """
        C = self.c_im_sharp(y) / A
        P = self.band_period_lower(y)
        return 4 * C * C * (1 / self.G**2 + 1 / (P * self.G))

    # -- the dual --------------------------------------------------------------

    def cap(self, theta: float, y: float) -> dict:
        """The band-lattice cap on sup_X [D(X) - (1-theta) R(X)].

        Cross-band charges are dropped (omega^2 >= 0: one-sided).  Each
        band gets the level-4 square completion against its OWN width's
        repulsion floor; the off-band allowance and the closed-form tail
        enter at single occupancy (both checked to be in the linear
        regime).
        """
        c = 1 - theta
        bs = self.bands(y)
        if not bs:
            return {"cap": 0.0, "bands": 0, "m_star": 0, "tail": 0.0}
        total = 0.0
        worst_m = 1
        K_min = math.inf
        for lo, hi, F in bs:
            K = self.band_charge(hi - lo)
            K_min = min(K_min, K)
            if c <= 0 or K <= 0:
                return {"cap": math.inf, "bands": len(bs), "m_star": None,
                        "tail": None}
            if F <= 2 * c * K:
                B, m = F, 1
            else:
                B = (F + c * K) ** 2 / (4 * c * K)
                m = int(round((F + c * K) / (2 * c * K)))
            total += B
            worst_m = max(worst_m, m)
        tail = self.tail_sum(y)
        off = self.off_band_allowance(y)
        C = self.c_im_sharp(y) / A
        F_G = 4 * C * C / self.G**2
        if F_G > 2 * c * K_min:
            raise AssertionError("tail band left the single-occupancy regime")
        return {"cap": 2 * (total + tail) + off, "bands": len(bs),
                "m_star": worst_m, "tail": 2 * tail, "off_band": off}

    def free_ratio(self, y: float) -> float:
        """Sum of all band maxima (both sides, plus tail and off-band)
        over the slack: the adversary's take when EVERY band is granted
        free at single occupancy (the theta -> 1 content of the dual)."""
        bs = self.bands(y)
        return (2 * (sum(F for _, _, F in bs) + self.tail_sum(y))
                + self.off_band_allowance(y)) / self.mt.slack(y)

    def theta_scan(self, ys=(0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.45, 0.49),
                   thetas=(0.9, 0.99, 0.995, 0.999, 0.9995, 0.9999)):
        """Largest grid theta with cap <= slack at every probe depth."""
        margins = {}
        star = None
        for theta in thetas:
            worst, arg = math.inf, None
            for y in ys:
                rec = self.cap(theta, y)
                m = self.mt.slack(y) - rec["cap"]
                if m < worst:
                    worst, arg = m, y
            margins[theta] = (worst, arg)
            if worst >= 0:
                star = theta
        return star, margins

    def multiplicity_threshold(self, y: float) -> float:
        """The theta at which double occupancy of the worst band turns
        profitable: c* = F_1 / (2 K_1), theta* = 1 - c*."""
        bs = self.bands(y)
        worst = max(bs, key=lambda b: b[2])
        K = self.band_charge(worst[1] - worst[0])
        return 1 - worst[2] / (2 * K)


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def dominates_explicit_adversary(bd: BandDual, ys=(0.3, 0.49),
                                 theta: float = 0.9):
    """The dual must dominate the measured band-riding adversary."""
    from mt_chain import explicit_single_pair_adversary
    out = []
    for y in ys:
        rec = explicit_single_pair_adversary(bd.mt, y)
        measured = rec["D"] - (1 - theta) * rec["R"]
        cap = bd.cap(theta, y)["cap"]
        out.append({"y": y, "measured": measured, "cap": cap,
                    "dominated": measured <= cap})
    return out


def band_structure_control(bd: BandDual, y: float = 0.49):
    """The partition's premises: bands are narrow, well separated, and
    the same-band repulsion is near 1 (six band widths below the
    kernel's first zero)."""
    bs = bd.bands(y)
    widths = [hi - lo for lo, hi, _ in bs[:8]]
    centres = [(lo + hi) / 2 for lo, hi, _ in bs[:8]]
    seps = [centres[i + 1] - centres[i] for i in range(len(centres) - 1)]
    return {
        "n_bands": len(bs),
        "width_first": widths[0],
        "width_max": max(widths),
        "sep_mean_gaps": [s / MEAN_GAP for s in seps],
        "first_centre_mean_gaps": centres[0] / MEAN_GAP,
        "K_band": bd.band_charge(max(widths)),
        "decay_ratios": [bs[i][2] / bs[i + 1][2] for i in range(4)],
    }


def cross_band_drop_is_one_sided(bd: BandDual, y: float = 0.49):
    """omega^2 >= 0 everywhere: dropping cross-band charges cannot help
    the bound.  Measured as a floor over the whole tested range."""
    rs = np.arange(0.0, 400.0, 0.01)
    return float(np.min(bd.mt.omega2(rs.astype(complex))))


def audit():
    bd = BandDual()
    mt = bd.mt
    print("= no missed bands (the partition is complete) =")
    for y in (0.02, 0.1, 0.3, 0.49):
        r = bd.no_missed_band(y)
        print(f"  y={y}: worst q / curvature bound = {r['worst_ratio']:.0f}"
              f"   clear={r['clear']}  (>1 means no band is narrower than "
              "the grid; the allowance is then exactly 0)")
    print("= the band structure (the partition's premises) =")
    st = band_structure_control(bd)
    print(f"  bands in (0, {bd.G}]: {st['n_bands']}   first centre at "
          f"{st['first_centre_mean_gaps']:.3f} mean gaps")
    print(f"  band widths: first {st['width_first']:.3f}, max "
          f"{st['width_max']:.3f} grid units   separations (mean gaps): "
          + ", ".join(f"{s:.3f}" for s in st['sep_mean_gaps'][:4]))
    print(f"  same-band repulsion floor K = {st['K_band']:.4f}  "
          "(kernel's first zero is at 6.64 = 6.9 band widths)")
    print(f"  band maxima decay ratios: "
          + ", ".join(f"{r:.2f}" for r in st['decay_ratios'])
          + "   (1/g^2 law -> ~4, 2.3, 1.8, 1.6)")
    print(f"  min omega^2 over [0, 400]: "
          f"{cross_band_drop_is_one_sided(bd):.3e}  "
          "(>= 0: dropping cross-band charges is one-sided)")
    print("= the free-band ratio: EVERY band granted, zero internal cost =")
    for y in (0.02, 0.05, 0.1, 0.2, 0.3, 0.45, 0.49):
        r = bd.cap(0.99, y)
        print(f"  y={y}: sum of all band maxima / slack = "
              f"{bd.free_ratio(y):.4f}   (tail {r['tail']:.2e}, off-band "
              f"{r['off_band']:.2e}, slack {bd.mt.slack(y):.5f})")
    print("  (the adversary cannot reach the slack even at theta = 1 with")
    print("   single occupancy: the whole band sum is ~0.31 of it)")
    print("= the multiplicity threshold (what actually binds) =")
    for y in (0.1, 0.3, 0.49):
        print(f"  y={y}: double occupancy of the worst band turns "
              f"profitable only below theta = "
              f"{bd.multiplicity_threshold(y):.5f}")
    print("= the theta scan (configuration-free, one-sided) =")
    star, margins = bd.theta_scan()
    for th, (m, arg) in margins.items():
        print(f"  theta={th}: worst margin {m:+.6f} at y={arg}  "
              f"{'ok' if m >= 0 else 'FAILS'}")
    print(f"  theta*_MT (grid) = {star}    (hunt window: 0.1)")
    print("= projection control: the dual dominates the measured adversary =")
    for row in dominates_explicit_adversary(bd):
        print(f"  y={row['y']}: measured {row['measured']:.5f} <= cap "
              f"{row['cap']:.5f}: {row['dominated']}")
    print("= theta = 1 must fail (no charge, unbounded multiplicity) =")
    r = bd.cap(1.0, 0.49)
    print(f"  cap(theta=1) = {r['cap']}  "
          f"(infinite: {not math.isfinite(r['cap'])})")


if __name__ == "__main__":
    audit()
