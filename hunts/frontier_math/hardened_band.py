"""The band-lattice dual at the MT window, under ball arithmetic.

The arb/acb hardening named at the end of :mod:`band_dual`, for the
SINGLE-PAIR reduction.  Everything entering the cap is rounded UP,
everything entering the slack is rounded DOWN, and the per-depth verdict
is ``cap <= slack``.

THE ROUTE: INTERVAL ARGUMENTS, NOT MEAN VALUE — AND WHY THAT DIFFERS
FROM THE OTHER WINDOW.  :mod:`hardened_direct` records that a naive
interval-ARGUMENT evaluation of the hunt window's Phi2 explodes: that
window's ramp^2 assembly carries integer coefficients up to ~1e4 with
alternating signs whose analytic cancellation interval radii cannot see,
and the measured amplification of the input radius was ~1.8e5.  It had to
fall back to a mean-value form (point balls of value and derivative plus
a curvature remainder).

At the MT window Phi2 is a THREE-TERM trigonometric expression,

    Phi2(z) = 0.5 sc(z) + 0.25 [sc(z + 2 sqrt2) + sc(z - 2 sqrt2)],
    sc(z)   = 2 sin(z/2) / z,

with no series truncation, no moment recursion and no catastrophic
cancellation, so the interval-argument route is available here.  It was
measured before being used, at depth y = 0.49 and input radius r = 5e-3:

    g = 1.1   rad(Re Phi2) = 5.30e-3   amplification 1.06
    g = 7.5   rad(Re Phi2) = 6.97e-4   amplification 0.14
    g = 50    rad(Re Phi2) = 6.11e-5   amplification 0.012
    g = 300   rad(Re Phi2) = 1.21e-5   amplification 0.0024

i.e. essentially lossless, and IMPROVING with g because sc decays.  That
is a real difference between the two windows, and it buys something the
mean-value route cannot give: an interval-argument enclosure covers the
CONTINUUM inside each cell, so no Lipschitz margin is granted anywhere,
and "no band is narrower than the grid" stops being an inference from a
curvature bound and becomes a property of the cover.

WHAT IS DIRECTED WHICH WAY

* ``sc`` uses the closed form away from its removable singularity and a
  truncated Taylor series with an explicit geometric remainder ball for
  |z| < 1 (needed at g ~ 2 sqrt2 and shallow y, where z - 2 sqrt2 passes
  through 0).  Both branches return enclosures.
* Band membership, band edges and the band maxima F_k: the UPPER endpoint
  of f = -4 q / A^2 over each cell, q = Re(Phi2)^2 - Im(Phi2)^2, with A
  a ball.  No slope margin is added because none is owed: the cell
  enclosure already contains every value of f on the cell.  Band edges
  are the OUTER edges of the flagged cells (bands widened, never
  narrowed).
* Same-band repulsion K_k: the LOWER endpoint of min omega^2 over
  [0, width], omega = Re Phi2(r)/A, on an interval cover of [0, width]
  with the widths rounded UP to the cover's step.
* Slack 8 sigma^2 + 8 sigma^4: LOWER endpoint of the sigma^2 ball, then
  deflated by (1 - 1e-9).
* The closed-form 1/g^2 tail: C_im/A rounded UP, the band period P
  rounded DOWN (fewer bands per unit length is the safe direction in the
  tail sum only), then 4 C^2 (1/G^2 + 1/(P G)) rounded UP.
* The off-band allowance: exactly 0, and it is allowed to be 0 only
  because every off-band cell's f enclosure has a NONPOSITIVE upper
  endpoint over the whole cell.  The curvature test of
  ``band_dual.no_missed_band`` is also reproduced with directed
  endpoints (q lower endpoint at cell centres against the upper endpoint
  of |q''| over the cell) as an independent witness; it uses closed-form
  acb balls for Phi2' and Phi2''.
* The square completion max_m [m F_k - c m(m-1) K_k], c = 1 - theta, is
  double-precision arithmetic on directed inputs; the band total is
  inflated by (1 + 1e-9), as at gate 1.

RESULTS (:func:`audit`, theta = 0.99, G = 400, 63 bands per side, all
four bands single-occupancy there).  The hardening costs nothing that
shows: at every depth the hardened cap comes in BELOW the float cap,
because the cover removes the float pass's blanket Lipschitz margins
(the float F_k carried ``slope * step``; an interval cell owes none):

    y      slack >=      cap <=        margin >=     cap/slack
    0.02   2.304683e-4   7.739518e-5   +1.530731e-4   0.336
    0.10   5.768282e-3   1.938606e-3   +3.829677e-3   0.336
    0.30   5.241061e-2   1.778540e-2   +3.462521e-2   0.339
    0.49   1.423407e-1   4.912314e-2   +9.321760e-2   0.345

(float ``band_dual`` at the same theta: 0.357 / 0.341 / 0.341 / 0.346.)
The hardened F_1 lands between the float raw grid sup and the float
margined F_1 at every depth, which is the control:
5.3884e-3 <= 5.3925e-3 <= 5.4200e-3 at y = 0.3.

The no-missed-band property survives hardening at every depth, in the
stronger cover-based form: of 20000 coarse cells, 221 / 708 / 1935 /
3054 are flagged at y = 0.02 / 0.1 / 0.3 / 0.49, and every cell not
flagged has f <= 0 THROUGHOUT the cell, not merely at a grid point, so
the off-band allowance is exactly 0.  The independent curvature witness
also clears at its own (coarse) step, worst ratio 8.1 / 24.2 / 69.0 /
118.9.

The largest scanned theta surviving the hardened pass at all four
depths is 0.9988 (worst margin +1.53e-4, at y = 0.02, where the slack
itself is only 2.3e-4); 0.9989 fails at y = 0.49 by -4.80e-3.  The
float pass has the same boundary — it clears 0.9988 by +3.96e-3 and
fails 0.9989 by -5.60e-3 — so the hardening moves the surviving theta
by less than one scan step.  The binding term is the multiplicity
threshold, exactly as in the float pass: at y = 0.49 double occupancy
of the first band turns profitable below theta = 0.991929, and by
theta = 0.9989 the square completion has m* = 8 there.  The damage sum
is never the binding term at any tested theta.

Nothing here computes a proportion, and nothing here is evidence about
the Riemann Hypothesis.

Run ``.venv/bin/python hunts/frontier_math/hardened_band.py`` (~45 s).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass, field
from pathlib import Path

from flint import acb, arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))

ctx.prec = 128

#: 2 sqrt2, the MT window's shift, as a ball
S2B = arb(2).sqrt()
TWO_S2 = 2 * S2B

#: |z| below which sc and its derivatives use the Taylor branch
_SMALL = 1.0
#: Taylor terms kept there (the remainder ball is added explicitly)
_NTERM = 22


def f_up(x: arb) -> float:
    """A float upper bound for the arb ball."""
    return math.nextafter(float(x.upper()), math.inf)


def f_lo(x: arb) -> float:
    """A float lower bound for the arb ball."""
    return math.nextafter(float(x.lower()), -math.inf)


# ---------------------------------------------------------------------------
# sc(z) = 2 sin(z/2)/z and its first two derivatives, as acb enclosures
# ---------------------------------------------------------------------------


def _sc_series(z: acb):
    """(sc, sc', sc'') from the Taylor series, with explicit remainder balls.

    sc(z) = sum_{n>=0} c_n z^{2n},  c_0 = 1,
    c_{n+1} = -c_n / (4 (2n+2)(2n+3)),
    sc'(z)  = z sum_{m>=0} 2(m+1) c_{m+1} z^{2m},
    sc''(z) = sum_{m>=0} (2m+2)(2m+1) c_{m+1} z^{2m}.

    Writing the two derivative series in z^{2m} (rather than dividing a
    z^{2n} series by z) is what keeps the branch usable across z = 0.
    With |z| <= 1 the successive term magnitudes shrink by a factor
    above 24, so each remainder is bounded by its first dropped term
    times a generous polynomial-times-geometric factor and added as a
    symmetric ball.
    """
    z2 = z * z
    # value series
    c = acb(1)
    s0 = acb(0)
    for n in range(_NTERM):
        s0 += c
        c = -c * z2 / (4 * (2 * n + 2) * (2 * n + 3))
    m0 = float(abs(c).upper()) * 1.05
    s0 = s0 + acb(arb(0, m0), arb(0, m0))
    # derivative series, in powers z^{2m}
    a = acb(-1) / (4 * 2 * 3)          # c_1
    p = acb(1)                          # z^{2m}, m = 0
    d1 = acb(0)
    d2 = acb(0)
    for m in range(_NTERM):
        d1 += (2 * (m + 1)) * a * p
        d2 += ((2 * m + 2) * (2 * m + 1)) * a * p
        a = -a / (4 * (2 * m + 4) * (2 * m + 5))
        p = p * z2
    md = float(abs(a * p).upper()) * 1.05
    M = _NTERM
    r1 = 4 * (M + 4) * md
    r2 = 8 * (M + 4) ** 2 * md
    d1 = d1 + acb(arb(0, r1), arb(0, r1))
    d2 = d2 + acb(arb(0, r2), arb(0, r2))
    return s0, z * d1, d2


def sc_all(z: acb):
    """Enclosures of (sc(z), sc'(z), sc''(z))."""
    if float(abs(z).upper()) < _SMALL:
        return _sc_series(z)
    h = z / 2
    s, c = h.sin(), h.cos()
    z2 = z * z
    sc0 = 2 * s / z
    sc1 = (z * c - 2 * s) / z2
    sc2 = (-(z2 / 2) * s - 2 * z * c + 4 * s) / (z2 * z)
    return sc0, sc1, sc2


def phi2_all(z: acb):
    """Enclosures of (Phi2(z), Phi2'(z), Phi2''(z)) at the MT window."""
    a0, a1, a2 = sc_all(z)
    b0, b1, b2 = sc_all(z + TWO_S2)
    c0, c1, c2 = sc_all(z - TWO_S2)
    return (0.5 * a0 + 0.25 * (b0 + c0),
            0.5 * a1 + 0.25 * (b1 + c1),
            0.5 * a2 + 0.25 * (b2 + c2))


def phi2_ball(z: acb) -> acb:
    """Enclosure of Phi2(z) alone (the cheap path used by the scans)."""
    a0, _, _ = sc_all(z)
    b0, _, _ = sc_all(z + TWO_S2)
    c0, _, _ = sc_all(z - TWO_S2)
    return 0.5 * a0 + 0.25 * (b0 + c0)


#: A = Phi2(0) = 1/2 + sin(sqrt2)/(2 sqrt2), as a ball
A_BALL = arb(0.5) + S2B.sin() / (2 * S2B)


# ---------------------------------------------------------------------------
# the hardened dual
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HardenedBand:
    """:class:`band_dual.BandDual` with every kernel evaluation a ball."""

    #: coarse interval cover of (0, G]: locates band candidates and carries
    #: the off-band emptiness statement
    coarse: float = 0.02
    #: fine interval cover inside each candidate: band edges and F_k
    fine: float = 0.0005
    #: cover step for the same-band repulsion floor
    k_step: float = 0.002
    #: resolved region; beyond it the closed-form 1/g^2 tail takes over
    G: float = 400.0
    #: inflation covering the double-precision square completion
    infl: float = 1.0 + 1e-9

    _cache: dict = field(default_factory=dict, repr=False, compare=False)

    # -- scalar quantities, directed ----------------------------------------

    def sigma2_ball(self, y: float) -> arb:
        return (phi2_ball(acb(0, 2 * arb(y))).real - A_BALL) / (2 * A_BALL)

    def slack_lo(self, y: float) -> float:
        """LOWER endpoint of 8 sigma^2 + 8 sigma^4."""
        s2 = max(0.0, f_lo(self.sigma2_ball(y)))
        return (8 * s2 + 8 * s2 * s2) * (1 - 1e-9)

    def f_cell_up(self, mid: float, rad: float, y: float) -> float:
        """UPPER endpoint of f = -2W = -4 q / A^2 over [mid-rad, mid+rad]."""
        v = phi2_ball(acb(arb(mid, rad), arb(y)))
        q = v.real * v.real - v.imag * v.imag
        return f_up(-4 * q / (A_BALL * A_BALL))

    # -- the interval cover: bands and off-band emptiness --------------------

    def scan(self, y: float) -> dict:
        """Interval cover of (0, G]: bands, F_k uppers, off-band verdict.

        Pass 1 covers (0, G] in cells of width ``coarse``.  A cell whose
        f enclosure has a nonpositive UPPER endpoint contributes nothing
        anywhere -- f <= 0 throughout it, not merely at a grid point --
        so the off-band allowance is 0 as long as every cell outside the
        candidate runs is of that kind, which is what pass 1 records.

        Pass 2 re-covers each candidate run (padded by one coarse cell
        each side) in cells of width ``fine``; the band is the union of
        the flagged fine cells, taken at their OUTER edges, and F_k is
        the largest cell upper endpoint on it.
        """
        key = ("scan", y)
        if key in self._cache:
            return self._cache[key]
        n = int(math.ceil(self.G / self.coarse))
        r = self.coarse / 2
        flagged = []
        for i in range(n):
            mid = (i + 0.5) * self.coarse
            if self.f_cell_up(mid, r, y) > 0.0:
                flagged.append(i)
        # merge into runs, pad by one coarse cell each side
        runs = []
        for i in flagged:
            if runs and i - runs[-1][1] <= 2:
                runs[-1][1] = i
            else:
                runs.append([i, i])
        bands = []
        rf = self.fine / 2
        for i0, i1 in runs:
            lo = max(0.0, (i0 - 1) * self.coarse)
            hi = (i1 + 2) * self.coarse
            m = int(math.ceil((hi - lo) / self.fine))
            on = []
            for j in range(m):
                mid = lo + (j + 0.5) * self.fine
                fu = self.f_cell_up(mid, rf, y)
                on.append(fu if fu > 0.0 else None)
            idx = [j for j, v in enumerate(on) if v is not None]
            if not idx:
                continue
            if idx[0] == 0 or idx[-1] == m - 1:
                raise AssertionError(
                    "a band reached the padded window edge; widen the padding")
            groups = []
            for j in idx:
                if groups and j - groups[-1][-1] == 1:
                    groups[-1].append(j)
                else:
                    groups.append([j])
            for gr in groups:
                b_lo = lo + gr[0] * self.fine
                b_hi = lo + (gr[-1] + 1) * self.fine
                F = max(on[j] for j in gr)
                bands.append((b_lo, b_hi, F))
        rec = {"bands": bands, "n_coarse": n, "n_flagged": len(flagged),
               "off_band_allowance": 0.0}
        self._cache[key] = rec
        return rec

    def bands(self, y: float):
        return self.scan(y)["bands"]

    # -- the curvature witness (band_dual's test, directed) ------------------

    def curvature_witness(self, y: float) -> dict:
        """Independent witness that no band hides between cover cells.

        q := Re(Phi2)^2 - Im(Phi2)^2, and q'' = Re(2 Phi2'^2
        + 2 Phi2 Phi2''), so |q''| <= 2(|Phi2'|^2 + |Phi2||Phi2''|).
        For every off-band coarse cell this compares the LOWER endpoint
        of q at the cell centre against the UPPER endpoint of
        (1/8)|q''| h^2 over the whole cell, h = ``coarse``.  A ratio
        above 1 everywhere excludes an unresolved interior dip, which is
        the statement :meth:`scan` gets for free from the cover; the two
        agreeing is the cross-check.
        """
        n = int(math.ceil(self.G / self.coarse))
        r = self.coarse / 2
        worst = math.inf
        for i in range(n):
            mid = (i + 0.5) * self.coarse
            if self.f_cell_up(mid, r, y) > 0.0:
                continue  # on/near a band: excluded from the test
            p, p1, p2 = phi2_all(acb(arb(mid, r), arb(y)))
            qpp = 2 * (abs(p1) * abs(p1) + abs(p) * abs(p2))
            bound = f_up(qpp) * self.coarse ** 2 / 8
            v = phi2_ball(acb(arb(mid), arb(y)))
            q = f_lo(v.real * v.real - v.imag * v.imag)
            if bound > 0:
                worst = min(worst, q / bound)
        return {"worst_ratio": worst, "clear": worst > 1.0,
                "step": self.coarse}

    # -- the same-band repulsion floor --------------------------------------

    def band_charge_lo(self, width: float) -> float:
        """LOWER endpoint of min omega^2 over [0, width], omega = RePhi2/A.

        The width is rounded UP to a whole number of cover cells (a wider
        interval can only lower the minimum) and the cover is by
        intervals, so no Lipschitz margin is owed.
        """
        cells = int(math.ceil(width / self.k_step))
        key = ("K", cells)
        if key in self._cache:
            return self._cache[key]
        r = self.k_step / 2
        lo = math.inf
        for i in range(cells):
            mid = (i + 0.5) * self.k_step
            v = phi2_ball(acb(arb(mid, r), arb(0))).real / A_BALL
            lo = min(lo, f_lo(v))
        K = max(0.0, lo) ** 2 * (1 - 1e-9) if lo > 0 else 0.0
        self._cache[key] = K
        return K

    # -- the closed-form tail ------------------------------------------------

    def c_im_over_A_up(self, y: float) -> float:
        """UPPER endpoint of C_im(y)/A, the 1/g majorant constant.

        |Im Phi2(g+iy)| <= C_im(y)/|g| by one integration by parts, with
        C_im = 2 phi^2(1/2) sinh(y/2) + TV(phi^2) sinh(y/2)
               + y cosh(y/2) A,  TV(phi^2) = 2(1 - cos^2(sqrt2/2)).
        """
        yb = arb(y)
        sh, ch = (yb / 2).sinh(), (yb / 2).cosh()
        edge = (S2B / 2).cos() ** 2
        tv = 2 * (1 - edge)
        c_im = 2 * edge * sh + tv * sh + yb * ch * A_BALL
        return f_up(c_im / A_BALL)

    def period_lo(self, y: float) -> float:
        """LOWER bound on consecutive band spacing (used in the tail only).

        Band centres come from the directed band edges; each is inside
        one fine cell of the true centre, so the measured minimum
        spacing is deflated by two fine cells.
        """
        bs = self.bands(y)
        if len(bs) < 3:
            return 2 * math.pi
        cs = [(lo + hi) / 2 for lo, hi, _ in bs]
        return min(cs[i + 1] - cs[i] for i in range(len(cs) - 1)) - 2 * self.fine

    def tail_up(self, y: float) -> float:
        """UPPER bound on sum over bands beyond G of F_k, one side.

        Only Im(Phi2) can push W negative and |Im Phi2| <= C/(A g), so
        F <= 4 (C/(A g))^2; with consecutive bands at least P apart,
        sum <= 4 C^2 [1/G^2 + 1/(P G)].
        """
        C = self.c_im_over_A_up(y)
        P = self.period_lo(y)
        return 4 * C * C * (1 / self.G ** 2 + 1 / (P * self.G)) * self.infl

    # -- the cap and the verdict --------------------------------------------

    def cap_up(self, theta: float, y: float) -> dict:
        """UPPER bound on sup_X [D(X) - (1-theta) R(X)] for one pair.

        Cross-band charges are dropped (omega^2 >= 0: one-sided in the
        adversary's favour).  Each band gets the square completion
        max_m [m F_k - c m(m-1) K_k] against its own width's repulsion
        floor; the tail enters at single occupancy, which is checked.
        """
        c = 1 - theta
        bs = self.bands(y)
        if not bs:
            return {"cap": 0.0, "bands": 0, "m_star": 0, "tail": 0.0,
                    "off_band": 0.0}
        total = 0.0
        worst_m = 1
        K_min = math.inf
        for lo, hi, F in bs:
            K = self.band_charge_lo(hi - lo)
            K_min = min(K_min, K)
            if c <= 0 or K <= 0:
                return {"cap": math.inf, "bands": len(bs), "m_star": None,
                        "tail": None, "off_band": 0.0}
            if F <= 2 * c * K:
                B, m = F, 1
            else:
                B = (F + c * K) ** 2 / (4 * c * K)
                m = int(round((F + c * K) / (2 * c * K)))
            total += B
            worst_m = max(worst_m, m)
        total *= self.infl
        tail = self.tail_up(y)
        C = self.c_im_over_A_up(y)
        F_G = 4 * C * C / self.G ** 2
        if F_G > 2 * c * K_min:
            raise AssertionError("tail band left the single-occupancy regime")
        off = self.scan(y)["off_band_allowance"]
        return {"cap": 2 * (total + tail) + off, "bands": len(bs),
                "m_star": worst_m, "tail": 2 * tail, "off_band": off}

    def verdict(self, theta: float, y: float) -> dict:
        slack = self.slack_lo(y)
        rec = self.cap_up(theta, y)
        return {"y": y, "theta": theta, "slack_lo": slack,
                "cap_up": rec["cap"], "margin": slack - rec["cap"],
                "closes": slack - rec["cap"] >= 0, "m_star": rec["m_star"],
                "tail": rec["tail"], "bands": rec["bands"]}

    def free_ratio(self, y: float) -> float:
        """Every band granted free at single occupancy, over the slack."""
        bs = self.bands(y)
        num = 2 * (sum(F for _, _, F in bs) * self.infl + self.tail_up(y))
        return num / self.slack_lo(y)

    def multiplicity_threshold(self, y: float) -> float:
        """theta below which double occupancy of the worst band pays:
        c* = F_1/(2 K_1), theta* = 1 - c*.  Directed so that the
        hardened threshold is LOWER than the float one (F up, K down)."""
        bs = self.bands(y)
        lo, hi, F = max(bs, key=lambda b: b[2])
        return 1 - F / (2 * self.band_charge_lo(hi - lo))

    def theta_scan(self, ys=(0.02, 0.1, 0.3, 0.49),
                   thetas=(0.9, 0.99, 0.995, 0.998, 0.9985, 0.9988, 0.9989,
                           0.999)):
        """Largest scanned theta whose hardened cap stays under the slack."""
        margins = {}
        star = None
        for theta in thetas:
            worst, arg = math.inf, None
            for y in ys:
                rec = self.verdict(theta, y)
                if rec["margin"] < worst:
                    worst, arg = rec["margin"], y
            margins[theta] = (worst, arg)
            if worst >= 0:
                star = theta
        return star, margins


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def interval_amplification(y: float = 0.49, rad: float = 5e-3):
    """The measurement that chose the route: radius in vs radius out.

    At the hunt window this ratio was ~1.8e5 and forced the mean-value
    form (`hardened_direct`); here it must stay O(1) and decay with g.
    """
    out = []
    for g in (1.1, 7.5, 50.0, 300.0):
        v = phi2_ball(acb(arb(g, rad), arb(y)))
        out.append((g, float(v.real.rad()), float(v.real.rad()) / rad))
    return out


def ball_agrees_with_float(hb: HardenedBand, y: float = 0.3):
    """The hardened objects must sit on the safe side of the float ones.

    The reference for F_1 is the float RAW grid maximum of f, not
    ``band_dual``'s F: the latter already carries a Lipschitz margin
    that the interval cover does not owe, so the hardened F_1 lands
    BETWEEN the two -- above the true grid sup (as an upper bound must
    be) and below the float bound (which is what the cover buys).
    """
    from band_dual import BandDual
    bd = BandDual()
    fb = bd.bands(y)
    raw = float(bd._field(y)[1].max())
    hbs = hb.bands(y)
    return {
        "n_float": len(fb), "n_ball": len(hbs),
        "F1_raw": raw, "F1_ball": hbs[0][2], "F1_float_margined": fb[0][2],
        "F1_above_raw": hbs[0][2] >= raw,
        "F1_below_float_margin": hbs[0][2] <= fb[0][2],
        "slack_float": bd.mt.slack(y), "slack_lo": hb.slack_lo(y),
        "slack_directed_down": hb.slack_lo(y) <= bd.mt.slack(y) * (1 + 1e-9),
    }


def resolution_ladder(theta: float = 0.99, ys=(0.02, 0.49)):
    """The hardened margins must not be an artifact of the cover step.

    Three rungs of (coarse, fine, k_step); a cover-based bound can only
    move by the interval overestimation it removes, so the margins
    should agree to a few parts in 1e4.
    """
    rungs = [(0.05, 0.002, 0.005), (0.02, 0.0005, 0.002),
             (0.01, 0.00025, 0.001)]
    out = []
    for coarse, fine, k_step in rungs:
        hb = HardenedBand(coarse=coarse, fine=fine, k_step=k_step)
        out.append({"coarse": coarse, "fine": fine, "k_step": k_step,
                    "margins": [hb.verdict(theta, y)["margin"] for y in ys],
                    "F1_deep": hb.bands(max(ys))[0][2]})
    return out


def theta_one_must_fail(hb: HardenedBand, y: float = 0.49):
    """No charge, unbounded multiplicity: the cap must diverge."""
    return hb.cap_up(1.0, y)["cap"]


def audit():
    hb = HardenedBand()
    print("= the route: interval-argument amplification at the MT window =",
          flush=True)
    for g, rad, amp in interval_amplification():
        print(f"  g={g:6.1f}: rad(Re Phi2) = {rad:.3e}   "
              f"amplification {amp:.4f}")
    print("  (hunt window, hardened_direct: ~1.8e5 -> mean-value form was")
    print("   forced there; here the interval-argument cover is used)")

    print("= no missed band: the cover statement, then the witness =",
          flush=True)
    for y in (0.02, 0.1, 0.3, 0.49):
        sc_ = hb.scan(y)
        cw = hb.curvature_witness(y)
        print(f"  y={y}: {sc_['n_flagged']}/{sc_['n_coarse']} coarse cells "
              f"flagged; every other cell has f <= 0 THROUGHOUT, so the "
              f"off-band allowance is {sc_['off_band_allowance']:.1f}")
        print(f"        curvature witness (step {cw['step']}): worst "
              f"q / (|q''| h^2 / 8) = {cw['worst_ratio']:.1f}  "
              f"clear={cw['clear']}")

    print("= hardened band structure =", flush=True)
    for y in (0.02, 0.1, 0.3, 0.49):
        bs = hb.bands(y)
        w = [hi - lo for lo, hi, _ in bs]
        K = hb.band_charge_lo(max(w))
        print(f"  y={y}: {len(bs)} bands in (0, {hb.G}]  first at "
              f"{(bs[0][0] + bs[0][1]) / 2:.3f}  widths {min(w):.4f}"
              f"-{max(w):.4f}  F_1 <= {bs[0][2]:.4e}  K >= {K:.6f}")

    print("= the free-band ratio: EVERY band granted, zero internal cost =",
          flush=True)
    for y in (0.02, 0.1, 0.3, 0.49):
        print(f"  y={y}: sum of band maxima (up) / slack (down) = "
              f"{hb.free_ratio(y):.4f}   tail <= "
              f"{2 * hb.tail_up(y):.3e}")

    print("= the hardened per-depth verdict at theta = 0.99 =", flush=True)
    print("    y       slack >=      cap <=        margin >=     m*")
    for y in (0.02, 0.1, 0.3, 0.49):
        r = hb.verdict(0.99, y)
        print(f"  {y:5.2f}   {r['slack_lo']:.6e}  {r['cap_up']:.6e}  "
              f"{r['margin']:+.6e}   {r['m_star']}   "
              f"{'ok' if r['closes'] else 'FAILS'}")

    print("= the hardened multiplicity threshold (what binds) =", flush=True)
    for y in (0.02, 0.1, 0.3, 0.49):
        print(f"  y={y}: double occupancy of the worst band pays only "
              f"below theta = {hb.multiplicity_threshold(y):.6f}")

    print("= the hardened theta scan =", flush=True)
    star, margins = hb.theta_scan()
    for th, (m, arg) in margins.items():
        print(f"  theta={th}: worst margin {m:+.6e} at y={arg}  "
              f"{'ok' if m >= 0 else 'FAILS'}")
    print(f"  largest scanned theta surviving the hardened pass = {star}")

    print("= controls =", flush=True)
    print("  resolution ladder (theta=0.99, margins at y=0.02 / 0.49):")
    for r in resolution_ladder():
        print(f"    coarse {r['coarse']:<5} fine {r['fine']:<8} k_step "
              f"{r['k_step']:<6}: "
              + " / ".join(f"{m:+.6e}" for m in r["margins"])
              + f"   F_1(0.49) <= {r['F1_deep']:.6e}")
    ag = ball_agrees_with_float(hb)
    print(f"  vs float band_dual at y=0.3: bands {ag['n_ball']} (float "
          f"{ag['n_float']})")
    print(f"    raw grid sup {ag['F1_raw']:.4e} <= hardened F_1 "
          f"{ag['F1_ball']:.4e}: {ag['F1_above_raw']}  <= float margined "
          f"{ag['F1_float_margined']:.4e}: {ag['F1_below_float_margin']}")
    print(f"    slack {ag['slack_lo']:.6e} <= float "
          f"{ag['slack_float']:.6e}: {ag['slack_directed_down']}")
    cap1 = theta_one_must_fail(hb)
    print(f"  theta = 1: cap = {cap1} (diverges as it must: "
          f"{not math.isfinite(cap1)})")


if __name__ == "__main__":
    audit()
