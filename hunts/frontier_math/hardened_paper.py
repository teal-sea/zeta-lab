"""The band-lattice dual at the PAPER field, under ball arithmetic.

The arb/acb hardening of :mod:`paper_chain`, in the same shape as
:mod:`hardened_band` (which hardened the T1 window's dual).  Everything
entering the cap is rounded UP, everything entering the slack is rounded
DOWN, and the per-depth verdict is ``cap <= slack``.

THE FIELD.  The paper's incidence kernel is

    Phi2(z) = s(z + sqrt2) + s(z - sqrt2),    s(u) = sin(u/2)/u,
    A = Phi2(0) = 2 sin(sqrt2/2)/sqrt2 = 0.9187253698...,

a TWO-term trigonometric form — one term friendlier than the T1 window's
three-term sc assembly, and far from the hunt window's ramp^2 assembly
whose interval-argument radii amplified by ~1.8e5 and forced a
mean-value fallback (`hardened_direct`).  Here the interval-argument
route is measured before being used (:func:`interval_amplification`)
and is essentially lossless: amplification ~1 at the first band and
DECAYING with g because s decays.  That buys the same thing it bought at
the T1 window: an interval-argument enclosure covers the CONTINUUM
inside each cell, so no Lipschitz margin is granted anywhere, and "no
band is narrower than the grid" is a property of the cover rather than
an inference from a curvature bound.

THE SINGULAR BRANCH.  s(u) has a removable singularity at u = 0, and the
scan crosses it (the fine cells near g = sqrt2 put z - sqrt2 through 0).
For |u| < 1 the module uses the Taylor series

    s(u)   = sum_{n>=0} c_n u^{2n},  c_0 = 1/2,
             c_{n+1} = -c_n / (4 (2n+2)(2n+3)),
    s'(u)  = u * sum_{m>=0} 2(m+1) c_{m+1} u^{2m},
    s''(u) = sum_{m>=0} (2m+2)(2m+1) c_{m+1} u^{2m},

truncated at N = 22 terms with an EXPLICIT remainder ball.  The bound:
for |u| <= 1 consecutive term magnitudes shrink by at least
4*(2n+2)(2n+3) >= 24, so the value tail is at most the first dropped
term |c_N u^{2N}| times 24/23 < 1.05; the derivative tails carry the
polynomial coefficient growth, which is covered generously by
4(N+4) and 8(N+4)^2 times the first dropped coefficient term.  At
N = 22 the first dropped term is ~1e-70, far below the working
precision (128 bits ~ 3e-39), so the remainder ball is invisible; it is
added anyway because the branch must be an enclosure, not an estimate.
The branch is pinned against mpmath at dps 40 in the test file.

WHAT IS DIRECTED WHICH WAY (identical to hardened_band):

* Band membership and the band maxima F_k: the UPPER endpoint of
  f = -4 q / A^2 over each cell, q = Re(Phi2)^2 - Im(Phi2)^2, A a ball.
  No slope margin is added because none is owed.  Band edges are the
  OUTER edges of the flagged fine cells.
* Every unflagged cell has f <= 0 THROUGHOUT the cell (its enclosure's
  upper endpoint is nonpositive), so the off-band allowance is exactly
  0.  The curvature test of paper_chain.no_missed_band is reproduced
  with directed endpoints as an independent witness.
* Same-band repulsion K_k: LOWER endpoint of min omega^2 over
  [0, width] on an interval cover, widths rounded UP.
* Slack 8 sigma^2 + 8 sigma^4: LOWER endpoint of the sigma^2 ball,
  deflated by (1 - 1e-9) — both sides of the verdict are one-sided.
* The closed-form 1/g^2 tail: C_im/A rounded UP (edge = cos(sqrt2/2)
  here, the paper window's phi^2(1/2); the T1 window had cos^2), the
  band period P rounded DOWN, then 4 C^2 (1/G^2 + 1/(P G)) rounded UP.
* The square completion is double-precision arithmetic on directed
  inputs, inflated by (1 + 1e-9).

If a cell cannot be decided the scan does not widen a margin: the fine
pass simply flags it (a flagged cell only ADDS to the cap), and the
padded-window guard raises rather than silently truncating a band.
Nothing here computes a proportion and nothing here is evidence about
RH.

Run ``.venv/bin/python hunts/frontier_math/hardened_paper.py`` (~4 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass, field
from pathlib import Path

from flint import acb, arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))

ctx.prec = 128

#: sqrt2, the paper window's shift, as a ball
S2B = arb(2).sqrt()

#: |u| below which s and its derivatives use the Taylor branch
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
# s(u) = sin(u/2)/u and its first two derivatives, as acb enclosures
# ---------------------------------------------------------------------------


def _s_series(u: acb):
    """(s, s', s'') from the Taylor series, with explicit remainder balls.

    Coefficients: c_0 = 1/2, c_{n+1} = -c_n / (4 (2n+2)(2n+3)); the
    leading terms 1/2 - u^2/48 + u^4/3840 (and -u/24 + u^3/960,
    -1/24 + u^2/320 for the derivatives) match the sympy-pinned series
    of paper_chain.  Writing the derivative series in u^{2m} (not
    dividing a u^{2n} series by u) keeps the branch usable across
    u = 0.  Remainders for |u| <= 1: term ratio <= 1/24, so the value
    tail <= first dropped term * 1.05; derivative tails carry the
    polynomial factors 2(m+1) resp. (2m+2)(2m+1), covered by
    4(N+4) resp. 8(N+4)^2 times the first dropped coefficient term.
    """
    u2 = u * u
    # value series
    c = acb(arb(1) / 2)
    s0 = acb(0)
    for n in range(_NTERM):
        s0 += c
        c = -c * u2 / (4 * (2 * n + 2) * (2 * n + 3))
    m0 = float(abs(c).upper()) * 1.05
    s0 = s0 + acb(arb(0, m0), arb(0, m0))
    # derivative series, in powers u^{2m}
    a = acb(arb(-1) / 48)               # c_1
    p = acb(1)                          # u^{2m}, m = 0
    d1 = acb(0)
    d2 = acb(0)
    for m in range(_NTERM):
        d1 += (2 * (m + 1)) * a * p
        d2 += ((2 * m + 2) * (2 * m + 1)) * a * p
        a = -a / (4 * (2 * m + 4) * (2 * m + 5))
        p = p * u2
    md = float(abs(a * p).upper()) * 1.05
    N = _NTERM
    r1 = 4 * (N + 4) * md
    r2 = 8 * (N + 4) ** 2 * md
    d1 = d1 + acb(arb(0, r1), arb(0, r1))
    d2 = d2 + acb(arb(0, r2), arb(0, r2))
    return s0, u * d1, d2


def s_all(u: acb):
    """Enclosures of (s(u), s'(u), s''(u)), s = sin(u/2)/u.

    Closed forms away from 0 (sympy-pinned in paper_chain):
    s'  = cos(u/2)/(2u) - sin(u/2)/u^2
    s'' = -sin(u/2)/(4u) - cos(u/2)/u^2 + 2 sin(u/2)/u^3
    """
    if float(abs(u).upper()) < _SMALL:
        return _s_series(u)
    h = u / 2
    s, c = h.sin(), h.cos()
    u2 = u * u
    v0 = s / u
    v1 = c / (2 * u) - s / u2
    v2 = -s / (4 * u) - c / u2 + 2 * s / (u2 * u)
    return v0, v1, v2


def phipap_all(z: acb):
    """Enclosures of (Phi2(z), Phi2'(z), Phi2''(z)) at the paper window."""
    a0, a1, a2 = s_all(z + S2B)
    b0, b1, b2 = s_all(z - S2B)
    return a0 + b0, a1 + b1, a2 + b2


def phipap_ball(z: acb) -> acb:
    """Enclosure of Phi2(z) alone (the cheap path used by the scans)."""
    a0, _, _ = s_all(z + S2B)
    b0, _, _ = s_all(z - S2B)
    return a0 + b0


#: A = Phi2(0) = 2 sin(sqrt2/2)/sqrt2, as a ball
A_BALL = 2 * (S2B / 2).sin() / S2B


# ---------------------------------------------------------------------------
# the hardened dual
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HardenedPaper:
    """:class:`paper_chain.PaperBandDual` with every evaluation a ball."""

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
        return (phipap_ball(acb(0, 2 * arb(y))).real - A_BALL) / (2 * A_BALL)

    def slack_lo(self, y: float) -> float:
        """LOWER endpoint of 8 sigma^2 + 8 sigma^4."""
        s2 = max(0.0, f_lo(self.sigma2_ball(y)))
        return (8 * s2 + 8 * s2 * s2) * (1 - 1e-9)

    def f_cell_up(self, mid: float, rad: float, y: float) -> float:
        """UPPER endpoint of f = -2W = -4 q / A^2 over [mid-rad, mid+rad]."""
        v = phipap_ball(acb(arb(mid, rad), arb(y)))
        q = v.real * v.real - v.imag * v.imag
        return f_up(-4 * q / (A_BALL * A_BALL))

    # -- the interval cover: bands and off-band emptiness --------------------

    def scan(self, y: float) -> dict:
        """Interval cover of (0, G]: bands, F_k uppers, off-band verdict.

        Pass 1 covers (0, G] in cells of width ``coarse``.  A cell whose
        f enclosure has a nonpositive UPPER endpoint contributes nothing
        anywhere — f <= 0 throughout it, not merely at a grid point —
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

    # -- the curvature witness (paper_chain's test, directed) ----------------

    def curvature_witness(self, y: float) -> dict:
        """Independent witness that no band hides between cover cells.

        q := Re(Phi2)^2 - Im(Phi2)^2, |q''| <= 2(|Phi2'|^2
        + |Phi2||Phi2''|).  For every off-band coarse cell this compares
        the LOWER endpoint of q at the cell centre against the UPPER
        endpoint of (1/8)|q''| h^2 over the whole cell, h = ``coarse``.
        A ratio above 1 everywhere excludes an unresolved interior dip —
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
            p, p1, p2 = phipap_all(acb(arb(mid, r), arb(y)))
            qpp = 2 * (abs(p1) * abs(p1) + abs(p) * abs(p2))
            bound = f_up(qpp) * self.coarse ** 2 / 8
            v = phipap_ball(acb(arb(mid), arb(y)))
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
            v = phipap_ball(acb(arb(mid, r), arb(0))).real / A_BALL
            lo = min(lo, f_lo(v))
        K = max(0.0, lo) ** 2 * (1 - 1e-9) if lo > 0 else 0.0
        self._cache[key] = K
        return K

    # -- the closed-form tail ------------------------------------------------

    def c_im_over_A_up(self, y: float) -> float:
        """UPPER endpoint of C_im(y)/A, the 1/g majorant constant.

        |Im Phi2(g+iy)| <= C_im(y)/|g| by one integration by parts, with
        C_im = 2 phi^2(1/2) sinh(y/2) + TV(phi^2) sinh(y/2)
               + y cosh(y/2) A.  At the paper window phi^2(t) =
        cos(sqrt2 t), so edge = phi^2(1/2) = cos(sqrt2/2) and
        TV(phi^2) = 2(1 - cos(sqrt2/2)) (monotone on each half-window).
        This matches paper_chain.c_im_sharp; the T1 window's version had
        cos^2(sqrt2/2) because its phi^2 was cos^2.
        """
        yb = arb(y)
        sh, ch = (yb / 2).sinh(), (yb / 2).cosh()
        edge = (S2B / 2).cos()
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
        sball = self.sigma2_ball(y)
        slack = self.slack_lo(y)
        rec = self.cap_up(theta, y)
        return {"y": y, "theta": theta, "slack_lo": slack,
                "sigma2_rad": float(sball.rad()),
                "cap_up": rec["cap"], "margin": slack - rec["cap"],
                "closes": slack - rec["cap"] >= 0, "m_star": rec["m_star"],
                "tail": rec["tail"], "bands": rec["bands"]}

    def free_ratio(self, y: float) -> float:
        """Every band granted free at single occupancy, over the slack."""
        bs = self.bands(y)
        num = 2 * (sum(F for _, _, F in bs) * self.infl + self.tail_up(y))
        return num / self.slack_lo(y)

    def multiplicity_threshold(self, y: float) -> float:
        """theta above which double occupancy of the worst band pays:
        it pays when c = 1 - theta < c* = F_1/(2 K_1), i.e. for
        theta > 1 - c*.  (The T1 modules print this with "below";
        their own numbers — m* = 8 at theta = 0.9989 > 0.9919 — show
        the profitable side is ABOVE the threshold.)  Directed so that
        the hardened threshold is LOWER than the float one (F up,
        K down): a lower threshold concedes multiplicity earlier."""
        bs = self.bands(y)
        lo, hi, F = max(bs, key=lambda b: b[2])
        return 1 - F / (2 * self.band_charge_lo(hi - lo))

    def theta_scan(self, ys=(0.02, 0.1, 0.3, 0.49),
                   thetas=(0.99, 0.995, 0.9988, 0.999)):
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
    """The measurement that admits the route: radius in vs radius out.

    At the hunt window this ratio was ~1.8e5 and forced the mean-value
    form (`hardened_direct`); at the T1 MT window it was 1.06 -> 0.0024.
    The paper field is a two-term form and must do at least as well.
    g = 1.05 is the first band; g = 1.414 crosses the removable
    singularity of s(z - sqrt2), exercising the series branch.
    """
    out = []
    for g in (1.05, 1.414, 7.5, 50.0, 300.0):
        v = phipap_ball(acb(arb(g, rad), arb(y)))
        out.append((g, float(v.real.rad()), float(v.real.rad()) / rad))
    return out


def _mp_mid(ball: acb):
    """The EXACT midpoint of an acb ball as an mpmath mpc.

    ``arb.mid().man_exp()`` is exact (mantissa, exponent) integers; the
    caller's working precision must exceed ctx.prec = 128 bits (dps 40
    is ~136) so the reconstruction does not round.
    """
    from mpmath import mp, mpc

    re_m, re_e = ball.real.mid().man_exp()
    im_m, im_e = ball.imag.mid().man_exp()
    return mpc(mp.ldexp(int(re_m), int(re_e)),
               mp.ldexp(int(im_m), int(im_e)))


def singular_branch_vs_mpmath(dps: int = 40):
    """The Taylor branch must enclose the mpmath value of s, s', s''.

    Points inside the series disc |u| < 1, real and complex, including
    a crossing of u = 0.  The comparison runs at mpmath precision
    (exact ball midpoints via man_exp — a double-precision detour would
    drown the 1e-38 radii in conversion noise), and the closed-form
    REFERENCE gets 45 guard digits on top of ``dps``: at u ~ 1e-8 the
    s'' closed form cancels ~24 digits (terms ~1/u^3 summing to -1/24),
    so a dps-40 reference would be wrong at 1e-26 — an error of the
    oracle, not of the ball.  The defect must be <= the radius: a
    reference outside its ball is a critical defect, not a tolerance
    issue.
    """
    from mpmath import mp, mpc

    out = []
    with mp.workdps(dps + 45):
        for u in (1e-6, 0.05, 0.3, 0.7, 0.97, -0.4,
                  complex(0.2, 0.3), complex(-0.6, 0.4),
                  complex(1e-8, 1e-8)):
            um = mpc(u)
            s_ref = mp.sin(um / 2) / um
            d1_ref = mp.cos(um / 2) / (2 * um) - mp.sin(um / 2) / um ** 2
            d2_ref = (-mp.sin(um / 2) / (4 * um) - mp.cos(um / 2) / um ** 2
                      + 2 * mp.sin(um / 2) / um ** 3)
            uz = acb(arb(complex(u).real), arb(complex(u).imag))
            balls = _s_series(uz)
            for name, ball, ref in (("s", balls[0], s_ref),
                                    ("d1", balls[1], d1_ref),
                                    ("d2", balls[2], d2_ref)):
                defect = float(abs(_mp_mid(ball) - ref))
                radius = math.hypot(float(ball.real.rad()),
                                    float(ball.imag.rad()))
                out.append({"u": u, "which": name, "defect": defect,
                            "rad": radius, "inside": defect <= radius})
    return out


def cross_backend_spot_check(hb: HardenedPaper, dps: int = 40):
    """flint enclosure midpoints vs mpmath at three (band, depth) points.

    The points are actual band centres from the hardened scan.  The
    comparison runs at mpmath precision (exact ball midpoints via
    man_exp).  A midpoint-to-mpmath distance beyond the enclosure
    radius is a critical defect and is reported as such — never
    widened away.
    """
    from mpmath import mp, mpc, sqrt

    picks = []
    for y, band_idx in ((0.02, 0), (0.3, 4), (0.49, -1)):
        bs = hb.bands(y)
        lo, hi, _ = bs[band_idx]
        picks.append(((lo + hi) / 2, y))
    out = []
    with mp.workdps(dps):
        s2m = sqrt(2)
        for g, y in picks:
            z = mpc(g, y)
            ref = (mp.sin((z + s2m) / 2) / (z + s2m)
                   + mp.sin((z - s2m) / 2) / (z - s2m))
            ball = phipap_ball(acb(arb(g), arb(y)))
            defect = float(abs(_mp_mid(ball) - ref))
            radius = math.hypot(float(ball.real.rad()),
                                float(ball.imag.rad()))
            out.append({"g": g, "y": y, "defect": defect, "rad": radius,
                        "inside": defect <= radius})
    return out


def ball_vs_float(hb: HardenedPaper, theta: float = 0.99,
                  ys=(0.02, 0.1, 0.3, 0.49)):
    """Hardened cap vs paper_chain's float cap at matched (theta, y).

    The T1 experience: the hardened cap came in BELOW float because the
    cover removes the float pass's blanket Lipschitz margins.  A
    hardened cap LARGER than float is not forbidden, but a large
    loosening would suggest a defect; the ratio is reported either way.
    """
    from paper_chain import PaperBandDual

    bd = PaperBandDual(G=hb.G)
    out = []
    for y in ys:
        cf = bd.cap(theta, y)["cap"]
        ch = hb.cap_up(theta, y)["cap"]
        out.append({"y": y, "cap_float": cf, "cap_hard": ch,
                    "ratio": ch / cf, "tighter": ch <= cf})
    return out


def theta_one_must_fail(hb: HardenedPaper, y: float = 0.49):
    """No charge, unbounded multiplicity: the cap must diverge."""
    return hb.cap_up(1.0, y)["cap"]


def audit():
    hb = HardenedPaper()
    print("= the route: interval-argument amplification at the paper field =",
          flush=True)
    for g, rad, amp in interval_amplification():
        note = "  (series branch: crosses u = 0)" if abs(g - 1.414) < 1e-9 \
            else ""
        print(f"  g={g:6.3f}: rad(Re Phi2) = {rad:.3e}   "
              f"amplification {amp:.4f}{note}")
    print("  (hunt window: ~1.8e5, mean-value form forced; T1 MT window:")
    print("   1.06 -> 0.0024; here the interval-argument cover is used)")

    print("= the singular branch vs mpmath (dps 40) =", flush=True)
    sb = singular_branch_vs_mpmath()
    worst = max(r["defect"] for r in sb)
    all_in = all(r["inside"] for r in sb)
    print(f"  {len(sb)} point/order checks: worst midpoint defect "
          f"{worst:.2e}, every reference inside its ball: {all_in}")

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

    print("= the hardened multiplicity threshold (what binds) =", flush=True)
    for y in (0.02, 0.1, 0.3, 0.49):
        print(f"  y={y}: double occupancy of the worst band pays once "
              f"theta exceeds {hb.multiplicity_threshold(y):.6f}")

    print("= the hardened theta scan =", flush=True)
    star, margins = hb.theta_scan()
    for th, (m, arg) in margins.items():
        print(f"  theta={th}: worst margin {m:+.6e} at y={arg}  "
              f"{'ok' if m >= 0 else 'FAILS'}")
    print(f"  largest scanned theta surviving the hardened pass = {star}"
          f"    (float paper_chain: 0.995; hardened T1 window: 0.9988)")

    if star is not None:
        print(f"= per-depth verdict at theta = {star} =", flush=True)
        print("    y       slack >=      cap <=        margin >=     "
              "sigma2 rad     m*")
        for y in (0.02, 0.1, 0.3, 0.49):
            r = hb.verdict(star, y)
            print(f"  {y:5.2f}   {r['slack_lo']:.6e}  {r['cap_up']:.6e}  "
                  f"{r['margin']:+.6e}   {r['sigma2_rad']:.2e}   "
                  f"{r['m_star']}   {'ok' if r['closes'] else 'FAILS'}")

    print("= hardened vs float at theta = 0.99 =", flush=True)
    for row in ball_vs_float(hb):
        tag = "tighter" if row["tighter"] else "LOOSER"
        print(f"  y={row['y']}: hardened cap {row['cap_hard']:.6e} vs float "
              f"{row['cap_float']:.6e}  ratio {row['ratio']:.4f}  ({tag})")

    print("= cross-backend spot check (flint vs mpmath dps 40) =", flush=True)
    for row in cross_backend_spot_check(hb):
        tag = "ok" if row["inside"] else "CRITICAL DEFECT"
        print(f"  g={row['g']:.4f} y={row['y']}: |mid - mpmath| = "
              f"{row['defect']:.2e}  <= rad {row['rad']:.2e}: {tag}")

    cap1 = theta_one_must_fail(hb)
    print(f"= theta = 1: cap = {cap1} (diverges as it must: "
          f"{not math.isfinite(cap1)}) =")


if __name__ == "__main__":
    audit()
