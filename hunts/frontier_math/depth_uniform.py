"""Depth-UNIFORM retention at the paper field: the missing universal quantifier.

THE GAP THIS CLOSES.  The paper-window retention chain (``paper_chain.py``,
``hardened_paper.py``, ``band_certificate.py``, ``paper_joint.py``) establishes
theta* = 0.995 at FOUR SAMPLED DEPTHS, y in {0.02, 0.1, 0.3, 0.49}.  An
off-line zero pair sits at an arbitrary depth y in (0, 1/2).  Sampled depths do
not establish the bound for all y, so the hypothesis

    D(X) >= theta* R(X)   for all admissible configurations

— which is what the kernel-checked composition corollary consumes — does not
follow from those four numbers.  That is a missing universal quantifier over
y, not a formalization issue.  This module quantifies over depth CELLS instead
of depth points, which is the construction ``counting_bound.py`` already uses
at the T1 (hunt) window, ported here with constants re-derived for the paper's
field.

THE FIELD.  The paper's window has phi^2(u) = cos(sqrt2 u) on [-1/2, 1/2]
(``paper_pin.py``), so with p(u) := cos(sqrt2 u),

    Phi2(z) = int_{-1/2}^{1/2} p(u) e^{izu} du = s(z+sqrt2) + s(z-sqrt2),
    s(u) = sin(u/2)/u,     A := Phi2(0) = 2 sin(sqrt2/2)/sqrt2 = 0.9187253699.

Splitting z = g + iy and using that p is even (odd parts integrate away):

    C(g,y) := Re Phi2(g+iy) = int p(u) cosh(yu) cos(gu) du,
    S(g,y) := -Im Phi2(g+iy) = int p(u) sinh(yu) sin(gu) du,

so the LAW L damage is  f(g,y) = -2W = 4 (S^2 - C^2) / A^2  and the pair
budget is  slack(y) = 8 sigma^2(y) + 8 sigma^4(y),
sigma^2(y) = (Phi2(2iy) - A)/(2A) = (1/A) int p sinh^2(yu) du.

THE FOUR DERIVATIVE BOUNDS, DERIVED FOR THIS FIELD.  Differentiating under the
integral sign (integrand entire, interval compact):

    dC/dg = -int u p cosh(yu) sin(gu) du    dC/dy = int u p sinh(yu) cos(gu) du
    dS/dg =  int u p sinh(yu) cos(gu) du    dS/dy = int u p cosh(yu) sin(gu) du

so dC/dy = dS/dg and dS/dy = -dC/dg exactly (Cauchy-Riemann for the
holomorphic Phi2), and only two magnitudes need bounding.  Each is bounded two
ways; both are valid, so the module uses the smaller:

  (i)  |dS/dg| = |dC/dy| <= int |u| p |sinh(yu)| du
       - Cauchy-Schwarz, the shape ``counting_bound`` uses:  |u| <= 1/2 (the
         box HALF-WIDTH; at the hunt window that factor is L/2 = 4, here it is
         1/2), then <= (1/2) sqrt( int p . int p sinh^2(yu) ) = (1/2) A sigma(y)
         because int p sinh^2(yu) du = A sigma^2(y) by the definition above.
       - direct majorant: |sinh(yu)| <= sinh(y/2) on |u| <= 1/2, giving
         sinh(y/2) L1 with L1 := int |u| p(u) du.
       At y = 1/2 these are 0.06432 and 0.05548: the direct majorant wins
       everywhere on (0, 1/2], and both are correct.

  (ii) |dC/dg| = |dS/dy| <= int |u| p cosh(yu) du
       - Cauchy-Schwarz / |u| <= 1/2:  <= (1/2) int p cosh(yu) du = (1/2) A E(y)
         with E(y) = Phi2(iy)/A >= 1, the depth inflation.
       - direct majorant: cosh(yu) <= cosh(y/2), giving cosh(y/2) L1.
       At y = 1/2: 0.46392 vs 0.22651 -- again the direct majorant is sharper.

  (iii) curvature, for the second-order Taylor remainder:
       |Phi2''(g+iy)| = |int u^2 p e^{i(g+iy)u} du| <= int u^2 p e^{-yu} du
       = int u^2 p cosh(yu) du = -Phi2''(iy) =: M(y),  a closed form
       (0.07250 at y = 1/2), and C, S are harmonic with Hessians
       [[Re Phi2'', -Im Phi2''], [-Im Phi2'', -Re Phi2'']] up to sign, whose
       operator norm is exactly |Phi2''|.

  Both (i) and (ii) are increasing in y (sigma, E, sinh, cosh all are), so a
  depth cell may take them at its DEEP lip y_hi.  ``derivative_bound_control``
  checks all four against central differences at scattered (g, y) and reports
  how close each comes to being attained; nothing below is used before that
  control has run.

ONE-SIDED CELL SUPS.  For a fine bin (g_c +- rg) x (y_m +- ry) inside a depth
cell, the module inflates S and deflates C by the SMALLER of

    global:  Lam_Sg(y_hi) rg + Lam_Sy(y_hi) ry      (resp. C)
    local :  |dS/dg(c)| rg + |dS/dy(c)| ry + (1/2) M(y_hi) (rg^2 + ry^2)

(the local form is Taylor-Lagrange with the exact centre gradient, which is
what keeps the far field from being smeared: at g ~ 100 the global constant
overstates the true slope by ~50x).  Then

    F_up(bin) = 4 ( S_bar^2 - C_und^2 )_+ / A^2   >=   sup_bin f_+ ,

which makes the cover complete BY CONSTRUCTION: a bin with F_up = 0 carries no
damage anywhere inside it, so no band can hide between grid points and no
``no_missed_band`` allowance is needed (``paper_chain`` needs one because its
band maxima come from raw grid values plus a band-level slope margin).

THE CAPACITY, unchanged from ``paper_chain.cap``: contiguous F_up > 0 bins are
grouped into bands; a band of width w charges K = min_{[0,w]} omega^2 for each
ordered same-band pair (cross-band charges dropped -- omega^2 >= 0, so that is
one-sided); per band B = F if F <= 2cK else (F + cK)^2/(4cK), c = 1 - theta;
beyond G the one-integration-by-parts majorant |S| <= c_im(y)/|g| gives
F <= 4 (c_im/(A g))^2 and bands at least P apart sum to
4 (c_im/A)^2 (1/G^2 + 1/(P G)).

THE SHALLOW CELL, which is the part with no analogue in ``counting_bound``.  A
geometric ladder cannot reach y = 0 in finitely many cells, and
``counting_bound.depth_ladder`` indeed starts at y_min = 0.002 and leaves
(0, 0.002) uncovered -- the same missing quantifier, one order of magnitude
lower.  Here the shallow end is closed by homogeneity instead of by cells.
Both sides vanish like y^2, so normalise by y^2:

    |S(g,y)|/y <= |Phi2'(g)| + eps_S,     eps_S := 2 L2 (cosh(y0/2) - 1),
    |C(g,y)|   >= |Phi2(g)|  - eps_C,     eps_C := 2 L1 (cosh(y0/2) - 1),

for all 0 < y <= y0, by integrating dS/dy = -Re Phi2'(g+iy) resp.
dC/dy = dS/dg from t = 0 and bounding the integrands with (i)/(ii) and
|Im Phi2''| <= sinh(y/2) L2.  Since 1/y^2 >= 1/y0^2 on the cell,

    f_+(g,y) <= y^2 F_hat(g),   F_hat := 4 ( S_hat^2 - (C_und/y0)^2 )_+ / A^2 ,

and B is convex with B(0) = 0, hence B(lambda F) <= lambda B(F) for lambda in
[0,1] (checked directly in ``convexity_control``), so the whole capacity scales:

    cap(y) <= (y^2/y0^2) cap_hat  for every y in (0, y0].

The budget scales the other way: sigma^2(y)/y^2 = (1/A) int p (sinh(yu)/y)^2 du
is INCREASING in y (sinh(t)/t is), so slack(y)/y^2 >= 8 L2/A = 0.6199944 on the
whole cell, its y -> 0+ limit.  The shallow test is therefore
cap_hat/y0^2 <= 8 L2/A, one finite inequality for an interval of depths that
contains no smallest point.

WORST CORNER.  sigma^2 and E are both increasing in y, so on a cell the SLACK
is smallest at the shallow lip y_lo and every damage-side constant is largest
at the deep lip y_hi; the module evaluates them there.  ``monotonicity_control``
measures both directions rather than asserting them.

WHAT COMES OUT (audit settings G = 200, step = 0.0025, 4 slices, 18 cells).
Every cell closes at theta = 0.995 -- the same grid point the four sampled
depths give -- with worst relative margin +0.173 on the deepest cell
[0.43666, 0.5], the only cells that bind being the three deep ones where the
square completion turns on (m* = 2, 2, 3).  Off the requested grid the
construction still closes at 0.996 (+0.080) and fails at 0.997 (-0.078), on
the same deepest cell; ``band_certificate.py``'s rational cover closes at
997/1000 at the four sampled depths, so the depth-uniform version costs one
grid step at the far end and nothing at 0.995.

WHAT IS AND IS NOT COVERED.

* This is the SINGLE-PAIR layer.  ``paper_joint.py``'s multi-pair (pair-pair)
  layer is still evaluated on configuration families at a handful of depth
  VALUES (0.02, 0.1, 0.3, 0.45, 0.49); closing the depth quantifier here does
  not close it there, and the joint layer's own depth quantifier remains open.
* Double precision throughout.  The arb-enclosure pass (``hardened_paper.py``)
  and the rational-cover pass (``band_certificate.py``) exist for the four
  sampled depths only; re-running either over these cells is the named next
  hardening step.
* The band-period input P for the beyond-G tail is measured on the resolved
  region and assumed to persist beyond it, exactly as in
  ``paper_chain.tail_sum``.  Inherited, not re-established here.
* Nothing in this module is evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/depth_uniform.py`` (~10 s).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    A,
    S2,
    PaperChain,
    phipap,
    phipap_d1,
    phipap_d2,
)

# ---------------------------------------------------------------------------
# window constants, in closed form (quadrature only ever checks them)
# ---------------------------------------------------------------------------

#: phi^2(1/2) = cos(sqrt2/2), the edge value of the box profile
EDGE = math.cos(S2 / 2)
#: total variation of phi^2 on [-1/2, 1/2] (monotone on each half-window)
TV = 2 * (1 - EDGE)
#: L1 = int_{-1/2}^{1/2} |u| cos(sqrt2 u) du
L1 = 2 * (math.cos(S2 / 2) / S2**2 + math.sin(S2 / 2) / (2 * S2) - 1 / S2**2)
#: L2 = int_{-1/2}^{1/2} u^2 cos(sqrt2 u) du
L2 = 2 * (math.cos(S2 / 2) / S2**2 + (0.25 / S2 - 2 / S2**3) * math.sin(S2 / 2))
#: the y-normalised one-integration-by-parts constant: |S(g,y)| <= y C_IM_UNIT
#: cosh(y/2) / |g|  (see c_im_unit_control)
C_IM_UNIT = EDGE + TV / 2 + A
#: slack(y)/y^2 at y -> 0+, the shallow cell's budget
NSLACK_0 = 8 * L2 / A

_PC = PaperChain()


def sigma(y: float) -> float:
    """sqrt of sigma^2(y) = (1/A) int p sinh^2(yu) du."""
    return math.sqrt(_PC.sigma2(y))


def E(y: float) -> float:
    """Depth inflation Phi2(iy)/A = (1/A) int p cosh(yu) du >= 1."""
    return _PC.E(y)


def nslack(y: float) -> float:
    """slack(y)/y^2, increasing in y, limit NSLACK_0 at y -> 0+."""
    return _PC.slack(y) / (y * y)


# ---------------------------------------------------------------------------
# the four derivative bounds (see the module docstring for each derivation)
# ---------------------------------------------------------------------------


def lam_Cg(y: float) -> float:
    """|dC/dg| = |dS/dy| <= min( (1/2) A E(y), cosh(y/2) L1 )."""
    return min(0.5 * A * E(y), math.cosh(y / 2) * L1)


def lam_Sg(y: float) -> float:
    """|dS/dg| = |dC/dy| <= min( (1/2) A sigma(y), sinh(y/2) L1 )."""
    return min(0.5 * A * sigma(y), math.sinh(y / 2) * L1)


lam_Sy = lam_Cg  # dS/dy = -dC/dg
lam_Cy = lam_Sg  # dC/dy =  dS/dg


def curvature(y: float) -> float:
    """sup_g |Phi2''(g+iy)| <= int u^2 p cosh(yu) du = -Phi2''(iy)."""
    return -float(phipap_d2(1j * y).real)


def c_im(y: float) -> float:
    """|S(g,y)| <= c_im(y)/|g|, one integration by parts (paper_chain's)."""
    sh, ch = math.sinh(y / 2), math.cosh(y / 2)
    return 2 * EDGE * sh + TV * sh + y * ch * A


def c_im_normalised(y0: float) -> float:
    """|S(g,y)| <= y cosh(y0/2) C_IM_UNIT / |g| for every y <= y0.

    sinh(y/2) <= (y/2) cosh(y0/2) turns c_im into a multiple of y:
    2 EDGE (y/2) + TV (y/2) + y A, all times cosh(y0/2).
    """
    return math.cosh(y0 / 2) * C_IM_UNIT


# ---------------------------------------------------------------------------
# the depth-uniform dual
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DepthUniform:
    """Band dual at the paper field, quantified over depth cells."""

    #: end of the resolved region; beyond it the 1/g^2 majorant takes over
    G: float = 200.0
    #: fine bin width on the offset axis
    step: float = 0.0025
    #: depth slices per regular cell (the local Taylor form is first-order
    #: exact in y, so few are needed; the count is a precision knob)
    slices: int = 4
    #: top of the shallow (homogeneity) cell; the ladder starts here
    y0: float = 0.05
    #: number of geometric cells covering [y0, y_max]
    n_cells: int = 17
    y_max: float = 0.5
    #: grid step for the repulsion-floor minimisation
    charge_step: float = 0.001
    #: memo for band_charge (keyed by the rounded-up width); not a parameter
    _charge_memo: dict = field(default_factory=dict, repr=False, compare=False)

    # -- grids ---------------------------------------------------------------

    def bin_centres(self) -> np.ndarray:
        n = int(round(self.G / self.step))
        return (np.arange(n) + 0.5) * self.step

    def cell_edges(self) -> list:
        """Exact geometric edges y0 .. y_max; endpoints are shared objects, so
        the tiling has no gap by construction (see the tiling control)."""
        r = (self.y_max / self.y0) ** (1.0 / self.n_cells)
        edges = [self.y0 * r**k for k in range(self.n_cells)]
        edges.append(self.y_max)
        return edges

    def depth_cells(self) -> list:
        """(y_lo, y_hi, kind) covering (0, y_max]; kind shallow/regular."""
        edges = self.cell_edges()
        cells = [(0.0, self.y0, "shallow")]
        cells += [(edges[k], edges[k + 1], "regular")
                  for k in range(len(edges) - 1)]
        return cells

    # -- one-sided damage sups ----------------------------------------------

    def cell_damage_sups(self, y_lo: float, y_hi: float) -> np.ndarray:
        """Per-bin one-sided sup of f_+ over bin x [y_lo, y_hi]."""
        gs = self.bin_centres()
        rg = self.step / 2
        dy = (y_hi - y_lo) / self.slices
        ry = dy / 2
        M = curvature(y_hi)
        lcg, lsg = lam_Cg(y_hi), lam_Sg(y_hi)
        quad = 0.5 * M * (rg * rg + ry * ry)
        out = np.zeros_like(gs)
        for s in range(self.slices):
            ym = y_lo + (s + 0.5) * dy if dy > 0 else y_lo
            z = gs + 1j * ym
            v = phipap(z)
            d1 = phipap_d1(z)
            C, S = v.real, -v.imag
            dCdg, dSdg = d1.real, -d1.imag
            dCdy, dSdy = dSdg, -dCdg
            inf_S = np.minimum(lsg * rg + lcg * ry,
                               np.abs(dSdg) * rg + np.abs(dSdy) * ry + quad)
            inf_C = np.minimum(lcg * rg + lsg * ry,
                               np.abs(dCdg) * rg + np.abs(dCdy) * ry + quad)
            S_bar = np.abs(S) + inf_S
            C_und = np.maximum(0.0, np.abs(C) - inf_C)
            F = np.maximum(0.0, 4 * (S_bar * S_bar - C_und * C_und)) / A**2
            out = np.maximum(out, F)
        return out

    def shallow_damage_sups(self) -> np.ndarray:
        """Per-bin F_hat with f_+(g,y) <= y^2 F_hat for all 0 < y <= y0."""
        gs = self.bin_centres()
        rg = self.step / 2
        y0 = self.y0
        ch = math.cosh(y0 / 2)
        eps_S = 2 * L2 * (ch - 1)
        eps_C = 2 * L1 * (ch - 1)
        chat = c_im_normalised(y0)
        v = phipap(gs.astype(complex))
        d1 = phipap_d1(gs.astype(complex))
        P0 = np.abs(v.real)                      # |Phi2(g)|  on the real axis
        P1 = np.abs(d1.real)                     # |Phi2'(g)| on the real axis
        slope = np.minimum(L1, P1 + rg * L2)     # sup_bin |Phi2'|
        S_hat = np.minimum(P1 + rg * L2 + eps_S,
                           chat / np.maximum(gs - rg, 1e-12))
        C_und = np.maximum(0.0, P0 - rg * slope - eps_C)
        return np.maximum(0.0, 4 * (S_hat * S_hat - (C_und / y0) ** 2)) / A**2

    # -- bands, charges, capacity -------------------------------------------

    def bands(self, F: np.ndarray) -> list:
        """Contiguous F > 0 bins grouped into (lo, hi, F_max) bands."""
        gs = self.bin_centres()
        idx = np.where(F > 0)[0]
        if len(idx) == 0:
            return []
        out = []
        for gr in np.split(idx, np.where(np.diff(idx) > 1)[0] + 1):
            out.append((float(gs[gr[0]]) - self.step / 2,
                        float(gs[gr[-1]]) + self.step / 2,
                        float(F[gr].max())))
        return out

    def band_charge(self, width: float) -> float:
        """One-sided min of omega^2 = (Re Phi2(r)/A)^2 over [0, width].

        Grid minimum minus the Lipschitz margin (L1/A) * charge_step, which
        covers every point between grid points (|d/dr Re Phi2| <= L1).  The
        width is rounded UP to the charge grid before the memo lookup, so a
        cached value always belongs to a width at least the one asked for --
        one-sided, because omega^2's minimum only falls as the width grows.
        """
        key = int(math.ceil(width / self.charge_step - 1e-12))
        hit = self._charge_memo.get(key)
        if hit is None:
            rs = np.arange(0.0, key * self.charge_step + self.charge_step,
                           self.charge_step)
            lo = float(np.min(phipap(rs.astype(complex)).real / A))
            lo -= (L1 / A) * self.charge_step
            hit = max(0.0, lo) ** 2
            self._charge_memo[key] = hit
        return hit

    @staticmethod
    def band_period(bs: list) -> float:
        if len(bs) < 3:
            return 2 * math.pi
        cs = [(lo + hi) / 2 for lo, hi, _ in bs]
        return min(cs[i + 1] - cs[i] for i in range(len(cs) - 1))

    def capacity(self, theta: float, bs: list, tail: float) -> dict:
        """paper_chain.cap's capacity, per band, with the tail appended."""
        c = 1 - theta
        if not bs:
            return {"cap": 2 * tail, "bands": 0, "m_star": 0, "K_min": None}
        total, K_min, m_star = 0.0, math.inf, 1
        for lo, hi, F in bs:
            K = self.band_charge(hi - lo)
            K_min = min(K_min, K)
            if c <= 0 or K <= 0:
                return {"cap": math.inf, "bands": len(bs), "m_star": None,
                        "K_min": K_min}
            if F <= 2 * c * K:
                B, m = F, 1
            else:
                B = (F + c * K) ** 2 / (4 * c * K)
                m = int(round((F + c * K) / (2 * c * K)))
            total += B
            m_star = max(m_star, m)
        return {"cap": 2 * (total + tail), "bands": len(bs),
                "m_star": m_star, "K_min": K_min}

    # -- the two cell kinds --------------------------------------------------

    def cell_profile(self, y_lo: float, y_hi: float, kind: str) -> dict:
        """Everything about a depth cell that does NOT depend on theta.

        ``scale`` converts the profile's band values into the units the
        verdict compares: 1 for a regular cell, y0^2 for the shallow cell
        (whose bands are y^2-normalised).
        """
        if kind == "shallow":
            F = self.shallow_damage_sups()
            scale = self.y0 ** 2
            chat = c_im_normalised(self.y0)
            tail_const = 4 * chat * chat / A**2
            slack_lo = NSLACK_0
        else:
            F = self.cell_damage_sups(y_lo, y_hi)
            scale = 1.0
            Ct = c_im(y_hi) / A
            tail_const = 4 * Ct * Ct
            slack_lo = _PC.slack(y_lo)
        bs = self.bands(F)
        P = self.band_period(bs)
        return {
            "kind": kind, "y_lo": y_lo, "y_hi": y_hi, "scale": scale,
            "bands_raw": bs, "period": P,
            "tail": scale * tail_const * (1 / self.G**2 + 1 / (P * self.G)),
            "F_at_G": scale * tail_const / self.G**2,
            "slack_lo": slack_lo,
        }

    def cell_verdict(self, theta: float, prof: dict) -> dict:
        scaled = [(lo, hi, prof["scale"] * f)
                  for lo, hi, f in prof["bands_raw"]]
        rec = self.capacity(theta, scaled, prof["tail"])
        K_min = rec["K_min"] if rec["K_min"] is not None else 1.0
        cap_up = rec["cap"] / prof["scale"]
        slack_lo = prof["slack_lo"]
        rec.update({
            "kind": prof["kind"], "y_lo": prof["y_lo"], "y_hi": prof["y_hi"],
            "cap_up": cap_up, "slack_lo": slack_lo,
            "tail": 2 * prof["tail"] / prof["scale"], "period": prof["period"],
            "margin": slack_lo - cap_up,
            "rel_margin": (slack_lo - cap_up) / slack_lo,
            "tail_single_occupancy": bool(
                prof["F_at_G"] <= 2 * (1 - theta) * K_min),
        })
        return rec

    def regular_cell(self, theta: float, y_lo: float, y_hi: float) -> dict:
        return self.cell_verdict(
            theta, self.cell_profile(y_lo, y_hi, "regular"))

    def shallow_cell(self, theta: float) -> dict:
        """The homogeneity cell (0, y0]: both sides divided by y^2."""
        rec = self.cell_verdict(
            theta, self.cell_profile(0.0, self.y0, "shallow"))
        ch = math.cosh(self.y0 / 2)
        rec["eps_S"] = 2 * L2 * (ch - 1)
        rec["eps_C"] = 2 * L1 * (ch - 1)
        return rec

    # -- the scan ------------------------------------------------------------

    def profiles(self) -> list:
        """One theta-free profile per depth cell, in depth order."""
        return [self.cell_profile(*cell) for cell in self.depth_cells()]

    def scan(self, theta: float, profs: list | None = None) -> list:
        """Every depth cell at one theta; cap_up vs slack_lo per cell.

        The shallow row is in y^2-normalised units (cap/y^2 vs slack/y^2);
        every other row is in raw units.  Both are one-sided comparisons of
        the same inequality.
        """
        return [self.cell_verdict(theta, p)
                for p in (profs or self.profiles())]

    def secured_theta(self, thetas=(0.9, 0.95, 0.99, 0.995),
                      profs: list | None = None) -> tuple:
        """Largest grid theta closing EVERY depth cell (so every y in (0,1/2]).

        The profiles are theta-free, so the field work is done once and the
        whole grid is scored on it.
        """
        profs = profs or self.profiles()
        star, table = None, {}
        for theta in thetas:
            rows = self.scan(theta, profs)
            binder = min(rows, key=lambda r: r["rel_margin"])
            tail_ok = all(r["tail_single_occupancy"] for r in rows)
            table[theta] = {
                "worst_rel_margin": binder["rel_margin"],
                "binding_cell": (binder["y_lo"], binder["y_hi"]),
                # a cell whose beyond-G bands could hold two points is not a
                # closed cell: the tail majorant assumes single occupancy, so
                # the flag is a precondition of the margin, not a footnote
                "all_closed": tail_ok and all(r["margin"] >= 0 for r in rows),
                "tail_ok": tail_ok,
            }
            if table[theta]["all_closed"]:
                star = theta
        return star, table


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def _CS(g, y):
    v = phipap(np.array([complex(g, y)]))
    return float(v.real[0]), float(-v.imag[0])


def derivative_bound_control(n: int = 24, h: float = 1e-5,
                             y_max: float = 0.5) -> dict:
    """The four bounds vs central differences at scattered (g, y).

    Reports, for each bound, the worst RATIO |numeric derivative| / bound over
    the sample (must stay below 1) and the worst defect of the closed-form
    identification against the same differences.
    """
    rng = np.random.default_rng(20260812)
    gs = np.concatenate([rng.uniform(0.05, 3.0, n // 3),
                         rng.uniform(3.0, 40.0, n // 3),
                         rng.uniform(40.0, 200.0, n - 2 * (n // 3))])
    ys = rng.uniform(0.002, y_max, n)
    worst = {k: 0.0 for k in ("Cg", "Sg", "Cy", "Sy")}
    ident = 0.0
    for g, y in zip(gs, ys):
        Cp, Sp = _CS(g + h, y)
        Cm, Sm = _CS(g - h, y)
        Cu, Su = _CS(g, y + h)
        Cd, Sd = _CS(g, y - h)
        dCdg, dSdg = (Cp - Cm) / (2 * h), (Sp - Sm) / (2 * h)
        dCdy, dSdy = (Cu - Cd) / (2 * h), (Su - Sd) / (2 * h)
        worst["Cg"] = max(worst["Cg"], abs(dCdg) / lam_Cg(y))
        worst["Sg"] = max(worst["Sg"], abs(dSdg) / lam_Sg(y))
        worst["Cy"] = max(worst["Cy"], abs(dCdy) / lam_Cy(y))
        worst["Sy"] = max(worst["Sy"], abs(dSdy) / lam_Sy(y))
        d1 = complex(phipap_d1(np.array([complex(g, y)]))[0])
        ident = max(ident, abs(d1.real - dCdg), abs(-d1.imag - dSdg),
                    abs(-d1.imag - dCdy), abs(-d1.real - dSdy))
    return {"worst_ratio": worst, "identification_defect": ident,
            "n_points": len(gs)}


def bound_attainment(y: float, g_max: float = 60.0,
                     step: float = 0.002) -> dict:
    """How close each bound comes to being attained at one depth: the scan
    maximum of each |derivative| divided by its constant.  A ratio near 1 is a
    sharp constant; a tiny ratio would say the bound is decorative."""
    gs = np.arange(step, g_max, step)
    d1 = phipap_d1(gs + 1j * y)
    dCdg, dSdg = np.abs(d1.real), np.abs(d1.imag)
    return {"Cg": float(dCdg.max()) / lam_Cg(y),
            "Sg": float(dSdg.max()) / lam_Sg(y)}


def curvature_bound_control(n: int = 16) -> float:
    """Worst |Phi2''(g+iy)| / curvature(y) over scattered points; must be <1."""
    rng = np.random.default_rng(11)
    worst = 0.0
    for _ in range(n):
        g = float(rng.uniform(0.05, 120.0))
        y = float(rng.uniform(0.002, 0.5))
        v = abs(complex(phipap_d2(np.array([complex(g, y)]))[0]))
        worst = max(worst, v / curvature(y))
    return worst


def c_im_unit_control(y0: float = 0.5, n: int = 40) -> float:
    """|S(g,y)| g / (y cosh(y0/2) C_IM_UNIT) over a scan: must stay below 1."""
    gs = np.arange(1.0, 200.0, 0.05)
    worst = 0.0
    for y in np.linspace(0.002, y0, n):
        S = -phipap(gs + 1j * y).imag
        worst = max(worst, float((np.abs(S) * gs).max())
                    / (y * math.cosh(y0 / 2) * C_IM_UNIT))
    return worst


def monotonicity_control(n: int = 200) -> dict:
    """sigma^2, E, c_im increasing in y (so the deep lip is the damage-side
    corner) and slack/y^2 increasing (so the SHALLOW lip is the budget-side
    corner, and NSLACK_0 is its floor)."""
    ys = np.linspace(1e-4, 0.5, n)
    s2 = np.array([_PC.sigma2(float(y)) for y in ys])
    Es = np.array([E(float(y)) for y in ys])
    cims = np.array([c_im(float(y)) for y in ys])
    ns = np.array([nslack(float(y)) for y in ys])
    return {
        "sigma2_increasing": bool(np.all(np.diff(s2) > 0)),
        "E_increasing": bool(np.all(np.diff(Es) > 0)),
        "c_im_increasing": bool(np.all(np.diff(cims) > 0)),
        "nslack_increasing": bool(np.all(np.diff(ns) > 0)),
        "nslack_floor": float(ns.min()),
        "NSLACK_0": NSLACK_0,
        "nslack_at_half": float(ns[-1]),
    }


def convexity_control(n: int = 40) -> float:
    """B(lambda F) <= lambda B(F) for lambda in [0,1]: the step the shallow
    cell's y^2-scaling rests on.  Returns the worst violation (must be <= 0)."""
    rng = np.random.default_rng(5)
    worst = -math.inf
    for _ in range(n):
        cK = float(rng.uniform(1e-4, 0.05))
        F = float(rng.uniform(0.0, 0.2))
        lam = float(rng.uniform(0.0, 1.0))

        def B(x):
            return x if x <= 2 * cK else (x + cK) ** 2 / (4 * cK)

        worst = max(worst, B(lam * F) - lam * B(F))
    return worst


def _excess_report(f: np.ndarray, cap: np.ndarray, worst: float,
                   worst_rel: float) -> tuple:
    """Track max(true - cap) and, where the field is live, max(true/cap - 1)."""
    worst = max(worst, float((f - cap).max()))
    live = f > 0
    if np.any(live):
        worst_rel = max(worst_rel,
                        float((f[live]
                               / np.maximum(cap[live], 1e-300)).max()) - 1)
    return worst, worst_rel


def one_sidedness_control(du: DepthUniform, y_lo: float, y_hi: float,
                          g_lo: float = 5.0, g_hi: float = 45.0,
                          sub: int = 7) -> dict:
    """The cell sups really do majorise the field inside the cell.

    Samples f_+ on a sub-grid of each bin at several depths in the cell and
    reports the worst (true - F_up), which must be <= 0, plus the worst
    (true/F_up - 1) over the bins where the field is live -- the second number
    is the one that carries information, since most bins have both sides zero.
    """
    F = du.cell_damage_sups(y_lo, y_hi)
    gs = du.bin_centres()
    sel = np.where((gs >= g_lo) & (gs <= g_hi))[0]
    worst, worst_rel = -math.inf, -math.inf
    for frac in np.linspace(0.0, 1.0, 5):
        y = y_lo + frac * (y_hi - y_lo)
        for k in range(sub):
            off = (-0.5 + k / (sub - 1)) * du.step
            v = phipap(gs[sel] + off + 1j * y)
            f = np.maximum(0.0, 4 * (v.imag**2 - v.real**2)) / A**2
            worst, worst_rel = _excess_report(f, F[sel], worst, worst_rel)
    return {"worst_excess": worst, "worst_rel_excess": worst_rel,
            "one_sided": worst <= 0.0}


def shallow_one_sidedness_control(du: DepthUniform, ys=(0.002, 0.01, 0.03),
                                  g_lo: float = 5.0, g_hi: float = 45.0,
                                  sub: int = 7) -> dict:
    """f_+(g,y) <= y^2 F_hat(g) at depths inside the shallow cell."""
    F = du.shallow_damage_sups()
    gs = du.bin_centres()
    sel = np.where((gs >= g_lo) & (gs <= g_hi))[0]
    worst, worst_rel = -math.inf, -math.inf
    for y in ys:
        for k in range(sub):
            off = (-0.5 + k / (sub - 1)) * du.step
            v = phipap(gs[sel] + off + 1j * y)
            f = np.maximum(0.0, 4 * (v.imag**2 - v.real**2)) / A**2
            worst, worst_rel = _excess_report(f, y * y * F[sel], worst,
                                              worst_rel)
    return {"worst_excess": worst, "worst_rel_excess": worst_rel,
            "one_sided": worst <= 0.0}


def nesting_control(du: DepthUniform, y_lo: float = 0.33304,
                    y_hi: float = 0.38135) -> dict:
    """A cell's sups dominate those of any cell inside it, and the degenerate
    cell at the deep lip.  Nothing in the construction enforces this
    bin-by-bin, so it is a check on the inflation, not a tautology."""
    wide = du.cell_damage_sups(y_lo, y_hi)
    mid = (y_lo + y_hi) / 2
    inner = du.cell_damage_sups(mid, y_hi)
    point = du.cell_damage_sups(y_hi, y_hi)
    return {"inner_excess": float((inner - wide).max()),
            "deep_point_excess": float((point - wide).max())}


def lesion_no_inflation(du: DepthUniform, y_lo: float, y_hi: float,
                        g_lo: float = 5.0, g_hi: float = 45.0) -> dict:
    """Drop the inflation and the cell sups stop majorising.

    The lesion evaluates each bin at the cell's shallow lip with no inflation
    at all -- exactly the construction the depth-cell machinery replaces -- and
    probes the cell interior for larger true values.  A positive worst excess
    is the lesion firing.
    """
    gs = du.bin_centres()
    sel = np.where((gs >= g_lo) & (gs <= g_hi))[0]
    v0 = phipap(gs[sel] + 1j * y_lo)
    lesion = np.maximum(0.0, 4 * (v0.imag**2 - v0.real**2)) / A**2
    worst = -math.inf
    for frac in (0.5, 1.0):
        y = y_lo + frac * (y_hi - y_lo)
        v = phipap(gs[sel] + 1j * y)
        f = np.maximum(0.0, 4 * (v.imag**2 - v.real**2)) / A**2
        worst = max(worst, float((f - lesion).max()))
    return {"worst_excess": worst, "lesion_fires": worst > 0.0}


def degenerate_vs_paper_chain(du: DepthUniform, theta: float = 0.995,
                              ys=(0.02, 0.1, 0.3, 0.49)) -> list:
    """Consistency with the four sampled depths: the degenerate cell [y,y].

    ``PaperBandDual`` is instantiated at the SAME G so the tail majorants
    match; what is left is the band-margin convention.  MEASURED at the audit
    settings: the ratio runs 0.9413 / 0.9881 / 0.9963 / 0.9971 at y = 0.02 /
    0.1 / 0.3 / 0.49, i.e. this construction lands BELOW paper_chain at every
    sampled depth, by most at the shallow end.  paper_chain inflates a whole
    band by 8 max|Phi2||Phi2'| step / A^2; this module inflates each bin by its
    own centre gradient plus a curvature remainder, which is smaller
    everywhere and relatively smallest where the band is narrow.  Both
    dominate the true field -- that is ``one_sidedness_control`` -- so the
    difference is a margin convention, not a disagreement about the field.
    """
    from paper_chain import PaperBandDual  # local: keeps import cost off audit

    bd = PaperBandDual(G=du.G)
    out = []
    for y in ys:
        mine = du.regular_cell(theta, y, y)
        theirs = bd.cap(theta, y)
        out.append({"y": y, "mine": mine["cap_up"],
                    "paper_chain": theirs["cap"],
                    "ratio": mine["cap_up"] / theirs["cap"],
                    "slack": _PC.slack(y),
                    "both_close": mine["cap_up"] <= _PC.slack(y)
                    and theirs["cap"] <= _PC.slack(y)})
    return out


def dominates_measured_adversary(du: DepthUniform, theta: float = 0.995,
                                 ys=(0.3, 0.49)) -> list:
    """The depth cell containing y must cap paper_chain's greedy adversary."""
    from paper_chain import explicit_single_pair_adversary

    out = []
    for y in ys:
        rec = explicit_single_pair_adversary(_PC, y, theta=theta)
        measured = rec["D"] - (1 - theta) * rec["R"]
        cell = next(c for c in du.depth_cells()
                    if c[0] < y <= c[1] or (c[2] == "shallow" and y <= c[1]))
        if cell[2] == "shallow":
            cap = du.shallow_cell(theta)["cap_up"] * y * y
        else:
            cap = du.regular_cell(theta, cell[0], cell[1])["cap_up"]
        out.append({"y": y, "measured": measured, "cell": (cell[0], cell[1]),
                    "cap": cap, "dominated": measured <= cap})
    return out


def precision_response(theta: float = 0.995, cell: tuple | None = None) -> list:
    """The cap must respond to the discretization, and settle.

    Run on the binding (deepest) cell unless another is named.
    """
    if cell is None:
        edges = DepthUniform().cell_edges()
        cell = (edges[-2], edges[-1])
    rows = []
    for step, slices, G in ((0.01, 2, 120.0), (0.005, 2, 120.0),
                            (0.0025, 4, 120.0), (0.0025, 8, 120.0),
                            (0.0025, 4, 200.0), (0.00125, 8, 200.0)):
        du = DepthUniform(G=G, step=step, slices=slices)
        rec = du.regular_cell(theta, *cell)
        rows.append({"step": step, "slices": slices, "G": G,
                     "cap": rec["cap_up"], "rel_margin": rec["rel_margin"]})
    return rows


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit(du: DepthUniform | None = None) -> None:
    du = du or DepthUniform()
    print(f"= the paper field's derivative constants (y = 1/2) =")
    print(f"  L1 = {L1:.10f}   L2 = {L2:.10f}   A = {A:.10f}")
    print(f"  |dC/dg| = |dS/dy| <= min((1/2)A E, cosh(y/2) L1) = "
          f"min({0.5*A*E(0.5):.6f}, {math.cosh(0.25)*L1:.6f}) = "
          f"{lam_Cg(0.5):.6f}")
    print(f"  |dS/dg| = |dC/dy| <= min((1/2)A sigma, sinh(y/2) L1) = "
          f"min({0.5*A*sigma(0.5):.6f}, {math.sinh(0.25)*L1:.6f}) = "
          f"{lam_Sg(0.5):.6f}")
    print(f"  |Phi2''| <= -Phi2''(iy) = {curvature(0.5):.6f}")
    print(f"  C_IM_UNIT = {C_IM_UNIT:.10f}   NSLACK_0 = 8 L2/A = "
          f"{NSLACK_0:.10f}")

    print("= control: bounds vs central differences =")
    rec = derivative_bound_control()
    print(f"  worst |numeric|/bound over {rec['n_points']} points: "
          + ", ".join(f"{k} {v:.4f}" for k, v in rec["worst_ratio"].items()))
    print(f"  closed-form identification defect: "
          f"{rec['identification_defect']:.2e}")
    for y in (0.05, 0.5):
        att = bound_attainment(y)
        print(f"  attainment at y={y}: Cg {att['Cg']:.3f}, Sg {att['Sg']:.3f}")
    print(f"  curvature bound worst ratio: {curvature_bound_control():.4f}")
    print(f"  c_im (normalised) worst ratio: {c_im_unit_control():.4f}")

    print("= control: direction of the worst corner =")
    mono = monotonicity_control()
    print(f"  sigma^2 up {mono['sigma2_increasing']}, E up "
          f"{mono['E_increasing']},"
          f" c_im up {mono['c_im_increasing']}, slack/y^2 up "
          f"{mono['nslack_increasing']}")
    print(f"  slack/y^2 runs {mono['nslack_floor']:.6f} (floor, = NSLACK_0 "
          f"{NSLACK_0:.6f}) -> {mono['nslack_at_half']:.6f} at y = 1/2")

    print(f"= the depth cells: (0, {du.y0}] by homogeneity + {du.n_cells} "
          f"geometric cells to {du.y_max} =")
    theta = 0.995
    profs = du.profiles()
    rows = du.scan(theta, profs)
    print(f"  theta = {theta}   G = {du.G}   step = {du.step}   "
          f"slices = {du.slices}")
    print(f"  {'cell':>22}  {'cap_up':>11}  {'slack_lo':>11}  {'margin':>11}"
          f"  {'rel':>7}  {'bands':>5} {'m*':>3}")
    for r in rows:
        lab = (f"(0, {r['y_hi']:.5f}]/y^2" if r["kind"] == "shallow"
               else f"[{r['y_lo']:.5f}, {r['y_hi']:.5f}]")
        print(f"  {lab:>22}  {r['cap_up']:11.5e}  {r['slack_lo']:11.5e}  "
              f"{r['margin']:+11.4e}  {r['rel_margin']:+7.4f}  "
              f"{r['bands']:5d} {r['m_star']:3d}")
    worst = min(rows, key=lambda r: r["rel_margin"])
    print(f"  worst cell: [{worst['y_lo']:.5f}, {worst['y_hi']:.5f}]  "
          f"relative margin {worst['rel_margin']:+.4f}")

    print(f"  tail single-occupancy holds on every cell: "
          f"{all(r['tail_single_occupancy'] for r in rows)}")
    print("= the depth-uniform secured theta =")
    star, table = du.secured_theta(profs=profs)
    for th, rec2 in table.items():
        print(f"  theta={th}: all cells close = {rec2['all_closed']}, worst "
              f"relative margin {rec2['worst_rel_margin']:+.4f} at cell "
              f"[{rec2['binding_cell'][0]:.5f}, {rec2['binding_cell'][1]:.5f}]")
    print(f"  depth-uniform theta* (grid) = {star}   "
          f"(four-sampled-depth value: 0.995)")
    print("  off-grid diagnostic (where the construction stops):")
    _, off = du.secured_theta(thetas=(0.996, 0.997, 0.998, 0.999), profs=profs)
    for th, rec2 in off.items():
        print(f"    theta={th}: all cells close = {rec2['all_closed']}, worst "
              f"relative margin {rec2['worst_rel_margin']:+.4f} at cell "
              f"[{rec2['binding_cell'][0]:.5f}, {rec2['binding_cell'][1]:.5f}]")

    print("= control: theta = 1 must diverge =")
    r1 = du.cell_verdict(1.0, profs[-1])
    r1s = du.cell_verdict(1.0, profs[0])
    print(f"  deepest cell cap(theta=1) = {r1['cap_up']}, shallow cell "
          f"{r1s['cap_up']}  (both infinite: "
          f"{not math.isfinite(r1['cap_up'] + r1s['cap_up'])})")

    print("= control: the sups are one-sided over the whole cell =")
    edges = du.cell_edges()
    for cell in ((edges[-3], edges[-2]), (edges[-2], edges[-1])):
        rec3 = one_sidedness_control(du, *cell)
        print(f"  cell [{cell[0]:.5f}, {cell[1]:.5f}]: worst (true - F_up) = "
              f"{rec3['worst_excess']:.3e}, worst (true/F_up - 1) on live bins "
              f"= {rec3['worst_rel_excess']:+.2e}  one-sided = "
              f"{rec3['one_sided']}")
    rec4 = shallow_one_sidedness_control(du)
    print(f"  shallow: worst (true - y^2 F_hat) = {rec4['worst_excess']:.3e}, "
          f"worst relative {rec4['worst_rel_excess']:+.2e}  one-sided = "
          f"{rec4['one_sided']}")
    nest = nesting_control(du, edges[-3], edges[-2])
    print(f"  nesting: inner-cell excess {nest['inner_excess']:.3e}, "
          f"deep-point excess {nest['deep_point_excess']:.3e} (both <= 0)")
    les = lesion_no_inflation(du, edges[-2], edges[-1])
    print(f"  lesion (no inflation, shallow-lip values): worst excess "
          f"{les['worst_excess']:.3e}  fires = {les['lesion_fires']}")

    print("= control: consistency with the four sampled depths =")
    for row in degenerate_vs_paper_chain(du):
        print(f"  y={row['y']}: degenerate cell {row['mine']:.6e}  "
              f"paper_chain {row['paper_chain']:.6e}  ratio {row['ratio']:.4f}"
              f"  both under slack = {row['both_close']}")
    for row in dominates_measured_adversary(du):
        print(f"  y={row['y']}: measured adversary {row['measured']:.5f} <= "
              f"cell cap {row['cap']:.5f}: {row['dominated']}")

    print("= control: precision response =")
    for row in precision_response():
        print(f"  step {row['step']:<8} slices {row['slices']}  G {row['G']:>5}"
              f"  cap {row['cap']:.6e}  rel margin {row['rel_margin']:+.4f}")


if __name__ == "__main__":
    audit()
