"""Level 2, marked two-gap consistency: the coexistence question, answered.

The directive's immediate question is: **can one actual off-line pair
simultaneously realise the worst signed incidence allowed by level 1 across
two consecutive on-line gaps?**  The answer is no, and the reason is sharper
than an incompatibility of offsets: *the level-1 envelope is not attained in
even one cell at nonzero offset*.

Everything below follows from one exact decomposition.  On the full grid the
signed cell value of an on-line zero at offset ``g`` from a pair of depth
``y`` is ``W(g,y) = 2 Re(Phi2(g+iy)^2)/(aL)^2``.  Writing
``Phi2(g+iy) = C - iS`` and using the parity of ``phi^2``,

    C(g,y) = int phi^2(u) cos(gu) cosh(yu) du        (even in g, even in y)
    S(g,y) = int phi^2(u) sin(gu) sinh(yu) du        (odd in g,  odd in y)
    W(g,y) = 2 (C^2 - S^2) / (aL)^2                  (even in g, even in y)

-- the two mixed parities integrate to zero.  Evenness in ``y`` is Phase 1's
symmetry under ``rho <-> 1 - conj(rho)``; evenness in ``g`` says a cell
depends only on ``|offset|``; and dependence on ``g`` alone (not on absolute
position) is Phase 1's translation covariance.  All three are exact.

**Why level 1 is never saturated (Phase 1.5, the immediate question).**  Level
1's floor came from ``|S| <= aL sigma(y)`` by Cauchy-Schwarz on
``int (phi sin gu)(phi sinh yu)``.  Saturation needs ``C = 0`` *and*
Cauchy-Schwarz equality, i.e. ``sin(gu) = lambda sinh(yu)`` for all ``u`` in
the support.  Matching Taylor coefficients at ``u = 0``: first order forces
``lambda = g/y``, third order forces ``-g^3/6 = lambda y^3/6 = g y^2/6``,
hence ``g (g^2 + y^2) = 0``.  With ``y > 0`` this gives ``g = 0``, where
``S = 0`` and there is no negativity at all.  So no cell is ever at the
level-1 floor, let alone two.

**LAW I (one-cell tightening; proved, uniform).**  Sharpening the same
Cauchy-Schwarz against ``sin^2`` rather than ``1``:

    S^2 <= (int phi^2 sin^2(gu) du)(int phi^2 sinh^2(yu) du)
         = [(aL - Phi2(2g))/2] * aL sigma^2(y),

so, with the single window constant ``m0 := - min_r omega(r) >= 0``
(``omega(r) = Phi2(r)/Phi2(0)``),

    W(g,y)  >=  -sigma^2(y) (1 - omega(2g))  >=  -(1 + m0) sigma^2(y).

Level 1 had ``-2 sigma^2(y)``.  For this window ``m0 = 0.21371725...``, so
**every cell carries a uniform factor ``2/(1+m0) = 1.6478`` of slack against
the level-1 envelope**, at every offset and every depth.  The measured sharp
ratio ``r(y) = |min_g W| / (2 sigma^2)`` runs from ``0.2979`` to ``0.4786``
across the strip, comfortably inside the proved cap ``(1+m0)/2 = 0.6069``.

**LAW J (periodic identity; exact).**  If the on-line zeros sit at the
critical grid, Poisson summation applies to ``F(r) = Phi2(r+iy)^2``, whose
density ``(phi^2 e^{-y.}) * (phi^2 e^{-y.})`` is supported in ``[-L, L]`` and
*vanishes at the endpoints*, so only the ``m = 0`` dual term survives:

    sum_{k in Z} W(t + k h, y)  =  2 b / a^2      (h = 2 pi / L)

with ``a = (1/L) int phi^2`` and ``b = (1/L) int phi^4`` -- the paper's own
(2.14) constants.  The value is **positive and independent of both the depth
and the ordinate**: a periodic word at critical spacing yields an off-line
pair exactly no negativity.  That is Phase 4's periodic near-obstruction
lesion, answered in closed form (``2b/a^2 = 2.2959062623...`` here).

**Phase 2/3: coexistence by itself is empty (a clean collapse).**  Two exact
constructions realise ``n min_g W`` with no penalty at all:

* *the mirror pair*: ``W`` is even, so its minimum is attained at both
  ``+g*`` and ``-g*``; two on-line zeros separated by exactly
  ``s = 2 g*(y)`` therefore both sit at the single-cell minimum, and the
  two-cell penalty is exactly zero (measured ``|Delta| < 4e-13``);
* *the cluster*: offsets need only be distinct, so ``n`` zeros packed at
  spacing ``delta`` near ``g*`` give penalty per cell ``-> 0`` as
  ``delta -> 0`` (measured ``7e-5`` at ``n = 10``, ``delta = 1e-3``).

So marked two-gap projective consistency, *on its own*, yields no positive
``Delta``.  This is the directive's OUTCOME B for the coexistence question,
and the escaping family is pinned exactly: the ``+-g*(y)`` cluster, which is
a near-multiple zero and is controlled only by density and multiplicity
(``gap_consistency.py``'s LAW H), never by gap geometry.  Imposing a
separation ``delta`` does convert it into a positive penalty, quantified by
:func:`separation_penalty` -- which is why the useful coupling is
consistency *plus* density, not consistency alone.

**Phase 5.**  LAW I gives the epsilon-robust statement directly and
uniformly: no cell is ever within ``(1 - m0) sigma^2(y)`` of the level-1
floor, so a configuration declaring ``n`` cells within ``epsilon`` of it is
excluded outright for ``epsilon < (1 - m0) sigma^2(y)``, and pays at least
``n [(1 - m0) sigma^2 - epsilon]`` otherwise -- linear in ``n``, uniform in
placement and depth.

**Phase 6 gate: not passed, and deliberately so.**  LAW I tightens the
*envelope*, not a proportion; the coexistence route that could have produced
an additive floor collapses.  No decimal search is opened.

Run ``.venv/bin/python hunts/frontier_math/two_gap_marked.py`` from the repo
root.
"""

from __future__ import annotations

import cmath
import math
import sys
from dataclasses import dataclass
from pathlib import Path

from mpmath import mp, mpc, mpf

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gap_consistency import Kernel, _f_cs_moments, _phi2_hat_f, _poly_sq_f  # noqa: E402
from incidence_law import RAMP, Window  # noqa: E402

_RAMP4_F = _poly_sq_f(_poly_sq_f([float(c) for c in RAMP]))


def _phi4_hat_f(z: complex, L: float, w: float) -> complex:
    """int phi^4(u) cos(zu) du -- the paper's b constant at z = 0."""
    half, inner = L / 2, L / 2 - w
    if abs(z) < 1e-12:
        mid = 2 * inner
    else:
        mid = 2 * cmath.sin(z * inner) / z
    C, S = _f_cs_moments(z * w, len(_RAMP4_F) - 1)
    ch, sh = cmath.cos(z * half), cmath.sin(z * half)
    return mid + 2 * w * sum(c * (ch * C[k] + sh * S[k]) for k, c in enumerate(_RAMP4_F) if c)


# ---------------------------------------------------------------------------
# Scalar optimisation helpers (deterministic: scan, then golden section)
# ---------------------------------------------------------------------------


def _golden(f, lo, hi, iters=200):
    phi = (math.sqrt(5) - 1) / 2
    a, b = lo, hi
    c, d = b - phi * (b - a), a + phi * (b - a)
    for _ in range(iters):
        if f(c) < f(d):
            b, d = d, c
            c = b - phi * (b - a)
        else:
            a, c = c, d
            d = a + phi * (b - a)
        if b - a < 1e-15:
            break
    mid = (a + b) / 2
    return mid, f(mid)


def _global_min(f, lo, hi, n=4000):
    xs = [lo + (hi - lo) * i / n for i in range(n + 1)]
    vals = [f(x) for x in xs]
    i = min(range(len(xs)), key=lambda j: vals[j])
    return _golden(f, xs[max(0, i - 1)], xs[min(len(xs) - 1, i + 1)])


# ---------------------------------------------------------------------------
# The marked cell
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class MarkedCell:
    """One off-line pair read against on-line zeros through the level-1 grid."""

    L: float = 8.0
    w: float = 1.0

    @property
    def aL(self) -> float:
        return _phi2_hat_f(0j, self.L, self.w).real

    def cs(self, g: float, y: float):
        """The exact (C, S) split of Phi2(g + iy)."""
        v = _phi2_hat_f(complex(g, y), self.L, self.w)
        return v.real, -v.imag

    def cell(self, g: float, y: float) -> float:
        """W(g, y) = 2 Re(Phi2(g+iy)^2)/(aL)^2, the signed incidence."""
        C, S = self.cs(g, y)
        return 2 * (C * C - S * S) / (self.aL**2)

    def cell_hermitian(self, g: float, y: float) -> float:
        """The conjugate-transpose geometry: 2|Bhat|^2, never negative.

        This is the geometry `CLEAN-KILL-REPORT.md` withdrew.  Kept as a
        Phase-4 lesion: swapping it in destroys the entire signed structure.
        """
        C, S = self.cs(g, y)
        return 2 * (C * C + S * S) / (self.aL**2)

    def sigma_sq(self, y: float) -> float:
        return (_phi2_hat_f(complex(0.0, 2 * y), self.L, self.w).real - self.aL) / (2 * self.aL)

    def omega(self, r: float) -> float:
        return _phi2_hat_f(complex(r, 0.0), self.L, self.w).real / self.aL

    # -- LAW I ------------------------------------------------------------

    def m0(self, rmax: float = 60.0, n: int = 12000) -> float:
        """The window constant m0 = -min_r omega(r) >= 0."""
        _, value = _global_min(self.omega, 0.0, rmax, n=n)
        return -value

    def level1_floor(self, y: float) -> float:
        """LAW E's envelope: -2 sigma^2(y)."""
        return -2 * self.sigma_sq(y)

    def proved_floor(self, y: float, m0: float | None = None) -> float:
        """LAW I's envelope: -(1 + m0) sigma^2(y), proved and uniform."""
        m0 = self.m0() if m0 is None else m0
        return -(1 + m0) * self.sigma_sq(y)

    def pointwise_floor(self, g: float, y: float) -> float:
        """The g-dependent form -sigma^2(y)(1 - omega(2g)), before the cap."""
        return -self.sigma_sq(y) * (1 - self.omega(2 * g))

    def sharp_cell(self, y: float, gmax: float = 40.0, n: int = 8000):
        """(g*, min_g W) -- the true one-cell optimum, measured."""
        return _global_min(lambda g: self.cell(g, y), 0.0, gmax, n=n)

    def looseness(self, y: float):
        """r(y) = |min_g W| / (2 sigma^2): how loose level 1 was."""
        _, value = self.sharp_cell(y)
        return -value / (2 * self.sigma_sq(y))

    # -- the saturation obstruction (the immediate question) ---------------

    def cauchy_schwarz_defect(self, g: float, y: float, samples: int = 200) -> float:
        """How far sin(gu) is from being proportional to sinh(yu).

        Saturation of the level-1 floor needs these proportional on the
        window's support.  Reported as the normalised L2 defect of the best
        proportional fit.  For ``y > 0`` it is bounded away from zero at
        *every* ``g``, including in the limit ``g -> 0``, where the ratio
        tends to the defect between ``u`` and ``sinh(yu)`` rather than to 0.
        The ``g = 0`` case needs no such argument: there ``S = 0``, so
        ``W(0,y) = 2C^2/(aL)^2 >= 0`` and the (negative) floor is missed
        outright.
        """
        half = self.L / 2
        us = [-half + 2 * half * i / samples for i in range(samples + 1)]
        f = [math.sin(g * u) for u in us]
        h = [math.sinh(y * u) for u in us]
        hh = sum(v * v for v in h)
        if hh == 0:
            return float("nan")
        lam = sum(a * b for a, b in zip(f, h)) / hh
        num = sum((a - lam * b) ** 2 for a, b in zip(f, h))
        den = sum(a * a for a in f)
        return math.sqrt(num / den) if den else 0.0

    # -- LAW J ------------------------------------------------------------

    def periodic_constant(self) -> float:
        """2b/a^2, the exact total over a critical-spacing periodic word."""
        a = self.aL / self.L
        b = _phi4_hat_f(0j, self.L, self.w).real / self.L
        return 2 * b / (a * a)

    def periodic_total(self, y: float, offset: float, half_width: int = 600) -> float:
        """The measured total sum_k W(offset + k h, y)."""
        h = 2 * math.pi / self.L
        return sum(self.cell(offset + k * h, y) for k in range(-half_width, half_width + 1))


# ---------------------------------------------------------------------------
# Phase 2/3: coexistence, and its collapse
# ---------------------------------------------------------------------------


def mirror_collapse(cell: MarkedCell, y: float):
    """Two zeros at +-g* attain 2 min W exactly: the two-cell penalty is 0."""
    g_star, value = cell.sharp_cell(y)
    s = 2 * g_star
    _, joint = _global_min(lambda o: cell.cell(o, y) + cell.cell(o + s, y), -6.0, 6.0, n=6000)
    return {
        "g_star": g_star,
        "mirror_gap": s,
        "single_cell_min": value,
        "two_cell_min": joint,
        "penalty": joint - 2 * value,
    }


def two_cell_penalty(cell: MarkedCell, gap: float, y: float):
    """Delta(s, y) = min_o [W(o) + W(o+s)] - 2 min_g W, for a general gap."""
    _, value = cell.sharp_cell(y)
    _, joint = _global_min(lambda o: cell.cell(o, y) + cell.cell(o + gap, y), -6.0, 6.0, n=6000)
    return joint - 2 * value


def cluster_collapse(cell: MarkedCell, y: float, n: int, delta: float):
    """n distinct offsets at spacing delta: the penalty per cell -> 0."""
    _, value = cell.sharp_cell(y)

    def total(o):
        return sum(cell.cell(o + j * delta, y) for j in range(n))

    _, joint = _global_min(total, -6.0, 6.0, n=4000)
    return {
        "n": n,
        "delta": delta,
        "total": joint,
        "n_times_min": n * value,
        "penalty": joint - n * value,
        "penalty_per_cell": (joint - n * value) / n,
    }


def separation_penalty(cell: MarkedCell, y: float, n: int, delta: float) -> float:
    """The positive object once a separation delta is imposed."""
    return cluster_collapse(cell, y, n, delta)["penalty_per_cell"]


# ---------------------------------------------------------------------------
# Phase 5
# ---------------------------------------------------------------------------


def epsilon_robustness(cell: MarkedCell, y: float, m0: float | None = None):
    """No cell comes within (1 - m0) sigma^2(y) of the level-1 floor."""
    m0 = cell.m0() if m0 is None else m0
    gap_to_floor = (1 - m0) * cell.sigma_sq(y)
    return {
        "depth": y,
        "excluded_band": gap_to_floor,
        "level1_floor": cell.level1_floor(y),
        "proved_floor": cell.proved_floor(y, m0),
        "per_cell_margin_is_linear_in_n": True,
    }


# ---------------------------------------------------------------------------
# Phase 4: lesions
# ---------------------------------------------------------------------------


def lesion_independent_cells(cell: MarkedCell, y: float, gap: float):
    """Treating the two projections as independent pairs (the named cheat)."""
    _, value = cell.sharp_cell(y)
    coupled = two_cell_penalty(cell, gap, y) + 2 * value
    return {"independent": 2 * value, "coupled": coupled, "coupled_is_higher": coupled >= 2 * value}


def lesion_independent_depths(cell: MarkedCell, y1: float, y2: float):
    """Letting the two projections carry different depths (not one pair).

    Recorded as a *negative* lesion result, honestly: since |min W| increases
    with depth, mixing depths can never beat using the deeper one twice, so
    the shared-depth half of the pair's identity is not the binding
    constraint.  The binding half is the shared ordinate
    (:func:`lesion_independent_cells`).
    """
    _, v1 = cell.sharp_cell(y1)
    _, v2 = cell.sharp_cell(y2)
    _, deep = cell.sharp_cell(max(y1, y2))
    return {
        "mixed_depth_sum": v1 + v2,
        "deepest_twice": 2 * deep,
        "mixing_helps": (v1 + v2) < 2 * deep,
    }


def lesion_hermitian_geometry(cell: MarkedCell, y: float, samples: int = 400):
    """Conjugate-transpose geometry: every cell becomes nonnegative."""
    worst_true = math.inf
    worst_herm = math.inf
    for i in range(samples + 1):
        g = 40.0 * i / samples
        worst_true = min(worst_true, cell.cell(g, y))
        worst_herm = min(worst_herm, cell.cell_hermitian(g, y))
    return {"worst_true": worst_true, "worst_hermitian": worst_herm}


def lesion_broken_spacing(cell: MarkedCell, y: float, stretch: float = 65 / 64, half_width=600):
    """Off-critical spacing: the periodic identity loses its exactness."""
    h = 2 * math.pi / cell.L * stretch
    total = sum(cell.cell(k * h, y) for k in range(-half_width, half_width + 1))
    return {"total": total, "exact_constant": cell.periodic_constant()}


def audit():
    cell = MarkedCell()
    m0 = cell.m0()
    print("= the immediate question: can two cells jointly saturate level 1? =")
    print("  NO -- no cell saturates it at all.  Cauchy-Schwarz equality needs")
    print("  sin(gu) proportional to sinh(yu); the defect never vanishes for y > 0:")
    for g, y in ((1e-6, 0.3), (0.3, 0.3), (0.767463, 0.3), (2.0, 0.3)):
        print(f"    g={g:<9} y={y}: proportionality defect = {cell.cauchy_schwarz_defect(g, y):.6f}")
    print(f"  and at g = 0 the floor is missed outright: W(0, 0.3) = {cell.cell(0.0, 0.3):+.6f} >= 0"
          f"  vs floor {cell.level1_floor(0.3):.6f}")
    print("= LAW I: the one-cell tightening =")
    print(f"  m0 = -min_r omega(r) = {m0:.10f}")
    print(f"  proved cell floor = -(1+m0) sigma^2 = -{1 + m0:.8f} sigma^2  (level 1: -2 sigma^2)")
    print(f"  uniform slack factor 2/(1+m0) = {2 / (1 + m0):.6f}")
    print(f"  {'y':>7} {'min_g W':>13} {'proved floor':>14} {'holds':>7} {'r(y)':>9}")
    for y in (0.01, 0.1, 0.3, 0.49):
        g, v = cell.sharp_cell(y)
        pf = cell.proved_floor(y, m0)
        print(f"  {y:7.3f} {v:13.8f} {pf:14.8f} {str(v >= pf):>7} {-v / (2 * cell.sigma_sq(y)):9.6f}")
    print("= LAW J: periodic word at critical spacing (exact) =")
    print(f"  2b/a^2 = {cell.periodic_constant():.10f}")
    for y in (0.0, 0.3, 0.49):
        for off in (0.0, 0.37):
            tot = cell.periodic_total(y, off)
            print(f"    y={y:.2f} offset={off:.2f}: total = {tot:.10f}  "
                  f"defect = {abs(tot - cell.periodic_constant()):.2e}")
    print("= Phase 2/3: coexistence collapses (OUTCOME B) =")
    for y in (0.1, 0.3, 0.49):
        rec = mirror_collapse(cell, y)
        print(f"  y={y}: mirror gap {rec['mirror_gap']:.8f} -> penalty {rec['penalty']:+.3e}")
    for n, delta in ((3, 0.1), (3, 0.001), (10, 0.01), (10, 0.001)):
        rec = cluster_collapse(cell, 0.3, n, delta)
        print(f"  cluster n={n:2d} delta={delta:<6}: penalty/cell = {rec['penalty_per_cell']:.3e}")
    print("= Phase 5: epsilon robustness (from LAW I) =")
    for y in (0.1, 0.3, 0.49):
        rec = epsilon_robustness(cell, y, m0)
        print(f"  y={y}: no cell within {rec['excluded_band']:.6f} of the level-1 floor "
              f"{rec['level1_floor']:.6f}")
    print("= Phase 4: lesions =")
    rec = lesion_independent_cells(cell, 0.3, 0.7854)
    print(f"  independent cells: independent {rec['independent']:.6f} vs coupled "
          f"{rec['coupled']:.6f} -- the cheat buys {rec['coupled'] - rec['independent']:.6f}")
    rec = lesion_independent_depths(cell, 0.2, 0.4)
    print(f"  independent depths: mixed {rec['mixed_depth_sum']:.6f} vs deepest twice "
          f"{rec['deepest_twice']:.6f} -- mixing helps: {rec['mixing_helps']} (negative lesion)")
    rec = lesion_hermitian_geometry(cell, 0.3)
    print(f"  hermitian geometry: worst true {rec['worst_true']:.6f}, worst hermitian "
          f"{rec['worst_hermitian']:+.3e} (all negativity destroyed)")
    rec = lesion_broken_spacing(cell, 0.3)
    print(f"  broken spacing: total {rec['total']:.8f} vs exact {rec['exact_constant']:.8f} "
          f"-- defect {abs(rec['total'] - rec['exact_constant']):.3e}")


if __name__ == "__main__":
    audit()
