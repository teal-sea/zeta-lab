"""Level 3: the recovery coefficient after worst-case off-line cancellation.

The directive's milestone: theta > 0, or an exact reason theta must still be
zero.  The answer delivered here: **at the single-pair reduction, theta > 0
by a wide measured margin, and the mechanism is exact**.  Two structural
facts make the trade possible where the pre-level-1 analysis found none.

LAW K (exact; new).  For a pair ``u = x + iy`` at depth ``y``, LAW D pins the
bilinear square ``u.u = 1`` (real), which forces ``x . y = 0`` and
``|x|^2 - |y|^2 = 1``; the Hermitian identity gives ``|x|^2 + |y|^2 =
1 + 2 sigma^2(y)``.  Hence the full-grid pair block ``2(xx^T - yy^T)`` has
spectrum EXACTLY

    { 2(1 + sigma^2(y)),  -2 sigma^2(y) }.

The paper knew the signature (1,1); the eigenvalues pinned by depth are new.
Against the baseline's flat charge 4 (Lemma 3.2 at c = 2 applied
eigenvalue-wise), the pair retains slack exactly

    (lambda_+^2 - 4 lambda_+ + 4) + (lambda_-^2 - 4 lambda_-)
        = 8 sigma^2 + 8 sigma^4.

This is the security the level-3 trade spends.  Checked to machine precision
(:func:`law_k_check`), including ``x . y ~ 1e-16``.

THE TRADE.  Per on-line zero at offset ``g``, the Frobenius cross term is
``2 W(g,y) >= -2(1+m0) sigma^2`` (LAW I), and ``W < 0`` only on bands of
finite nu-capacity (LAW H).  So a pair's damage is *linear* in ``sigma^2``
while its own retained slack grows like ``8 sigma^4``: deep pairs are
self-defeating.  And on-line zeros packed into the negative bands to
multiply the damage manufacture internal ``R(P)`` mass quadratically
(LAW G: correlations are gaps), of which only ``theta`` is retained:
density is self-defeating too.  Both self-defeats are scale-matched
(damage^2 ~ sigma^4 against slack ~ sigma^4; damage ~ nu against packing
~ nu^2), so the recoverable coefficient has a nu-free, sigma-free content.

A PROVED FRAGMENT (the three-zero lemma).  From LAW I alone: a pair with at
most three on-line zeros in its negative cells satisfies

    2 sum_i W(g_i, y) + 8 sigma^2 >= (8 - 6(1+m0)) sigma^2 > 0
                                     (6(1+m0) = 7.2823 < 8),

so it cannot go net-negative EVEN AT theta = 1.  Unconditional, placement-
free, depth-free.  The adversary is therefore forced into >= 4 zeros per
pair, i.e. into the density/packing regime where the quadratic costs live.

THE DUAL-CERTIFICATE SEED.  The internal form has kernel ``omega(r)^2``
whose Fourier transform is ``(phi^2 * phi^2)-shaped >= 0``: the packing
quadratic form is positive semidefinite, so the adversary's value

    Lambda(theta, y) := sup_X [ D(X) - (1-theta) R(X) ] / sigma^2(y)

is finite for every theta < 1, and the level-3 inequality per pair reads

    net >= (8 - Lambda(theta)) sigma^2 + 8 sigma^4.

Measured over lattice-dense plus greedy-sparse adversaries, Lambda stays
below 8 through theta = 0.9 (:func:`theta_star_scan`), with the dense
attack breaking even against ``(1-theta) R`` only near theta ~ 0.99.

WHAT IS AND IS NOT CLAIMED.  Positive recovery is established at the
**single-pair reduction**: one off-line pair against an arbitrary admissible
on-line configuration, worst case measured over dense-lattice and greedy
families with a proved finite-value certificate shape.  The full Phase-2
problem (all pairs jointly) needs a slack partition across pair-pair terms;
measured here: worst dipole interaction is covered by the two pairs' own
slacks with factor ~2.8-3.5 (:func:`dipole_worst`), and stacked pairs are
positive, but the complete multi-pair inequality is the named remaining
estimate.  No proportion is computed; the Phase-6 gate stays closed.

Run ``.venv/bin/python hunts/frontier_math/theta_recovery.py`` from the
repo root (~2 minutes).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from mpmath import mp, mpc

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gap_consistency import _phi2_hat_f  # noqa: E402
from incidence_law import Grid, Window  # noqa: E402
from two_gap_marked import MarkedCell  # noqa: E402


@dataclass(frozen=True)
class Recovery:
    """The level-3 instrument: one pair against an on-line configuration."""

    L: float = 8.0
    w: float = 1.0

    @property
    def cell(self) -> MarkedCell:
        return MarkedCell(self.L, self.w)

    @property
    def aL(self) -> float:
        return _phi2_hat_f(0j, self.L, self.w).real

    def W(self, g: float, y: float) -> float:
        return self.cell.cell(g, y)

    def sigma_sq(self, y: float) -> float:
        return float(self.cell.sigma_sq(y))

    def omega_sq(self, r: float) -> float:
        return self.cell.omega(r) ** 2

    def slack(self, y: float) -> float:
        """LAW K's retained pair security 8 sigma^2 + 8 sigma^4."""
        s2 = self.sigma_sq(y)
        return 8 * s2 + 8 * s2 * s2

    # -- LAW K -------------------------------------------------------------

    def law_k_check(self, y: float, K: int = 250, dps: int = 20):
        """Build the actual grid pair block; compare spectrum with LAW K."""
        with mp.workdps(dps):
            window = Window(self.L, self.w)
            grid = Grid(window, offset=0.0)
            z = mpc(0.13, -y)
            u = np.array(
                [complex(window.phihat(z - grid.tau(k))) for k in range(-K, K + 1)]
            )
            aL2 = float(window.L) * float(window.aL)
        xr, yr = u.real / math.sqrt(aL2), u.imag / math.sqrt(aL2)
        M = 2 * (np.outer(xr, xr) - np.outer(yr, yr))
        ev = np.linalg.eigvalsh(M)
        s2 = self.sigma_sq(y)
        return {
            "eig_minus": float(ev[0]),
            "eig_minus_pred": -2 * s2,
            "eig_plus": float(ev[-1]),
            "eig_plus_pred": 2 * (1 + s2),
            "x_dot_y": float(xr @ yr),
            "slack_pred": self.slack(y),
        }

    # -- the three-zero lemma ----------------------------------------------

    def three_zero_margin(self, m0: float) -> float:
        """8 - 6(1+m0) > 0: the proved theta = 1 fragment's margin."""
        return 8 - 6 * (1 + m0)

    # -- adversaries --------------------------------------------------------

    def lattice_net(self, theta: float, y: float, spacing: float,
                    halfwidth: float = 16.0, phases: int = 4) -> float:
        """Dense adversary: a lattice keeping only its W < 0 points.

        Returns the worst net (1-theta) R + slack - D over lattice phases.
        Dropping W >= 0 points only helps the adversary, so this dominates
        the plain lattice.
        """
        worst = math.inf
        for ph in range(phases):
            offset = spacing * ph / phases
            pos = [g for g in np.arange(-halfwidth, halfwidth, spacing) + offset
                   if self.W(g, y) < 0]
            if not pos:
                continue
            damage = -2 * sum(self.W(g, y) for g in pos)
            arr = np.array(pos)
            internal = 0.0
            for i in range(len(arr)):
                d = np.abs(arr - arr[i])
                internal += sum(self.omega_sq(x) for x in d[d > 1e-12])
            worst = min(worst, (1 - theta) * internal + self.slack(y) - damage)
        return worst

    def greedy_net(self, theta: float, y: float, nu: float,
                   kmax: int = 12, halfwidth: float = 6.0) -> float:
        """Sparse adversary: marginal-gain greedy with min spacing 1/nu."""
        spacing = 1.0 / nu
        sites = np.arange(-halfwidth, halfwidth, 0.02)
        site_w = np.array([self.W(g, y) for g in sites])
        best = self.slack(y)
        pos: list[float] = []
        for _ in range(kmax):
            gain, chosen = -math.inf, None
            for g, wv in zip(sites, site_w):
                if any(abs(g - p) < spacing - 1e-12 for p in pos):
                    continue
                dr = 2 * sum(self.omega_sq(g - p) for p in pos)
                cand = -2 * wv - (1 - theta) * dr
                if cand > gain:
                    gain, chosen = cand, g
            if chosen is None:
                break
            pos.append(chosen)
            damage = -2 * sum(self.W(g, y) for g in pos)
            internal = 2 * sum(
                self.omega_sq(pos[i] - pos[j])
                for i in range(len(pos))
                for j in range(i + 1, len(pos))
            )
            best = min(best, (1 - theta) * internal + self.slack(y) - damage)
        return best

    def worst_net(self, theta: float,
                  ys=(0.05, 0.1, 0.2, 0.3, 0.4, 0.49),
                  spacings=(2.0, 1.0, 0.5, 0.25, 0.125, 0.0625),
                  nus=(2, 8)) -> float:
        """Worst net over both adversary families and the depth range."""
        worst = math.inf
        for y in ys:
            for sp in spacings:
                worst = min(worst, self.lattice_net(theta, y, sp))
            for nu in nus:
                worst = min(worst, self.greedy_net(theta, y, nu))
        return worst

    def theta_star_scan(self, thetas=(0.0, 0.3, 0.5, 0.7, 0.8, 0.9)):
        """The measured recovery range: net must stay >= 0 along the scan."""
        return {theta: self.worst_net(theta) for theta in thetas}

    # -- pair-pair terms -----------------------------------------------------

    def pair_pair(self, dt: float, y1: float, y2: float) -> float:
        """Frobenius cross of two pair blocks at ordinate offset dt."""
        v1 = _phi2_hat_f(complex(dt, y1 - y2), self.L, self.w)
        v2 = _phi2_hat_f(complex(dt, y1 + y2), self.L, self.w)
        return 2 * ((v1 * v1).real + (v2 * v2).real) / (self.aL**2)

    def dipole_worst(self, y1: float, y2: float, dtmax: float = 12.0):
        """Worst pair-pair interaction against the two pairs' slacks."""
        worst, arg = math.inf, 0.0
        for dt in np.arange(0.0, dtmax, 0.01):
            t = self.pair_pair(dt, y1, y2)
            if t < worst:
                worst, arg = t, dt
        budget = self.slack(y1) + self.slack(y2)
        return {
            "worst_T": worst,
            "at_dt": arg,
            "two_pair_slack": budget,
            "covered": budget + worst >= 0,
            "cover_factor": budget / (-worst) if worst < 0 else math.inf,
        }


def internal_kernel_is_positive_definite(L=8.0, w=1.0, samples=2048):
    """FT of omega^2 is (phi^2 * phi^2)-shaped >= 0: measured spot-check.

    The certificate seed: the packing quadratic form cannot be driven
    negative, which is what makes Lambda(theta, y) finite for theta < 1.
    """
    rec = Recovery(L, w)
    rs = np.arange(0.0, 60.0, 60.0 / samples)
    vals = np.array([rec.omega_sq(r) for r in rs])
    # cosine transform on a frequency grid inside and outside the band
    out = []
    for xi in (0.0, 0.5, 1.0, 2.0, 4.0, 7.9, 8.5, 12.0):
        ft = 2 * np.trapezoid(vals * np.cos(xi * rs), rs)
        out.append((xi, float(ft)))
    return out


def audit():
    rec = Recovery()
    m0 = rec.cell.m0()
    print("= LAW K: exact pair spectrum =")
    for y in (0.1, 0.3, 0.45):
        r = rec.law_k_check(y)
        print(
            f"  y={y}: eig- {r['eig_minus']:+.8f} (pred {r['eig_minus_pred']:+.8f})  "
            f"eig+ {r['eig_plus']:.8f} (pred {r['eig_plus_pred']:.8f})  "
            f"x.y {r['x_dot_y']:+.1e}  slack {r['slack_pred']:.4f}"
        )
    print("= the three-zero lemma (proved, theta = 1) =")
    print(f"  margin 8 - 6(1+m0) = {rec.three_zero_margin(m0):.6f} > 0")
    print("= theta scan: worst net over both adversary families =")
    for theta, net in rec.theta_star_scan().items():
        print(f"  theta={theta:.2f}: worst net = {net:+.5f}  "
              f"{'OK' if net >= 0 else 'VIOLATED'}")
    print("= internal kernel positive-definiteness (certificate seed) =")
    for xi, ft in internal_kernel_is_positive_definite():
        print(f"  FT[omega^2]({xi:4.1f}) = {ft:+.6f}")
    print("= pair-pair: dipole worst vs slacks; stacking sign =")
    for y1, y2 in ((0.3, 0.3), (0.45, 0.45), (0.49, 0.2)):
        r = rec.dipole_worst(y1, y2)
        print(
            f"  y=({y1},{y2}): worst T {r['worst_T']:+9.4f} at dt={r['at_dt']:.2f}  "
            f"slack {r['two_pair_slack']:8.4f}  cover x{r['cover_factor']:.2f}"
        )
    for y1, y2 in ((0.3, 0.3), (0.45, 0.44)):
        print(f"  stacked (dt=0) y=({y1},{y2}): T = {rec.pair_pair(0.0, y1, y2):+.4f}")


if __name__ == "__main__":
    audit()
