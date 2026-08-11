"""Level 6c: LAW M, and the Fourier bridge — the joint energy in one variable.

Two deliverables, both exact, both the groundwork for the joint cap dual.

LAW M (mean positivity, exact and depth-blind).  With ``K := phi^2 * phi^2``
(the autocorrelation, supported in [-L, L]),

    Phi2(g+iy)^2 = int_{-L}^{L} K(v) e^{i(g+iy)v} dv,

so integrating over the offset line kills every frequency but v = 0:

    int_R W(g, y) dg  =  (2/(aL)^2) * 2 pi K(0)  =  4 pi b / (a^2 L),

EXACTLY, at EVERY depth — the mean of the signed damage field is a positive
constant, and only its fluctuation is dangerous.  LAW J is this law read at
the critical lattice: the periodized sum (1/h) int W = (L/2pi)(4pi b/a^2 L)
= 2b/a^2, which is the constant level 2 measured to 6e-8.  The chi collapse
of level 6b (dense pair sets are near-immune to on-line attack) is its
finite-density shadow: a dense sampling of the field sees the mean.

THE FOURIER BRIDGE (the representation theorem).  For any conjugate-closed
configuration {z_j} (on-line zeros real, pair members t +- iy), define the
joint exponential sum

    F(v) = sum_j e^{i z_j v}     (an on-line zero contributes e^{ixv};
                                  a pair contributes e^{itv} 2 cosh(yv)),

which is a finite sum, real-positive in modulus squared by conjugate
closure.  Then the ENTIRE normalised Frobenius energy is one nonnegative-
kernel quadratic form in one real frequency variable:

    E_total := sum_{j,k} Bhat(z_j, z_k)^2
             = (1/(aL)^2) int_{-L}^{L} K(v) |F(v)|^2 dv,       K >= 0.

Every object of levels 1-6 is a shadow of this identity: the diagonal is
the census N; the on-line off-diagonal is R(P); the on/off cross terms are
the W sums; the pair-pair terms are LAW L's T; the intra-pair cross is
LAW K's E(2y)^2 (and 2 + 2E(2y)^2 = 4 + 8 sigma^2 + 8 sigma^4 recovers the
pair block energy).  Verified here to machine precision on mixed
configurations (:func:`bridge_check`).

WHY THIS IS THE RIGHT ROOM FOR THE JOINT CAP.  Splitting F = F_on + F_p,
the joint inequality of the assembly is equivalent to

    int K(v) [ |F_on + F_p|^2 - theta |F_on|^2 - d(v) ] dv  >=  -err,

where d(v) collects the diagonal/slack subtractions (s_1 for the on-line
part, sum_r 4 cosh^2(y_r v) for the pairs — the slack IS the pair diagonal
in this language).  The adversary's whole game — on-line placement AND
pair density — is the choice of two exponential sums against one fixed
nonnegative kernel.  The mutual exclusion of level 6b is visible here
pointwise: the cross term 2 Re(F_on conj(F_p)) that damages is controlled
by the same |F_p|^2 that pays, at the same v.  The remaining theorem
object is the pointwise-in-v certificate (the d(v) budget spread over
[-L, L] cells), which is one-dimensional and finite — the same shape as
every hardened object in this chain.  :func:`pinch_spectrum` measures the
integrand of the pinch configuration to show where in v the battle is.

Run ``.venv/bin/python hunts/frontier_math/fourier_bridge.py`` (~30 s).
"""

from __future__ import annotations

import cmath
import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gap_consistency import _phi2_hat_f  # noqa: E402
from pair_energy import PairEnergy  # noqa: E402


@dataclass(frozen=True)
class FourierBridge:
    L: float = 8.0
    w: float = 1.0

    @property
    def pe(self) -> PairEnergy:
        return PairEnergy(self.L, self.w)

    @property
    def aL(self) -> float:
        return _phi2_hat_f(0j, self.L, self.w).real

    # -- the kernel K = phi^2 * phi^2 ---------------------------------------

    def phi_sq(self, u: float) -> float:
        """phi(u)^2 for the septic-ramp window (piecewise polynomial)."""
        au = abs(u)
        half = self.L / 2
        if au >= half:
            return 0.0
        if au <= half - self.w:
            return 1.0
        x = (half - au) / self.w
        ramp = 35 * x**4 - 84 * x**5 + 70 * x**6 - 20 * x**7
        return ramp * ramp

    def K(self, v: float, n: int = 400) -> float:
        """The autocorrelation (phi^2 * phi^2)(v), by quadrature."""
        av = abs(v)
        if av >= self.L:
            return 0.0
        lo, hi = -self.L / 2, self.L / 2 - av
        if hi <= lo:
            return 0.0
        step = (hi - lo) / n
        total = 0.0
        for i in range(n + 1):
            u = lo + i * step
            weight = 0.5 if i in (0, n) else 1.0
            total += weight * self.phi_sq(u) * self.phi_sq(u + av)
        return total * step

    def bL(self) -> float:
        """K(0) = int phi^4 = bL, the paper's (2.14) second constant."""
        return self.K(0.0)

    # -- LAW M ---------------------------------------------------------------

    def law_m_exact(self) -> float:
        """4 pi b / (a^2 L): the exact depth-blind mean of W."""
        a = self.aL / self.L
        b = self.bL() / self.L
        return 4 * math.pi * b / (a * a * self.L)

    def law_m_measured(self, y: float, g_max: float = 60.0, n: int = 24000) -> float:
        """int W(g, y) dg by quadrature, to compare against the constant."""
        pe = self.pe
        step = 2 * g_max / n
        total = 0.0
        for i in range(n + 1):
            g = -g_max + i * step
            weight = 0.5 if i in (0, n) else 1.0
            total += weight * pe.W(g, y)
        return total * step

    # -- the bridge -----------------------------------------------------------

    def F(self, v: float, online, pairs) -> complex:
        """The joint exponential sum at frequency v."""
        total = 0j
        for x in online:
            total += cmath.exp(1j * x * v)
        for t, y in pairs:
            total += cmath.exp(1j * t * v) * 2 * math.cosh(y * v)
        return total

    def energy_direct(self, online, pairs) -> float:
        """sum_{j,k} Bhat^2 assembled from the level-1..6 term dictionary."""
        pe = self.pe
        rec = pe.rec
        n_on = len(online)
        total = float(n_on)  # on-line diagonal
        for i in range(n_on):  # R(P): on-line off-diagonal
            for j in range(n_on):
                if i != j:
                    total += rec.omega_sq(online[i] - online[j])
        for t, y in pairs:  # LAW K: per-pair block energy
            s2 = pe.sigma_sq(y)
            total += 4 + 8 * s2 + 8 * s2 * s2
        for i, (t1, y1) in enumerate(pairs):  # LAW L: pair-pair cross
            for j, (t2, y2) in enumerate(pairs):
                if i != j:
                    total += pe.T(t1 - t2, y1, y2)
        for x in online:  # on/off cross, both orders
            for t, y in pairs:
                total += 2 * rec.W(x - t, y)
        return total

    def energy_fourier(self, online, pairs, n: int = 6000) -> float:
        """(1/(aL)^2) int_{-L}^{L} K(v) |F(v)|^2 dv by quadrature."""
        step = 2 * self.L / n
        total = 0.0
        for i in range(n + 1):
            v = -self.L + i * step
            weight = 0.5 if i in (0, n) else 1.0
            total += weight * self.K(v) * abs(self.F(v, online, pairs)) ** 2
        return total * step / (self.aL**2)

    def bridge_check(self, configs=None) -> float:
        """Worst relative defect of the representation over mixed configs."""
        if configs is None:
            configs = [
                ([0.3, 1.7], [(0.9, 0.25)]),
                ([0.0, 0.77, 2.1], [(0.4, 0.45), (1.6, 0.1)]),
                ([-1.2, 0.5], [(0.0, 0.49)]),
            ]
        worst = 0.0
        for online, pairs in configs:
            direct = self.energy_direct(online, pairs)
            fourier = self.energy_fourier(online, pairs)
            worst = max(worst, abs(direct - fourier) / abs(direct))
        return worst

    # -- the pinch, spectrally ------------------------------------------------

    def pinch_spectrum(self, nu_p: float = 1.5, y: float = 0.49,
                       span: float = 10.0, n_bins: int = 8):
        """Where in v the pinch configuration's energy lives.

        Reports the K-weighted integrand of |F_p|^2 - (pair diagonal) in
        coarse v-bins: negative bins are where the pair lattice's
        off-diagonal fluctuation fights the mean; the balance is LAW M's
        constant appearing at v = 0 and the diagonal cosh^2 growth at the
        band edge.
        """
        spacing = 1.0 / nu_p
        pairs = [(k * spacing, y) for k in range(int(span / spacing))]
        bins = [0.0] * n_bins
        n = 4000
        step = 2 * self.L / n
        for i in range(n + 1):
            v = -self.L + i * step
            diag = sum(4 * math.cosh(yy * v) ** 2 for _, yy in pairs)
            fluct = abs(self.F(v, [], pairs)) ** 2 - diag
            idx = min(n_bins - 1, int(abs(v) / self.L * n_bins))
            bins[idx] += self.K(v) * fluct * step / (self.aL**2)
        return bins


def audit():
    fb = FourierBridge()
    print("= LAW M: the exact depth-blind mean of the damage field =")
    exact = fb.law_m_exact()
    print(f"  4 pi b / (a^2 L) = {exact:.10f}")
    for y in (0.0, 0.1, 0.3, 0.49):
        measured = fb.law_m_measured(y)
        print(f"  int W(., {y}) dg = {measured:.8f}   defect {abs(measured - exact):.2e}")
    h = 2 * math.pi / fb.L
    print(f"  consistency with LAW J: (1/h) int W = {exact / h:.10f} "
          f"(LAW J constant 2b/a^2 = {2 * (fb.bL() / fb.L) / (fb.aL / fb.L) ** 2:.10f})")
    print("= the Fourier bridge: E_total = (1/(aL)^2) int K |F|^2 =")
    defect = fb.bridge_check()
    print(f"  worst relative defect over mixed configurations: {defect:.3e}")
    print("= the pinch, spectrally (K-weighted pair fluctuation by |v| bin) =")
    bins = fb.pinch_spectrum()
    for i, val in enumerate(bins):
        lo, hi = i * fb.L / len(bins), (i + 1) * fb.L / len(bins)
        print(f"  |v| in [{lo:.0f}, {hi:.0f}): {val:+10.4f}")
    print(f"  total fluctuation: {sum(bins):+.4f}  "
          "(the negative bins are the pinch; the v=0 mean and the")
    print("   band-edge cosh^2 diagonal are what the certificate must spread)")


if __name__ == "__main__":
    audit()
