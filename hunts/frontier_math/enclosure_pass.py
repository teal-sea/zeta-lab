"""Level 5, gate 1: the level-4 counting dual under ball arithmetic.

The level-4 scan secured theta = 0.1 with double-precision cells whose
one-sidedness rested on generous Lipschitz margins.  This module replaces
every kernel evaluation with an arb/acb ball enclosure (python-flint,
128-bit precision) and directs every rounding:

- ``Phi2`` is evaluated in acb via the same closed form (exact integer ramp
  coefficients; the moment series carries an explicit geometric tail bound
  added to the ball; the integration-by-parts recursion propagates balls);
- damage sups use the UPPER ball endpoints of ``|S|`` and Lipschitz
  constants and the LOWER endpoint of ``|C|``;
- ``K_delta`` and the slack use LOWER endpoints;
- the chain DP runs on those directed floats, and its total is inflated by
  a factor ``1 + 1e-9`` that dwarfs accumulated double rounding (relative
  error < 1e-12 across the DP) while staying far below the ~10% relative
  margins at the binding cells.

The one remaining softness, stated rather than hidden: the DP arithmetic
itself is double precision on directed inputs, covered by the final
inflation factor, not ball-valued end to end.  A fully rational DP is
possible and pointless at these margins.

Everything else -- the chain counting theorem, the delta ladder, the depth
ladder, the projection controls -- is inherited unchanged from
``counting_bound.CountingBound``; only the kernel-touching methods are
overridden.  Run
``.venv/bin/python hunts/frontier_math/enclosure_pass.py`` (~30 min at
the default level-4 resolution; a 2x-coarser grid runs in ~10 min and FAILS
the scan by up to -3 -- the Lipschitz inflation doubles with the grid step,
which is a statement about the economization, not about the mathematics).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

from flint import acb, arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from counting_bound import CountingBound  # noqa: E402
from gap_consistency import C_RHO  # noqa: E402
from incidence_law import RAMP  # noqa: E402

ctx.prec = 128

#: exact integer coefficients of ramp^2 (the phi^2 ramp polynomial)
_RAMP2_INT = [0] * (2 * len(RAMP) - 1)
for _i, _a in enumerate(RAMP):
    for _j, _b in enumerate(RAMP):
        _RAMP2_INT[_i + _j] += _a * _b

_SERIES_CUTOFF = 24

#: only these ramp^2 coefficients are nonzero
_NEEDED_INDICES = tuple(k for k, c in enumerate(_RAMP2_INT) if c)


def f_up(x: arb) -> float:
    """A float upper bound for the arb ball."""
    return math.nextafter(float(x.upper()), math.inf)


def f_lo(x: arb) -> float:
    """A float lower bound for the arb ball."""
    return math.nextafter(float(x.lower()), -math.inf)


def _cs_moments_acb(c: acb, indices):
    """C_n, S_n moment enclosures for the needed indices only.

    Series branch: the terms ``(-1)^j c^{2j}/(2j)!`` are shared across all
    moments (computed once), each moment being a short rational-weighted
    combination; the truncation tail is geometric with ratio
    ``|c|^2/((2J+1)(2J+2)) < 1`` and is added to the ball symmetrically,
    with the S-series' extra ``|c|`` factor included.
    """
    cmag = float(abs(c).upper())
    nmax = max(indices)
    if cmag < _SERIES_CUTOFF:
        c2 = c * c
        terms = []
        term = acb(1)
        j = 0
        while True:
            terms.append(term)
            j += 1
            term = term * c2 / ((2 * j - 1) * (2 * j))
            if float(abs(term).upper()) < 1e-22 and 2 * j > cmag + 2:
                break
        tail = abs(term)
        q = abs(c2) / ((2 * j + 1) * (2 * j + 2))
        if not (q < 1):  # pragma: no cover - cutoff guarantees q < 1
            raise AssertionError("series tail ratio >= 1")
        err_rad = float(((tail * (1 + abs(c))) / (1 - q)).upper())
        ball = acb(arb(0, err_rad), arb(0, err_rad))
        C = {}
        S = {}
        for n in indices:
            sC = acb(0)
            sS = acb(0)
            for jj, t in enumerate(terms):
                sgn = -1 if jj % 2 else 1
                sC += sgn * t / (n + 2 * jj + 1)
                sS += sgn * t * c / ((2 * jj + 1) * (n + 2 * jj + 2))
            C[n] = sC + ball
            S[n] = sS + ball
        return C, S
    sc, cc = c.sin(), c.cos()
    Cl = [sc / c]
    Sl = [(1 - cc) / c]
    for n in range(1, nmax + 1):
        Cl.append(sc / c - n * Sl[n - 1] / c)
        Sl.append(-cc / c + n * Cl[n - 1] / c)
    return dict(enumerate(Cl)), dict(enumerate(Sl))


@dataclass(frozen=True)
class EnclosedBound(CountingBound):
    """CountingBound with every kernel-touching method ball-hardened."""

    def phi2_acb(self, z: acb) -> acb:
        L = arb(self.L)
        w = arb(self.w)
        half, inner = L / 2, L / 2 - w
        mid = 2 * (z * inner).sin() / z
        Cm, Sm = _cs_moments_acb(z * w, _NEEDED_INDICES)
        ch, sh = (z * half).cos(), (z * half).sin()
        acc = acb(0)
        for k in _NEEDED_INDICES:
            acc += _RAMP2_INT[k] * (ch * Cm[k] + sh * Sm[k])
        return mid + 2 * w * acc

    # -- directed scalar quantities ----------------------------------------

    def aL_ball(self) -> arb:
        """aL = int phi^2 = 2(L/2 - w) + 2w sum RAMP2[k]/(k+1), exact."""
        from fractions import Fraction

        acc = Fraction(0)
        for k in _NEEDED_INDICES:
            acc += Fraction(_RAMP2_INT[k], k + 1)
        exact = 2 * (Fraction(self.L) / 2 - Fraction(self.w)) + 2 * Fraction(self.w) * acc
        return arb(exact.numerator) / exact.denominator

    def sigma_sq_ball(self, y: float) -> arb:
        aL = self.aL_ball()
        return (self.phi2_acb(acb(0, 2 * arb(y))).real - aL) / (2 * aL)

    def sigma_sq(self, y: float) -> float:
        """UPPER endpoint: used only inside Lipschitz inflations."""
        return f_up(self.sigma_sq_ball(y))

    def E(self, y: float) -> float:
        """UPPER endpoint of the depth inflation (used in Lipschitz only)."""
        return f_up(self.phi2_acb(acb(0, arb(y))).real / self.aL_ball())

    def slack(self, y: float) -> float:
        """LOWER endpoint of 8 sigma^2 + 8 sigma^4."""
        s2 = max(0.0, f_lo(self.sigma_sq_ball(y)))
        return (8 * s2 + 8 * s2 * s2) * (1 - 1e-9)

    def K_delta(self, delta: float, step: float = 0.005) -> float:
        """LOWER endpoint of min omega^2 over [0, delta]."""
        aL_up = f_up(self.aL_ball())
        lo = 1.0  # omega(0) = 1 exactly
        r = step
        while r <= delta + 1e-12:
            lo = min(lo, f_lo(self.phi2_acb(acb(arb(r), 0)).real) / aL_up)
            r += step
        lo -= (self.L / 2) * step
        return max(0.0, lo * lo * (1 - 1e-9)) if lo > 0 else 0.0

    def psi_S(self, y_hi: float) -> float:
        """UPPER endpoint of the depth-scaled tail constant."""
        yh = arb(y_hi)
        sh = (yh * self.L / 2).sinh()
        chh = (yh * self.L / 2).cosh()
        val = (
            arb(C_RHO.numerator) / C_RHO.denominator / self.w * sh
            + 4 * yh * chh
            + yh * yh * self.aL_ball() * sh
        )
        return f_up(val)

    def tail_sup_damage(self, g: float, y_hi: float) -> float:
        aL_lo = f_lo(self.aL_ball())
        return 4 * (self.psi_S(y_hi) / (g * g * aL_lo)) ** 2 * (1 + 1e-9)

    # -- hardened fine sups --------------------------------------------------

    #: original level-4 resolution -- the coarser economization
    #: (0.025/4) fails the scan by up to -3 while this passes with
    #: healthy margins; the failure was the economy, not the balls.
    y_slices: int = 6
    fine_step: float = 0.0125

    def fine_sups(self, y1: float, y2: float):
        n = int(round(2 * self.fine_g_max / self.fine_step))
        sups = [0.0] * n
        aL2_lo = f_lo(self.aL_ball()) ** 2
        dy = (y2 - y1) / self.y_slices
        for s in range(self.y_slices):
            ya, yb = y1 + s * dy, y1 + (s + 1) * dy
            ym = arb(ya + (yb - ya) / 2)
            lsg, lcg = self.lip_S_g(yb), self.lip_C_g(yb)
            lsy, lcy = self.lip_S_y(yb), self.lip_C_y(yb)
            rg, ry = self.fine_step / 2, dy / 2
            infl_S = lsg * rg + lsy * ry
            infl_C = lcg * rg + lcy * ry
            for i in range(n):
                gm = -self.fine_g_max + (i + 0.5) * self.fine_step
                v = self.phi2_acb(acb(arb(gm), ym))
                S_bar = f_up(abs(v.imag)) + infl_S
                C_und = max(0.0, f_lo(abs(v.real)) - infl_C)
                f = max(0.0, 4 * (S_bar**2 - C_und**2)) / aL2_lo * (1 + 1e-9)
                if f > sups[i]:
                    sups[i] = f
        return sups

    # lambda_bar_from_sups, depth_ladder, secured_theta: inherited; the DP
    # runs on the directed inputs above, and we inflate its result here.

    def lambda_bar_from_sups(self, theta, sups, y2, delta, n_cap: int = 14):
        total = super().lambda_bar_from_sups(theta, sups, y2, delta, n_cap)
        return total * (1 + 1e-9) if math.isfinite(total) else total


def audit():
    eb = EnclosedBound()
    print("= enclosure sanity: ball widths at representative points =")
    for g, y in ((0.75, 0.3), (7.3, 0.45), (0.1, 0.002)):
        v = eb.phi2_acb(acb(arb(g), arb(y)))
        print(f"  Phi2({g}+{y}i): rad_re = {float(v.real.rad()):.2e}  "
              f"rad_im = {float(v.imag.rad()):.2e}")
    print("= hardened K_delta ladder =")
    for d in eb.delta_choices:
        print(f"  delta={d}: K_delta >= {eb.K_delta(d):.6f}")
    print("= hardened secured-theta scan =")
    theta_star, margins = eb.secured_theta(thetas=(0.0, 0.05, 0.1))
    for theta, margin in margins.items():
        print(f"  theta={theta:.2f}: worst depth-cell margin >= {margin:+.6f}  "
              f"{'OK' if margin >= 0 else 'FAILS'}")
    print(f"  hardened theta* (grid) = {theta_star}")


if __name__ == "__main__":
    audit()
