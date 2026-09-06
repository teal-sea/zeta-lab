"""Burden (b): the band-lattice dual at the RAMP-MOLLIFIED paper window.

WHY THIS MODULE EXISTS.  paper_chain.py measured theta* = 0.995 at the
paper's field Phi2 = FT(phi^2) with phi^2 = cos(sqrt2 .) on the pure
width-1 box.  The source paper's actual window is ramp-mollified: in
box-normalized units the taper is

    eta(u) = Psi((1/2 - |u|)/eps),    eps = w/L in (0, 1/8],

with Psi a fixed C^3 nondecreasing shape, Psi = 0 on (-inf, 0] and
Psi = 1 on [1, inf).  The taper multiplies phi, so phi^2 carries eta^2:

    phi^2_eps(u) = cos(sqrt2 u) * eta(u)^2   on |u| <= 1/2,

and the incidence kernel becomes

    Phi2_eps(z) = int_{-1/2}^{1/2} phi^2_eps(u) e^{izu} du
                = 2 int_0^{1/2} phi^2_eps(u) cos(zu) du   (even integrand;
                  the cosine form holds for complex z as well).

The paper states the window constants differ from the pure box by
O(1/L) = O(eps); this module measures whether the retention theta*
survives the ramp, for eps in {1/8, 1/16, 1/32} and as eps -> 0.

THE SHAPE.  The paper fixes Psi once and for all but leaves its shape
free.  Here Psi is fixed concretely as the C^3 polynomial smoothstep

    Psi(x) = 35 x^4 - 84 x^5 + 70 x^6 - 20 x^7   on [0, 1],

whose first three derivatives vanish at both endpoints (pinned
symbolically by sympy in test_ramped_field.py; Psi' = 140 x^3 (1-x)^3
>= 0, so Psi is nondecreasing).  CAVEAT: every number below is
shape-dependent in principle; shape_spot_check() measures the movement
under one alternative admissible shape (the degree-9 smoothstep, whose
first FOUR endpoint derivatives vanish) at one (eps, y) and finds it
small, but no supremum over shapes is taken.

QUADRATURE, NOT CLOSED FORMS.  phi^2_eps has no closed-form transform,
so the field is computed by fixed-node Gauss-Legendre quadrature on two
panels, [0, 1/2 - eps] (pure cos, C-infinity) and [1/2 - eps, 1/2] (the
ramp, polynomial times cos, C-infinity on the closed panel), so the
rule converges spectrally on each panel.  Derivatives in z are taken
under the integral (integrand times -u sin(zu), -u^2 cos(zu)).  Three
controls pin the rule:

  * a quadrature LADDER: the same integrals at doubled node counts,
    worst defect over a probe set that includes the largest resolved g;
  * an mpmath tanh-sinh ORACLE at mp.workdps(30) (all mpmath work is
    inside mp.workdps context managers; no global state is modified);
  * an eps -> 0 control: at eps = 1e-4 (and 1e-3) the field must match
    paper_chain.phipap to the derived O(eps) bound
    2 * eps * c_psi * cosh(|Im z|/2), c_psi = int_0^1 (1 - Psi^2);
    the constant is measured, not assumed.

ERROR ACCOUNTING, ONE-SIDED.  The pinned quadrature-error bounds e0,
e1, e2 (10x the worst ladder/oracle defect for Phi2, Phi2', Phi2'') are
ADDED one-sidedly wherever a field value enters a bound: band maxima
are raised by the field error and by the (error-inflated) local slope
margin, off-band curvature uses q lowered by e0-terms against
|q''| raised by e1/e2-terms, the band-charge floor is lowered, and the
slack side is computed from a down-shifted sigma2.  The relative error
e0/A ~ 1e-13 of the normalisation A itself is absorbed by the 10x
safety factor in the pins and is stated here rather than threaded
through every denominator.

Everything else follows band_dual.py / paper_chain.py discipline: band
membership on the raw grid of the POSITIVE part of the damage field,
LOCAL slope margins only (never a per-cell Lipschitz blanket summed
over cells), cross-band charges dropped one-sidedly (omega^2 >= 0 is a
square), per-band square completion, closed-form 1/g^2 tail from a
one-integration-by-parts Im-majorant recomputed for the ramped window
(whose boundary term vanishes: eta(1/2) = 0), and the cap MUST diverge
at theta = 1.  The band lattice is recomputed from the ramped field's
own zeros at every eps; no eps = 0 band data is reused.  If the
no-missed-band completeness test does not clear at some (eps, y), the
cap for that pair is reported as not-established (infinite) rather
than patched with a blanket allowance.

Nothing here computes a proportion and nothing here is evidence about
RH; all grades are measured/observed, never anything stronger.

Run ``.venv/bin/python hunts/frontier_math/ramped_field.py`` (~4 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np
from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import (  # noqa: E402
    MEAN_GAP,
    explicit_single_pair_adversary,
    phipap,
)

S2 = math.sqrt(2.0)

#: Psi(x) = 35x^4 - 84x^5 + 70x^6 - 20x^7, highest power first (np.polyval).
PSI7 = np.array([-20.0, 70.0, -84.0, 35.0, 0.0, 0.0, 0.0, 0.0])
#: alternative admissible shape for the spot check: the degree-9
#: smoothstep 126x^5 - 420x^6 + 540x^7 - 315x^8 + 70x^9 (C^4, hence C^3).
PSI9 = np.array([70.0, -315.0, 540.0, -420.0, 126.0, 0.0, 0.0, 0.0, 0.0, 0.0])


def _gauss(n: int, a: float, b: float):
    """Gauss-Legendre nodes/weights on [a, b]."""
    x, w = np.polynomial.legendre.leggauss(n)
    return 0.5 * (b - a) * x + 0.5 * (a + b), 0.5 * (b - a) * w


class RampedField:
    """Phi2_eps and its first two z-derivatives, quadrature-computed.

    Parameters: eps in (0, 1/8]; n1/n2 Gauss-Legendre node counts on the
    box panel [0, 1/2 - eps] and the ramp panel [1/2 - eps, 1/2];
    psi_coeffs the smoothstep polynomial (np.polyval order); gmax_pin
    the largest |Re z| the error pins must cover (set it to the dual's
    resolved G).
    """

    def __init__(self, eps: float, n1: int = 160, n2: int = 64,
                 psi_coeffs: np.ndarray = PSI7, gmax_pin: float = 400.0,
                 pin: bool = True):
        if not 0.0 < eps <= 0.125:
            raise ValueError("eps must lie in (0, 1/8]")
        self.eps = float(eps)
        self.n1, self.n2 = int(n1), int(n2)
        self.psi_coeffs = np.asarray(psi_coeffs, float)
        self.dpsi_coeffs = np.polyder(self.psi_coeffs)
        self.gmax_pin = float(gmax_pin)
        self._rules: dict[int, tuple[np.ndarray, np.ndarray]] = {}
        u, c = self._rule(1)
        #: normalisation A_eps = Phi2_eps(0) = sum of rule coefficients
        self.A = float(np.sum(c))
        #: Lip constant of Re Phi2_eps on the real axis: int |u| phi^2_eps
        #: (phi^2_eps >= 0), 1.001 inflation as in paper_chain
        self.L1 = float(np.sum(c * u)) * 1.001
        self._tvh = self._tv_half()
        self.e0 = self.e1 = self.e2 = 0.0
        if pin:
            self.pin_errors()

    # -- the taper ----------------------------------------------------------

    def psi(self, t):
        t = np.asarray(t, float)
        return np.where(t >= 1.0, 1.0,
                        np.where(t <= 0.0, 0.0,
                                 np.polyval(self.psi_coeffs,
                                            np.clip(t, 0.0, 1.0))))

    def eta(self, u):
        return self.psi((0.5 - np.abs(np.asarray(u, float))) / self.eps)

    # -- the quadrature rule ------------------------------------------------

    def _rule(self, mult: int):
        """(nodes u_k, coefficients c_k) with Phi2(z) = sum c_k cos(z u_k)."""
        if mult not in self._rules:
            a = 0.5 - self.eps
            u1, w1 = _gauss(self.n1 * mult, 0.0, a)
            u2, w2 = _gauss(self.n2 * mult, a, 0.5)
            u = np.concatenate([u1, u2])
            w = np.concatenate([w1, w2])
            c = 2.0 * w * np.cos(S2 * u) * self.eta(u) ** 2
            self._rules[mult] = (u, c)
        return self._rules[mult]

    # -- generic (any complex z) evaluation ---------------------------------

    def phi2(self, z, mult: int = 1):
        u, c = self._rule(mult)
        z = np.atleast_1d(np.asarray(z, complex))
        return np.cos(z[:, None] * u[None, :]) @ c

    def d1(self, z, mult: int = 1):
        u, c = self._rule(mult)
        z = np.atleast_1d(np.asarray(z, complex))
        return -(np.sin(z[:, None] * u[None, :]) @ (c * u))

    def d2(self, z, mult: int = 1):
        u, c = self._rule(mult)
        z = np.atleast_1d(np.asarray(z, complex))
        return -(np.cos(z[:, None] * u[None, :]) @ (c * u * u))

    # -- fast path: z = g + iy on a long real grid at fixed depth ----------

    def field_grid(self, gs, y: float, mult: int = 1, chunk: int = 40000):
        """(Phi2, Phi2', Phi2'') at gs + iy, chunked real-trig matmuls.

        cos((g+iy)u) = cos(gu)cosh(yu) - i sin(gu)sinh(yu),
        sin((g+iy)u) = sin(gu)cosh(yu) + i cos(gu)sinh(yu).
        """
        u, c = self._rule(mult)
        gs = np.asarray(gs, float)
        ch, sh = np.cosh(y * u), np.sinh(y * u)
        c0c, c0s = c * ch, c * sh
        c1c, c1s = c * u * ch, c * u * sh
        c2c, c2s = c * u * u * ch, c * u * u * sh
        v0 = np.empty(len(gs), complex)
        v1 = np.empty(len(gs), complex)
        v2 = np.empty(len(gs), complex)
        for lo in range(0, len(gs), chunk):
            g = gs[lo:lo + chunk]
            G = g[:, None] * u[None, :]
            cg, sg = np.cos(G), np.sin(G)
            v0[lo:lo + chunk] = cg @ c0c - 1j * (sg @ c0s)
            v1[lo:lo + chunk] = -(sg @ c1c) - 1j * (cg @ c1s)
            v2[lo:lo + chunk] = -(cg @ c2c) + 1j * (sg @ c2s)
        return v0, v1, v2

    # -- the mpmath oracle (workdps context managers, no state leak) --------

    def _psi_mp(self, t):
        if t >= 1:
            return mp.mpf(1)
        if t <= 0:
            return mp.mpf(0)
        acc = mp.mpf(0)
        for coeff in self.psi_coeffs:
            acc = acc * t + mp.mpf(coeff)
        return acc

    def _oracle(self, z, order: int = 0, dps: int = 30):
        """Phi2_eps / d1 / d2 at complex z via mp.quad at workdps(dps)."""
        with mp.workdps(dps):
            eps = mp.mpf(self.eps)
            half = mp.mpf(1) / 2
            a = half - eps
            zz = mp.mpc(z)
            s2 = mp.sqrt(2)

            def integrand(u):
                p = 2 * mp.cos(s2 * u) * self._psi_mp((half - u) / eps) ** 2
                if order == 0:
                    return p * mp.cos(zz * u)
                if order == 1:
                    return -p * u * mp.sin(zz * u)
                return -p * u * u * mp.cos(zz * u)

            val = mp.quad(integrand, [0, a, half])
            return complex(val)

    # -- error pins ---------------------------------------------------------

    def pin_errors(self, safety: float = 10.0) -> dict:
        """Measure quadrature defects; set one-sided bounds e0, e1, e2.

        Ladder: rule vs doubled rule over a probe set including the
        largest resolved g (worst oscillation) and the pure-imaginary
        points the slack side uses.  Oracle: rule vs mp.workdps(30)
        tanh-sinh at moderate-g points (real and complex).  Each e_i is
        ``safety`` times the worst observed defect (floored at 1e-15).
        """
        gm = self.gmax_pin
        ladder_z = [0.7, 5.3 + 0.3j, 31.4 + 0.49j, 0.31 * gm + 0.1j,
                    0.97 * gm + 0.49j, 0.98j, 0.49j]
        worst = [0.0, 0.0, 0.0]
        for z in ladder_z:
            fs = [self.phi2, self.d1, self.d2]
            for i, f in enumerate(fs):
                d = abs(complex(f(z)[0]) - complex(f(z, mult=2)[0]))
                worst[i] = max(worst[i], d)
        self.ladder_worst = tuple(worst)
        oracle_z = [0.9, 3.7 + 0.49j, 21.3 + 0.1j, 0.6j]
        oworst = [0.0, 0.0, 0.0]
        for z in oracle_z:
            for i, f in enumerate([self.phi2, self.d1, self.d2]):
                d = abs(complex(f(z)[0]) - self._oracle(z, order=i))
                oworst[i] = max(oworst[i], d)
        self.oracle_worst = tuple(oworst)
        e = [safety * max(worst[i], oworst[i], 1e-15) for i in range(3)]
        self.e0, self.e1, self.e2 = e
        return {"ladder": self.ladder_worst, "oracle": self.oracle_worst,
                "e": tuple(e)}

    # -- window constants for the tail majorant -----------------------------

    def _tv_half(self) -> float:
        """Upper bound on int_0^{1/2} |(phi^2_eps)'(u)| du.

        Box panel: (phi^2_eps)' = -sqrt2 sin(sqrt2 u) <= 0, so the
        contribution is exactly 1 - cos(sqrt2 (1/2 - eps)).  Ramp panel:
        fine-grid trapezoid of |.| with a 1.05 one-sided inflation
        (this constant only needs to be an over-estimate)."""
        a = 0.5 - self.eps
        box = 1.0 - math.cos(S2 * a)
        us = np.linspace(a, 0.5, 2001)
        t = (0.5 - us) / self.eps
        e = np.polyval(self.psi_coeffs, np.clip(t, 0.0, 1.0))
        de = -np.polyval(self.dpsi_coeffs, np.clip(t, 0.0, 1.0)) / self.eps
        dp = -S2 * np.sin(S2 * us) * e * e + 2.0 * np.cos(S2 * us) * e * de
        ramp = float(np.trapezoid(np.abs(dp), us)) * 1.05
        return box + ramp

    def c_im(self, y: float) -> float:
        """|Im Phi2_eps(g+iy)| <= c_im(y)/|g|: one integration by parts of
        -2 int_0^{1/2} phi^2_eps(u) sinh(yu) sin(gu) du.  The boundary
        term vanishes (eta(1/2) = 0), leaving
        c = 2 sinh(y/2) TV_half + y cosh(y/2) A_eps, plus the pinned e0
        on the half-mass, one-sided."""
        return (2.0 * math.sinh(y / 2) * self._tvh
                + y * math.cosh(y / 2) * (self.A + self.e0))


class RampedBandDual:
    """band_dual / paper_chain's single-pair band-lattice dual at the
    ramped field, with the quadrature error pins added one-sidedly.

    Also implements the ``pc``-shaped surface (W, omega2) that
    paper_chain.explicit_single_pair_adversary consumes, so the greedy
    adversary control is reused rather than re-implemented."""

    def __init__(self, rf: RampedField, step: float = 0.0005,
                 G: float = 400.0):
        self.rf = rf
        self.step = float(step)
        self.G = float(G)
        self.A = rf.A
        self._fields: dict[float, tuple] = {}
        self._band_cache: dict[float, list] = {}
        self._charge_cache: dict[float, float] = {}
        # the pc-compat alias used by reused paper_chain controls
        self.pc = self

    # -- the chain layer (pc-compatible) ------------------------------------

    def W(self, g, y: float):
        g = np.asarray(g, float)
        v = self.rf.phi2(g.ravel() + 1j * y)
        return (2 * (v.real ** 2 - v.imag ** 2) / self.A ** 2).reshape(g.shape)

    def omega2(self, r):
        r = np.asarray(r, complex)
        v = self.rf.phi2(r.ravel()).real / self.A
        return (v * v).reshape(r.shape)

    def sigma2(self, y: float) -> float:
        """Down-shifted (one-sided) sigma2: quadrature error subtracted
        from the numerator and added to the denominator, so the slack
        side can only be under-stated."""
        v = float(self.rf.phi2(np.array([2j * y]))[0].real)
        e0 = self.rf.e0
        return (v - e0 - (self.A + e0)) / (2 * (self.A + e0))

    def slack(self, y: float) -> float:
        s2 = self.sigma2(y)
        return 8 * s2 + 8 * s2 * s2

    # -- the field on the raw grid ------------------------------------------

    def _field(self, y: float):
        if y not in self._fields:
            gs = np.arange(self.step, self.G, self.step)
            v0, v1, v2 = self.rf.field_grid(gs, y)
            ph = np.abs(v0)
            p1 = np.abs(v1)
            p2 = np.abs(v2)
            f = -4 * (v0.real ** 2 - v0.imag ** 2) / self.A ** 2
            self._fields[y] = (gs, f, ph, p1, p2)
        return self._fields[y]

    def bands(self, y: float):
        """One-sided band list [(lo, hi, F_up)] on g > 0: membership on
        the raw grid (singleton groups kept, strictly safer than
        paper_chain, which dropped them), F_up raised by the pointwise
        quadrature error AND the LOCAL error-inflated slope margin."""
        if y in self._band_cache:
            return self._band_cache[y]
        gs, f, ph, p1, _ = self._field(y)
        e0, e1 = self.rf.e0, self.rf.e1
        idx = np.where(f > 0)[0]
        out = []
        if len(idx):
            groups = np.split(idx, np.where(np.diff(idx) > 1)[0] + 1)
            for gr in groups:
                lo = float(gs[gr[0]]) - self.step
                hi = float(gs[gr[-1]]) + self.step
                # |df/dg| <= 8 |Phi2||Phi2'|/A^2, LOCAL max, errors added
                slope = 8 * float(((ph[gr] + e0) * (p1[gr] + e1)).max()) \
                    / self.A ** 2
                # pointwise field error: |delta f| <= 4(2|Phi2|+e0)e0/A^2
                # per component, doubled across Re/Im (one-sided)
                ef = 8 * e0 * (2 * float(ph[gr].max()) + e0) / self.A ** 2
                F = float(f[gr].max()) + ef + slope * self.step
                out.append((lo, hi, F))
        self._band_cache[y] = out
        return out

    def no_missed_band(self, y: float) -> dict:
        """Completeness: off the (one-cell-widened) resolved bands,
        q := Re^2 - Im^2 must dominate (1/8)|q''| step^2 with
        |q''| <= 2(|Phi2'|^2 + |Phi2||Phi2''|).  Quadrature errors are
        applied one-sidedly: q lowered, |q''| raised."""
        gs, f, ph, p1, p2 = self._field(y)
        e0, e1, e2 = self.rf.e0, self.rf.e1, self.rf.e2
        q = -f * self.A ** 2 / 4
        on = f > 0
        widened = on.copy()
        widened[1:] |= on[:-1]
        widened[:-1] |= on[1:]
        off = ~widened
        if not np.any(off):
            return {"worst_ratio": math.inf, "clear": True}
        q_low = q[off] - 2 * e0 * (2 * ph[off] + e0)
        qpp_up = 2 * ((p1[off] + e1) ** 2 + (ph[off] + e0) * (p2[off] + e2))
        bound = qpp_up * self.step ** 2 / 8
        ratio = float(np.min(q_low / bound))
        return {"worst_ratio": ratio, "clear": ratio > 1.0}

    def off_band_allowance(self, y: float) -> float:
        """Exactly 0 when completeness clears; any (eps, y) where it does
        not clear is reported as NOT ESTABLISHED by cap(), never patched
        with a summed per-cell blanket."""
        return 0.0 if self.no_missed_band(y)["clear"] else math.nan

    def band_charge(self, width: float) -> float:
        """One-sided min of omega^2 over [0, width]: grid min lowered by
        the Lipschitz step margin AND the quadrature error e0/A."""
        key = round(width / self.step)
        if key not in self._charge_cache:
            rs = np.arange(0.0, width + self.step, self.step)
            v0, _, _ = self.rf.field_grid(rs, 0.0)
            lo = float(np.min(v0.real / self.A))
            lo -= (self.rf.L1 / self.A) * self.step + self.rf.e0 / self.A
            self._charge_cache[key] = max(0.0, lo) ** 2
        return self._charge_cache[key]

    # -- the tail ------------------------------------------------------------

    def band_period_lower(self, y: float) -> float:
        bs = self.bands(y)
        if len(bs) < 3:
            return MEAN_GAP
        centres = [(lo + hi) / 2 for lo, hi, _ in bs]
        return min(centres[i + 1] - centres[i]
                   for i in range(len(centres) - 1))

    def tail_sum(self, y: float) -> float:
        """Closed-form majorant of the band maxima beyond G, one side:
        F <= 4 (c_im/(A g))^2, bands at least P apart."""
        C = self.rf.c_im(y) / self.A
        P = self.band_period_lower(y)
        return 4 * C * C * (1 / self.G ** 2 + 1 / (P * self.G))

    # -- the dual ------------------------------------------------------------

    def cap(self, theta: float, y: float) -> dict:
        """Band-lattice cap on sup_X [D(X) - (1-theta) R(X)]: cross-band
        charges dropped one-sidedly (omega^2 >= 0), per-band square
        completion max_m [m F - c m(m-1) K], closed-form tail.  If the
        completeness control has not cleared at this (eps, y) the cap is
        reported infinite (not established)."""
        if not self.no_missed_band(y)["clear"]:
            return {"cap": math.inf, "bands": None, "m_star": None,
                    "tail": None, "off_band": None,
                    "note": "completeness did not clear; cap not "
                            "established at this (eps, y)"}
        c = 1 - theta
        bs = self.bands(y)
        if not bs:
            return {"cap": 0.0, "bands": 0, "m_star": 0, "tail": 0.0,
                    "off_band": 0.0}
        total = 0.0
        worst_m = 1
        K_min = math.inf
        for lo, hi, F in bs:
            K = self.band_charge(hi - lo)
            K_min = min(K_min, K)
            if c <= 0 or K <= 0:
                return {"cap": math.inf, "bands": len(bs), "m_star": None,
                        "tail": None, "off_band": None}
            if F <= 2 * c * K:
                B, m = F, 1
            else:
                B = (F + c * K) ** 2 / (4 * c * K)
                m = int(round((F + c * K) / (2 * c * K)))
            total += B
            worst_m = max(worst_m, m)
        tail = self.tail_sum(y)
        C = self.rf.c_im(y) / self.A
        F_G = 4 * C * C / self.G ** 2
        if F_G > 2 * c * K_min:
            raise AssertionError("tail band left the single-occupancy regime")
        return {"cap": 2 * (total + tail), "bands": len(bs),
                "m_star": worst_m, "tail": 2 * tail, "off_band": 0.0}

    def theta_scan(self, ys=(0.02, 0.1, 0.3, 0.49),
                   thetas=(0.9, 0.99, 0.995, 0.999)):
        """Largest grid theta with cap <= slack at every probe depth."""
        margins = {}
        star = None
        for theta in thetas:
            worst, arg = math.inf, None
            for y in ys:
                m = self.slack(y) - self.cap(theta, y)["cap"]
                if m < worst:
                    worst, arg = m, y
            margins[theta] = (worst, arg)
            if worst >= 0:
                star = theta
        return star, margins

    def multiplicity_threshold(self, y: float) -> float:
        bs = self.bands(y)
        worst = max(bs, key=lambda b: b[2])
        K = self.band_charge(worst[1] - worst[0])
        return 1 - worst[2] / (2 * K)


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def c_psi(psi_coeffs=PSI7, n: int = 96) -> float:
    """int_0^1 (1 - Psi(t)^2) dt, the constant in the O(eps) field bound."""
    t, w = _gauss(n, 0.0, 1.0)
    return float(np.sum(w * (1.0 - np.polyval(psi_coeffs, t) ** 2)))


def eps_zero_convergence(eps_list=(1e-3, 1e-4),
                         zs=(0.5, 2.7, 14.9, 3.0 + 0.49j, 30.0 + 0.1j)):
    """The ramped field must approach paper_chain's closed form phipap as
    eps -> 0, inside the derived bound
    |Phi2_eps(z) - phihat_mt(z)| <= 2 eps c_psi cosh(|Im z|/2).
    Returns per-eps worst defect, defect/eps, and the derived cap on it."""
    cp = c_psi()
    out = {}
    for eps in eps_list:
        rf = RampedField(eps, pin=False)
        worst = worst_rel = 0.0
        for z in zs:
            bound_c = 2 * cp * math.cosh(abs(complex(z).imag) / 2)
            d = abs(complex(rf.phi2(z)[0]) - complex(phipap(z)))
            worst = max(worst, d)
            worst_rel = max(worst_rel, d / (eps * bound_c))
        out[eps] = {"worst_defect": worst, "constant": worst / eps,
                    "derived_cap_on_constant": 2 * cp * math.cosh(0.245),
                    "inside_bound": worst_rel <= 1.0}
    return out


def shape_spot_check(eps: float = 0.125, y: float = 0.49,
                     theta: float = 0.995, G: float = 120.0):
    """One alternative C^3-admissible shape (degree-9 smoothstep) at one
    (eps, y): how far do the cap and slack move?  A caveat-measurer,
    not a supremum over shapes."""
    out = {}
    for name, coeffs in (("psi7", PSI7), ("psi9", PSI9)):
        rf = RampedField(eps, psi_coeffs=coeffs, gmax_pin=G)
        bd = RampedBandDual(rf, G=G)
        out[name] = {"A": rf.A, "cap": bd.cap(theta, y)["cap"],
                     "slack": bd.slack(y)}
    c7, c9 = out["psi7"]["cap"], out["psi9"]["cap"]
    s7, s9 = out["psi7"]["slack"], out["psi9"]["slack"]
    out["rel_move_cap"] = abs(c9 - c7) / c7
    out["rel_move_slack"] = abs(s9 - s7) / s7
    out["margin_sign_same"] = (s7 - c7 > 0) == (s9 - c9 > 0)
    return out


def dominates_adversary(bd: RampedBandDual, ys=(0.3, 0.49),
                        theta: float = 0.995, halfrange: float = 110.0):
    """The dual must dominate the measured greedy adversary (primal <=
    dual); the adversary itself is paper_chain's, reused unchanged."""
    out = []
    for y in ys:
        rec = explicit_single_pair_adversary(bd, y, theta=theta,
                                             halfrange=halfrange)
        measured = rec["D"] - (1 - theta) * rec["R"]
        cap = bd.cap(theta, y)["cap"]
        out.append({"y": y, "measured": measured, "cap": cap,
                    "dominated": measured <= cap})
    return out


# ---------------------------------------------------------------------------
# the audit
# ---------------------------------------------------------------------------


def audit():
    ys = (0.02, 0.1, 0.3, 0.49)
    print("= eps -> 0 control: ramped field vs paper closed form =")
    for eps, rec in eps_zero_convergence().items():
        print(f"  eps={eps:g}: worst defect {rec['worst_defect']:.3e}, "
              f"defect/eps = {rec['constant']:.4f} "
              f"(derived cap {rec['derived_cap_on_constant']:.4f}), "
              f"inside bound: {rec['inside_bound']}")
    print(f"  c_psi = {c_psi():.6f}")
    results = {}
    for eps in (0.125, 0.0625, 0.03125):
        rf = RampedField(eps, gmax_pin=400.0)
        bd = RampedBandDual(rf, G=400.0)
        print(f"\n== eps = {eps} (A = {rf.A:.8f}, L1 = {rf.L1:.6f}) ==")
        print(f"  quadrature pins: ladder worst {max(rf.ladder_worst):.2e}, "
              f"oracle worst {max(rf.oracle_worst):.2e}, "
              f"e = ({rf.e0:.1e}, {rf.e1:.1e}, {rf.e2:.1e})")
        ok = True
        for y in ys:
            r = bd.no_missed_band(y)
            good = r["clear"] and r["worst_ratio"] > 100
            ok &= good
            print(f"  completeness y={y}: worst ratio "
                  f"{r['worst_ratio']:.0f}  {'PASS' if good else 'FAIL'}")
        if not ok:
            print("  !! completeness did not clear at > 100; NO theta claim"
                  " at this eps (no blanket substituted).")
            results[eps] = (None, None)
            continue
        star, margins = bd.theta_scan(ys=ys)
        for th, (m, arg) in margins.items():
            print(f"  theta={th}: worst margin {m:+.6f} at y={arg}  "
                  f"{'ok' if m >= 0 else 'FAILS'}")
        print(f"  theta*(eps={eps}) = {star}")
        if star is not None:
            for y in ys:
                rec = bd.cap(star, y)
                s = bd.slack(y)
                print(f"    y={y}: cap {rec['cap']:.6f}  slack {s:.6f}  "
                      f"margin {s - rec['cap']:+.6f}  bands {rec['bands']}"
                      f"  m* {rec['m_star']}")
            for y in (0.3, 0.49):
                print(f"    multiplicity threshold y={y}: "
                      f"{bd.multiplicity_threshold(y):.5f}")
        r = bd.cap(1.0, 0.49)
        print(f"  theta=1 cap = {r['cap']} "
              f"(diverges: {not math.isfinite(r['cap'])})")
        for row in dominates_adversary(bd, theta=star if star else 0.9,
                                       halfrange=350.0):
            print(f"  adversary y={row['y']}: measured {row['measured']:.5f}"
                  f" <= cap {row['cap']:.5f}: {row['dominated']}")
        results[eps] = (star, margins)
    print("\n= theta*(eps) table =")
    for eps, (star, _) in results.items():
        print(f"  eps = {eps:<8g} theta* = {star}   (eps=0 paper box: 0.995)")
    print("\n= shape-dependence spot check (eps=1/8, y=0.49, theta=0.995) =")
    sc = shape_spot_check()
    print(f"  psi7: cap {sc['psi7']['cap']:.6f} slack {sc['psi7']['slack']:.6f}"
          f"   psi9: cap {sc['psi9']['cap']:.6f} slack "
          f"{sc['psi9']['slack']:.6f}")
    print(f"  relative cap move {sc['rel_move_cap']:.4f}, slack move "
          f"{sc['rel_move_slack']:.4f}, margin sign unchanged: "
          f"{sc['margin_sign_same']}")


if __name__ == "__main__":
    audit()
