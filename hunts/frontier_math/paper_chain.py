"""The band-lattice dual re-run at the PAPER's field: Phi2 = FT(cos box).

WHY THIS MODULE EXISTS.  paper_pin.py pinned the source paper's Theorem D
window: the cos(sqrt2 .) profile sits on **phi squared**, not on phi.  The
whole T1 chain (mt_chain.py, band_dual.py) was built at the T1 window,
whose incidence kernel is Phi2 = FT(cos^2 box) = phi2_mt.  The paper's
incidence kernel is instead

    Phi2_paper(z) = phihat_mt(z) = s(z + sqrt2) + s(z - sqrt2),
    s(u) = sin(u/2)/u,        A = Phi2_paper(0) = 2 sin(sqrt2/2)/sqrt2,

whose normalised square at real argument is exactly the Montgomery-Taylor
kernel g (paper_pin.paper_window_mass_kernel_is_g, defect ~1e-16), so at
this field the mass kernel and the Cheer-Goldston floor kernel coincide by
construction, the kernel zeros sit at 1.0573, 2.0301, 3.0202... mean gaps
(non-arithmetic), and the CG floor is live.  This module transplants the
band-lattice single-pair dual of band_dual.py to that field: same LAW L
damage structure W(dt, y1-y2) + W(dt, y1+y2), same pair-block slack, same
band partition of the negative part of the field with LOCAL closed-form
derivative bounds, the same no-missed-band curvature completeness test,
per-band square completion, and the closed-form 1/g^2 tail.

The underlying window has phi^2(t) = cos(sqrt2 t) on [-1/2, 1/2], which is
strictly positive (>= cos(sqrt2/2) > 0), so every bound of the mt_chain
form carries over with the recomputed constants: L1 = int |t| phi^2,
L2 = int t^2 phi^2, |Phi2(g+iy)| <= A E(y) with E(y) = Phi2(iy)/A, and the
one-integration-by-parts Im-majorant |Im Phi2(g+iy)| <= C_im(y)/|g| with
edge = phi^2(1/2) = cos(sqrt2/2) and TV(phi^2) = 2(1 - cos(sqrt2/2)).

DERIVATIVES, PINNED BY SYMPY (and by the numeric-derivative control):

    s'(u)  = cos(u/2)/(2u) - sin(u/2)/u^2
    s''(u) = -sin(u/2)/(4u) - cos(u/2)/u^2 + 2 sin(u/2)/u^3

    series at 0 (used for |u| < 1e-4; next term < 1e-17):
    s   = 1/2 - u^2/48 + u^4/3840 - ...
    s'  = -u/24 + u^3/960 - ...          (NOT u^3/1920: sympy pins /960)
    s'' = -1/24 + u^2/320 - ...

Everything is measured-grade and one-sided in the same sense as
band_dual.py: band membership on the raw grid, LOCAL slope margins only,
cross-band charges dropped (omega^2 >= 0), tail in closed form, never a
blanket per-cell margin.  Nothing here computes a proportion and nothing
here is evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/paper_chain.py`` (~4 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import g_kernel  # noqa: E402

S2 = math.sqrt(2.0)
MEAN_GAP = 2 * math.pi

# ---------------------------------------------------------------------------
# the kernel s(u) = sin(u/2)/u and its first two derivatives, vectorized
# over complex arrays with a series fallback near u = 0
# ---------------------------------------------------------------------------

_SMALL = 1e-4


def _s(u):
    u = np.asarray(u, complex)
    small = np.abs(u) < _SMALL
    us = np.where(small, 1.0, u)
    val = np.sin(us / 2) / us
    ser = 0.5 - u * u / 48 + u**4 / 3840
    return np.where(small, ser, val)


def _s_d1(u):
    u = np.asarray(u, complex)
    small = np.abs(u) < _SMALL
    us = np.where(small, 1.0, u)
    val = np.cos(us / 2) / (2 * us) - np.sin(us / 2) / us**2
    ser = -u / 24 + u**3 / 960
    return np.where(small, ser, val)


def _s_d2(u):
    u = np.asarray(u, complex)
    small = np.abs(u) < _SMALL
    us = np.where(small, 1.0, u)
    val = (-np.sin(us / 2) / (4 * us) - np.cos(us / 2) / us**2
           + 2 * np.sin(us / 2) / us**3)
    ser = -1 / 24 + u * u / 320
    return np.where(small, ser, val)


def phipap(z):
    """Phi2 at the paper's window: FT of phi^2 = cos(sqrt2 t) box."""
    z = np.asarray(z, complex)
    return _s(z + S2) + _s(z - S2)


def phipap_d1(z):
    z = np.asarray(z, complex)
    return _s_d1(z + S2) + _s_d1(z - S2)


def phipap_d2(z):
    z = np.asarray(z, complex)
    return _s_d2(z + S2) + _s_d2(z - S2)


A = float(phipap(0j).real)  # 2 sin(sqrt2/2)/sqrt2 = 0.9187253698...

_ts = np.linspace(-0.5, 0.5, 20001)
#: int |t| phi^2 dt, the Lipschitz constant of Phi2 in g (phi^2 >= 0)
_L1 = float(np.trapezoid(np.abs(_ts) * np.cos(S2 * _ts), _ts)) * 1.001
#: int t^2 phi^2 dt, the second-derivative constant
_L2 = float(np.trapezoid(_ts * _ts * np.cos(S2 * _ts), _ts)) * 1.001


@dataclass(frozen=True)
class PaperChain:
    """The mt_chain.MTChain analogue at the paper's field."""

    def W(self, g, y: float):
        v = phipap(np.asarray(g, float) + 1j * y)
        return 2 * (v.real**2 - v.imag**2) / A**2

    def omega2(self, r):
        v = phipap(np.asarray(r, complex)).real / A
        return v * v

    def sigma2(self, y: float) -> float:
        return float((phipap(2j * y).real - A) / (2 * A))

    def slack(self, y: float) -> float:
        s2 = self.sigma2(y)
        return 8 * s2 + 8 * s2 * s2

    def E(self, y: float) -> float:
        return float(phipap(1j * y).real / A)

    @property
    def L1(self) -> float:
        return _L1

    def lip_W(self, y: float) -> float:
        """|dW/dg| <= 8 |Phi2||Phi2'|/A^2 <= 8 A E(y) L1 cosh(y/2)/A^2."""
        return 8 * self.E(y) * self.L1 * math.cosh(y / 2) / A

    # -- LAW L pair layer -----------------------------------------------------

    def T(self, dt: float, y1: float, y2: float) -> float:
        return float(self.W(np.array([dt]), abs(y1 - y2))[0]
                     + self.W(np.array([dt]), y1 + y2)[0])


@dataclass(frozen=True)
class PaperBandDual:
    """band_dual.BandDual transplanted to Phi2 = phihat_mt.

    RESOLUTION CAVEAT (audit 2026-08-12).  A damage band has half-width
    ~y, and ``bands()`` adds a slope margin proportional to ``step``, so
    at the default step the cap is inflated by a factor ~(1 + 2 step/y):
    at y = 5e-4 the verdict comes out falsely NEGATIVE, and below
    y ~ 1e-4 no band is resolved at all.  Use :meth:`for_depth` for any
    probe below y ~ 5e-3; the four certificate depths are all safely
    above the artifact."""

    pc: PaperChain = PaperChain()
    #: fine step for band location and maxima (grid units)
    step: float = 0.0005
    #: resolved region; beyond, the closed-form 1/g^2 tail takes over
    G: float = 400.0

    @classmethod
    def for_depth(cls, y_min: float, G: float = 400.0,
                  pc: PaperChain | None = None) -> "PaperBandDual":
        """An instance whose grid resolves bands at depth y_min: forty
        cells across the band half-width (measured to bring the shipped
        step's shallow-depth cap inflation under ~2%)."""
        return cls(pc=pc or PaperChain(),
                   step=min(0.0005, y_min / 40.0), G=G)

    @property
    def L2(self) -> float:
        return _L2

    # -- the field and its LOCAL derivative magnitudes ------------------------

    def _field(self, y: float):
        gs = np.arange(self.step, self.G, self.step)
        z = gs + 1j * y
        ph = np.abs(phipap(z))
        p1 = np.abs(phipap_d1(z))
        p2 = np.abs(phipap_d2(z))
        f = -2 * self.pc.W(gs, y)
        return gs, f, ph, p1, p2

    def bands(self, y: float):
        """One-sided band list [(lo, hi, F_up)] on g > 0; membership on the
        raw grid, F_up carries the LOCAL slope margin only."""
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
            slope = 8 * float((ph[gr] * p1[gr]).max()) / A**2
            F = float(f[gr].max()) + slope * self.step
            out.append((lo, hi, F))
        return out

    def no_missed_band(self, y: float) -> dict:
        """Rule out a band narrower than the grid: off the (widened)
        resolved bands, q := Re^2 - Im^2 > (1/8)|q''| step^2 with
        |q''| <= 2(|Phi2'|^2 + |Phi2||Phi2''|), all LOCAL closed forms."""
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
        rec = self.no_missed_band(y)
        if rec["clear"]:
            return 0.0
        gs, f, ph, p1, p2 = self._field(y)
        off = f <= 0
        qpp = 2 * (p1[off] ** 2 + ph[off] * p2[off])
        return float(np.sum(qpp)) * self.step**2 / 8 * 4 / A**2

    def band_charge(self, width: float) -> float:
        """One-sided min of omega^2 over [0, width]; Lip(Re Phi2) <= L1."""
        rs = np.arange(0.0, width + self.step, self.step)
        lo = float(np.min(phipap(rs.astype(complex)).real / A))
        lo -= (self.pc.L1 / A) * self.step
        return max(0.0, lo) ** 2

    # -- the tail --------------------------------------------------------------

    def band_period_lower(self, y: float) -> float:
        bs = self.bands(y)
        if len(bs) < 3:
            return MEAN_GAP
        centres = [(lo + hi) / 2 for lo, hi, _ in bs]
        return min(centres[i + 1] - centres[i] for i in range(len(centres) - 1))

    def c_im_sharp(self, y: float) -> float:
        """|Im Phi2(g+iy)| <= c/|g|, one integration by parts:
        c = 2 phi^2(1/2) sinh(y/2) + TV(phi^2) sinh(y/2) + y cosh(y/2) A,
        with phi^2(1/2) = cos(sqrt2/2), TV = 2(1 - cos(sqrt2/2))
        (phi^2 = cos(sqrt2 t) is monotone on each half-window)."""
        sh, ch = math.sinh(y / 2), math.cosh(y / 2)
        edge = math.cos(S2 / 2)
        tv = 2 * (1 - edge)
        return 2 * edge * sh + tv * sh + y * ch * A

    def tail_sum(self, y: float) -> float:
        """Closed-form majorant of sum of band maxima beyond G, one side:
        F <= 4 (C_im/(A g))^2, bands at least P apart."""
        C = self.c_im_sharp(y) / A
        P = self.band_period_lower(y)
        return 4 * C * C * (1 / self.G**2 + 1 / (P * self.G))

    # -- the dual --------------------------------------------------------------

    def cap(self, theta: float, y: float) -> dict:
        """Band-lattice cap on sup_X [D(X) - (1-theta) R(X)]: cross-band
        charges dropped (omega^2 >= 0, one-sided), per-band square
        completion max_m [m F - c m(m-1) K], closed-form tail."""
        c = 1 - theta
        bs = self.bands(y)
        if not bs:
            # An empty band list is a verdict ("the field is nonpositive
            # everywhere") ONLY if the completeness control agrees no
            # band hides between grid points.  Below y ~ step/5 it does
            # not, and the old silent {"cap": 0.0} here was a false PASS
            # (audit 2026-08-12): report undecided instead.
            if not self.no_missed_band(y)["clear"]:
                return {"cap": math.inf, "bands": 0, "m_star": None,
                        "tail": None, "off_band": None, "undecided": True}
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
        off = self.off_band_allowance(y)
        C = self.c_im_sharp(y) / A
        F_G = 4 * C * C / self.G**2
        if F_G > 2 * c * K_min:
            raise AssertionError("tail band left the single-occupancy regime")
        return {"cap": 2 * (total + tail) + off, "bands": len(bs),
                "m_star": worst_m, "tail": 2 * tail, "off_band": off}

    def free_ratio(self, y: float) -> float:
        bs = self.bands(y)
        return (2 * (sum(F for _, _, F in bs) + self.tail_sum(y))
                + self.off_band_allowance(y)) / self.pc.slack(y)

    def theta_scan(self, ys=(0.02, 0.1, 0.3, 0.49),
                   thetas=(0.9, 0.99, 0.995, 0.999)):
        """Largest grid theta with cap <= slack at every probe depth."""
        margins = {}
        star = None
        for theta in thetas:
            worst, arg = math.inf, None
            for y in ys:
                rec = self.cap(theta, y)
                m = self.pc.slack(y) - rec["cap"]
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


def kernel_identity_control(us=(0.2, 0.5, 0.9, 1.3, 2.5)) -> float:
    """(phihat_mt(2 pi u)/phihat_mt(0))^2 == g_kernel(u): worst rel defect.

    The identity that makes this THE paper field: the incidence weight
    omega^2 is exactly the Montgomery-Taylor kernel."""
    worst = 0.0
    for u in us:
        rhs = float(g_kernel(np.array([u]))[0])
        lhs = float((phipap(np.array([2 * math.pi * u], complex)).real[0]
                     / A) ** 2)
        worst = max(worst, abs(lhs - rhs) / max(abs(rhs), 1e-30))
    return worst


def derivative_pin_control(n: int = 20, h: float = 1e-5,
                           h2: float = 3e-4) -> dict:
    """Closed-form d1/d2 of phipap vs central differences at scattered
    points (real and complex): worst relative defect.

    d2 uses a larger step: the second central difference carries
    ~4 eps/h^2 of roundoff (4e-6 at h = 1e-5), so h = 1e-5 measures the
    differencer, not the closed form; at h = 3e-4 the total defect
    bottoms out near 1e-8 (checked on a step ladder)."""
    rng = np.random.default_rng(7)
    pts = np.concatenate([
        rng.uniform(0.3, 30.0, n // 2),
        rng.uniform(0.3, 30.0, n - n // 2) + 1j * rng.uniform(0.05, 0.5,
                                                              n - n // 2),
    ])
    worst1 = worst2 = 0.0
    for z in pts:
        num1 = (phipap(z + h) - phipap(z - h)) / (2 * h)
        num2 = (phipap(z + h2) - 2 * phipap(z) + phipap(z - h2)) / h2**2
        c1 = complex(phipap_d1(z))
        c2 = complex(phipap_d2(z))
        worst1 = max(worst1, abs(c1 - complex(num1))
                     / max(abs(c1), 1e-12))
        worst2 = max(worst2, abs(c2 - complex(num2))
                     / max(abs(c2), 1e-12))
    return {"d1_worst": worst1, "d2_worst": worst2}


def series_pin_control() -> dict:
    """The Taylor fallback must join the closed form smoothly at the
    threshold: compare both branches just outside |u| = 1e-4."""
    out = {}
    for u in (1.2e-4, 5e-4, 1e-3):
        z = np.array([u], complex)
        out[u] = {
            "s": abs(complex(_s(z)[0]) - (0.5 - u * u / 48 + u**4 / 3840)),
            "d1": abs(complex(_s_d1(z)[0]) - (-u / 24 + u**3 / 960)),
            "d2": abs(complex(_s_d2(z)[0]) - (-1 / 24 + u * u / 320)),
        }
    return out


def explicit_single_pair_adversary(pc: PaperChain, y: float = 0.49,
                                   theta: float = 1.0,
                                   halfrange: float = 350.0):
    """Greedy band-riding adversary against one pair (mt_chain's control,
    at the paper field).  theta = 1.0 here selects FULL charge c = 1 (see
    the convention warning in mt_chain.py); pass theta < 1 for the
    inequality's charge."""
    sites = np.arange(-halfrange, halfrange, 0.05)
    w = 2 * pc.W(sites, y)
    c = 1 - theta if theta < 1 else 1.0
    c = max(c, 1e-12)
    chosen: list[float] = []
    profit = 0.0
    order = np.argsort(w)
    for idx in order[:4000]:
        x = float(sites[idx])
        if w[idx] >= 0:
            break
        if any(abs(x - p) < 0.5 for p in chosen):
            continue
        dmg = -float(w[idx])
        internal = 2 * c * sum(float(pc.omega2(x - p)) for p in chosen)
        if dmg - internal > 0:
            chosen.append(x)
            profit += dmg - internal
    D = sum(-2 * float(pc.W(np.array([x]), y)[0]) for x in chosen)
    R = 2 * sum(float(pc.omega2(a - b))
                for i, a in enumerate(chosen) for b in chosen[i + 1:])
    return {"profit": profit, "zeros": len(chosen), "D": D, "R": R}


def dominates_explicit_adversary(bd: PaperBandDual, ys=(0.3, 0.49),
                                 theta: float = 0.9):
    """The dual must dominate the measured adversary (primal <= dual)."""
    out = []
    for y in ys:
        rec = explicit_single_pair_adversary(bd.pc, y, theta=theta)
        measured = rec["D"] - (1 - theta) * rec["R"]
        cap = bd.cap(theta, y)["cap"]
        out.append({"y": y, "measured": measured, "cap": cap,
                    "dominated": measured <= cap})
    return out


def cross_band_drop_is_one_sided(bd: PaperBandDual) -> float:
    """omega^2 >= 0 everywhere (it is a square): measured floor."""
    rs = np.arange(0.0, 400.0, 0.01)
    return float(np.min(bd.pc.omega2(rs.astype(complex))))


def band_structure_card(bd: PaperBandDual, y: float = 0.49) -> dict:
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
        "decay_ratios": [bs[i][2] / bs[i + 1][2]
                         for i in range(min(4, len(bs) - 1))],
    }


def audit():
    bd = PaperBandDual()
    pc = bd.pc
    print(f"= the paper field: A = {A:.10f}, L1 = {_L1:.6f}, "
          f"L2 = {_L2:.6f} =")
    print("= control: the mass kernel IS the MT kernel g =")
    d = kernel_identity_control()
    print(f"  worst |(phihat/A)^2 - g|/g over the probe set: {d:.2e}  "
          f"({'PASS' if d < 1e-12 else 'FAIL'} at 1e-12)")
    print("= control: closed-form derivatives vs central differences =")
    dp = derivative_pin_control()
    print(f"  d1 worst rel defect {dp['d1_worst']:.2e}, d2 worst "
          f"{dp['d2_worst']:.2e}  "
          f"({'PASS' if max(dp.values()) < 1e-6 else 'FAIL'} at 1e-6)")
    print("= control: series/closed-form join at the threshold =")
    sp = series_pin_control()
    worst_join = max(v for rec in sp.values() for v in rec.values())
    print(f"  worst branch mismatch near |u|=1e-4: {worst_join:.2e}")
    print("= no missed bands (completeness; must clear > 100) =")
    nmb_ok = True
    for y in (0.02, 0.1, 0.3, 0.49):
        r = bd.no_missed_band(y)
        ok = r["clear"] and r["worst_ratio"] > 100
        nmb_ok &= ok
        print(f"  y={y}: worst q / curvature bound = {r['worst_ratio']:.0f}"
              f"   clear={r['clear']}  {'PASS' if ok else 'FAIL'}")
    if not nmb_ok:
        print("  !! completeness did not clear at >100; STOPPING before any"
              " theta claim (no blanket margin substituted).")
        return
    print("= the band structure =")
    st = band_structure_card(bd)
    print(f"  bands in (0, {bd.G}]: {st['n_bands']}   first centre at "
          f"{st['first_centre_mean_gaps']:.4f} mean gaps")
    print(f"  widths: first {st['width_first']:.3f}, max "
          f"{st['width_max']:.3f} grid units   separations (mean gaps): "
          + ", ".join(f"{s:.3f}" for s in st['sep_mean_gaps'][:4]))
    print(f"  same-band repulsion floor K = {st['K_band']:.4f}")
    print(f"  band maxima decay ratios: "
          + ", ".join(f"{r:.2f}" for r in st['decay_ratios']))
    print(f"  min omega^2 over [0, 400]: "
          f"{cross_band_drop_is_one_sided(bd):.3e} (>= 0: one-sided drop)")
    print("= the free-band ratio (every band granted at zero cost) =")
    for y in (0.02, 0.1, 0.3, 0.49):
        r = bd.cap(0.99, y)
        print(f"  y={y}: band sum / slack = {bd.free_ratio(y):.4f}   "
              f"(tail {r['tail']:.2e}, off-band {r['off_band']:.2e}, "
              f"slack {pc.slack(y):.5f})")
    print("= the multiplicity threshold =")
    for y in (0.1, 0.3, 0.49):
        print(f"  y={y}: double occupancy profitable only below theta = "
              f"{bd.multiplicity_threshold(y):.5f}")
    print("= the theta scan =")
    star, margins = bd.theta_scan()
    for th, (m, arg) in margins.items():
        print(f"  theta={th}: worst margin {m:+.6f} at y={arg}  "
              f"{'ok' if m >= 0 else 'FAILS'}")
    print(f"  theta*_paper (grid) = {star}    (T1 window: 0.995)")
    if star is not None:
        print(f"= per-depth cap vs slack at theta* = {star} =")
        for y in (0.02, 0.1, 0.3, 0.49):
            rec = bd.cap(star, y)
            s = pc.slack(y)
            print(f"  y={y}: cap {rec['cap']:.6f}  slack {s:.6f}  margin "
                  f"{s - rec['cap']:+.6f}  bands {rec['bands']}  "
                  f"m* {rec['m_star']}")
    print("= control: the dual dominates the measured adversary =")
    theta_chk = star if star is not None else 0.9
    for row in dominates_explicit_adversary(bd, theta=theta_chk):
        print(f"  y={row['y']}: measured {row['measured']:.5f} <= cap "
              f"{row['cap']:.5f}: {row['dominated']}")
    print("= control: theta = 1 must diverge (no charge, unbounded m) =")
    r = bd.cap(1.0, 0.49)
    print(f"  cap(theta=1) = {r['cap']}  "
          f"(infinite: {not math.isfinite(r['cap'])})")


if __name__ == "__main__":
    audit()
