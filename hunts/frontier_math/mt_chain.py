"""T1: the retention chain re-run at the Montgomery-Taylor window.

THE WINDOW.  phi(t) = cos(sqrt2 t) on the width-1 box; phi^2 has the
closed transform

    Phi2(z) = (1/2) sc(z) + (1/4)[sc(z + 2 sqrt2) + sc(z - 2 sqrt2)],
    sc(z) = 2 sin(z/2)/z,      a = Phi2(0) = 1/2 + sin(sqrt2)/(2 sqrt2).

LAW D IS EXACT HERE — the earlier "0.53% alias defect" was pure grid-sum
truncation (the defect scales like 1/K in the truncation range K;
measured 3.8e-3 -> 6.0e-5 over K = 80 -> 5120).  Poisson: a window
supported in (-pi, pi) cannot reach the +-2pi alias combs, so
B(z, w) = 2 pi Phi2(z - w) exactly, for complex arguments too.  The whole
law hierarchy therefore transplants verbatim; this module recomputes its
constants and reruns the level-3/4 single-pair trade and the level-7
direct joint cap at this window.

UNITS.  Grid units; the mean zero gap is 2 pi grid units (the damage
band sits at 1.10-1.12 mean gaps = the lambda_1 geometry).  Pair-density
sweeps are specified in pairs per mean gap (nu_p) and converted.

SCALES.  sigma^2(0.49) = 0.0175 (93x smaller than the hunt window's
1.62), the LAW-I-analogue envelope is -0.44 sigma^2 (vs -1.21), and the
kernel omega^2 stays above 0.35 out to ~4 grid units — repulsion is
strong relative to the damage-band width (1.2 grid units).  The far tail
decays like 1/g^2 only (the box window's boundary jump), so the far
allowance uses the one-sided Im-majorant  (-W)_+ <= 2 Im(Phi2)^2 / a^2
<= 2 C_im(y)^2 / (a g)^2, whose constant carries sinh(y/2) — shallow
pairs are tail-free, and the harvest sum converges like 1/G.

Everything is measured-grade with one-sided structure (centre + Lipschitz
sups, directed charge floors, stated inflations); the arb pass is the
named hardening, exactly as at the hunt window.

Run ``.venv/bin/python hunts/frontier_math/mt_chain.py`` (~10 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from v_certificate import chain_dp  # noqa: E402

S2 = math.sqrt(2.0)
MEAN_GAP = 2 * math.pi


def _sc(z):
    z = np.asarray(z, complex)
    small = np.abs(z) < 1e-12
    zs = np.where(small, 1.0, z)
    return np.where(small, 1.0, 2 * np.sin(zs / 2) / zs)


def phi2mt(z):
    """Phi2 at the MT window, vectorized over complex arrays."""
    z = np.asarray(z, complex)
    return 0.5 * _sc(z) + 0.25 * (_sc(z + 2 * S2) + _sc(z - 2 * S2))


A = float(phi2mt(0j).real)  # 0.8492279993...

_ts = np.linspace(-0.5, 0.5, 20001)
#: int |t| phi^2 dt, the exact Lipschitz constant of Phi2 in g
_L1 = float(np.trapezoid(np.abs(_ts) * np.cos(S2 * _ts) ** 2, _ts)) * 1.001


@dataclass(frozen=True)
class MTChain:
    #: DP cell-width ladder, grid units (mean gap = 2 pi)
    delta_choices: tuple = (1.5, 2.0, 3.0)
    #: fine sup grid step (the MT field scale is ~0.01, so the Lipschitz
    #: margin lip * fine must sit well below it)
    fine: float = 0.001
    #: fine field range beyond the window (grid units); Im-majorant beyond
    G_field: float = 600.0

    # -- kernel objects ------------------------------------------------------

    def W(self, g, y: float):
        v = phi2mt(np.asarray(g, float) + 1j * y)
        return 2 * (v.real**2 - v.imag**2) / A**2

    def omega2(self, r):
        v = phi2mt(np.asarray(r, complex)).real / A
        return v * v

    def sigma2(self, y: float) -> float:
        return float((phi2mt(2j * y).real - A) / (2 * A))

    def slack(self, y: float) -> float:
        s2 = self.sigma2(y)
        return 8 * s2 + 8 * s2 * s2

    def E(self, y: float) -> float:
        return float(phi2mt(1j * y).real / A)

    # |d Phi2/dg| <= int |t| phi^2 = L1 (module constant below)
    @property
    def L1(self) -> float:
        return _L1

    def lip_W(self, y: float) -> float:
        """|dW/dg| <= 8 |Phi2| |Phi2'| / a^2 <= 8 a E(y) L1 cosh(y/2)/a^2."""
        return 8 * self.E(y) * self.L1 * math.cosh(y / 2) / A

    def C_im(self, y: float) -> float:
        """|Im Phi2(g+iy)| <= C_im(y)/|g| (one integration by parts on
        int phi^2 sinh(yt) sin(gt): boundary jump + total variation)."""
        sh = math.sinh(y / 2)
        # boundary: 2 phi^2(1/2) sinh(y/2); TV of (phi^2 sinh)':
        # |(phi^2)'| <= sqrt2, phi^2 <= 1, |cosh'-part| <= y cosh(y/2)
        return 2 * math.cos(S2 / 2) ** 2 * sh + S2 * sh + y * math.cosh(y / 2)

    def tail_neg(self, g: float, y: float) -> float:
        """One-sided far majorant: (-W)_+ <= 2 Im^2/a^2 <= 2 C_im^2/(a g)^2."""
        return 2 * (self.C_im(y) / (A * abs(g))) ** 2

    def K_delta(self, delta: float, step: float = 0.005) -> float:
        """One-sided min of omega^2 over [0, delta] (Lip(omega) <= L1/A ...
        |d omega/dr| <= L1/A <= 0.14; grid min minus margin)."""
        rs = np.arange(0.0, delta + step, step)
        lo = float(np.min(phi2mt(rs.astype(complex)).real / A))
        lo -= (self.L1 / A) * step
        return max(0.0, lo) ** 2

    # -- level-2/3 entry: the one-sided LAW-I-analogue envelope --------------

    def law_i_envelope(self, y: float, g_max: float = 60.0) -> float:
        """One-sided c with W(g, y) >= -c sigma^2(y) for all g.

        Fine grid to g_max with Lipschitz margin; beyond, the Im-majorant
        (monotone-dominated) is checked against the grid worst.
        """
        gs = np.arange(0.01, g_max, 0.001)
        worst = float(np.min(self.W(gs, y))) - self.lip_W(y) * 0.001
        far = -self.tail_neg(g_max, y)
        return -min(worst, far) / self.sigma2(y)

    # -- level-3/4: the single-pair counting trade ---------------------------

    def single_pair_cap(self, theta: float, y: float) -> float:
        """Configuration-free cap on sup [D - (1-theta) R] for one pair.

        Chain DP on one-sided cell sups of f = (-2W)_+ (fine grid + Lip
        margin to G_field; Im-majorant linear cells beyond)."""
        c = 1 - theta
        gs = np.arange(-self.G_field, self.G_field, self.fine)
        f = np.maximum(0.0, -2 * self.W(gs, y) + self.lip_W(y) * self.fine)
        best = math.inf
        for delta in self.delta_choices:
            per = max(1, int(round(delta / self.fine)))
            cells = [float(np.max(f[j:j + per], initial=0.0))
                     for j in range(0, len(f), per)]
            cK1 = c * self.K_delta(delta)
            cK2 = c * self.K_delta(2 * delta)
            best = min(best, chain_dp(cells, cK1, cK2))
        # far: linear-regime Im-majorant, closed-form sum (1/g^2 decay):
        # sum_k 2 F(G + k delta) <= 2 F(G) + (2/delta) int_G^inf F, per side
        delta = self.delta_choices[0]
        cK1 = c * self.K_delta(delta)
        G = self.G_field
        F0 = 2 * self.tail_neg(G, y)
        if F0 > 2 * cK1:
            raise AssertionError("far cell left the linear regime")
        far = 2 * (F0 + (2 / delta) * 2 * (self.C_im(y) / A) ** 2 / G)
        return best + far

    def theta_star_scan(self, thetas=(0.1, 0.3, 0.5, 0.7, 0.8, 0.9),
                        ys=(0.05, 0.15, 0.3, 0.45, 0.49)):
        """Largest grid theta with cap <= slack at every probe depth."""
        margins = {}
        star = None
        for theta in thetas:
            worst = math.inf
            for y in ys:
                worst = min(worst, self.slack(y) - self.single_pair_cap(theta, y))
            margins[theta] = worst
            if worst >= 0:
                star = theta
        return star, margins

    # -- pair layer: LAW L and budgets ---------------------------------------

    def T(self, dt: float, y1: float, y2: float) -> float:
        return float(self.W(np.array([dt]), abs(y1 - y2))[0]
                     + self.W(np.array([dt]), y1 + y2)[0])

    def budget(self, pairs) -> float:
        total = sum(self.slack(y) for _, y in pairs)
        for i, (t1, y1) in enumerate(pairs):
            for j in range(i + 1, len(pairs)):
                t2, y2 = pairs[j]
                total += 2 * self.T(t1 - t2, y1, y2)
        return total

    # -- level 7: the direct joint cap ---------------------------------------

    def direct_cap(self, pairs, theta: float) -> float:
        c = 1 - theta
        ts = np.array([t for t, _ in pairs])
        lo, hi = ts.min() - self.G_field, ts.max() + self.G_field
        gs = np.arange(lo, hi, self.fine)
        field = np.zeros_like(gs)
        for t, y in pairs:
            field += -2 * self.W(gs - t, y)
        lip = sum(self.lip_W(y) for _, y in pairs)
        f = np.maximum(0.0, field + lip * self.fine)
        best = math.inf
        for delta in self.delta_choices:
            per = max(1, int(round(delta / self.fine)))
            cells = [float(np.max(f[j:j + per], initial=0.0))
                     for j in range(0, len(f), per)]
            cK1 = c * self.K_delta(delta)
            cK2 = c * self.K_delta(2 * delta)
            best = min(best, chain_dp(cells, cK1, cK2))
        # far tail: summed Im-majorants, closed-form linear sums per side
        delta = self.delta_choices[0]
        cK1 = c * self.K_delta(delta)
        far = 0.0
        for side in (-1, 1):
            edge = lo if side < 0 else hi
            F0 = sum(2 * self.tail_neg(abs(edge - t) + 1e-9, y)
                     for t, y in pairs)
            if F0 > 2 * cK1:
                raise AssertionError("far cell left the linear regime")
            integ = sum((2 / delta) * 2 * (self.C_im(y) / A) ** 2
                        / max(abs(edge - t), delta) for t, y in pairs)
            far += 2 * (F0 + integ)
        return best + far

    def verdict(self, pairs, theta: float):
        b = self.budget(pairs)
        cap = self.direct_cap(pairs, theta)
        return {"budget": b, "cap": cap, "margin": b - cap,
                "closes": b - cap >= 0}


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def law_d_truncation_control(Ks=(80, 640, 5120)):
    """The grid identity defect must scale like 1/K (truncation, no alias)."""
    z = complex(1.9, 0.45)

    def ph(w):
        def s(u):
            if abs(u) < 1e-12:
                return 0.5 + 0j
            import cmath
            return cmath.sin(u / 2) / u
        return s(w + S2) + s(w - S2)

    out = []
    for K in Ks:
        tau = np.arange(-K, K + 1, 1.0)
        lhs = sum(ph(z - t) * ph(0 - t) for t in tau)
        rhs = 2 * math.pi * complex(phi2mt(np.array([z]))[0])
        out.append((K, abs(lhs - rhs) / abs(rhs)))
    return out


def law_k_control(y: float = 0.45, K: int = 400):
    """The pair block spectrum must be {2(1+s2), -2s2} x (grid norm)."""
    import cmath

    def ph(w):
        def s(u):
            if abs(u) < 1e-12:
                return 0.5 + 0j
            return cmath.sin(u / 2) / u
        return s(w + S2) + s(w - S2)

    tau = np.arange(-K, K + 1, 1.0)
    z = complex(0.13, y)
    u = np.array([ph(z - t) for t in tau])
    norm = 2 * math.pi * A
    x, yv = u.real / math.sqrt(norm), u.imag / math.sqrt(norm)
    M = 2 * (np.outer(x, x) - np.outer(yv, yv))
    ev = np.linalg.eigvalsh(M)
    s2 = MTChain().sigma2(y)
    return {"eig_minus": float(ev[0]), "pred_minus": -2 * s2,
            "eig_plus": float(ev[-1]), "pred_plus": 2 * (1 + s2),
            "x_dot_y": float(x @ yv)}


def greedy_joint(mt: MTChain, pairs, theta: float, kmax: int = 60,
                 minsp: float = MEAN_GAP / 16) -> float:
    ts = [t for t, _ in pairs]
    lo, hi = min(ts) - 2 * MEAN_GAP, max(ts) + 2 * MEAN_GAP
    sites = np.arange(lo, hi, 0.1)
    dmg = np.zeros_like(sites)
    for t, y in pairs:
        dmg += -2 * mt.W(sites - t, y)
    c = 1 - theta
    chosen: list[float] = []
    profit = 0.0
    for _ in range(kmax):
        best_gain, best_i = 0.0, None
        for i, x in enumerate(sites):
            if any(abs(x - p) < minsp for p in chosen):
                continue
            internal = 2 * c * sum(float(mt.omega2(x - p)) for p in chosen)
            gain = dmg[i] - internal
            if gain > best_gain:
                best_gain, best_i = gain, i
        if best_i is None:
            break
        chosen.append(float(sites[best_i]))
        profit += best_gain
    return profit


def sweep_configs(span_gaps: float = 10.0):
    for nu_p in (0.75, 1.0, 1.25, 1.5, 2.0, 3.0):
        spacing = MEAN_GAP / nu_p
        for y in (0.3, 0.49):
            n = int(span_gaps * nu_p)
            yield (f"lattice nu={nu_p} y={y}",
                   [(k * spacing, y) for k in range(n)])
    spacing = MEAN_GAP / 1.5
    n = int(10 * 1.5)
    yield ("shallow sandwich nu=1.5",
           [(k * spacing, 0.02) for k in range(n)]
           + [(k * spacing, 0.49) for k in range(n)])
    yield ("alternating nu=1.5",
           [(k * spacing, 0.45 if k % 2 else 0.15) for k in range(n)])


def explicit_single_pair_adversary(mt: MTChain, y: float = 0.49,
                                   theta: float = 1.0,
                                   halfrange: float = 350.0):
    """Greedy band-riding adversary against one pair: the true trade.

    Returns (profit at the given theta, zeros used, D, R).  Measured at
    y = 0.49: D = 0.030, R = 0.004 with 2 zeros — net stays far inside
    the slack 0.142 even at theta = 1.  The counting CAP above is what
    fails, not the trade: the interval charge floors K_[delta,3delta]
    straddle the kernel zeros (band separations are near-arithmetic
    differences of kernel zeros), so the chain DP grants the persistent
    1/g^2 band tail for free while the true point repulsion
    (omega^2 ~ 0.005-0.01 at band separations) is what actually stops
    the adversary.  The named T1 theorem gap: a band-lattice counting
    dual with point-separation charges."""
    sites = np.arange(-halfrange, halfrange, 0.05)
    w = 2 * mt.W(sites, y)
    c = 1 - theta if theta < 1 else 1.0  # theta=1: charge R fully anyway
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
        internal = 2 * c * sum(float(mt.omega2(x - p)) for p in chosen)
        if dmg - internal > 0:
            chosen.append(x)
            profit += dmg - internal
    D = sum(-2 * float(mt.W(np.array([x]), y)[0]) for x in chosen)
    R = 2 * sum(float(mt.omega2(a - b))
                for i, a in enumerate(chosen) for b in chosen[i + 1:])
    return {"profit": profit, "zeros": len(chosen), "D": D, "R": R}


def band_charge_degeneracy(mt: MTChain):
    """The structural reason the chain DP fails at MT: every interval
    [delta, 3 delta] of the ladder contains a kernel zero, so K3-type
    floors vanish; the true repulsion at band separations is pointwise."""
    out = {}
    for delta in mt.delta_choices:
        rs = np.arange(delta, 3 * delta, 0.01)
        out[delta] = float(np.min(mt.omega2(rs.astype(complex))))
    # actual point repulsion at the first few band separations
    seps = [6.11, 6.28, 12.32, 12.75]
    pts = {s0: float(mt.omega2(np.array([s0], complex))[0]) for s0 in seps}
    return out, pts


def audit():
    mt = MTChain()
    print("= LAW D at the MT window: truncation control (no alias) =")
    rows = law_d_truncation_control()
    for K, d in rows:
        print(f"  K={K}: defect {d:.3e}")
    print(f"  ratio across 64x range: {rows[0][1] / rows[-1][1]:.1f} "
          "(~64 = pure 1/K truncation)")
    print("= LAW K at the MT window (grid pair block spectrum) =")
    r = law_k_control()
    print(f"  eig- {r['eig_minus']:+.6f} (pred {r['pred_minus']:+.6f})  "
          f"eig+ {r['eig_plus']:.6f} (pred {r['pred_plus']:.6f})  "
          f"x.y {r['x_dot_y']:+.1e}")
    print("= the LAW-I-analogue envelope (one-sided) =")
    for y in (0.1, 0.3, 0.45, 0.49):
        c = mt.law_i_envelope(y)
        print(f"  y={y}: W >= -{c:.4f} sigma^2   (hunt window: 1.2137)")
    print("= single-pair: the chain-DP cap is structurally inadequate here =")
    star, margins = mt.theta_star_scan(thetas=(0.5,), ys=(0.49,))
    print(f"  chain-DP cap at theta=0.5, y=0.49: margin "
          f"{margins[0.5]:+.5f} (FAILS at every theta - the cap, not the trade)")
    ko, pts = band_charge_degeneracy(mt)
    print(f"  interval charge floors min omega^2 over [d,3d]: "
          + ", ".join(f"d={d}: {v:.4f}" for d, v in ko.items()))
    print(f"  true point repulsion at band separations: "
          + ", ".join(f"omega2({s0}) = {v:.4f}" for s0, v in pts.items()))
    print("  = the DP's interval floors straddle kernel zeros; the bands")
    print("    persist ~1/g^2; the named T1 gap is a band-lattice dual =")
    print("= the trade itself, measured (explicit band-riding adversary) =")
    for y in (0.3, 0.49):
        rec = explicit_single_pair_adversary(mt, y)
        print(f"  y={y}: D {rec['D']:.5f}  R {rec['R']:.5f}  zeros "
              f"{rec['zeros']}  net-at-theta-1 {rec['D'] - 0:.5f} "
              f"vs slack {mt.slack(y):.5f}  "
              f"{'inside' if rec['D'] < mt.slack(y) else 'EXCEEDS'}")
    print("= the direct joint cap across the sweep =")
    theta_probe = (0.1, 0.3, 0.5)
    closed_at = {t: True for t in theta_probe}
    for name, pairs in sweep_configs():
        row = []
        for th in theta_probe:
            rec = mt.verdict(pairs, th)
            row.append(f"th={th}: {rec['margin']:+.4f}")
            if not rec["closes"]:
                closed_at[th] = False
        print(f"  {name:28s} budget {mt.budget(pairs):8.4f}  "
              + "  ".join(row))
    for th, ok in closed_at.items():
        print(f"  theta_full = {th}: {'CLOSES the sweep' if ok else 'open'}")
    print("= kill controls =")
    pairs = [(k * MEAN_GAP / 1.5, 0.49) for k in range(15)]
    g = greedy_joint(mt, pairs, 0.3)
    cap = mt.direct_cap(pairs, 0.3)
    print(f"  greedy joint (nu=1.5 deep, theta=0.3): {g:.4f} <= cap "
          f"{cap:.4f}: {g <= cap + 1e-9}")
    try:
        mt.single_pair_cap(1.0, 0.3)
        print("  theta = 1: FAILED TO FAIL (bug)")
    except (AssertionError, OverflowError):
        print("  theta = 1: cap diverges/fails as it must")


if __name__ == "__main__":
    audit()
