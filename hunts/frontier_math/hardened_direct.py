"""Level 7, the arb pass: the direct joint-field dual under ball arithmetic.

Gate-1 discipline (`enclosure_pass.py`) applied to the object that closed
the axis: the chain counting DP on the joint damage field.

THE INTERVAL SUBTLETY, RECORDED.  A naive interval-argument evaluation of
Phi2 over a fine cell explodes: the ramp^2 assembly has integer
coefficients up to ~1e4 with alternating signs whose analytic
cancellation interval radii cannot see (measured amplification ~1.8e5:
a 1e-6 input radius becomes 0.18 on Phi2).  The hardened field therefore
uses the MEAN-VALUE form per cell,

    W over [m-r, m+r]  in  W(m) + W'(m) [-r, r] + (1/2) Wpp r^2 [-1, 1],

with W(m) and W'(m) tight point balls and the global second-derivative
blanket  |d^2W/dg^2| <= 128 E(y)^2  per pair (from |Phi2'| <= (L/2) aL E,
|Phi2''| <= (L/2)^2 aL E), whose r^2 term is ~1e-3 per pair at r = 0.0025.
Phi2' gets its own ball route: Phi2'(z) = -2 int_0^{L/2} u phi^2 sin(zu) du,
assembled from the same C/S moment enclosures with indices shifted by one.

Everything else is directed as at gate 1: per-pair W balls are summed
exactly and the JOINT upper endpoint is clipped at zero (so the
coincident-pair shielding survives hardening); charges use the lower
endpoints of K_delta; the DP total is inflated 1 + 1e-9; the far tail is
the hardened psi_S majorant; the budget is directed downward (slack lower
endpoints, T from directed lower balls of the LAW L layers).

Run ``.venv/bin/python hunts/frontier_math/hardened_direct.py``
(~20-40 min, seven configurations).
"""

from __future__ import annotations

import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from flint import acb, arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enclosure_pass import (  # noqa: E402
    _NEEDED_INDICES, _RAMP2_INT, _cs_moments_acb, EnclosedBound, f_lo, f_up,
)
from v_certificate import chain_dp  # noqa: E402

ctx.prec = 128

#: moment indices for Phi2 and Phi2' (the u-weighted part shifts by one)
_PRIME_INDICES = tuple(sorted(set(_NEEDED_INDICES)
                              | {k + 1 for k in _NEEDED_INDICES}))


@dataclass(frozen=True)
class EnclosedDirect(EnclosedBound):
    """The direct joint-field dual with every ingredient ball-directed."""

    #: fine cell width for the mean-value field evaluation
    fine: float = 0.005
    #: DP cell widths
    delta_choices: tuple = (0.25, 0.35, 0.45)
    #: mid/far handoff distance (beyond: hardened psi tail)
    G_mid: float = 24.0

    # -- Phi2 and Phi2' point balls (shared moments) --------------------------

    def phi2_pair_acb(self, z: acb):
        """(Phi2(z), Phi2'(z)) as balls from one moment computation."""
        L = arb(self.L)
        w = arb(self.w)
        half, inner = L / 2, L / 2 - w
        Cm, Sm = _cs_moments_acb(z * w, _PRIME_INDICES)
        ch, sh = (z * half).cos(), (z * half).sin()
        # Phi2 = 2 sin(z c)/z + 2w sum ramp2_k (ch C_k + sh S_k)
        acc = acb(0)
        for k in _NEEDED_INDICES:
            acc += _RAMP2_INT[k] * (ch * Cm[k] + sh * Sm[k])
        phi2 = 2 * (z * inner).sin() / z + 2 * w * acc
        # Phi2' = -2 [ (sin(zc) - zc cos(zc))/z^2
        #              + (L/2) sum ramp2_k (sh C_k - ch S_k)
        #              -       sum ramp2_k (sh C_{k+1} - ch S_{k+1}) ]
        zc = z * inner
        flat = (zc.sin() - zc * zc.cos()) / (z * z)
        acc1 = acb(0)
        acc2 = acb(0)
        for k in _NEEDED_INDICES:
            acc1 += _RAMP2_INT[k] * (sh * Cm[k] - ch * Sm[k])
            acc2 += _RAMP2_INT[k] * (sh * Cm[k + 1] - ch * Sm[k + 1])
        phi2p = -2 * (flat + half * acc1 - acc2)
        return phi2, phi2p

    def wpp_blanket(self, y: float) -> float:
        """|d^2 W/dg^2| <= 4 (|Phi2'|^2 + |Phi2| |Phi2''|)/aL^2
        <= 4 ((L/2)^2 + (L/2)^2) aL^2 E^2 / aL^2 = 2 L^2 E(y)^2."""
        return 2 * self.L * self.L * self.E(y) ** 2

    def field_cells(self, pairs, lo: float, hi: float):
        """Directed cell uppers of the joint field (-(sum_r 2W))_+ .

        Mean-value per (cell, pair): point balls of W, W' at the centre
        plus the global curvature remainder; the per-pair intervals are
        summed exactly and the JOINT upper endpoint clipped at zero.
        """
        n = int(math.ceil((hi - lo) / self.fine))
        r = self.fine / 2
        aL2 = self.aL_ball() ** 2
        rem = {y: 0.5 * self.wpp_blanket(y) * r * r for _, y in pairs}
        cells = []
        for i in range(n):
            mid = lo + (i + 0.5) * self.fine
            tot = arb(0)
            for t, y in pairs:
                z = acb(arb(mid - t), arb(y))
                p, pp = self.phi2_pair_acb(z)
                wv = 2 * (p.real * p.real - p.imag * p.imag) / aL2
                wp = 4 * (p.real * pp.real - p.imag * pp.imag) / aL2
                slope = f_up(abs(wp)) * r + rem[y]
                tot += wv + arb(0, slope)
            cells.append(max(0.0, f_up(-2 * tot)))
        return cells

    # -- the hardened cap ------------------------------------------------------

    def direct_cap(self, pairs, theta: float, progress: bool = False):
        ts = [t for t, _ in pairs]
        lo, hi = min(ts) - self.G_mid, max(ts) + self.G_mid
        c = 1 - theta
        t0 = time.time()
        fine_cells = self.field_cells(pairs, lo, hi)
        if progress:
            print(f"    [field: {len(fine_cells)} mean-value cells, "
                  f"{time.time() - t0:.0f}s]", flush=True)
        best = math.inf
        for delta in self.delta_choices:
            per = max(1, int(round(delta / self.fine)))
            cells = [max(fine_cells[j:j + per], default=0.0)
                     for j in range(0, len(fine_cells), per)]
            cK1 = c * self.K_delta(delta)
            cK2 = c * self.K_delta(2 * delta)
            best = min(best, chain_dp(cells, cK1, cK2))
        best *= 1 + 1e-9
        # hardened far tail
        delta = self.delta_choices[0]
        cK1 = c * self.K_delta(delta)
        far = 0.0
        for side in (-1, 1):
            g = 0.0
            while True:
                edge = (lo - g) if side < 0 else (hi + g)
                F = sum(self.tail_sup_damage(abs(edge - t), y)
                        for t, y in pairs)
                if F > 2 * cK1:
                    raise AssertionError("far cell left the linear regime")
                far += F
                if F < 1e-12:
                    break
                g += delta
        return best + far

    # -- the hardened budget ---------------------------------------------------

    def budget_lower(self, pairs) -> float:
        """Directed lower bound of sum slack + T_signed.

        slack: lower endpoints (inherited).  T: per ordered pair, the
        LOWER endpoint of the LAW L sum W(dt, y1-y2) + W(dt, y1+y2),
        from exact-point Phi2 balls.
        """
        aL2 = self.aL_ball() ** 2

        def w_ball(dt: float, y: float) -> arb:
            v = self.phi2_acb(acb(arb(dt), arb(y)))
            return 2 * (v.real * v.real - v.imag * v.imag) / aL2

        total = arb(0)
        for _, y in pairs:
            s2 = self.sigma_sq_ball(y)
            total += 8 * s2 + 8 * s2 * s2
        for i, (t1, y1) in enumerate(pairs):
            for j in range(i + 1, len(pairs)):
                t2, y2 = pairs[j]
                total += 2 * (w_ball(t1 - t2, abs(y1 - y2))
                              + w_ball(t1 - t2, y1 + y2))
        return f_lo(total)

    def verdict(self, pairs, theta: float = 0.02, progress: bool = False):
        budget = self.budget_lower(pairs)
        cap = self.direct_cap(pairs, theta, progress=progress)
        return {"budget_lo": budget, "cap_up": cap,
                "margin": budget - cap, "closes": budget - cap >= 0}


def audit():
    ed = EnclosedDirect()
    theta = 0.02
    configs = [
        ("former hole nu=1.1 y=0.49", [(k / 1.1, 0.49) for k in range(11)]),
        ("former hole nu=1.2 y=0.49", [(k / 1.2, 0.49) for k in range(12)]),
        ("former hole nu=1.3 y=0.49", [(k / 1.3, 0.49) for k in range(13)]),
        ("former hole nu=1.4 y=0.49", [(k / 1.4, 0.49) for k in range(14)]),
        ("pinch nu=1.5 y=0.49", [(k / 1.5, 0.49) for k in range(15)]),
        ("sparse nu=0.75 y=0.49", [(k / 0.75, 0.49) for k in range(7)]),
        ("shallow sandwich nu=1.5",
         [(k / 1.5, 0.02) for k in range(15)]
         + [(k / 1.5, 0.49) for k in range(15)]),
    ]
    print(f"= hardened direct dual: theta = {theta}, fine = {ed.fine} =",
          flush=True)
    worst = (math.inf, None)
    for name, pairs in configs:
        rec = ed.verdict(pairs, theta, progress=True)
        if rec["margin"] < worst[0]:
            worst = (rec["margin"], name)
        print(f"  {name:28s}: budget >= {rec['budget_lo']:8.2f}  "
              f"cap <= {rec['cap_up']:7.2f}  margin >= {rec['margin']:+8.2f}"
              f"  {'closes' if rec['closes'] else 'OPEN'}", flush=True)
    print(f"= worst hardened margin: {worst[0]:+.2f} at {worst[1]} =",
          flush=True)


if __name__ == "__main__":
    audit()
