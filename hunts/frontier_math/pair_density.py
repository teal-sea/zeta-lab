"""Level 6b: the pair-density question — where theta_full = 0.02 lives.

Level 6a delivered theta_full = 0.02 at unit pair density with a per-pair
assembly.  This module asks the next question the directive's road demands:
what happens when the pair density is the adversary's to choose?

THE GLOBAL ASSEMBLY.  The per-pair split was a proof device; what the
energy actually needs is global.  The level-6a hardened caps are
configuration-free per pair, so summing them is valid (each (x, pair)
damage term belongs to exactly one pair's row), and the requirement
becomes

    sum_pairs T_signed  >=  - sum_r (1 - capfrac(y_r, theta)) slack_r,

where T_signed keeps BOTH signs of the pair-pair interaction — the
adversary's own stacking payments now count against it, which the eta
accounting of levels 5-6a (negative parts only) deliberately ignored.

MEASURED VERDICT (:func:`global_verdict`).  Across lattice families
(nu_p = 0.5 .. 3, all probe depths, phases) and the collective battery:
where does the global budget hold and where does it break?  Expected and
found: it holds through nu_p ~ 1.5 and breaks at dense deep clusters —
NOT because the energy fails, but because summed per-pair caps overshoot
when negative bands overlap.

THE COMPENSATION FACTOR (:func:`joint_compensation`).  A single on-line
configuration cannot deal every pair its worst case at once: a zero at one
pair's most negative offset sits in a neighbouring pair's positive region.
We measure chi = (best joint on-line damage against the whole cluster,
greedy) / (sum of per-pair caps).  chi < 1 quantifies exactly the slack
the separable accounting wastes; the JOINT cap (an on-line counting dual
against a cluster of pairs) is the named theorem object that would bank it.

THE STACKING FLOOR (:func:`stacking_floor`).  The provable seed for
density self-limitation: for |dt| <= delta_p, both layers of LAW L are
near coincidence and

    T(dt, y, y') >= 2 [cos(dt L/2)^2 E(|y-y'|)^2 - (dt L/2)^2 sigma-terms]

stays positive uniformly in the depths for delta_p ~ 0.2 (one-sided grid
check with Lipschitz margin).  Every same-window pair the adversary adds
pays this floor — the third instance of the self-defeat pattern (depth,
on-line density, and now pair density).

Nothing here computes a proportion; the Phase-7 gate stays closed.
Run ``.venv/bin/python hunts/frontier_math/pair_density.py`` (~3 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pair_energy import PairEnergy  # noqa: E402
from theta_recovery import Recovery  # noqa: E402

#: level-6a hardened cap fractions at theta = 0.02, by probe depth
HARDENED_CAPFRAC = {
    0.01: 0.5712, 0.05: 0.5847, 0.15: 0.5884, 0.25: 0.5949,
    0.35: 0.6703, 0.45: 0.6960, 0.49: 0.6795,
}


def capfrac(y: float) -> float:
    key = min(HARDENED_CAPFRAC, key=lambda k: abs(k - y))
    return HARDENED_CAPFRAC[key]


@dataclass(frozen=True)
class PairDensity:
    L: float = 8.0
    w: float = 1.0

    @property
    def pe(self) -> PairEnergy:
        return PairEnergy(self.L, self.w)

    # -- the global assembly --------------------------------------------------

    def global_margin(self, pairs) -> dict:
        """[sum T_signed + sum (1-capfrac) slack] / sum slack for a config."""
        pe = self.pe
        slack_total = sum(pe.slack(y) for _, y in pairs)
        budget = sum((1 - capfrac(y)) * pe.slack(y) for _, y in pairs)
        t_signed = 0.0
        for i, (t1, y1) in enumerate(pairs):
            for j in range(i + 1, len(pairs)):
                t2, y2 = pairs[j]
                t_signed += 2 * pe.T(t1 - t2, y1, y2)  # both orders
        return {
            "t_signed_over_slack": t_signed / slack_total,
            "budget_over_slack": budget / slack_total,
            "margin": (t_signed + budget) / slack_total,
        }

    def lattice_configs(self, nu_values=(0.5, 1.0, 1.5, 2.0, 3.0),
                        depths=(0.15, 0.3, 0.45, 0.49), span: float = 10.0):
        for nu_p in nu_values:
            spacing = 1.0 / nu_p
            for y in depths:
                for phase_frac in (0.0, 1.0 / 3, 0.5):
                    offset = spacing * phase_frac
                    pairs = [
                        (k * spacing + offset, y)
                        for k in range(int(span / spacing))
                    ]
                    yield (f"lattice nu={nu_p} y={y} ph={phase_frac:.2f}", pairs)

    def battery_configs(self, span: float = 10.0):
        for nu_p in (1.0, 2.0):
            spacing = 1.0 / nu_p
            n = int(span / spacing)
            yield (f"alternating nu={nu_p}",
                   [(k * spacing, 0.45 if k % 2 else 0.15) for k in range(2 * n)])
            yield (f"staggered nu={nu_p}",
                   [(k * spacing, 0.3) for k in range(n)]
                   + [(k * spacing + spacing / 2, 0.4) for k in range(n)])
            yield (f"sandwich nu={nu_p}",
                   [(k * spacing, 0.05) for k in range(n)]
                   + [(k * spacing, 0.49) for k in range(n)])
            yield (f"edge cluster nu={nu_p}",
                   [(k * spacing, 0.49) for k in range(n)])

    def global_verdict(self):
        """The measured global budget across all families; worst rows."""
        rows = []
        for name, pairs in list(self.lattice_configs()) + list(self.battery_configs()):
            rec = self.global_margin(pairs)
            rows.append((rec["margin"], name, rec))
        rows.sort()
        return rows

    # -- the compensation factor ----------------------------------------------

    def joint_compensation(self, y: float, nu_p: float, theta: float = 0.02,
                           span: float = 6.0, kmax: int = 40) -> dict:
        """chi = greedy joint on-line damage / summed per-pair caps.

        The on-line adversary places zeros (min spacing 1/8, i.e. an
        essentially unconstrained density for this purpose) to maximise
        total signed damage minus (1-theta) internal mass, against ALL
        pairs of a spacing-1/nu_p lattice at depth y.
        """
        pe = self.pe
        rec = Recovery(self.L, self.w)
        spacing = 1.0 / nu_p
        centres = [k * spacing for k in range(int(span / nu_p ** -1 / spacing) or 1)]
        centres = [k * spacing for k in range(max(1, int(span / spacing)))]
        c = 1 - theta
        sites = [(-2.0 + 0.02 * i) for i in range(int((span + 4.0) / 0.02))]
        chosen: list[float] = []
        profit = 0.0
        for _ in range(kmax):
            best_gain, best_x = 0.0, None
            for x in sites:
                if any(abs(x - p) < 0.125 for p in chosen):
                    continue
                dmg = -sum(2 * rec.W(x - t, y) for t in centres)
                internal = 2 * c * sum(rec.omega_sq(x - p) for p in chosen)
                gain = dmg - internal
                if gain > best_gain:
                    best_gain, best_x = gain, x
            if best_x is None:
                break
            chosen.append(best_x)
            profit += best_gain
        summed_caps = sum(capfrac(y) * pe.slack(y) for _ in centres)
        return {
            "n_pairs": len(centres),
            "joint_profit": profit,
            "summed_caps": summed_caps,
            "chi": profit / summed_caps if summed_caps else 0.0,
        }

    # -- the stacking floor ---------------------------------------------------

    def stacking_floor(self, delta_p: float = 0.2,
                       depth_grid=(0.01, 0.1, 0.2, 0.3, 0.4, 0.49),
                       step: float = 0.01) -> dict:
        """One-sided min of T over |dt| <= delta_p and all depth pairs.

        Grid minimum minus a Lipschitz margin: |dT/d(dt)| <= 2 |dW/dg| at
        each layer, and |dW/dg| <= 8 |Phi2| Lip(Phi2) / aL^2 <= 8 * aL E *
        (L/2) aL E / aL^2 = 4 L E^2 with E at the layer depth.
        """
        pe = self.pe
        worst = math.inf
        arg = None
        for y1 in depth_grid:
            for y2 in depth_grid:
                if y2 < y1:
                    continue
                lip = 4 * self.L * (
                    (1 + 2 * pe.sigma_sq(abs(y1 - y2) / 2 + 1e-9)) ** 2
                    + (1 + 2 * pe.sigma_sq((y1 + y2) / 2)) ** 2
                )
                dt = 0.0
                local = math.inf
                while dt <= delta_p + 1e-12:
                    local = min(local, pe.T(dt, y1, y2))
                    dt += step
                floor = local - lip * step
                if floor < worst:
                    worst, arg = floor, (y1, y2)
        return {"floor": worst, "at_depths": arg, "delta_p": delta_p,
                "positive": worst > 0}


def audit():
    pd = PairDensity()
    print("= stacking floor (one-sided): same-window pairs pay =")
    for dp in (0.1, 0.2, 0.3):
        rec = pd.stacking_floor(delta_p=dp)
        print(f"  delta_p={dp}: floor {rec['floor']:+8.4f} at depths "
              f"{rec['at_depths']}  positive={rec['positive']}")
    print("= global verdict: worst configurations by margin =")
    rows = pd.global_verdict()
    for margin, name, rec in rows[:8]:
        print(f"  {name:34s} T/slack {rec['t_signed_over_slack']:+8.4f}  "
              f"budget {rec['budget_over_slack']:.4f}  margin {margin:+8.4f}")
    holds = [r for r in rows if r[0] >= 0]
    print(f"  ({len(holds)}/{len(rows)} configurations hold the global budget)")
    print("= compensation factor chi (joint on-line vs summed caps) =")
    for y in (0.3, 0.45, 0.49):
        for nu_p in (1.0, 2.0):
            rec = pd.joint_compensation(y, nu_p)
            print(f"  y={y} nu_p={nu_p}: joint {rec['joint_profit']:8.4f}  "
                  f"summed caps {rec['summed_caps']:8.4f}  chi = {rec['chi']:.3f}")


if __name__ == "__main__":
    audit()
