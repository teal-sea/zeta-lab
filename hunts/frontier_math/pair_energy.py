"""Level 5, gate 2: the multi-pair energy, LAW L, and the partition audit.

PHASE 2 — THE EXACT ALGEBRA.  For pairs indexed by r at ordinates t_r and
depths y_r, the full-grid Frobenius energy of the off-line block is

    ||Qhat||_F^2 = sum_r ||M_r||^2 + sum_{r != s} T(t_r - t_s, y_r, y_s),

and LAW K gives each self term exactly: ``||M_r||^2 = 4 + 8 sigma_r^2 +
8 sigma_r^4`` = baseline charge 4 + slack_r.  The cross term is the new
exact identity:

  LAW L.  T(dt, y, y') = W(dt, y - y') + W(dt, y + y')

-- the *single-pair* signed kernel evaluated at the difference and sum
depths.  (From ``u_r . u_s = L Phi2(z_r - z_s)`` and ``u_r . conj(u_s) =
L Phi2(z_r - conj(z_s))``, both instances of LAW D's complex Poisson
identity.)  Everything levels 3-4 established about W therefore applies to
the pair layer verbatim.  The sign-indefinite terms of the total energy are
exactly: the on/off cross (bounded by the level-4 counting dual) and the
``T`` terms (this module).  Structural consequences, each measured here:

- **the difference layer is nonnegative at equal depths**:
  ``T(dt, y, y) = W(dt, 0) + W(dt, 2y)`` with ``W(., 0) >= 0`` -- stacked
  or near-ordinate equal-depth pairs interact positively except for the
  depth-scaled ``W(dt, 2y)`` part, which vanishes as ``sigma^2(2y)``;
- **negativity is depth-split**: from the sinh addition formula,

      sigma^2(y ± y') <= 2 cosh^2(y'L/2) sigma^2(y)
                       + 2 cosh^2(yL/2) sigma^2(y'),

  so every negative T is chargeable to its two participants in proportion
  to their own sigma^2 -- a shallow pair is charged asymptotically nothing
  (PHASE 3's half-charging, made depth-graded);
- **the far tail is depth-scaled**: ``|T(dt,.)|_- <= 2[psi_S(|y-y'|)^2 +
  psi_S(y+y')^2]/(dt^4 (aL)^2)`` since only ``S^2`` can push W negative.

PHASE 3/6 — THE PARTITION, MEASURED.  ``eta_table`` computes, on a depth
grid, the worst per-pair charge ratio

    eta(nu_p) = max_r  [ sum_s charge_r(T_rs) ] / slack_r

over adversarial ordinate lattices of pair density nu_p, with the exact
proportional depth split above.  eta < 1 means a definite fraction of the
total slack survives all pair-pair interaction -- combined with the
(hardened) level-4 single-pair scan at the reduced slack this yields
``theta_full > 0`` at that pair density.  PHASE 4's collective modes are
run in ``collective_battery``: stacked columns, alternating-depth dipole
lattices, staggered lattices, shallow/deep sandwiches, strip-edge
clusters, periodic pair words.  Each is checked against the pairwise
charging: a collective mode defeating it would show up as a battery row
whose total energy falls below the charged prediction.

WHAT THIS IS NOT.  The eta table and battery are measured objects over
explicit adversary families, not a configuration-free theorem; the
configuration-free closure of the pair layer is the level-4 counting dual
applied to the T kernel at mixed depths (2D cells), which is the named
level-6 task.  Pair density is capped in the measurements at the values
shown; the unconditional cap is ``nu_p <= A_0 log T`` as in LAW H.

Run ``.venv/bin/python hunts/frontier_math/pair_energy.py`` (~1 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gap_consistency import _phi2_hat_f  # noqa: E402
from theta_recovery import Recovery  # noqa: E402


@dataclass(frozen=True)
class PairEnergy:
    L: float = 8.0
    w: float = 1.0

    @property
    def rec(self) -> Recovery:
        return Recovery(self.L, self.w)

    @property
    def aL(self) -> float:
        return _phi2_hat_f(0j, self.L, self.w).real

    def W(self, g: float, y: float) -> float:
        v = _phi2_hat_f(complex(g, y), self.L, self.w)
        return 2 * (v.real**2 - v.imag**2) / (self.aL**2)

    def T(self, dt: float, y1: float, y2: float) -> float:
        """LAW L: the pair-pair cross energy via the two W layers."""
        return self.W(dt, y1 - y2) + self.W(dt, y1 + y2)

    def T_direct(self, dt: float, y1: float, y2: float) -> float:
        """The independent route (theta_recovery.pair_pair) for the check."""
        return self.rec.pair_pair(dt, y1, y2)

    def sigma_sq(self, y: float) -> float:
        return (self.phi2_real(0, 2 * y) - self.aL) / (2 * self.aL)

    def phi2_real(self, g: float, y: float) -> float:
        return _phi2_hat_f(complex(g, y), self.L, self.w).real

    def slack(self, y: float) -> float:
        s2 = self.sigma_sq(y)
        return 8 * s2 + 8 * s2 * s2

    # -- the depth split ----------------------------------------------------

    def split_weights(self, y1: float, y2: float):
        """Proportional depth split of a shared negative T term.

        Weights from the sinh addition bound: w1 ~ cosh^2(y2 L/2) sigma^2(y1),
        w2 ~ cosh^2(y1 L/2) sigma^2(y2), normalised.  Shallow pairs get
        asymptotically nothing.
        """
        a = math.cosh(y2 * self.L / 2) ** 2 * self.sigma_sq(y1)
        b = math.cosh(y1 * self.L / 2) ** 2 * self.sigma_sq(y2)
        tot = a + b
        if tot == 0:
            return 0.5, 0.5
        return a / tot, b / tot

    # -- Phase 2: the energy, assembled exactly ------------------------------

    def total_energy(self, pairs):
        """(sum slack, sum cross T, baseline) for pairs = [(t, y), ...].

        The Frobenius energy of the off-line block is
        baseline + slack_total + cross_total, with cross the only
        sign-indefinite part (LAW K pins the self terms).
        """
        slack_total = sum(self.slack(y) for _, y in pairs)
        baseline = 4 * len(pairs)
        cross_total = 0.0
        for i, (t1, y1) in enumerate(pairs):
            for j, (t2, y2) in enumerate(pairs):
                if i != j:
                    cross_total += self.T(t1 - t2, y1, y2)
        return {"baseline": baseline, "slack_total": slack_total,
                "cross_total": cross_total,
                "survives": slack_total + cross_total}

    # -- Phase 3/6: the measured eta ----------------------------------------

    def row_charge(self, y_r: float, neighbours, dt_grid=None) -> float:
        """Worst charge to a depth-y_r pair from a lattice of neighbours.

        neighbours = [(dt, y_s), ...]; each negative T is split by
        split_weights and the y_r share accumulated.
        """
        charge = 0.0
        for dt, y_s in neighbours:
            t = self.T(dt, y_r, y_s)
            if t < 0:
                w_r, _ = self.split_weights(y_r, y_s)
                charge += -t * w_r
        return charge

    def eta_for(self, y_r: float, nu_p: float, y_grid, span: float = 12.0) -> float:
        """Worst charge ratio for a pair at depth y_r against density-nu_p
        lattices of neighbours at each candidate depth (worst single depth,
        both signs of dt, phase-scanned)."""
        spacing = 1.0 / nu_p
        worst = 0.0
        for y_s in y_grid:
            for phase in (0.0, spacing / 3, spacing / 2):
                neigh = []
                dt = spacing + phase
                while dt < span:
                    neigh.append((dt, y_s))
                    neigh.append((-dt, y_s))
                    dt += spacing
                worst = max(worst, self.row_charge(y_r, neigh))
        return worst / self.slack(y_r)

    def eta_table(self, nu_values=(0.5, 1.0, 2.0),
                  y_grid=(0.05, 0.15, 0.25, 0.35, 0.45, 0.49)):
        out = {}
        for nu_p in nu_values:
            out[nu_p] = max(self.eta_for(y_r, nu_p, y_grid) for y_r in y_grid)
        return out

    # -- Phase 4: collective modes -------------------------------------------

    def collective_battery(self, nu_p: float = 1.0):
        """Named collective configurations vs the pairwise charging.

        For each: (total cross)/(total slack) must stay above -eta-like
        levels, and in particular above -1 (energy survival).
        """
        span = 10.0
        spacing = 1.0 / nu_p
        configs = {}
        # stacked column: same ordinate, depth ladder
        configs["stacked column"] = [(0.0, y) for y in (0.1, 0.2, 0.3, 0.4, 0.45)]
        # alternating-depth dipole lattice
        configs["alternating dipoles"] = [
            (k * spacing, 0.45 if k % 2 else 0.15)
            for k in range(int(2 * span / spacing))
        ]
        # staggered double lattice
        configs["staggered lattices"] = [
            (k * spacing, 0.3) for k in range(int(span / spacing))
        ] + [(k * spacing + spacing / 2, 0.4) for k in range(int(span / spacing))]
        # shallow/deep sandwich
        configs["shallow/deep sandwich"] = [
            (k * spacing, 0.05) for k in range(int(span / spacing))
        ] + [(k * spacing, 0.49) for k in range(int(span / spacing))]
        # strip-edge cluster
        configs["strip-edge cluster"] = [
            (k * spacing, 0.49) for k in range(int(span / spacing))
        ]
        # periodic pair word at the critical spacing
        h = 2 * math.pi / self.L
        configs["periodic pair word"] = [(k * h, 0.3) for k in range(int(span / h))]
        rows = {}
        for name, pairs in configs.items():
            rec = self.total_energy(pairs)
            rows[name] = {
                "pairs": len(pairs),
                "cross_over_slack": rec["cross_total"] / rec["slack_total"],
                "survives": rec["survives"] > 0,
            }
        return rows

    # -- Phase 6: theta_full assembly ----------------------------------------

    def eta_by_depth(self, nu_p: float = 1.0,
                     y_grid=(0.05, 0.15, 0.25, 0.35, 0.45, 0.49)):
        """The charge ratio resolved by the charged pair's depth."""
        return {y_r: self.eta_for(y_r, nu_p, y_grid) for y_r in y_grid}

    def assembly_audit(self, level4_cap_fraction, nu_p: float = 1.0):
        """The combined per-pair budget: on-line cap + pair charge vs slack.

        level4_cap_fraction maps depth -> cap/slack from the (hardened)
        level-4 scan.  The requirement for theta_full > 0 via this per-pair
        linear assembly is cap_fraction + eta(y) <= 1 at every depth.
        Returns per-depth overdraws; positive overdraw = the assembly fails
        there and its size is the named deficit.
        """
        etas = self.eta_by_depth(nu_p)
        rows = {}
        for y, eta in etas.items():
            cap_frac = level4_cap_fraction(y)
            rows[y] = {
                "cap_fraction": cap_frac,
                "pair_charge_fraction": eta,
                "combined": cap_frac + eta,
                "overdraw": max(0.0, cap_frac + eta - 1.0),
            }
        return rows


def law_l_check(pe: PairEnergy, samples=((0.7, 0.3, 0.2), (2.1, 0.45, 0.1),
                                         (0.0, 0.25, 0.25), (5.5, 0.49, 0.49))):
    """LAW L vs the independent pair_pair route: exact identity."""
    return max(abs(pe.T(dt, a, b) - pe.T_direct(dt, a, b)) for dt, a, b in samples)


def audit():
    pe = PairEnergy()
    print("= LAW L: T = W(dt, y-y') + W(dt, y+y') =")
    print(f"  identity defect vs independent route: {law_l_check(pe):.3e}")
    print("= the difference layer at equal depths is W(dt, 0) >= 0 =")
    worst = min(pe.W(0.05 * k, 0.0) for k in range(1, 320))
    print(f"  min W(dt, 0) over dt in (0, 16]: {worst:+.3e}")
    print("= shallow-shallow negativity vanishes with depth =")
    for y in (0.02, 0.05, 0.1):
        worst = min(pe.T(0.05 * k, y, y) for k in range(1, 320))
        print(f"  y={y}: min T = {worst:+.6f}   (-(1+m0) s^2(2y) = "
              f"{-(1.2137) * pe.sigma_sq(2 * y):+.6f})")
    print("= measured eta table (worst charge ratio) =")
    for nu_p, eta in pe.eta_table().items():
        print(f"  nu_p = {nu_p}: eta = {eta:.4f}  "
              f"{'< 1: slack survives' if eta < 1 else '>= 1: FAILS'}")
    print("= Phase 4: collective battery =")
    for nu_p in (1.0, 2.0):
        print(f"  -- nu_p = {nu_p} --")
        for name, row in pe.collective_battery(nu_p).items():
            print(f"  {name:24s}: pairs {row['pairs']:3d}  cross/slack "
                  f"{row['cross_over_slack']:+.4f}  survives={row['survives']}")
    print("= Phase 6: per-depth eta and the combined budget =")
    for y, eta in pe.eta_by_depth(1.0).items():
        print(f"  y={y}: pair-charge fraction eta = {eta:.4f}")
    # level-4 cap fractions at the binding cells, read from the level-4 scan
    cap_fractions = {0.05: 0.90, 0.15: 0.92, 0.25: 0.92, 0.35: 0.86,
                     0.45: 0.85, 0.49: 0.85}
    rows = pe.assembly_audit(lambda y: cap_fractions[min(
        cap_fractions, key=lambda k: abs(k - y))], nu_p=1.0)
    for y, row in rows.items():
        print(f"  y={y}: cap {row['cap_fraction']:.2f} + charge "
              f"{row['pair_charge_fraction']:.3f} = {row['combined']:.3f}  "
              f"overdraw {row['overdraw']:.3f}")


if __name__ == "__main__":
    audit()
