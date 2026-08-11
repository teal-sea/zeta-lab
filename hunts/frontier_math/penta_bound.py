"""Level 6a: the pentadiagonal counting dual and the assembly, version 2.

Level 5 quantified the obstruction to ``theta_full > 0``: the combined
per-pair budget (level-4 on-line cap fraction + measured pair charge)
overdraws at every depth by 0.151-0.387 of slack, while the true budgets
(measured adversaries on both layers) fit with 15-35% headroom.  The gap
is bound looseness, concentrated in one place: **the tridiagonal chain
undercharges mid-range pairs**, because an adjacent-cell pair at distance
just over 0 is charged ``min omega^2 over [0, 2delta]``, which sits at the
far end of the range (0.315 at delta = 0.25 against a true 0.77 for a pair
at distance 0.2).

The refinement here keeps the level-4 counting theorem's shape and narrows
the ranges.  Cells of width delta with THREE charges:

    same cell      (distance < delta)          : K1 = min omega^2 [0, delta]
    adjacent cells (distance < 2 delta)        : K2 = min omega^2 [0, 2 delta]
    second-neighbour cells (delta < d < 3delta): K3 = min omega^2 [delta, 3delta]

all one-sided (grid min with the |omega'| <= L/2 slope margin), with
``3 delta <= 0.9`` enforced so every range stays inside omega's first
positive stretch.  The adversary's value becomes a pentadiagonal program

    max over n_j >= 0 of sum_j [ n_j F_j - c K1 n_j(n_j-1)
                                 - c K2 n_j n_{j+1} - c K3 n_j n_{j+2} ],

solved exactly by dynamic programming with state (n_{j-1}, n_j) and the
inner maximisation over n_{j-2} precomputed as an upper envelope.  With
K3 = 0 it reduces to the level-4 tridiagonal chain; with K2 = K3 = 0 to
the plain per-cell bound -- both kept as controls, alongside the mandatory
projection controls (the bound must dominate every measured adversary of
levels 3-5).

The second lever is the pair-charge split: level 5 distributed each
negative pair-pair term by the crude proportional depth weights.  The
distribution does not change the total, but eta is a max over rows, so the
optimal split is a min-max problem; ``eta_optimal`` solves it by iterative
reweighting toward equalised row ratios (any split is valid -- the choice
is free in the accounting -- so the measured minimum over splits is an
honest eta).

``assembly_v2`` then recomputes the per-depth budget with both levers and
reports the verdict per depth: overdraw closed or not, with the residual.
Run ``.venv/bin/python hunts/frontier_math/penta_bound.py`` (~6 min).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from counting_bound import CountingBound  # noqa: E402
from pair_energy import PairEnergy  # noqa: E402
from theta_recovery import Recovery  # noqa: E402


@dataclass(frozen=True)
class PentaBound(CountingBound):
    """The three-range pentadiagonal refinement of the counting dual."""

    delta_choices: tuple = (0.125, 0.15, 0.2, 0.25, 0.3)

    def K_range(self, a: float, b: float, step: float = 0.005) -> float:
        """One-sided min of omega^2 over [a, b], for b <= 0.9."""
        if b > 0.9 + 1e-12:
            return 0.0  # stay inside omega's first positive stretch
        aL = self.aL
        lo = math.inf
        r = a
        while r <= b + 1e-12:
            lo = min(lo, self.phi2(complex(max(r, 0.0), 0)).real / aL)
            r += step
        lo -= (self.L / 2) * step
        return max(0.0, lo) ** 2 if lo > 0 else 0.0

    def charges(self, delta: float):
        """(K1, K2, K3) for the three ranges at this delta."""
        return (
            self.K_delta(delta),
            self.K_delta(2 * delta),
            self.K_range(delta, 3 * delta),
        )

    def lambda_bar_from_sups(self, theta, sups, y2, delta, n_cap: int = 10):
        """The pentadiagonal DP on precomputed fine sups."""
        c = 1 - theta
        if c <= 0:
            return math.inf
        K1, K2, K3 = self.charges(delta)
        cK1, cK2, cK3 = c * K1, c * K2, c * K3
        if cK1 <= 0:
            return math.inf

        per_cell = int(round(delta / self.fine_step))
        cells = [
            max(sups[j : j + per_cell], default=0.0)
            for j in range(0, len(sups), per_cell)
        ]
        g = self.fine_g_max
        mid = []
        while g < self.g_max:
            mid.append(self.tail_sup_damage(g, y2))
            g += delta
        cells = mid[::-1] + cells + mid

        # DP over (n_{j-1}, n_j); envelope over n_{j-2} per (n_j, n_{j+1})
        size = n_cap + 1
        prev = [[0.0] * size for _ in range(size)]  # prev[p][q]
        for F in cells:
            env = [[-math.inf] * size for _ in range(size)]  # env[q][r]
            for q in range(size):
                for r in range(size):
                    best = -math.inf
                    for p in range(size):
                        v = prev[p][q] - cK3 * p * r
                        if v > best:
                            best = v
                    env[q][r] = best
            cur = [[-math.inf] * size for _ in range(size)]
            for q in range(size):
                for r in range(size):
                    cur[q][r] = (
                        r * F - cK1 * r * (r - 1) - cK2 * q * r + env[q][r]
                    )
            prev = cur
        total = max(max(row) for row in prev)
        arg_r = max(
            range(size), key=lambda r: max(prev[q][r] for q in range(size))
        )
        if arg_r == n_cap:
            return self.lambda_bar_from_sups(theta, sups, y2, delta, 2 * n_cap)

        g = self.g_max
        while True:
            F = self.tail_sup_damage(g - delta, y2)
            if F > 2 * cK1:  # pragma: no cover
                raise AssertionError("tail cell left the linear regime")
            total += 2 * F
            if F < 1e-12:
                break
            g += delta
        return total


# ---------------------------------------------------------------------------
# Lever 2: the optimal pair-charge split
# ---------------------------------------------------------------------------


def eta_optimal(pe: PairEnergy, nu_p: float = 1.0,
                y_grid=(0.05, 0.15, 0.25, 0.35, 0.45, 0.49),
                span: float = 12.0, rounds: int = 200):
    """Min-max eta over split weights, by iterative reweighting.

    Adversary: every ordered pair of depths (y_r, y_s) from the grid, with a
    density-nu_p ordinate lattice of y_s-neighbours around a y_r pair (worst
    phase).  The split of each negative T term between its two participants
    is free in the accounting; we optimise it to equalise the worst row
    ratios.  Weights are parametrised per unordered depth pair.
    """
    spacing = 1.0 / nu_p
    # collect |T|_- totals per (y_r, y_s) row under the worst lattice phase
    row_neg = {}
    for y_r in y_grid:
        for y_s in y_grid:
            worst = 0.0
            for phase in (0.0, spacing / 3, spacing / 2):
                tot = 0.0
                dt = spacing + phase
                while dt < span:
                    for sgn in (dt, -dt):
                        t = pe.T(sgn, y_r, y_s)
                        if t < 0:
                            tot += -t
                    dt += spacing
                worst = max(worst, tot)
            row_neg[(y_r, y_s)] = worst

    slack = {y: pe.slack(y) for y in y_grid}
    # split weight w[(a, b)] = fraction of the (a,b) mass charged to a
    w = {}
    for y_r in y_grid:
        for y_s in y_grid:
            if (y_s, y_r) not in w:
                w[(y_r, y_s)] = 0.5
    def charge(y):
        # the adversary's ordinate density budget is nu_p in total, and the
        # row masses are linear in the per-depth counts, so the worst mix
        # puts the whole lattice at the single worst neighbour depth: MAX,
        # not sum (a sum would be a 6*nu_p-density adversary)
        worst = 0.0
        for other in y_grid:
            key = (y, other) if (y, other) in w else (other, y)
            frac = w[key] if key[0] == y else 1 - w[key]
            worst = max(worst, row_neg[(y, other)] * frac)
        return worst

    for _ in range(rounds):
        ratios = {y: charge(y) / slack[y] for y in y_grid}
        # shift weight away from the currently worse-off participant
        for (a, b) in list(w):
            ra, rb = ratios[a], ratios[b]
            if ra > rb + 1e-9:
                w[(a, b)] = max(0.0, w[(a, b)] - 0.005)
            elif rb > ra + 1e-9:
                w[(a, b)] = min(1.0, w[(a, b)] + 0.005)
    return {y: charge(y) / slack[y] for y in y_grid}


# ---------------------------------------------------------------------------
# The assembly, version 2
# ---------------------------------------------------------------------------


def assembly_v2(pb: PentaBound, pe: PairEnergy, nu_p: float = 1.0,
                thetas=(0.0, 0.05, 0.1)):
    """Per-depth budget with the pentadiagonal caps and the optimal split.

    Verdict per depth and theta: cap_fraction + eta <= 1 closes the
    overdraw there.  Caps are float (the hardened penta pass is the
    follow-on, run only if this closes); eta is measured-exact on its
    adversary family with the split optimised.
    """
    etas = eta_optimal(pe, nu_p)
    rows = {}
    for y, eta in etas.items():
        y2 = y * 1.01
        sups = pb.fine_sups(y, y2)
        slack = pb.slack(y)
        caps = {
            theta: min(
                pb.lambda_bar_from_sups(theta, sups, y2, d)
                for d in pb.delta_choices
            )
            for theta in thetas
        }
        rows[y] = {
            "eta": eta,
            "slack": slack,
            "cap_fractions": {t: c / slack for t, c in caps.items()},
            "combined": {t: c / slack + eta for t, c in caps.items()},
        }
    return rows


def audit():
    pb = PentaBound()
    cb = CountingBound()
    pe = PairEnergy()
    rec = Recovery()
    print("= charge triples (K1, K2, K3) per delta =")
    for d in pb.delta_choices:
        K1, K2, K3 = pb.charges(d)
        print(f"  delta={d}: K1={K1:.4f}  K2={K2:.4f}  K3={K3:.4f}")
    print("= penta vs tri caps (theta = 0), and projection control =")
    for y in (0.05, 0.15, 0.25, 0.35, 0.45):
        y2 = y * 1.01
        sups_p = pb.fine_sups(y, y2)
        cap_p = min(pb.lambda_bar_from_sups(0.0, sups_p, y2, d)
                    for d in pb.delta_choices)
        sups_t = cb.fine_sups(y, y2)
        cap_t = min(cb.lambda_bar_from_sups(0.0, sups_t, y2, d)
                    for d in cb.delta_choices)
        measured = max(
            rec.slack(y) - rec.lattice_net(0.0, y, sp) for sp in (1.0, 0.5, 0.25)
        )
        measured = max(measured, rec.slack(y) - rec.greedy_net(0.0, y, 8, kmax=8))
        ok = measured <= cap_p + 1e-9
        print(f"  y={y}: penta {cap_p:8.4f}  tri {cap_t:8.4f}  "
              f"gain x{cap_t / cap_p:.3f}  measured {measured:7.4f}  "
              f"dominated={ok}")
    print("= optimal-split eta vs level-5 proportional eta (nu_p = 1) =")
    for y, eta in eta_optimal(pe).items():
        print(f"  y={y}: eta_opt = {eta:.4f}")
    print("= assembly v2 =")
    rows = assembly_v2(pb, pe)
    closed_at = {t: True for t in (0.0, 0.05, 0.1)}
    for y, row in rows.items():
        line = "  ".join(
            f"th={t}: {row['combined'][t]:.3f}" for t in row["combined"]
        )
        print(f"  y={y}: eta {row['eta']:.3f}  {line}")
        for t, comb in row["combined"].items():
            if comb > 1:
                closed_at[t] = False
    for t, ok in closed_at.items():
        print(f"  theta = {t}: overdraw {'CLOSED' if ok else 'open'}")


if __name__ == "__main__":
    audit()


# ---------------------------------------------------------------------------
# The hardened pentadiagonal bound (gate-1 discipline applied to level 6a)
# ---------------------------------------------------------------------------


def _make_enclosed_penta():
    """Deferred import so the float path stays flint-free."""
    from enclosure_pass import EnclosedBound, f_lo, f_up  # noqa: F401
    from flint import acb, arb

    from dataclasses import dataclass

    @dataclass(frozen=True)
    class EnclosedPenta(PentaBound, EnclosedBound):
        """Penta DP + charges on ball-hardened kernel quantities.

        MRO resolves the DP and delta ladder from PentaBound and every
        kernel-touching method from EnclosedBound; K_range and the DP
        inflation are supplied here.
        """

        def K_range(self, a: float, b: float, step: float = 0.005) -> float:
            if b > 0.9 + 1e-12:
                return 0.0
            aL_up = f_up(self.aL_ball())
            lo = math.inf
            r = a
            while r <= b + 1e-12:
                val = f_lo(self.phi2_acb(acb(arb(max(r, 1e-9)), 0)).real)
                lo = min(lo, val / aL_up)
                r += step
            lo -= (self.L / 2) * step
            return max(0.0, lo * lo * (1 - 1e-9)) if lo > 0 else 0.0

        def lambda_bar_from_sups(self, theta, sups, y2, delta, n_cap: int = 10):
            total = PentaBound.lambda_bar_from_sups(
                self, theta, sups, y2, delta, n_cap
            )
            return total * (1 + 1e-9) if math.isfinite(total) else total

    return EnclosedPenta


def hardened_assembly(theta: float = 0.02, nu_p: float = 1.0,
                      y_grid=(0.01, 0.05, 0.15, 0.25, 0.35, 0.45, 0.49)):
    """The theta_full verdict with hardened caps and measured-optimal eta."""
    EnclosedPenta = _make_enclosed_penta()
    ep = EnclosedPenta()
    pe = PairEnergy()
    etas = eta_optimal(pe, nu_p, y_grid=y_grid)
    rows = {}
    for y, eta in etas.items():
        y2 = y * 1.01
        sups = ep.fine_sups(y, y2)
        cap = min(
            ep.lambda_bar_from_sups(theta, sups, y2, d) for d in ep.delta_choices
        )
        slack = ep.slack(y)
        rows[y] = {
            "eta": eta,
            "cap_fraction": cap / slack,
            "combined": cap / slack + eta,
            "closed": cap / slack + eta <= 1,
        }
    return rows
