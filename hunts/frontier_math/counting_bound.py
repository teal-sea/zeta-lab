"""Level 4: the counting dual — a configuration-free bound on the adversary.

Level 3 established theta > 0 at the single-pair reduction with the worst
case *measured* over two adversary families, and named its first gap: a
bound on

    Lambda(theta, y) = sup_X [ D(X) - (1-theta) R_int(X) ]

valid over ALL finite on-line configurations X, not just tested families.
This module closes that gap with an elementary counting argument whose only
inputs are the closed-form kernel, two Cauchy-Schwarz Lipschitz constants,
and the fact that same-cell points repel.

THE COUNTING BOUND.  Partition the offset line into cells of width delta.
Any two points in the same cell are within delta, so each same-cell pair
pays internal mass at least ``K_delta := min_{[0,delta]} omega^2``
(dropping cross-cell payments is one-sided in the adversary's favour).  If
cell j holds n_j points and ``F_j >= sup_cell f+`` (``f = -2W``), then

    D(X) - c R_int(X)  <=  sum_j max_n [ n F_j - c K_delta n (n-1) ]
                       <=  sum_j B_j,          c := 1 - theta,
    B_j = F_j                          if F_j <= 2 c K_delta,
    B_j = (F_j + c K_delta)^2 / (4 c K_delta)   otherwise.

The two regimes are the mechanism made visible: a cell whose damage is
below ``2 c K_delta`` is worth at most ONE adversary point (density is
pointless there), and a hotter cell's value is capped by the square
completion.  Everything is per-cell, so the bound holds for every finite
configuration, every placement, every size.

ONE-SIDED CELLS.  ``F_j`` is computed from the closed-form centre values of
``C = Re Phi2(g+iy)`` and ``S = -Im Phi2(g+iy)`` inflated by elementary
Lipschitz constants (Cauchy-Schwarz on the defining integrals):

    |dS/dg| <= (L/2) aL sigma(y),   |dC/dg| <= (L/2) aL E(y),
    |dS/dy| <= (L/2) aL E(y),       |dC/dy| <= (L/2) aL sigma(y),

with ``E(y) = Phi2(iy)/Phi2(0)`` and both monotone in y, so a cell in
``(g, y)`` gets a valid sup for ``S^2`` and a valid inf for ``C^2``; then
``f+ <= 4 (Sbar^2 - Cund^2)+ / (aL)^2`` (``f = -2W`` carries a
factor 4 against the C/S split) on the whole cell.  Far cells use
the integration-by-parts majorant ``psi_y`` instead.  Everything is
evaluated in double precision with the inflation margins doing the
one-sided work; the arb-enclosure pass over the same finitely many cells is
the named final hardening step.

WHAT COMES OUT.  ``secured_theta`` scans a geometric depth ladder and
returns the largest theta on the grid for which

    sum_j B_j(theta, y-cell)  <=  8 sigma^2(y_low) + 8 sigma^4(y_low)

on every depth cell — the level-3 per-pair inequality, now with the
adversary side configuration-free.  The projection rule of the hierarchy's
level-4 row is enforced as tests: the bound dominates every level-3
measured adversary, the level-2 escaping cluster, and reduces to LAW I on
a single cell.

The second level-3 gap (multi-pair slack partition) is treated in
:func:`pair_layer_audit`: the pair-pair kernel has the same shape as the
on/off one (positive at coincidence, negative bands, decaying tail), the
halved-slack partition covers the measured worst dipoles, and the remaining
step — the pair-pair analogue of THIS module's cell bound at combined
depths — is named, not blurred.

Run ``.venv/bin/python hunts/frontier_math/counting_bound.py`` from the
repo root (~1 minute).
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gap_consistency import C_RHO, _phi2_hat_f  # noqa: E402
from theta_recovery import Recovery  # noqa: E402


@dataclass(frozen=True)
class CountingBound:
    """The level-4 dual object: per-cell capacities, no configurations."""

    L: float = 8.0
    w: float = 1.0
    delta_choices: tuple = (0.25, 0.3, 0.35, 0.4, 0.45)
    g_max: float = 40.0

    @property
    def aL(self) -> float:
        return _phi2_hat_f(0j, self.L, self.w).real

    def phi2(self, z: complex) -> complex:
        return _phi2_hat_f(z, self.L, self.w)

    def sigma_sq(self, y: float) -> float:
        return (self.phi2(complex(0, 2 * y)).real - self.aL) / (2 * self.aL)

    def E(self, y: float) -> float:
        """Depth inflation Phi2(iy)/Phi2(0) >= 1, increasing in |y|."""
        return self.phi2(complex(0, y)).real / self.aL

    def slack(self, y: float) -> float:
        s2 = self.sigma_sq(y)
        return 8 * s2 + 8 * s2 * s2

    # -- Lipschitz constants (Cauchy-Schwarz on the defining integrals) ----

    def lip_S_g(self, y_hi: float) -> float:
        return (self.L / 2) * self.aL * math.sqrt(self.sigma_sq(y_hi))

    def lip_C_g(self, y_hi: float) -> float:
        return (self.L / 2) * self.aL * self.E(y_hi)

    # mixed derivatives swap the two bounds
    def lip_S_y(self, y_hi: float) -> float:
        return self.lip_C_g(y_hi)

    def lip_C_y(self, y_hi: float) -> float:
        return self.lip_S_g(y_hi)

    # -- the repulsion floor ----------------------------------------------

    def K_delta(self, delta: float, step: float = 0.005) -> float:
        """One-sided min of omega^2 over [0, delta].

        Grid min minus the slope margin |omega'| <= L/2 times the step.
        """
        lo = math.inf
        r = 0.0
        while r <= delta + 1e-12:
            lo = min(lo, self.phi2(complex(r, 0)).real / self.aL)
            r += step
        lo -= (self.L / 2) * step
        return max(0.0, lo) ** 2

    # -- one-sided cell sup of the damage ----------------------------------

    def cell_sup_damage(self, g1: float, g2: float, y1: float, y2: float) -> float:
        """sup over the cell of f+ = max(0, -2W), one-sided by inflation."""
        gm, ym = (g1 + g2) / 2, (y1 + y2) / 2
        v = self.phi2(complex(gm, ym))
        C_c, S_c = v.real, -v.imag
        rg, ry = (g2 - g1) / 2, (y2 - y1) / 2
        S_bar = abs(S_c) + self.lip_S_g(y2) * rg + self.lip_S_y(y2) * ry
        C_und = max(0.0, abs(C_c) - self.lip_C_g(y2) * rg - self.lip_C_y(y2) * ry)
        return max(0.0, 4 * (S_bar**2 - C_und**2)) / (self.aL**2)

    def psi_S(self, y_hi: float) -> float:
        """||(phi^2 sinh(y.))''||_1: the depth-scaled tail constant for S.

        (phi^2 sinh)'' = (phi^2)'' sinh + 2 (phi^2)' y cosh + phi^2 y^2 sinh,
        bounded by (c_rho/w) sinh(yL/2) + 4 y cosh(yL/2) + y^2 aL sinh(yL/2)
        using the paper's (2.13) norms.  Vanishes linearly as y -> 0, which
        is what lets the far tail scale down with the slack.
        """
        sh = math.sinh(y_hi * self.L / 2)
        ch = math.cosh(y_hi * self.L / 2)
        return (float(C_RHO) / self.w) * sh + 4 * y_hi * ch + y_hi * y_hi * self.aL * sh

    def tail_sup_damage(self, g: float, y_hi: float) -> float:
        """Beyond the fine region: f+ <= 4 S^2/(aL)^2 <= 4 psi_S^2/(g^4 aL^2)."""
        return 4 * (self.psi_S(y_hi) / (g * g * self.aL)) ** 2

    # -- the bound ----------------------------------------------------------

    #: fine sup-evaluation grid: the capacity partition delta and the
    #: sup-evaluation step are decoupled -- sups are taken on this fine
    #: subgrid (small Lipschitz inflation), then grouped into delta-cells
    #: for the capacity count.  fine_step must divide every delta.
    fine_step: float = 0.0125
    fine_g_max: float = 16.0
    y_slices: int = 6

    def fine_sups(self, y1: float, y2: float):
        """One-sided sups of f+ on the fine grid over the depth cell.

        The depth cell is subdivided into y_slices; each fine bin's sup is
        the max over slices of the centre value inflated by the Lipschitz
        radii of the *fine* bin and the *slice* -- small on both axes.
        """
        n = int(round(2 * self.fine_g_max / self.fine_step))
        sups = [0.0] * n
        dy = (y2 - y1) / self.y_slices
        for s in range(self.y_slices):
            ya, yb = y1 + s * dy, y1 + (s + 1) * dy
            ym = (ya + yb) / 2
            lsg, lcg = self.lip_S_g(yb), self.lip_C_g(yb)
            lsy, lcy = self.lip_S_y(yb), self.lip_C_y(yb)
            rg, ry = self.fine_step / 2, dy / 2
            for i in range(n):
                gm = -self.fine_g_max + (i + 0.5) * self.fine_step
                v = self.phi2(complex(gm, ym))
                S_bar = abs(v.imag) + lsg * rg + lsy * ry
                C_und = max(0.0, abs(v.real) - lcg * rg - lcy * ry)
                f = max(0.0, 4 * (S_bar**2 - C_und**2)) / (self.aL**2)
                if f > sups[i]:
                    sups[i] = f
        return sups

    def lambda_bar_from_sups(self, theta: float, sups, y2: float,
                             delta: float, n_cap: int = 14) -> float:
        """The chain capacity bound for one delta, from precomputed sups.

        Same-cell pairs pay K_delta, adjacent-cell pairs (distance < 2delta)
        pay K_{2delta}; non-adjacent payments are dropped (one-sided).  The
        resulting per-window optimum

            max over n_j >= 0 of
                sum_j [ n_j F_j - cK1 n_j(n_j - 1) - cK2 n_j n_{j+1} ]

        is solved exactly by dynamic programming over the cell chain.  For
        2delta past the first zero of omega, K2 = 0 and the chain reduces to
        the plain per-cell bound.
        """
        c = 1 - theta
        if c <= 0:
            return math.inf
        cK1 = c * self.K_delta(delta)
        cK2 = c * self.K_delta(2 * delta)
        if cK1 <= 0:
            return math.inf

        per_cell = int(round(delta / self.fine_step))
        cells = [
            max(sups[j : j + per_cell], default=0.0)
            for j in range(0, len(sups), per_cell)
        ]
        # mid tail: fine_g_max < |g| <= g_max via the depth-scaled majorant,
        # appended as ordinary chain cells (their neighbours only help)
        g = self.fine_g_max
        mid = []
        while g < self.g_max:
            mid.append(self.tail_sup_damage(g, y2))
            g += delta
        cells = mid[::-1] + cells + mid  # both signs of g

        # chain DP; state = count in the previous cell
        prev = [0.0] * (n_cap + 1)
        for F in cells:
            cur = [-math.inf] * (n_cap + 1)
            for n in range(n_cap + 1):
                own = n * F - cK1 * n * (n - 1)
                best = max(prev[m] - cK2 * m * n for m in range(n_cap + 1))
                cur[n] = own + best
            prev = cur
        total = max(prev)
        arg = max(range(n_cap + 1), key=lambda n: prev[n])
        if arg == n_cap:
            # the cap binds: retry with a doubled cap (rare, deep + high theta)
            return self.lambda_bar_from_sups(theta, sups, y2, delta,
                                             n_cap=2 * n_cap)

        # far tail: all linear (asserted), summed to negligibility
        g = self.g_max
        while True:
            F = self.tail_sup_damage(g - delta, y2)
            if F > 2 * cK1:  # pragma: no cover - would break one-sidedness
                raise AssertionError("tail cell left the linear regime")
            total += 2 * F
            if F < 1e-12:
                break
            g += delta
        return total

    def lambda_bar(self, theta: float, y1: float, y2: float,
                   delta: float) -> float:
        """Configuration-free adversary cap (single delta)."""
        return self.lambda_bar_from_sups(theta, self.fine_sups(y1, y2), y2, delta)

    def best_lambda_bar(self, theta: float, y1: float, y2: float) -> float:
        """Min over the delta ladder — each delta is one-sided, so min is."""
        sups = self.fine_sups(y1, y2)
        return min(
            self.lambda_bar_from_sups(theta, sups, y2, d) for d in self.delta_choices
        )

    # -- the securing scan -------------------------------------------------------

    def depth_ladder(self, y_min: float = 0.002, y_max: float = 0.499,
                     ratio: float = 1.18, deep_ratio: float = 1.04,
                     deep_from: float = 0.09):
        """Geometric depth cells, refined at the deep end where sigma^2
        changes fastest relative to the slack evaluated at the shallow lip."""
        cells = []
        y = y_min
        while y < y_max:
            r = deep_ratio if y >= deep_from else ratio
            cells.append((y, min(y * r, y_max)))
            y *= r
        return cells

    def secured_theta(self, thetas=(0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6),
                        **ladder_kw):
        """Largest grid theta with sum B_j <= slack on every depth cell.

        Returns (theta_star, per-theta worst margins).  The slack is taken
        at the shallow end of each depth cell (sigma increasing), keeping
        the comparison one-sided; the fine sups are shared across thetas.
        """
        cells = self.depth_ladder(**ladder_kw)
        sups_per_cell = [(y1, y2, self.fine_sups(y1, y2)) for y1, y2 in cells]
        margins = {}
        theta_star = None
        for theta in thetas:
            worst = math.inf
            for y1, y2, sups in sups_per_cell:
                cap = min(
                    self.lambda_bar_from_sups(theta, sups, y2, d)
                    for d in self.delta_choices
                )
                worst = min(worst, self.slack(y1) - cap)
            margins[theta] = worst
            if worst >= 0:
                theta_star = theta
        return theta_star, margins


# ---------------------------------------------------------------------------
# Projection controls: the bound must dominate every lower level
# ---------------------------------------------------------------------------


def bound_dominates_measured_adversaries(cb: CountingBound, theta: float,
                                         ys=(0.1, 0.3, 0.45)):
    """Level-3 lattice/greedy profits must sit below the level-4 cap."""
    rec = Recovery(cb.L, cb.w)
    out = []
    for y in ys:
        cap = cb.best_lambda_bar(theta, y, y * 1.0001)
        measured = -math.inf
        for sp in (1.0, 0.5, 0.25, 0.125):
            profit = rec.slack(y) - rec.lattice_net(theta, y, sp)
            measured = max(measured, profit)
        profit = rec.slack(y) - rec.greedy_net(theta, y, 8)
        measured = max(measured, profit)
        out.append({"y": y, "measured_profit": measured, "level4_cap": cap,
                    "dominated": measured <= cap})
    return out


def lesion_no_inflation(cb: CountingBound, y: float, delta: float = 0.75) -> dict:
    """The Lipschitz inflation is load-bearing: drop it and cell 'sups' from
    coarse centre values stop majorising the true damage.

    The lesion evaluates each coarse cell's damage at its centre only (no
    inflation, no fine subgrid) and probes the cell interior for true values
    exceeding it.  A positive worst violation is the lesion firing -- the
    direct check that the inflation is what makes the cells one-sided.
    """
    rec = Recovery(cb.L, cb.w)
    worst = 0.0
    g = -cb.fine_g_max
    while g < cb.fine_g_max - 1e-12:
        v = cb.phi2(complex(g + delta / 2, y))
        lesion_sup = max(0.0, 4 * (v.imag**2 - v.real**2)) / (cb.aL**2)
        probe = g + delta / 8
        while probe < g + delta:
            f_true = 2 * max(0.0, -rec.W(probe, y))
            worst = max(worst, f_true - lesion_sup)
            probe += delta / 4
        g += delta
    return {"worst_sup_violation": worst, "lesion_fires": worst > 1e-6}


# ---------------------------------------------------------------------------
# Gap 2: the pair-pair layer and the halved-slack partition
# ---------------------------------------------------------------------------


def pair_layer_audit(cb: CountingBound):
    """The partition frame: half the slack against on-line damage, half
    against pair-pair terms; the measured worst dipoles must fit."""
    rec = Recovery(cb.L, cb.w)
    rows = []
    for y1, y2 in ((0.3, 0.3), (0.45, 0.45), (0.49, 0.2)):
        worst, arg = math.inf, 0.0
        dt = 0.0
        while dt < 12.0:
            t = rec.pair_pair(dt, y1, y2)
            if t < worst:
                worst, arg = t, dt
            dt += 0.01
        # the shared term is charged half to each pair against half-slack
        half_budget = (cb.slack(y1) + cb.slack(y2)) / 2
        rows.append({
            "depths": (y1, y2), "worst_T": worst, "at_dt": arg,
            "half_slack_budget": half_budget,
            "fits": half_budget + worst >= 0,
        })
    # stacking control: coincident ordinates must be positive
    stacked = [rec.pair_pair(0.0, a, b) for a, b in ((0.3, 0.3), (0.45, 0.44))]
    return rows, stacked


def audit():
    cb = CountingBound()
    print("= K_delta ladder (one-sided repulsion floors) =")
    for d in cb.delta_choices:
        print(f"  delta={d}: K_delta = {cb.K_delta(d):.6f}")
    print("= secured theta scan (configuration-free) =")
    theta_star, margins = cb.secured_theta()
    for theta, margin in margins.items():
        print(f"  theta={theta:.1f}: worst depth-cell margin = {margin:+.5f}  "
              f"{'OK' if margin >= 0 else 'FAILS'}")
    print(f"  secured theta* (grid) = {theta_star}")
    print("= projection: level-3 measured adversaries under the cap =")
    for row in bound_dominates_measured_adversaries(cb, 0.3):
        print(f"  y={row['y']}: measured {row['measured_profit']:+.4f}  "
              f"cap {row['level4_cap']:.4f}  dominated={row['dominated']}")
    print("= lesion: cells without inflation stop majorising =")
    for y in (0.15, 0.3, 0.45):
        row = lesion_no_inflation(cb, y)
        print(f"  y={y}: worst sup violation {row['worst_sup_violation']:.4f}  "
              f"fires={row['lesion_fires']}")
    print("= gap 2 frame: halved-slack partition vs measured dipoles =")
    rows, stacked = pair_layer_audit(cb)
    for row in rows:
        print(f"  depths {row['depths']}: worst T {row['worst_T']:+9.4f} at "
              f"dt={row['at_dt']:.2f}  half budget {row['half_slack_budget']:8.4f}"
              f"  fits={row['fits']}")
    print(f"  stacked positivity: {['%+.3f' % s for s in stacked]}")


if __name__ == "__main__":
    audit()
