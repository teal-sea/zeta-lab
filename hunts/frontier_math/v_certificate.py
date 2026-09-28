"""Level 7, phase 1: the pointwise-in-v certificate, LAW N and the joint cap.

THE TARGET.  Level 6b's joint verdict (worst pinch margin +0.0704) rests on
a greedy measured on-line adversary.  The named theorem object is the joint
cap: an upper bound on the joint on-line profit

    J(pairs) := sup over on-line X of [ -X_cross - (1-theta) R(X) ]

valid for EVERY finite on-line configuration, so that the requirement

    (1-theta) R + sum_r slack_r + T_signed + X_cross >= 0
    <=>  J(pairs) <= sum_r slack_r + T_signed(pairs)      (the budget)

becomes configuration-free on the on-line side.  This module builds that
cap in the Fourier bridge's one variable, from four exact ingredients.

LAW N (the windowed spectral floor; exact, new).  For n on-line points in
an interval of length S,

    |F_on(v)|  >=  n cos(vS/2)      for |v| <= pi/S,

because every unit phasor e^{i(x_j - m)v} (m the midpoint) has argument in
[-vS/2, vS/2].  Consequence: the on-line spectral mass in the floor region
|v| <= V_f <= pi/S is at least  kappa_00 n^2, with kappa_00 =
(2/(aL)^2) int_0^{V_f} K cos^2(vS/2) dv.  Since the total spectral mass is
exactly n + R, the internal mass obeys  R >= kappa_00 n^2 - n: density is
self-defeating IN v, the v-space form of the level-3/4 packing quadratic,
and the exact reason a spectrally-concentrated adversary (the sub-critical
lattice that defeats any naive pointwise-in-v budget, see
:func:`pointwise_form_obstruction`) pays for its own count.

THE SAFE CELL (exact).  For on-line points and pair ordinates in a common
span-S window, arg(F_on conj(F_p)) is within [-vS, vS], so the cross
integrand 2 Re(F_on conj(F_p)) is >= 0 on |v| <= pi/(2S): the band where a
dense pair cluster hides its spectral mass cannot be attacked at all,
level 6b's chi collapse, pointwise.

THE THREE-ZONE DECOMPOSITION (all one-sided).  On-line zeros are split by
distance from the pair window (near / mid / far); R >= R_near + R_mid +
R_far drops only nonnegative cross terms.  The near zone's cross term is
split by a smooth even taper m_I (=1 on |v| <= v1/2, cos^2 ramp to 0 at
v1, m_I + m_II = 1):

- ZONE N-I (coherent band, |v| <~ v1): the cross is the g-space field of
  the LOW-PASS kernel W_I(g, y) = (1/(aL)^2) int K m_I 4 cos(gv) cosh(yv) dv
  summed over pair centres; bounded by the level-4 chain counting DP with
  internal charge rho (1-theta) K_delta.  LAW M fixes int W_I dg =
  4 pi b/(a^2 L) at every depth AND every taper, the mean is not
  attackable, only the band-limited ripple is, and the ripple is small
  and 1/g^2-summable (smooth taper, no boundary terms).
- ZONE N-II (the rest of the band): per-cell Cauchy-Schwarz against the
  pair mass.  Summed over cells the bound telescopes to ONE number,
      M_II(pairs) := (1/(aL)^2) int K m_II |F_p|^2 dv,
  charged at 1/((1-rho)(1-theta)); the remaining on-line freedom is paid
  by LAW N:  the leak is at most  (1-rho)(1-theta) max_n (n - kappa_00 n^2)
  = (1-rho)(1-theta)/(4 kappa_00).
- ZONE M (mid, window edge + [0, G_mid]): the full measured damage field
  summed over pairs, chain DP at full charge (grid sups + Lipschitz).
- ZONE F (far): the depth-scaled psi_S majorant, linear-regime tail cells.

    J_cap = DP_I + M_II/((1-rho)(1-theta)) + (1-rho)(1-theta)/(4 kappa_00)
            + DP_mid + err_far,

minimised over the (v1, rho) ladder, each choice is one-sided, so the min
is.

THE DIRECT ROUTE (:meth:`VCertificate.direct_cap`).  Level 6b's originally
named object, the level-4 chain counting dual on the damage field summed
over pair centres, f(g) = (-(sum_r 2 W(g - t_r, y_r)))_+ , at full charge,
turns out to dominate the v-route almost everywhere once the positive part
is taken of the JOINT field (clipping per pair would discard the
coincident-pair shielding and reproduce the separable accounting's
looseness; that near-miss is kept as a control).  The v-route remains the
independent cross-check and the carrier of the exact laws; the final cap
is the min of the two routes, each one-sided.  The verdict per pair
configuration:  margin = budget - J_cap.

WHAT THE MEASUREMENTS MUST SHOW (the directive's kill controls): J_cap
dominates the greedy joint adversary and every lower level's measured
single-pair adversary; theta = 1 makes the cap infinite (fails, as it
must); the pinch lattice, the 6b sweep and the mixed-depth battery get
honest margins, and wherever the certificate does not close, the escaping
v-share is pinned term by term.

Run ``.venv/bin/python hunts/frontier_math/v_certificate.py`` (~10 min).
"""

from __future__ import annotations

import cmath
import math
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from counting_bound import CountingBound  # noqa: E402
from fourier_bridge import FourierBridge  # noqa: E402
from pair_energy import PairEnergy  # noqa: E402
from theta_recovery import Recovery  # noqa: E402


def chain_dp(cells, cK1, cK2, n_cap: int = 14) -> float:
    """The level-4 tridiagonal chain DP: max over occupation numbers of
    sum_j [n_j F_j - cK1 n_j (n_j - 1) - cK2 n_j n_{j+1}]."""
    if cK1 <= 0:
        return math.inf
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
        return chain_dp(cells, cK1, cK2, 2 * n_cap)
    return total


@dataclass(frozen=True)
class VCertificate:
    L: float = 8.0
    w: float = 1.0
    #: near-zone half-extension beyond the pair ordinate span
    G_near: float = 2.0
    #: mid zone reaches this far beyond the near window (measured field)
    G_mid: float = 32.0
    #: quadrature points per unit v
    quad_per_unit: int = 400
    #: fine g-grid step for zone-I / mid field sups
    fine_step: float = 0.05
    #: DP cell width ladder
    delta_choices: tuple = (0.25, 0.35, 0.45)
    #: (v1, rho) ladder
    v1_choices: tuple = (0.8, 1.2, 1.4, 1.6)
    rho_choices: tuple = (0.001, 0.005, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45)

    @property
    def fb(self) -> FourierBridge:
        return FourierBridge(self.L, self.w)

    @property
    def pe(self) -> PairEnergy:
        return PairEnergy(self.L, self.w)

    @property
    def cb(self) -> CountingBound:
        return CountingBound(self.L, self.w)

    @property
    def aL(self) -> float:
        return self.fb.aL

    # -- kernel table (quadrature once, reused everywhere) -------------------

    @lru_cache(maxsize=4)
    def _K_table(self, n: int):
        fb = self.fb
        step = self.L / n
        return [fb.K(i * step) for i in range(n + 1)], step

    def K_at(self, v: float) -> float:
        tab, step = self._K_table(self.quad_per_unit * int(self.L))
        av = abs(v)
        if av >= self.L:
            return 0.0
        i = av / step
        i0 = min(int(i), len(tab) - 2)
        frac = i - i0
        return tab[i0] * (1 - frac) + tab[i0 + 1] * frac

    # -- the taper -----------------------------------------------------------

    @staticmethod
    def m_I(v: float, v1: float) -> float:
        av = abs(v)
        if av <= v1 / 2:
            return 1.0
        if av >= v1:
            return 0.0
        return math.cos(math.pi * (av - v1 / 2) / v1) ** 2

    def m_II(self, v: float, v1: float) -> float:
        return 1.0 - self.m_I(v, v1)

    # -- LAW N: floor constant, one-sided lower --------------------------------

    def kappa00(self, S: float, v1: float) -> float:
        """(2/(aL)^2) int_0^{V_f} K cos^2(vS/2) dv, lower one-sided.

        V_f = min(pi/S, v1/2) keeps the floor inside both the LAW N range
        and the m_I = 1 plateau.  Grid lower Riemann value minus a
        Lipschitz margin: |K'| <= TV(phi^2) sup phi^2 <= 2, and
        |d cos^2(vS/2)/dv| <= S/2, so Lip <= 2 + sup K * S / 2.
        """
        V_f = min(math.pi / S, v1 / 2)
        n = 200
        h = V_f / n
        total = 0.0
        for i in range(n):
            va, vb = i * h, (i + 1) * h
            fa = self.K_at(va) * math.cos(va * S / 2) ** 2
            fb_ = self.K_at(vb) * math.cos(vb * S / 2) ** 2
            lip = 2.0 + self.K_at(0.0) * S / 2
            total += max(0.0, min(fa, fb_) - lip * h) * h
        return 2 * total / (self.aL**2)

    # -- zone N-I: the low-pass field ------------------------------------------

    def W_I(self, g: float, y: float, v1: float) -> float:
        """(1/(aL)^2) int_{-v1}^{v1} K m_I 4 cos(gv) cosh(yv) dv."""
        n = max(64, int(self.quad_per_unit * v1))
        h = v1 / n
        total = 0.0
        for i in range(n + 1):
            v = i * h
            wgt = 0.5 if i in (0, n) else 1.0
            total += (wgt * self.K_at(v) * self.m_I(v, v1)
                      * math.cos(g * v) * math.cosh(y * v))
        return 2 * total * h * 4 / (self.aL**2)

    def lip_W_I(self, y: float, v1: float) -> float:
        """|dW_I/dg| <= (4/(aL)^2) int K m_I |v| cosh dv... x2 for both signs."""
        n = max(64, int(self.quad_per_unit * v1))
        h = v1 / n
        total = 0.0
        for i in range(n + 1):
            v = i * h
            wgt = 0.5 if i in (0, n) else 1.0
            total += wgt * self.K_at(v) * self.m_I(v, v1) * v * math.cosh(y * v)
        return 2 * total * h * 4 / (self.aL**2)

    @lru_cache(maxsize=64)
    def _W_I_table(self, y: float, v1: float, umax: float = 24.0,
                   step: float = 0.01):
        return [self.W_I(i * step, y, v1)
                for i in range(int(umax / step) + 2)], step

    def W_I_fast(self, u: float, y: float, v1: float) -> float:
        tab, step = self._W_I_table(y, v1)
        au = abs(u)
        i = au / step
        i0 = min(int(i), len(tab) - 2)
        frac = i - i0
        return tab[i0] * (1 - frac) + tab[i0 + 1] * frac

    def zone_I_sups(self, pairs, v1: float, G: float,
                    field_out: list | None = None):
        """One-sided fine-grid sups of the low-pass damage field.

        The field is charged over the NEAR window only: zeros beyond it
        are mid/far-zone zeros whose whole cross (all v) is charged by
        dp_mid / err_far, so extending the zone-I cells past the window
        would double-cover them.  The kernel-table interpolation error is
        covered by the margin lip * (fine_step/2 + table_step).
        """
        ts = [t for t, _ in pairs]
        lo, hi = min(ts) - G, max(ts) + G
        lip = sum(self.lip_W_I(y, v1) for _, y in pairs)
        margin = lip * (self.fine_step / 2 + 0.01)
        sups = []
        g = lo
        while g <= hi:
            f = sum(-self.W_I_fast(g - t, y, v1) for t, y in pairs)
            sups.append(max(0.0, f + margin))
            if field_out is not None:
                field_out.append((g, f))
            g += self.fine_step
        return sups

    def dp_zone_I(self, pairs, v1: float, rho: float, theta: float,
                  G: float | None = None, sups=None) -> float:
        """Chain DP on the zone-I sups with internal charge rho (1-theta)."""
        if sups is None:
            sups = self.zone_I_sups(pairs, v1, G or self.G_near)
        best = math.inf
        for delta in self.delta_choices:
            per = max(1, int(round(delta / self.fine_step)))
            cells = [max(sups[j:j + per], default=0.0)
                     for j in range(0, len(sups), per)]
            cK1 = rho * (1 - theta) * self.cb.K_delta(delta)
            cK2 = rho * (1 - theta) * self.cb.K_delta(2 * delta)
            best = min(best, chain_dp(cells, cK1, cK2))
        return best

    # -- zone N-II: pair mass beyond the taper + the LAW N leak ----------------

    def F_p_sq(self, v: float, pairs) -> float:
        tot = 0j
        for t, y in pairs:
            tot += cmath.exp(1j * t * v) * 2 * math.cosh(y * v)
        return abs(tot) ** 2

    def M_II(self, pairs, v1: float) -> float:
        """(2/(aL)^2) int_0^L K m_II |F_p|^2 dv (upper-biased quadrature)."""
        n = self.quad_per_unit * int(self.L)
        h = self.L / n
        total = 0.0
        for i in range(n + 1):
            v = i * h
            m2 = self.m_II(v, v1)
            if m2 == 0.0:
                continue
            wgt = 0.5 if i in (0, n) else 1.0
            total += wgt * self.K_at(v) * m2 * self.F_p_sq(v, pairs)
        return 2 * total * h / (self.aL**2)

    # -- zones M and F: the mid and far g-space fields -------------------------

    def mid_far_caps(self, pairs, theta: float,
                     mid_step: float = 0.01,
                     G: float | None = None) -> tuple[float, float]:
        """(DP_mid, err_far): measured field DP on the mid zone, psi tail far.

        Mid-zone sups are dense-grid measured with a measured-slope margin
        (max local slope over the zone, times the step, times a factor 2):
        the field there is the smooth 1/g^4-scale tail of 2W, and the arb
        pass over these finitely many cells is the named remaining
        hardening (the analytic Lipschitz constant is ~10^2 too coarse at
        these distances and would bury the field in its own margin).
        """
        pe, cb = self.pe, self.cb
        ts = [t for t, _ in pairs]
        G = G if G is not None else self.G_near
        lo, hi = min(ts) - G, max(ts) + G
        c = 1 - theta

        vals = []
        for side in (-1, 1):
            start = lo if side < 0 else hi
            n = int(self.G_mid / mid_step)
            run = []
            for i in range(n):
                g = start + side * i * mid_step
                run.append(max(0.0, sum(-2 * pe.W(g - t, y)
                                        for t, y in pairs)))
            vals.append(run)

        best = math.inf
        for delta in self.delta_choices:
            per = max(1, int(round(delta / mid_step)))
            cells = []
            for run in vals:
                for j in range(0, len(run), per):
                    seg = run[j:j + per + 1]  # include the shared endpoint
                    if not seg:
                        continue
                    # per-cell margin from the cell's own measured slope:
                    # a blanket global-slope margin over ~500 cells was
                    # most of dp_mid at the seam budgets
                    local = max(
                        (abs(seg[i + 1] - seg[i]) for i in range(len(seg) - 1)),
                        default=0.0,
                    )
                    cells.append(max(seg) + 2 * local)
            cK1 = c * cb.K_delta(delta)
            cK2 = c * cb.K_delta(2 * delta)
            best = min(best, chain_dp(cells, cK1, cK2))
        # far: psi majorant, linear-regime cells
        delta = self.delta_choices[0]
        cK1 = c * cb.K_delta(delta)
        err_far = 0.0
        for side in (-1, 1):
            g = self.G_mid
            while True:
                edge = (lo - g) if side < 0 else (hi + g)
                F = sum(cb.tail_sup_damage(abs(edge - t), y) for t, y in pairs)
                if F > 2 * cK1:
                    raise AssertionError("far cell left the linear regime")
                err_far += F
                if F < 1e-12:
                    break
                g += delta
        return best, err_far

    # -- the direct route: the counting DP on the joint damage field ----------

    def direct_cap(self, pairs, theta: float,
                   fine: float = 0.0125) -> float:
        """Level 6b's originally named object: the level-4 chain counting
        dual with the damage field summed over pair centres,

            f(g) = sum_r max(0, -2 W(g - t_r, y_r)),

        one DP over the whole interaction range at full charge (1-theta).
        No taper, no leak, no Cauchy-Schwarz: LAW M's positive mean sits
        inside the summed field itself, so at lattice densities the field
        is negative-part-small and the cap is tight exactly where the
        v-route's band-edge grant is loose (the seam).  Field sups are
        dense-grid measured with per-cell measured-slope margins (same
        grade as the mid zone; the arb pass is the named hardening).
        """
        pe, cb = self.pe, self.cb
        ts = [t for t, _ in pairs]
        lo, hi = min(ts) - self.G_mid, max(ts) + self.G_mid
        c = 1 - theta
        # the positive part of the JOINT field, clipping per pair instead
        # would discard the coincident-pair shielding and reproduce the
        # separable accounting's looseness
        n = int((hi - lo) / fine) + 1
        run = [
            max(0.0, sum(-2 * pe.W(lo + i * fine - t, y) for t, y in pairs))
            for i in range(n)
        ]
        best = math.inf
        for delta in self.delta_choices:
            per = max(1, int(round(delta / fine)))
            cells = []
            for j in range(0, len(run), per):
                seg = run[j:j + per + 1]
                if not seg:
                    continue
                local = max(
                    (abs(seg[i + 1] - seg[i]) for i in range(len(seg) - 1)),
                    default=0.0,
                )
                cells.append(max(seg) + 2 * local)
            cK1 = c * cb.K_delta(delta)
            cK2 = c * cb.K_delta(2 * delta)
            best = min(best, chain_dp(cells, cK1, cK2))
        # far tail beyond G_mid, linear-regime psi cells (both sides)
        delta = self.delta_choices[0]
        cK1 = c * cb.K_delta(delta)
        far = 0.0
        for side in (-1, 1):
            g = 0.0
            while True:
                edge = (lo - g) if side < 0 else (hi + g)
                F = sum(cb.tail_sup_damage(abs(edge - t), y) for t, y in pairs)
                if F > 2 * cK1:
                    raise AssertionError("far cell left the linear regime")
                far += F
                if F < 1e-12:
                    break
                g += delta
        return best + far

    # -- the joint cap ---------------------------------------------------------

    #: near-window half-extension ladder (each choice is one-sided)
    G_near_choices: tuple = (2.0,)

    def joint_cap(self, pairs, theta: float = 0.02, detail: bool = False):
        """min over the (G_near, v1, rho) ladder of the five-term cap."""
        if theta >= 1:
            # every internal charge vanishes: the cap is honestly infinite
            return (math.inf, None) if detail else math.inf
        ts = [t for t, _ in pairs]
        direct = self.direct_cap(pairs, theta)
        best = (direct, {"route": "direct", "direct": direct})
        for G in self.G_near_choices:
            S = (max(ts) - min(ts)) + 2 * G
            dp_mid, err_far = self.mid_far_caps(pairs, theta, G=G)
            for v1 in self.v1_choices:
                m2 = self.M_II(pairs, v1)
                k00 = self.kappa00(S, v1)
                sups = self.zone_I_sups(pairs, v1, G)
                for rho in self.rho_choices:
                    dp1 = self.dp_zone_I(pairs, v1, rho, theta, sups=sups)
                    cII = (1 - rho) * (1 - theta)
                    cap = dp1 + m2 / cII + cII / (4 * k00) + dp_mid + err_far
                    if cap < best[0]:
                        best = (cap, {
                            "route": "v-cells",
                            "G_near": G, "v1": v1, "rho": rho, "dp_I": dp1,
                            "M_II": m2, "M_II_term": m2 / cII,
                            "leak": cII / (4 * k00), "kappa00": k00,
                            "dp_mid": dp_mid, "err_far": err_far, "S": S,
                            "direct": direct,
                        })
        return best if detail else best[0]

    def verdict(self, pairs, theta: float = 0.02):
        """margin = budget - J_cap; positive closes REQ for this pair set."""
        pe = self.pe
        slack_total = sum(pe.slack(y) for _, y in pairs)
        t_signed = 0.0
        for i, (t1, y1) in enumerate(pairs):
            for j in range(i + 1, len(pairs)):
                t2, y2 = pairs[j]
                t_signed += 2 * pe.T(t1 - t2, y1, y2)
        cap, detail = self.joint_cap(pairs, theta, detail=True)
        budget = slack_total + t_signed
        return {
            "budget": budget, "slack_total": slack_total,
            "t_signed": t_signed, "j_cap": cap,
            "margin": budget - cap, "closes": budget - cap >= 0,
            "detail": detail,
        }


# ---------------------------------------------------------------------------
# The obstruction to the naive pointwise form (the promoted kill control)
# ---------------------------------------------------------------------------


def pointwise_form_obstruction(vc: VCertificate, taus=(0.55, 0.7),
                               Ns=(20, 40, 80)):
    """The sub-critical on-line lattice defeats any FIXED pointwise budget.

    A lattice of N zeros at spacing tau < 2 pi / L has its nonzero spectral
    spikes outside the kernel band entirely, so on most of (0, L] the
    diagonal-subtracted integrand H(v) = |F_on + F_p|^2 - theta |F_on|^2
    - (1-theta) s_1 - sum_r 4 cosh^2(y_r v) sits near -(1-theta) N: any
    d(v) with a configuration-independent budget is violated linearly in N.
    (The certificate above survives this family through LAW N: the same
    concentration that empties the mid-band fills the floor region, and
    the n - kappa_00 n^2 credit caps the leak.)  Returns, per (tau, N),
    the measured H at a mid-band v and the LAW N accounting.
    """
    theta = 0.02
    y = 0.49
    pairs = [(k / 1.5, y) for k in range(15)]
    rows = []
    for tau in taus:
        for N in Ns:
            online = [j * tau for j in range(N)]
            v = 4.7
            F_on = sum(cmath.exp(1j * x * v) for x in online)
            F_p = sum(cmath.exp(1j * t * v) * 2 * math.cosh(yy * v)
                      for t, yy in pairs)
            diag_p = sum(4 * math.cosh(yy * v) ** 2 for _, yy in pairs)
            H = (abs(F_on + F_p) ** 2 - theta * abs(F_on) ** 2
                 - (1 - theta) * N - diag_p)
            rec = Recovery(vc.L, vc.w)
            R = sum(rec.omega_sq((i - j) * tau)
                    for i in range(N) for j in range(N) if i != j)
            rows.append({"tau": tau, "N": N, "H_mid": H,
                         "F_on_sq_mid": abs(F_on) ** 2, "R": R})
    return rows


# ---------------------------------------------------------------------------
# Sweeps and controls
# ---------------------------------------------------------------------------


def lattice_configs(nu_values=(0.75, 1.0, 1.25, 1.5, 2.0, 3.0),
                    depths=(0.3, 0.45, 0.49), span=10.0):
    for nu_p in nu_values:
        spacing = 1.0 / nu_p
        for y in depths:
            pairs = [(k * spacing, y) for k in range(int(span / spacing))]
            yield (f"lattice nu={nu_p} y={y}", pairs)


def mixed_depth_configs(nu_values=(1.0, 1.5, 2.0), span=10.0):
    """Phase 2a: the level-5 battery shapes at the joint level."""
    for nu_p in nu_values:
        spacing = 1.0 / nu_p
        n = int(span / spacing)
        yield (f"alternating nu={nu_p}",
               [(k * spacing, 0.45 if k % 2 else 0.15) for k in range(n)])
        yield (f"staggered nu={nu_p}",
               [(k * spacing, 0.3) for k in range(n)]
               + [(k * spacing + spacing / 2, 0.4) for k in range(n)])
        yield (f"sandwich nu={nu_p}",
               [(k * spacing, 0.05) for k in range(n)]
               + [(k * spacing, 0.49) for k in range(n)])
        # the eta-assembly's failing band, at the joint level: a shallow
        # y = 0.02 layer riding a deep lattice
        yield (f"shallow sandwich nu={nu_p}",
               [(k * spacing, 0.02) for k in range(n)]
               + [(k * spacing, 0.49) for k in range(n)])
        yield (f"edge cluster nu={nu_p}",
               [(k * spacing, 0.49) for k in range(n)])


def greedy_joint_profit(vc: VCertificate, pairs, theta=0.02, kmax=40,
                        halfext=2.0, minsp=0.125) -> float:
    """The level-6b greedy joint adversary (lower bound on J), for the
    domination control.  The extended variant (halfext=8, kmax=100,
    minsp=1/16) is the seam kill control: at nu_p = 1.3, y = 0.49 it
    extracts 7.23 with 18 zeros against a budget of 35.1, the truth
    sits far inside the budget where both bounds fail."""
    rec = Recovery(vc.L, vc.w)
    ts = [t for t, _ in pairs]
    lo, hi = min(ts) - halfext, max(ts) + halfext
    sites = [lo + 0.02 * i for i in range(int((hi - lo) / 0.02))]
    c = 1 - theta
    chosen: list[float] = []
    dmg_cache: dict[float, float] = {}
    profit = 0.0
    for _ in range(kmax):
        best_gain, best_x = 0.0, None
        for x in sites:
            if any(abs(x - p) < minsp for p in chosen):
                continue
            if x not in dmg_cache:
                dmg_cache[x] = -sum(2 * rec.W(x - t, y) for t, y in pairs)
            internal = 2 * c * sum(rec.omega_sq(x - p) for p in chosen)
            gain = dmg_cache[x] - internal
            if gain > best_gain:
                best_gain, best_x = gain, x
        if best_x is None:
            break
        chosen.append(best_x)
        profit += best_gain
    return profit


def audit():
    vc = VCertificate()
    theta = 0.02
    print("= LAW N spot checks: |F_on(v)| >= n cos(vS/2) on |v| <= pi/S =")
    import random
    rng = random.Random(7)
    worst = math.inf
    for _ in range(200):
        S = rng.uniform(4, 30)
        n = rng.randint(1, 40)
        xs = [rng.uniform(0, S) for _ in range(n)]
        v = rng.uniform(0, math.pi / S)
        F = abs(sum(cmath.exp(1j * x * v) for x in xs))
        worst = min(worst, F - n * math.cos(v * S / 2))
    print(f"  worst margin over 200 random windowed configs: {worst:+.3e}")
    print("= safe cell: cross >= 0 on |v| <= pi/(2S) =")
    worst = math.inf
    for _ in range(200):
        S = rng.uniform(4, 30)
        xs = [rng.uniform(0, S) for _ in range(rng.randint(1, 20))]
        prs = [(rng.uniform(0, S), rng.uniform(0.01, 0.49))
               for _ in range(rng.randint(1, 10))]
        v = rng.uniform(0, math.pi / (2 * S))
        F_on = sum(cmath.exp(1j * x * v) for x in xs)
        F_p = sum(cmath.exp(1j * t * v) * 2 * math.cosh(y * v) for t, y in prs)
        worst = min(worst, 2 * (F_on * F_p.conjugate()).real)
    print(f"  worst cross over 200 random windowed configs: {worst:+.3e}")
    print("= LAW M under the taper: int W_I dg = 2 x LAW M, taper-free =")
    exact = vc.fb.law_m_exact()
    for v1 in (0.4, 0.8):
        tot = 0.0
        g, h = -250.0, 0.05
        while g < 250.0:
            tot += vc.W_I(g, 0.49, v1) * h
            g += h
        print(f"  v1={v1}: int W_I = {tot:.6f} (2 x LAW M constant = "
              f"{2 * exact:.6f}; W_I is the low-pass of the cross 2W)")
    print("= the pinch: term-by-term cap vs budget =")
    pairs = [(k / 1.5, 0.49) for k in range(15)]
    rec = vc.verdict(pairs, theta)
    d = rec["detail"]
    print(f"  budget = slack {rec['slack_total']:.2f} + T {rec['t_signed']:.2f}"
          f" = {rec['budget']:.2f}")
    print(f"  J_cap = {rec['j_cap']:.2f} via {d['route']} "
          f"(direct {d['direct']:.2f}); v-route detail: "
          + ("[dp_I {dp_I:.2f} + M_II-term {M_II_term:.2f} + leak "
             "{leak:.2f} + dp_mid {dp_mid:.2f} + far {err_far:.2f}] "
             "at v1={v1}, rho={rho}".format(**d)
             if d['route'] == 'v-cells' else '(direct wins)'))
    print(f"  margin = {rec['margin']:+.2f}  closes={rec['closes']}")
    greedy = greedy_joint_profit(vc, pairs, theta)
    print(f"  domination control: greedy joint profit {greedy:.2f} <= cap "
          f"{rec['j_cap']:.2f}: {greedy <= rec['j_cap']}")
    print("= theta = 1 must fail =")
    cap1 = vc.joint_cap(pairs, theta=1.0)
    print(f"  J_cap(theta=1) = {cap1} (infinite/failing: "
          f"{not math.isfinite(cap1)})")
    print("= single-pair domination (levels 3/4 measured adversaries) =")
    rec3 = Recovery(vc.L, vc.w)
    for y in (0.1, 0.3, 0.45):
        single = [(0.0, y)]
        cap = vc.joint_cap(single, 0.3)
        measured = max(
            rec3.slack(y) - rec3.lattice_net(0.3, y, sp)
            for sp in (1.0, 0.5, 0.25)
        )
        measured = max(measured,
                       rec3.slack(y) - rec3.greedy_net(0.3, y, 8, kmax=8))
        print(f"  y={y}: measured {measured:8.4f}  v-cap {cap:8.4f}  "
              f"dominated={measured <= cap}")
    print("= the naive pointwise form: the sub-critical lattice obstruction =")
    for row in pointwise_form_obstruction(vc):
        print(f"  tau={row['tau']} N={row['N']:3d}: H(4.7) = "
              f"{row['H_mid']:+9.2f}  |F_on(4.7)|^2 = "
              f"{row['F_on_sq_mid']:7.2f}  R = {row['R']:.2f}")
    print("= the sweep: lattices =")
    for name, pairs in lattice_configs():
        rec = vc.verdict(pairs, theta)
        d = rec["detail"]
        print(f"  {name:26s} budget {rec['budget']:8.2f}  cap "
              f"{rec['j_cap']:8.2f}  margin {rec['margin']:+9.2f}  "
              f"{'closes' if rec['closes'] else 'OPEN'}  "
              f"route {d['route']} (direct {d['direct']:.1f})")
    print("= the sweep: mixed depths (phase 2a) =")
    for name, pairs in mixed_depth_configs():
        rec = vc.verdict(pairs, theta)
        d = rec["detail"]
        print(f"  {name:26s} budget {rec['budget']:8.2f}  cap "
              f"{rec['j_cap']:8.2f}  margin {rec['margin']:+9.2f}  "
              f"{'closes' if rec['closes'] else 'OPEN'}  "
              f"route {d['route']} (direct {d['direct']:.1f})")


if __name__ == "__main__":
    audit()
