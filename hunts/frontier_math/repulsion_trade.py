"""The repulsion trade: paying for clustered damage out of the E-form's own repulsion term.

WHAT THIS IS FOR
================

`zeta23ext/Zeta23Ext/EForm3/` carries the retention inequality

    E[F + P]  >=  theta * E[F] + (1 - theta) * n + 4,        theta = 199/200

for every `n`, every centre `t` and every `y` in `[0, 1/2]`, **under a
separation hypothesis** `x_i + d <= x_{i+1}` with `d >= 4`
(`Retention.retention_separated_of_le`).  That hypothesis is a dead end for
closure: zero gaps have no positive lower bound anyone can supply, so no fixed
`d > 0` covers every configuration.

The exact gap identity (`Retention.retention_gap`) is

    E[F+P] - E[F] - 4  =  (1/A^2) * ( 4 * sum_j (Qre(y,s_j)^2 - Qim(y,s_j)^2)
                                      + 2 * Shq(y) ),        s_j = x_j - t,

and `E[F] = (1/A^2) sum_{j,k} phiR(x_j - x_k)^2` with `phiR = Qre(0, .)`,
`phiR(0) = A`.  Subtracting the target's right-hand side turns the whole
retention question into one scalar inequality:

    sum_j damage(y, x_j - t)  <=  Shq(y)/2  +  ((1-theta)/4) * Rraw(x),   (RT)

    damage(y, s) := Qim(y,s)^2 - Qre(y,s)^2,
    Rraw(x)      := sum_{j != k} phiR(x_j - x_k)^2  =  A^2 * (E[F] - n).

`Rraw >= 0` is the **repulsion term**, and it is exactly what the separation
hypothesis was throwing away: clustered points make `Rraw` large (two
coincident points contribute a full `2 A^2`), and clustered points are
precisely the configurations `d >= 4` excludes.  At `theta = 199/200` the
relief coefficient is `(1-theta)/4 = 1/800`.  Dropping the `Rraw` term from
(RT) recovers `Retention.retention_of_damage`'s hypothesis
`sum_j damage <= Shq/2` exactly, so (RT) is a strict strengthening of what
EForm3 already carries, with the separation hypothesis deleted.

This module measures whether (RT) is true, where it is tight, and what the
sharpest constant is.

WHAT IT MEASURES (all numbers at y = 1/2 unless stated; see `__main__`)
======================================================================

1. **The geometry that makes the trade work.**  `damage(y, .)` is
   `-Re(ghat(s - i y)^2)`, so it is positive only in narrow windows around the
   real zeros of `ghat` (6.6431, 12.7553, 18.9768, ... -> spacing 2*pi).  Each
   window has half-width ~ y.  Measured at y = 1/2: no-damage radius 6.0653,
   maximum window width 0.98590, minimum gap between consecutive windows
   5.18350.  Hence **any two damaging points are either within one window --
   gap <= 0.9859, so `phiR(gap)^2 >= 0.78239`, near the maximum `A^2 =
   0.84406` -- or at least 5.1835 apart.**  Damage inside a window grows
   linearly in the multiplicity while `Rraw` grows quadratically.  That is the
   whole mechanism.

2. **The marginal trade fails, in both directions, and that is not the
   question.**  Adding one point at gap `g` from an existing one buys relief
   `2 * phiR(g)^2 / 800` and can cost up to `max_s damage = 4.396e-3`.  The
   ratio (extra damage)/(extra relief) exceeds 1 for a pair at every gap, and
   the worst value in `0 < g <= 4` is **8.698 at g = 4.00** (second point on
   the first damage peak, `s0 = 2.515`, `phiR(4)^2 = 0.20218`) -- and it is
   worst at the edge of that interval only because `phiR` is decreasing there:
   allowed past 4 the ratio diverges at `g = 6.64308`, `phiR`'s first zero.
   Within a window (`g -> 0`) the ratio is `4.1670/m` for a cluster of `m`: it
   crosses 1 between m = 4 (1.0418) and m = 5 (0.8334).  So the marginal
   framing has no positive answer, and neither the base budget nor the
   repulsion term closes the case alone.  The correct question is the global
   one below: the marginal deficit does not accumulate, because a point can
   only carry damage inside a window, and a window can only hold points that
   repel each other.

3. **The global answer: (RT) holds, and no scan found a violation.**  Two
   margins, because there are two questions.  *As an inequality*, the largest
   value of `sum_j damage - Rraw/800` any search reached is **1.8221e-02**
   against `Shq(1/2)/2 = 3.3754e-02` (factor 1.85), and the window-separable
   majorant caps it at 1.9617e-02 (factor 1.72) without depending on the
   search.  *As a constant*, the worst configuration found -- coincident
   clusters at the damage peaks, multiplicity 6 on the first window and 2 on
   the second, each side, one point on every remaining window -- has

       c_crit = max over configurations of (sum_j damage - Shq/2) / Rraw
              = 4.7496e-04       (at y = 1/2; the maximum over y in (0,1/2])

   against the available `1/800 = 1.25e-03`, a factor 2.63.  Equivalently (RT)
   supports `theta` up to `1 - 4 * c_crit = 0.998100`, better than the 0.995
   EForm3 carries, and with no separation hypothesis.

4. **theta = 1 genuinely fails.**  At `theta = 1` the relief coefficient is 0
   and (RT) becomes `sum_j damage <= Shq/2 = 3.37542e-02`; **eight coincident
   points at s = 6.517 give 3.51714e-02** and break it.  The repulsion term
   pays for that same configuration 2.6x over.

DISCIPLINE
==========

Everything here is measured on a float instrument at a stated resolution, and
the extremal search is a search: it reports the best configuration it found,
not a bound over all configurations.  Nothing in this file is a theorem and
nothing here is evidence for or against RH.  The named gaps between these
measurements and a proof of (RT) are listed in `NAMED_GAPS`.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Callable, Sequence

import numpy as np

__all__ = [
    "SQRT2", "A_CONST", "A_SQ", "THETA_EFORM3", "C_EFORM3", "relief_coefficient",
    "ghat", "phi_R", "qre", "qim", "damage", "shq", "c2",
    "energy_quad", "energy_F", "energy_FP", "gap_identity_residual",
    "repulsion_raw", "repulsion_R", "damage_total", "budget", "trade_slack",
    "retention_margin", "critical_c",
    "DamageWindow", "damage_windows", "WindowGeometry", "window_geometry",
    "MarginalTrade", "marginal_trade", "worst_marginal_ratio",
    "ExtremalConfig", "extremal_multiplicities", "separable_worst_excess",
    "local_position_refinement", "resolution_ladder", "adversarial_search",
    "lattice_scan", "random_scan", "cluster_embedded_scan", "gap_profile",
    "ScanResult", "eform3_crosscheck", "theta_one_counterexample",
    "SHARPEST_STATEMENT", "PINNED", "NAMED_GAPS",
]

# ---------------------------------------------------------------------------
# 1.  The E-form's functions, in EForm3's conventions
# ---------------------------------------------------------------------------

SQRT2 = math.sqrt(2.0)

#: `theta` of `Retention.retention_separated_of_le`.
THETA_EFORM3 = 199.0 / 200.0
#: the relief coefficient (1-theta)/4 that multiplies `Rraw` in (RT).
C_EFORM3 = 1.0 / 800.0


def relief_coefficient(theta: float = THETA_EFORM3) -> float:
    """`(1 - theta)/4`, the coefficient `Rraw` carries in (RT)."""
    return (1.0 - theta) / 4.0


def _hh(w):
    """`sin(w/2)/w`, with the removable singularity at `w = 0` filled in."""
    arr = np.asarray(w)
    small = np.abs(arr) < 1e-6
    safe = np.where(small, 1.0, arr)
    main = np.sin(safe / 2.0) / safe
    w2 = arr * arr
    series = 0.5 * (1.0 - w2 / 24.0 + w2 * w2 / 1920.0)
    return np.where(small, series, main)


def ghat(z):
    """`ghat(z) = int g(u) cos(z u) du`, entire, `g(u) = cos(sqrt2 u) 1_{|u|<=1/2}`.

    Closed form `sin((sqrt2-z)/2)/(sqrt2-z) + sin((sqrt2+z)/2)/(sqrt2+z)`.
    `Qre(y,s) + i Qim(y,s) = ghat(s - i y)` -- see `EForm3/ClosedForm.lean`.
    """
    return _hh(SQRT2 - np.asarray(z)) + _hh(SQRT2 + np.asarray(z))


#: `A = sqrt2 sin(1/sqrt2) = ghat(0) = int g`.
A_CONST = float(np.real(ghat(0.0)))
A_SQ = A_CONST * A_CONST


def phi_R(s):
    """`phiR(s) = Qre(0, s) = ghat(s)`; `phiR(0) = A`."""
    return np.real(ghat(np.asarray(s, dtype=float)))


def _q(y, s):
    return ghat(np.asarray(s, dtype=float) - 1j * float(y))


def qre(y, s):
    """`Qre(y,s) = int g(u) cosh(y u) cos(s u) du`."""
    return np.real(_q(y, s))


def qim(y, s):
    """`Qim(y,s) = int g(u) sinh(y u) sin(s u) du`."""
    return np.imag(_q(y, s))


def damage(y, s):
    """`damage(y,s) = Qim^2 - Qre^2 = -Re(ghat(s - i y)^2)`.

    Positive exactly where the offset costs the retention inequality.
    """
    z = _q(y, s)
    return -np.real(z * z)


def shq(y: float) -> float:
    """`Shq(y) = ghat(2y)^2 - A^2` (the prover's normalisation)."""
    return float(np.real(ghat(-2j * float(y)))) ** 2 - A_SQ


def c2(w):
    """`c2(w) = int g(u) g(u+w) du`, supported on `|w| <= 1`."""
    a = np.abs(np.asarray(w, dtype=float))
    val = 0.5 * (1.0 - a) * np.cos(SQRT2 * a) + np.sin(SQRT2 * (1.0 - a)) / (2.0 * SQRT2)
    return np.where(a >= 1.0, 0.0, val)


# ---------------------------------------------------------------------------
# 2.  Two independent evaluators for the energy
# ---------------------------------------------------------------------------

def energy_quad(G: Callable[[np.ndarray], np.ndarray], order: int = 400) -> float:
    """`Eng(G) = (1/A^2) int_{-1}^{1} c2(w) |G(w)|^2 dw` by Gauss-Legendre.

    `c2` has a corner at `w = 0`, so the two halves are integrated separately.
    This is the *definition* route: it never touches the closed forms, and is
    what the gap identity is checked against.
    """
    nodes, weights = np.polynomial.legendre.leggauss(order)
    total = 0.0
    for lo, hi in ((-1.0, 0.0), (0.0, 1.0)):
        mid, half = 0.5 * (lo + hi), 0.5 * (hi - lo)
        w = mid + half * nodes
        total += half * float(np.sum(weights * c2(w) * np.abs(G(w)) ** 2))
    return total / A_SQ


def _F_of(x: Sequence[float]) -> Callable[[np.ndarray], np.ndarray]:
    xs = np.asarray(x, dtype=float)

    def F(w: np.ndarray) -> np.ndarray:
        return np.exp(1j * np.outer(xs, w)).sum(axis=0) if xs.size else np.zeros_like(w, dtype=complex)

    return F


def _P_of(y: float, t: float) -> Callable[[np.ndarray], np.ndarray]:
    def P(w: np.ndarray) -> np.ndarray:
        return 2.0 * np.cosh(y * w) * np.exp(1j * t * w)

    return P


def energy_F(x: Sequence[float]) -> float:
    """`Eng(F) = (1/A^2) sum_{j,k} phiR(x_j - x_k)^2` (`EForm3.energy_F`)."""
    xs = np.asarray(x, dtype=float)
    if xs.size == 0:
        return 0.0
    M = phi_R(xs[:, None] - xs[None, :]) ** 2
    return float(M.sum()) / A_SQ


def energy_FP(x: Sequence[float], y: float, t: float) -> float:
    """`Eng(F+P)` from `EForm3.energy_FP`'s closed form."""
    xs = np.asarray(x, dtype=float)
    cross = float(np.sum(qre(y, xs - t) ** 2 - qim(y, xs - t) ** 2)) if xs.size else 0.0
    diag = 2.0 * A_SQ + 2.0 * float(np.real(ghat(-2j * y))) ** 2
    return (A_SQ * energy_F(xs) + 4.0 * cross + diag) / A_SQ


def gap_identity_residual(x: Sequence[float], y: float, t: float,
                          order: int = 400) -> dict:
    """Control (a): the gap identity against the definition-route quadrature.

    Returns the three residuals `|closed - quadrature|` for `Eng(F)`,
    `Eng(F+P)`, and the identity `retention_gap` itself.
    """
    F = _F_of(x)
    P = _P_of(y, t)
    eF_q = energy_quad(F, order)
    eFP_q = energy_quad(lambda w: F(w) + P(w), order)
    eF_c = energy_F(x)
    eFP_c = energy_FP(x, y, t)
    xs = np.asarray(x, dtype=float)
    cross = float(np.sum(qre(y, xs - t) ** 2 - qim(y, xs - t) ** 2)) if xs.size else 0.0
    gap_rhs = eF_c + 4.0 + (4.0 * cross + 2.0 * shq(y)) / A_SQ
    return {
        "energy_F_residual": abs(eF_c - eF_q),
        "energy_FP_residual": abs(eFP_c - eFP_q),
        "gap_identity_residual": abs(eFP_c - gap_rhs),
        "gap_identity_vs_quadrature": abs(eFP_q - gap_rhs),
    }


# ---------------------------------------------------------------------------
# 3.  The trade quantities
# ---------------------------------------------------------------------------

def repulsion_raw(x: Sequence[float]) -> float:
    """`Rraw = sum_{j != k} phiR(x_j - x_k)^2 = A^2 (Eng(F) - n) >= 0`."""
    xs = np.asarray(x, dtype=float)
    if xs.size < 2:
        return 0.0
    M = phi_R(xs[:, None] - xs[None, :]) ** 2
    return float(M.sum() - np.trace(M))


def repulsion_R(x: Sequence[float]) -> float:
    """`R = Rraw / A^2 = Eng(F) - n`; two coincident points contribute 2."""
    return repulsion_raw(x) / A_SQ


def damage_total(x: Sequence[float], y: float, t: float = 0.0,
                 inflate: float = 1.0) -> float:
    """`sum_j damage(y, x_j - t)`.  `inflate` is the planted-fault knob."""
    xs = np.asarray(x, dtype=float)
    if xs.size == 0:
        return 0.0
    return inflate * float(np.sum(damage(y, xs - t)))


def budget(x: Sequence[float], y: float, theta: float = THETA_EFORM3) -> float:
    """The right-hand side of (RT): `Shq(y)/2 + ((1-theta)/4) * Rraw(x)`."""
    return shq(y) / 2.0 + relief_coefficient(theta) * repulsion_raw(x)


def trade_slack(x: Sequence[float], y: float, t: float = 0.0,
                theta: float = THETA_EFORM3, inflate: float = 1.0) -> float:
    """`budget - damage_total`.  (RT) is the statement that this is `>= 0`."""
    return budget(x, y, theta) - damage_total(x, y, t, inflate=inflate)


def retention_margin(x: Sequence[float], y: float, t: float = 0.0,
                     theta: float = THETA_EFORM3) -> float:
    """`E[F+P] - theta E[F] - (1-theta) n - 4`, from the closed forms.

    Equals `(4/A^2) * trade_slack`, which `test_repulsion_trade` pins.
    """
    xs = np.asarray(x, dtype=float)
    n = float(xs.size)
    return energy_FP(xs, y, t) - theta * energy_F(xs) - (1.0 - theta) * n - 4.0


def critical_c(x: Sequence[float], y: float, t: float = 0.0) -> float:
    """`(sum damage - Shq/2) / Rraw`: the smallest relief coefficient this
    configuration needs.  `-inf` when the configuration needs none and has no
    repulsion at all."""
    r = repulsion_raw(x)
    excess = damage_total(x, y, t) - shq(y) / 2.0
    if r <= 0.0:
        return -math.inf if excess <= 0.0 else math.inf
    return excess / r


# ---------------------------------------------------------------------------
# 4.  The geometry: where damage lives and how far apart it can sit
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DamageWindow:
    """One connected component of `{s > 0 : damage(y,s) > 0}`."""
    lo: float
    hi: float
    peak_s: float
    peak: float

    @property
    def width(self) -> float:
        return self.hi - self.lo


def damage_windows(y: float, s_max: float = 400.0, step: float = 2e-4,
                   refine: bool = True) -> list[DamageWindow]:
    """The positive-`s` damage windows out to `s_max`, one per zero of `ghat`."""
    ss = np.arange(0.0, s_max, step)
    vals = damage(y, ss)
    idx = np.flatnonzero(vals > 0.0)
    if idx.size == 0:
        return []
    brk = np.flatnonzero(np.diff(idx) > 1)
    starts = np.concatenate(([idx[0]], idx[brk + 1]))
    ends = np.concatenate((idx[brk], [idx[-1]]))
    out: list[DamageWindow] = []
    for a, b in zip(starts, ends):
        seg = vals[a:b + 1]
        i = int(seg.argmax())
        peak_s, peak = float(ss[a + i]), float(seg.max())
        lo, hi = float(ss[a]) - step, float(ss[b]) + step
        if refine:
            peak_s, peak = _golden_max(lambda s: float(damage(y, s)),
                                       peak_s - step, peak_s + step)
            lo = _bisect_sign(lambda s: float(damage(y, s)), lo, float(ss[a]))
            hi = _bisect_sign(lambda s: float(damage(y, s)), float(ss[b]), hi)
        out.append(DamageWindow(lo, hi, peak_s, peak))
    return out


def _golden_max(f: Callable[[float], float], a: float, b: float,
                iters: int = 80) -> tuple[float, float]:
    inv = (math.sqrt(5.0) - 1.0) / 2.0
    c, d = b - inv * (b - a), a + inv * (b - a)
    for _ in range(iters):
        if f(c) > f(d):
            b, d = d, c
            c = b - inv * (b - a)
        else:
            a, c = c, d
            d = a + inv * (b - a)
    m = 0.5 * (a + b)
    return m, f(m)


def _bisect_sign(f: Callable[[float], float], a: float, b: float,
                 iters: int = 80) -> float:
    fa = f(a)
    for _ in range(iters):
        m = 0.5 * (a + b)
        if (f(m) > 0.0) == (fa > 0.0):
            a = m
        else:
            b = m
    return 0.5 * (a + b)


@dataclass(frozen=True)
class WindowGeometry:
    """The structural facts that make (RT) work, all measured."""
    y: float
    no_damage_radius: float
    max_window_width: float
    min_window_gap: float
    phi_floor: float            #: `phiR(max_window_width)^2`, the within-window floor
    peak_max: float
    peak_argmax: float
    peaks: tuple[float, ...]
    peak_positions: tuple[float, ...]
    tail_bound: float           #: majorant for the peaks beyond the scanned range
    shq_half: float

    @property
    def one_side_total(self) -> float:
        return sum(self.peaks) + self.tail_bound

    @property
    def separated_ratio(self) -> float:
        """`2 * (sum of all peaks) / (Shq/2)` -- the `d >= 4` worst case."""
        return 2.0 * self.one_side_total / self.shq_half


@lru_cache(maxsize=64)
def window_geometry(y: float, s_max: float = 400.0, step: float = 2e-4) -> WindowGeometry:
    """Cached: the scans call it with the same arguments many times over."""
    wins = damage_windows(y, s_max=s_max, step=step)
    if not wins:
        return WindowGeometry(y, math.inf, 0.0, math.inf, A_SQ, 0.0, 0.0, (), (),
                              0.0, shq(y) / 2.0)
    widths = [w.width for w in wins]
    gaps = [wins[i + 1].lo - wins[i].hi for i in range(len(wins) - 1)]
    peaks = [w.peak for w in wins]
    k = np.arange(1, len(peaks) + 1)
    # `p_k k^2` is measured decreasing; `sum_{k>K} p_k <= max(p_k k^2)/K`.
    tail = float(np.max(np.asarray(peaks) * k * k)) / len(peaks)
    imax = int(np.argmax(peaks))
    wmax = max(widths)
    return WindowGeometry(
        y=y,
        no_damage_radius=wins[0].lo,
        max_window_width=wmax,
        min_window_gap=min(gaps) if gaps else math.inf,
        phi_floor=float(phi_R(wmax)) ** 2,
        peak_max=peaks[imax],
        peak_argmax=wins[imax].peak_s,
        peaks=tuple(peaks),
        peak_positions=tuple(w.peak_s for w in wins),
        tail_bound=tail,
        shq_half=shq(y) / 2.0,
    )


# ---------------------------------------------------------------------------
# 5.  The marginal trade: does a cluster's damage grow faster than its Rraw?
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class MarginalTrade:
    y: float
    m: int
    gap: float
    s0: float
    extra_damage: float
    extra_relief: float

    @property
    def ratio(self) -> float:
        if self.extra_relief <= 0.0:
            return math.inf if self.extra_damage > 0.0 else 0.0
        return self.extra_damage / self.extra_relief


def marginal_trade(y: float, m: int, gap: float, s0: float,
                   theta: float = THETA_EFORM3) -> MarginalTrade:
    """A cluster `s0, s0+g, ..., s0+(m-1)g` against the single point `s0`.

    `extra_damage` is what the `m-1` added points cost; `extra_relief` is
    `(1-theta)/4` times the `Rraw` the cluster's own pairs supply.
    """
    ls = np.arange(1, m)
    extra_damage = float(np.sum(damage(y, s0 + ls * gap))) if m > 1 else 0.0
    extra_raw = 2.0 * float(np.sum((m - ls) * phi_R(ls * gap) ** 2)) if m > 1 else 0.0
    return MarginalTrade(y, m, gap, s0, extra_damage,
                         relief_coefficient(theta) * extra_raw)


def worst_marginal_ratio(y: float, m: int, gaps: np.ndarray | None = None,
                         s_max: float = 40.0, s_step: float = 0.005,
                         theta: float = THETA_EFORM3) -> MarginalTrade:
    """The worst `(extra damage)/(extra relief)` over gap and cluster position."""
    if gaps is None:
        gaps = np.arange(0.01, 4.0001, 0.01)
    s0 = np.arange(0.0, s_max, s_step)
    ls = np.arange(1, m)
    best: MarginalTrade | None = None
    for g in np.atleast_1d(gaps):
        raw = 2.0 * float(np.sum((m - ls) * phi_R(ls * g) ** 2)) if m > 1 else 0.0
        relief = relief_coefficient(theta) * raw
        if relief <= 0.0:
            continue
        ed = np.zeros_like(s0)
        for l in ls:
            ed = ed + damage(y, s0 + l * float(g))
        i = int(np.argmax(ed))
        cand = MarginalTrade(y, m, float(g), float(s0[i]), float(ed[i]), relief)
        if best is None or cand.ratio > best.ratio:
            best = cand
    assert best is not None
    return best


# ---------------------------------------------------------------------------
# 6.  The extremal search over configurations
# ---------------------------------------------------------------------------

@dataclass
class ExtremalConfig:
    """The worst configuration the search found, and its numbers."""
    y: float
    theta: float
    positions: tuple[float, ...]
    multiplicities: tuple[int, ...]     #: on the signed window peaks
    window_peaks: tuple[float, ...]     #: the signed peak positions
    damage_total: float
    tail_damage: float
    repulsion_raw: float
    shq_half: float
    critical_c: float
    relief_available: float
    slack: float
    margin_factor: float = field(init=False)

    def __post_init__(self) -> None:
        self.margin_factor = (self.relief_available / self.critical_c
                              if self.critical_c > 0.0 else math.inf)

    @property
    def theta_supported(self) -> float:
        """The largest `theta` this configuration leaves room for."""
        return 1.0 - 4.0 * self.critical_c

    @property
    def budget(self) -> float:
        return self.shq_half + self.relief_available * self.repulsion_raw

    @property
    def damage_over_budget(self) -> float:
        """(RT) holds on this configuration exactly when this is `<= 1`."""
        return self.damage_total / self.budget


def _multiplicity_objective(mults: np.ndarray, peaks: np.ndarray,
                            gram: np.ndarray, shq_half: float, tail: float,
                            objective: str, c: float) -> tuple[float, float, float]:
    """`(score, damage, Rraw)` for coincident clusters at the window peaks.

    `objective="ratio"` scores `critical_c` -- the smallest relief coefficient
    the configuration needs, i.e. the sharpest constant question.
    `objective="excess"` scores `damage - budget` at the given `c` -- i.e. how
    close the configuration comes to refuting (RT) as stated.
    """
    m = mults.astype(float)
    dam = float(m @ peaks) + tail
    raw = float(m @ gram @ m) - A_SQ * float(m.sum())
    if objective == "excess":
        return dam - shq_half - c * raw, dam, raw
    if raw <= 0.0:
        return (-math.inf if dam <= shq_half else math.inf), dam, raw
    return (dam - shq_half) / raw, dam, raw


def extremal_multiplicities(y: float, theta: float = THETA_EFORM3,
                            n_windows: int = 24, m_max: int = 24,
                            s_max: float = 400.0, step: float = 2e-4,
                            sweeps: int = 40,
                            objective: str = "ratio") -> ExtremalConfig:
    """Coordinate ascent on `critical_c` (or on the excess) over multiplicities.

    The search space is: `m_k` coincident points at the peak of the k-th damage
    window, independently on each side of `t`, for the first `n_windows`
    windows.  Every remaining window carries one point, and the peaks beyond
    the scanned range are charged as damage with **no** repulsion credit.
    Off-peak and spread-out placements are checked separately by
    `local_position_refinement`; both lower `critical_c`.
    """
    geo = window_geometry(y, s_max=s_max, step=step)
    if not geo.peaks:
        raise ValueError(f"no damage windows at y={y}")
    n_windows = min(n_windows, len(geo.peaks))
    pos = np.concatenate([np.asarray(geo.peak_positions), -np.asarray(geo.peak_positions)])
    peaks = np.concatenate([np.asarray(geo.peaks), np.asarray(geo.peaks)])
    gram = phi_R(pos[:, None] - pos[None, :]) ** 2
    free = np.concatenate([np.arange(n_windows), len(geo.peaks) + np.arange(n_windows)])

    avail = relief_coefficient(theta)
    tail = 2.0 * geo.tail_bound
    mults = np.ones(pos.size, dtype=int)
    best, dam, raw = _multiplicity_objective(mults, peaks, gram, geo.shq_half,
                                             tail, objective, avail)
    for _ in range(sweeps):
        improved = False
        for k in free:
            keep = int(mults[k])
            for cand in range(0, m_max + 1):
                if cand == keep:
                    continue
                mults[k] = cand
                sc, d, r = _multiplicity_objective(mults, peaks, gram, geo.shq_half,
                                                   tail, objective, avail)
                if sc > best + 1e-18:
                    best, dam, raw, keep = sc, d, r, cand
                    improved = True
            mults[k] = keep
        if not improved:
            break
    _, dam, raw = _multiplicity_objective(mults, peaks, gram, geo.shq_half,
                                          tail, objective, avail)
    positions = np.repeat(pos, mults)
    ccrit = (dam - geo.shq_half) / raw if raw > 0.0 else -math.inf
    return ExtremalConfig(
        y=y, theta=theta,
        positions=tuple(float(v) for v in positions),
        multiplicities=tuple(int(v) for v in mults[free]),
        window_peaks=tuple(float(v) for v in pos[free]),
        damage_total=dam, tail_damage=tail,
        repulsion_raw=raw, shq_half=geo.shq_half,
        critical_c=ccrit, relief_available=avail,
        slack=geo.shq_half + avail * raw - dam,
    )


def separable_worst_excess(y: float, theta: float = THETA_EFORM3,
                           gamma: float | None = None,
                           s_max: float = 400.0, step: float = 2e-4) -> dict:
    """The window-separable upper bound on the worst-case damage.

    Discards **all** cross-window repulsion, charges each within-cluster pair
    only `gamma` (default: the within-window floor `phiR(W)^2`, so it also
    covers clusters that are spread across a whole window rather than
    coincident), and takes the multiplicity that maximises each window
    independently.  The resulting number is an upper bound for the left-hand
    side of (RT) under those two reductions, and it is the shape a prover
    would carry.
    """
    geo = window_geometry(y, s_max=s_max, step=step)
    if gamma is None:
        gamma = geo.phi_floor
    c = relief_coefficient(theta)
    step_relief = 2.0 * c * gamma
    total = 0.0
    profile: list[int] = []
    for p in geo.peaks:
        m = 0
        while True:
            marginal = p - step_relief * m
            if marginal <= 0.0:
                break
            total += marginal
            m += 1
        profile.append(m)
    total += geo.tail_bound
    return {
        "y": y, "theta": theta, "gamma": gamma,
        "worst_one_side": total,
        "worst_both_sides": 2.0 * total,
        "shq_half": geo.shq_half,
        "slack": geo.shq_half - 2.0 * total,
        "margin_factor": geo.shq_half / (2.0 * total),
        "multiplicity_profile": tuple(profile[:8]),
        "step_relief": step_relief,
    }


def local_position_refinement(cfg: ExtremalConfig, trials: int = 200,
                              scale: float = 0.25, seed: int = 20260813) -> dict:
    """Control: perturb the extremal configuration's positions off the peaks.

    Coincident-at-the-peak is the search's ansatz; this checks it by random
    local moves on the raw positions, maximising `critical_c` directly.  The
    baseline is the ansatz's own positions with the tail charge dropped, so
    the two numbers are the same functional.
    """
    rng = np.random.default_rng(seed)
    x = np.asarray(cfg.positions, dtype=float)
    start = critical_c(x, cfg.y)
    best, best_x = start, x.copy()
    for _ in range(trials):
        cand = best_x + rng.normal(0.0, scale, size=best_x.size)
        c = critical_c(cand, cfg.y)
        if c > best:
            best, best_x = c, cand
    return {"start": start, "best": best,
            "improved": best > start + 1e-12,
            "gain": best - start,
            "max_shift": float(np.max(np.abs(best_x - x))) if x.size else 0.0}


def resolution_ladder(y: float = 0.5, theta: float = THETA_EFORM3,
                      rungs: Sequence[tuple[int, int, float, float]] | None = None
                      ) -> list[dict]:
    """`c_crit` up a four-knob refinement ladder (windows, multiplicity cap,
    scanned range, grid step).  MISSION.md's precision-response rule."""
    if rungs is None:
        rungs = ((6, 12, 100.0, 5e-4), (12, 16, 200.0, 5e-4),
                 (24, 24, 400.0, 2e-4), (32, 32, 600.0, 2e-4))
    out = []
    for nw, mm, smax, step in rungs:
        cfg = extremal_multiplicities(y, theta=theta, n_windows=nw, m_max=mm,
                                      s_max=smax, step=step)
        out.append({"n_windows": nw, "m_max": mm, "s_max": smax, "step": step,
                    "critical_c": cfg.critical_c, "margin_factor": cfg.margin_factor,
                    "profile": cfg.multiplicities[:6], "tail_damage": cfg.tail_damage,
                    "n_points": len(cfg.positions)})
    return out


def adversarial_search(y: float = 0.5, theta: float = THETA_EFORM3,
                       sizes: Sequence[int] = (2, 4, 8, 16, 32),
                       restarts: int = 6, steps: int = 2500,
                       seed: int = 20260813, s_max: float = 200.0,
                       step: float = 5e-4) -> dict:
    """Free-position annealing on `damage_total - budget`; `> 0` refutes (RT).

    No peak ansatz, no multiplicity ansatz: the positions are continuous and
    the moves include long jumps.  This is the control that would find a
    violation the structured search cannot see.
    """
    rng = np.random.default_rng(seed)
    geo = window_geometry(y, s_max=s_max, step=step)
    peaks = np.asarray(geo.peak_positions)
    B = geo.shq_half
    c = relief_coefficient(theta)

    def excess(x: np.ndarray) -> float:
        return damage_total(x, y, 0.0) - (B + c * repulsion_raw(x))

    best_e, best_x = -math.inf, np.zeros(0)
    per_size = {}
    for n in sizes:
        best_n = -math.inf
        for r in range(restarts):
            mode = r % 3
            if mode == 0:
                x = rng.uniform(-60.0, 60.0, size=n)
            elif mode == 1:
                x = rng.choice(peaks, size=n) * rng.choice([-1.0, 1.0], size=n)
                x = x + rng.normal(0.0, 0.05, size=n)
            else:
                x = np.full(n, peaks[0]) + rng.normal(0.0, 0.3, size=n)
            cur = excess(x)
            for it in range(steps):
                T = 0.6 * (1.0 - it / steps) + 1e-3
                j = int(rng.integers(0, n))
                cand = x.copy()
                u = rng.random()
                if u < 0.5:
                    cand[j] += rng.normal(0.0, 0.4 * T + 0.01)
                elif u < 0.8:
                    cand[j] = float(rng.choice(peaks) * rng.choice([-1.0, 1.0])
                                    + rng.normal(0.0, 0.05))
                else:
                    cand[j] = float(rng.uniform(-60.0, 60.0))
                e = excess(cand)
                if e > cur or rng.random() < math.exp(min(0.0, (e - cur) / (0.002 * T))):
                    x, cur = cand, e
                if cur > best_n:
                    best_n = cur
                    if cur > best_e:
                        best_e, best_x = cur, x.copy()
        per_size[n] = best_n
    return {"y": y, "theta": theta, "best_excess": best_e,
            "per_size": per_size, "violated": best_e > 0.0,
            "best_config": tuple(float(v) for v in np.sort(best_x))}


# ---------------------------------------------------------------------------
# 7.  Broad scans -- the sharpest statement tested on families
# ---------------------------------------------------------------------------

@dataclass
class ScanResult:
    """`worst_ratio = max damage_total/budget` is the scale-free verdict: (RT)
    holds on the family exactly when it is `<= 1`.  `worst_slack` is reported
    too but is not comparable across `y`, since both sides scale like `y^2`
    while `Rraw` does not."""
    name: str
    n_configs: int
    worst_ratio: float
    worst_slack: float
    worst_c: float
    worst_config: tuple[float, ...]
    worst_y: float
    worst_t: float
    violations: int

    @property
    def holds(self) -> bool:
        return self.violations == 0


def _record(name: str, cases, theta: float) -> ScanResult:
    worst_ratio = -math.inf
    worst_slack = math.inf
    worst_c = -math.inf
    worst_cfg: tuple[float, ...] = ()
    worst_y = worst_t = 0.0
    viol = 0
    n = 0
    for x, y, t in cases:
        n += 1
        b = budget(x, y, theta)
        d = damage_total(x, y, t)
        s = b - d
        c = critical_c(x, y, t)
        ratio = d / b if b > 0.0 else math.inf
        if ratio > worst_ratio:
            worst_ratio = ratio
            worst_slack = s
            worst_cfg, worst_y, worst_t = tuple(float(v) for v in x), y, t
        if c > worst_c:
            worst_c = c
        if s < 0.0:
            viol += 1
    return ScanResult(name, n, worst_ratio, worst_slack, worst_c, worst_cfg,
                      worst_y, worst_t, viol)


def lattice_scan(spacings: Sequence[float] | None = None,
                 sizes: Sequence[int] = (2, 3, 5, 8, 13, 21),
                 ys: Sequence[float] = (0.5, 0.4, 0.25, 0.1),
                 offsets: Sequence[float] = (0.0, 0.5, 1.0, 2.0, 3.25),
                 theta: float = THETA_EFORM3) -> ScanResult:
    """Uniform lattices at every spacing in 0.1 .. 8, centred every which way."""
    if spacings is None:
        spacings = np.round(np.arange(0.1, 8.0001, 0.05), 4)

    def cases():
        for sp in spacings:
            for n in sizes:
                x = np.arange(n) * float(sp)
                for y in ys:
                    for off in offsets:
                        # place the lattice so that its centre sits `off` from
                        # the first damage peak, and also at the peak itself
                        yield x, y, float(np.mean(x)) - 6.517 + off
                        yield x, y, float(x[0]) - 6.517 + off

    return _record("uniform lattices", cases(), theta)


def gap_profile(y: float = 0.5, gaps: Sequence[float] | None = None,
                sizes: Sequence[int] = (2, 3, 4, 5, 6),
                n_windows: int = 31, theta: float = THETA_EFORM3,
                s_max: float = 200.0, step: float = 5e-4) -> list[dict]:
    """The task's decisive scan: for each gap `g` in (0,4) and cluster size `m`,
    the extra damage the cluster costs, the extra relief its own repulsion
    buys, and the slack of the whole embedded configuration.

    The background is one point on every damage peak out to `n_windows`, both
    sides; consecutive background points are more than 5.18 apart, so the
    background alone is 4-separated and is the worst case EForm3 covers.  The
    cluster replaces the first-window point, at the peak.
    """
    if gaps is None:
        gaps = np.round(np.arange(0.02, 4.0001, 0.02), 4)
    geo = window_geometry(y, s_max=s_max, step=step)
    peaks = np.asarray(geo.peak_positions[:n_windows])
    background = np.concatenate([peaks[1:], -peaks])
    base_damage = damage_total(background, y, 0.0)
    base_raw = repulsion_raw(background)
    c = relief_coefficient(theta)
    rows = []
    for g in np.atleast_1d(gaps):
        for m in sizes:
            cluster = peaks[0] + np.arange(m) * float(g)
            x = np.concatenate([background, cluster])
            d, raw = damage_total(x, y, 0.0), repulsion_raw(x)
            extra_damage = d - base_damage
            extra_relief = c * (raw - base_raw)
            rows.append({
                "gap": float(g), "m": int(m),
                "extra_damage": extra_damage, "extra_relief": extra_relief,
                "marginal_ratio": (extra_damage / extra_relief
                                   if extra_relief > 0 else math.inf),
                "damage_total": d, "budget": geo.shq_half + c * raw,
                "slack": geo.shq_half + c * raw - d,
                "ratio": d / (geo.shq_half + c * raw),
            })
    return rows


def cluster_embedded_scan(y: float = 0.5, gaps: Sequence[float] | None = None,
                          sizes: Sequence[int] = (2, 3, 4, 5, 6),
                          n_windows: int = 31, theta: float = THETA_EFORM3,
                          s_max: float = 200.0, step: float = 5e-4) -> ScanResult:
    """The task's configuration family: a cluster at gap `g` in (0,4), embedded
    in an otherwise 4-separated background that maximises the base damage.

    The background is one point on every damage peak out to `n_windows`, both
    sides -- consecutive background points are >= 5.18 apart, so the background
    alone satisfies the EForm3 separation hypothesis.  The cluster replaces the
    first-window point.
    """
    if gaps is None:
        gaps = np.round(np.arange(0.02, 4.0001, 0.02), 4)
    geo = window_geometry(y, s_max=s_max, step=step)
    peaks = np.asarray(geo.peak_positions[:n_windows])
    background = np.concatenate([peaks[1:], -peaks])

    def cases():
        for g in gaps:
            for m in sizes:
                cluster = peaks[0] + np.arange(m) * float(g)
                yield np.concatenate([background, cluster]), y, 0.0

    return _record(f"clusters in (0,4) on a separated background (y={y})", cases(), theta)


def random_scan(n: int = 2000, ys: Sequence[float] = (0.5, 0.45, 0.3, 0.15),
                n_points: tuple[int, int] = (1, 30), spread: float = 60.0,
                theta: float = THETA_EFORM3, seed: int = 20260813,
                clustered_fraction: float = 0.5) -> ScanResult:
    """Randomised configurations: half uniform on `[-spread, spread]`, half
    built as clusters around the damage peaks (the adversarial shape)."""
    rng = np.random.default_rng(seed)
    geo = window_geometry(0.5, s_max=120.0, step=5e-4)
    peaks = np.asarray(geo.peak_positions)

    def cases():
        for i in range(n):
            y = float(rng.choice(ys))
            k = int(rng.integers(n_points[0], n_points[1] + 1))
            if rng.random() < clustered_fraction and peaks.size:
                base = rng.choice(peaks, size=k) * rng.choice([-1.0, 1.0], size=k)
                x = base + rng.normal(0.0, rng.choice([0.001, 0.05, 0.3, 1.0]), size=k)
            else:
                x = rng.uniform(-spread, spread, size=k)
            t = float(rng.uniform(-2.0, 2.0)) if rng.random() < 0.5 else 0.0
            yield x, y, t

    return _record("randomised configurations", cases(), theta)


def eform3_crosscheck(y: float = 0.5, s_max: float = 400.0,
                      step: float = 2e-4) -> dict:
    """Against the two arms this measurement has to agree with.

    * `EForm3/Estimates.lean`: `Shq_half_lower` gives `Shq y / 2 >= 187/1440 y^2`
      and `Counting.separated_damage` gives `sum damage <= 1228/10000 y^2` for
      4-separated configurations.  Both are conservative statements about the
      same quantities this module measures.
    * `FAR-FIELD-EXCHANGE.md` §3: peak damage `4.39642e-03` at `s = 6.51700`,
      no-damage radius `6.0653187731`, `sum of all peaks = 6.8591e-03` per
      side, budget `Shq/2 = 3.3754e-02`, both sides at 40.6% of it.
    """
    geo = window_geometry(y, s_max=s_max, step=step)
    lean_shq_floor = (187.0 / 1440.0) * y * y
    lean_damage_cap = (1228.0 / 10000.0) * y * y
    both_sides = 2.0 * geo.one_side_total
    return {
        "y": y,
        "shq_half": geo.shq_half,
        "lean_shq_half_lower": lean_shq_floor,
        "shq_half_respects_lean_floor": geo.shq_half >= lean_shq_floor,
        "separated_damage_measured": both_sides,
        "lean_separated_damage_cap": lean_damage_cap,
        "separated_respects_lean_cap": both_sides <= lean_damage_cap,
        "lean_margin": lean_shq_floor / lean_damage_cap,
        "measured_margin": geo.shq_half / both_sides,
        "far_field_peak": geo.peak_max,
        "far_field_peak_s": geo.peak_argmax,
        "far_field_R0": geo.no_damage_radius,
        "far_field_one_side_total": geo.one_side_total,
        "far_field_budget_fraction": both_sides / geo.shq_half,
    }


def theta_one_counterexample(y: float = 0.5, s_max: float = 60.0,
                             step: float = 2e-4) -> dict:
    """The smallest coincident cluster that breaks (RT) at `theta = 1`.

    At `theta = 1` the relief coefficient is 0, so (RT) reduces to EForm3's
    `sum_j damage <= Shq/2` with no separation hypothesis -- and that is false.
    """
    geo = window_geometry(y, s_max=s_max, step=step)
    peak, s = geo.peak_max, geo.peak_argmax
    m = 1
    while m * peak <= geo.shq_half:
        m += 1
        if m > 10_000:
            raise RuntimeError("no counterexample found")
    x = [s] * m
    return {
        "y": y, "m": m, "s": s, "peak": peak,
        "damage_total": m * peak,
        "shq_half": geo.shq_half,
        "theta_one_slack": trade_slack(x, y, 0.0, theta=1.0),
        "theta_eform3_slack": trade_slack(x, y, 0.0, theta=THETA_EFORM3),
        "repulsion_raw": repulsion_raw(x),
        "retention_margin_theta_one": retention_margin(x, y, 0.0, theta=1.0),
        "retention_margin_theta_eform3": retention_margin(x, y, 0.0, theta=THETA_EFORM3),
    }


# ---------------------------------------------------------------------------
# 8.  The statement, and what is still missing
# ---------------------------------------------------------------------------

SHARPEST_STATEMENT = """\
(RT)  For every n in N, every x : N -> R, every t in R and every y in [0, 1/2],

        sum_{j<n} ( Qim(y, x_j - t)^2 - Qre(y, x_j - t)^2 )
              <=  Shq(y) / 2  +  (1/800) * sum_{j != k} Qre(0, x_j - x_k)^2 .

Via Retention.retention_gap this is equivalent to the retention inequality

        (199/200) * Eng(F) + n/200 + 4  <=  Eng(F + P)

with NO separation hypothesis; it strictly contains
Retention.retention_of_damage (drop the last term) and therefore
Retention.retention_separated_of_le.

Two margins, measured at y = 1/2 and both reported because they answer
different questions:

  * as an inequality, the worst configuration found reaches
    `sum damage - Rraw/800 = 1.8221e-02` against `Shq/2 = 3.3754e-02`
    -- a factor 1.85 -- and the window-separable majorant below caps that
    quantity at 1.9617e-02, a factor 1.72;
  * as a constant, the coefficient 1/800 = 1.25e-03 can be lowered to
    c_crit = 4.7496e-04 before some configuration needs it, i.e. a factor
    2.63, which corresponds to theta = 0.998100 rather than 0.995.

Supporting structural statements, each measured here and each a separate
proof obligation:

 (S1)  damage(y, s) > 0  =>  |s| >= R0(y), with R0(1/2) = 6.0653187.
 (S2)  {s > 0 : damage(y,s) > 0} is a disjoint union of windows of width
       <= W(y), one around each positive zero of ghat; W(1/2) = 0.98600.
       (damage(y,s) = -Re(ghat(s - i y)^2), and near a simple real zero s0 of
       ghat that is -|ghat'|^2 ((s-s0)^2 - y^2) + O(.), so the half-width is
       ~ y and the window is centred on the zero.)
 (S3)  consecutive windows are separated by >= D(y) - W(y), where D(y) is the
       minimum spacing of consecutive zeros of ghat.  ghat's zeros are
       6.64308, 12.75529, 18.97675, ... rising to spacing 2*pi from below, so
       D = 6.11221 and the measured minimum window gap at y = 1/2 is 5.18297.
 (S4)  phiR is decreasing on [0, 2*pi], so any two points inside one window
       carry phiR(gap)^2 >= phiR(W(y))^2; at y = 1/2 that floor is 0.782375
       against phiR(0)^2 = A^2 = 0.844056.
 (S5)  the k-th window peak p_k satisfies p_k * k^2 <= p_1 = 4.396424e-03
       (measured decreasing in k), so sum_k p_k <= 6.8591e-03 at y = 1/2.

Given (S1)-(S5), (RT) follows from the window-separable count in
separable_worst_excess: every cross-window pair is discarded, each window is
maximised independently, damage in a window of multiplicity m is at most
m*p_k while the within-window repulsion is at least m(m-1)*phiR(W)^2, and the
sum of the per-window maxima over both sides is 1.9617e-02 against
Shq(1/2)/2 = 3.3754e-02.  The maximiser is multiplicity 3 on the first window
each side and 1 everywhere else.
"""

NAMED_GAPS = (
    "(S1)-(S5) are measured on a float grid at the stated step, not proved; "
    "each is a real-analysis statement about ghat that a prover must supply.",
    "the extremal search is a search: coordinate ascent over cluster "
    "multiplicities at the window peaks plus random position refinement. It "
    "reports the worst configuration found, not a bound over all of them. The "
    "separable bound in separable_worst_excess is the part that does not "
    "depend on the search having found the maximum.",
    "the peak tail beyond the scanned range is charged by the measured "
    "majorant max_k(p_k k^2)/K, which is itself a measured monotonicity, not "
    "a derived rate.",
    "(RT) is one quantifier of the paper's argument. Nothing here says the "
    "other quantifiers close, and nothing here is evidence for or against RH.",
)

#: numbers this module pins; the tests read them.
PINNED = {
    # the E-form's constants, against `FAR-FIELD-EXCHANGE.md` §5
    "A": 0.9187253698655684,
    "A_sq": 0.8440563052346255,
    "ghat_1": 0.9547589816782313,
    "shq_half_at_half": 0.03375420393031381,
    # the damage geometry, against `FAR-FIELD-EXCHANGE.md` §3
    "peak_damage": 0.004396424117822008,
    "peak_argmax": 6.517,
    "no_damage_radius": 6.0653187731,
    "max_window_width": 0.98600,
    "min_window_gap": 5.18297,
    "min_peak_spacing": 6.1813,
    "phi_floor": 0.782375,
    "one_side_peak_sum": 6.8591e-3,
    "separated_ratio": 0.4064,
    # the marginal trade
    "worst_marginal_ratio_pair": 8.6981,
    "marginal_coincident_numerator": 4.1670,   # ratio = 4.1670/m for a cluster of m
    "coincident_pair_R": 2.0,
    # the global trade: the sharpest coefficient
    "critical_c": 4.7496e-4,
    "relief_available": 1.25e-3,
    "coefficient_margin": 2.6318,
    "theta_supported": 0.998100,
    "extremal_profile": (6, 2, 1, 1, 1, 1),
    # the global trade: how close (RT) comes to failing at 1/800
    "worst_reduced_damage": 1.8221e-2,         # max of `damage - Rraw/800` found
    "separable_upper_bound": 1.9617e-2,        # the window-separable majorant
    "inequality_margin": 1.7207,               # Shq/2 divided by that majorant
    "worst_damage_over_budget": 0.6687,
    # theta = 1
    "theta_one_cluster": 8,
}


def report() -> None:  # pragma: no cover - operator console
    """Print everything this module measures."""
    print("=" * 78)
    print("THE REPULSION TRADE -- measurement report")
    print("=" * 78)
    print(f"A = {A_CONST:.13f}   A^2 = {A_SQ:.13f}   ghat(1) = {float(np.real(ghat(-1j))):.13f}")
    print()

    print("-- 1. geometry of the damage set ------------------------------------")
    print(f"{'y':>5} {'R0':>10} {'W_max':>9} {'gap_min':>9} {'phiR(W)^2':>10} "
          f"{'sum p_k':>11} {'Shq/2':>11} {'2*sum/Shq/2':>11}")
    for y in (0.5, 0.4, 0.3, 0.2, 0.1, 0.05):
        g = window_geometry(y)
        print(f"{y:5.2f} {g.no_damage_radius:10.5f} {g.max_window_width:9.5f} "
              f"{g.min_window_gap:9.5f} {g.phi_floor:10.6f} {g.one_side_total:11.4e} "
              f"{g.shq_half:11.4e} {g.separated_ratio:11.4f}")
    print()

    print("-- 2. the marginal trade (extra damage)/(extra relief) --------------")
    for y in (0.5, 0.3, 0.1):
        for m in (2, 3, 4, 5, 6):
            w = worst_marginal_ratio(y, m)
            print(f" y={y:.2f} m={m}: worst ratio {w.ratio:9.4f} at g={w.gap:.2f} "
                  f"s0={w.s0:.3f}  (extra damage {w.extra_damage:.4e}, "
                  f"relief {w.extra_relief:.4e})")
    wide = worst_marginal_ratio(0.5, 2, gaps=np.arange(4.0, 6.6401, 0.02))
    print(f" and past the scanned interval the marginal framing diverges: "
          f"pair ratio {wide.ratio:.4f} at g={wide.gap:.2f}, phiR zero at 6.64308")
    print()

    print("-- 3a. the sharpest coefficient (objective: max critical_c) ----------")
    for y in (0.5, 0.4, 0.3, 0.2, 0.1):
        cfg = extremal_multiplicities(y)
        print(f" y={y:.2f}: c_crit={cfg.critical_c:.6e}  available={cfg.relief_available:.4e} "
              f" margin={cfg.margin_factor:.4f}x  theta_max={cfg.theta_supported:.6f}  "
              f"profile={cfg.multiplicities[:6]}")
    print()
    print(" resolution ladder at y=1/2:")
    for row in resolution_ladder(0.5):
        print(f"   windows={row['n_windows']:3d} m_max={row['m_max']:3d} "
              f"s_max={row['s_max']:6.0f} step={row['step']:g}: "
              f"c_crit={row['critical_c']:.6e} margin={row['margin_factor']:.4f}x "
              f"profile={row['profile']}")
    print()

    print("-- 3b. how close (RT) comes to failing at 1/800 (objective: excess) --")
    for y in (0.5, 0.3, 0.1):
        cfg = extremal_multiplicities(y, objective="excess")
        print(f" y={y:.2f}: damage={cfg.damage_total:.6e} budget={cfg.budget:.6e} "
              f"ratio={cfg.damage_over_budget:.6f} slack={cfg.slack:.6e} "
              f"profile={cfg.multiplicities[:6]}")
    print()
    sep = separable_worst_excess(0.5)
    print(f" separable bound at y=1/2, gamma={sep['gamma']:.6f}: "
          f"worst={sep['worst_both_sides']:.6e} vs Shq/2={sep['shq_half']:.6e} "
          f"-> margin {sep['margin_factor']:.4f}x, profile {sep['multiplicity_profile']}")
    sepA = separable_worst_excess(0.5, gamma=A_SQ)
    print(f" separable bound, gamma=A^2:            "
          f"worst={sepA['worst_both_sides']:.6e} -> margin {sepA['margin_factor']:.4f}x, "
          f"profile {sepA['multiplicity_profile']}")
    print()
    adv = adversarial_search(0.5)
    print(f" free-position annealing: best excess = {adv['best_excess']:+.6e} "
          f"(violation iff > 0); per size {adv['per_size']}")
    print()

    print("-- 3c. the gap profile in (0,4), cluster on a separated background ---")
    rows = gap_profile(0.5, gaps=np.arange(0.05, 4.0001, 0.05))
    for m in (2, 3, 4, 5, 6):
        sub = [r for r in rows if r["m"] == m]
        worst_ratio = max(sub, key=lambda r: r["ratio"])
        worst_marg = max(sub, key=lambda r: r["marginal_ratio"])
        print(f" m={m}: worst damage/budget {worst_ratio['ratio']:.6f} at g={worst_ratio['gap']:.2f}"
              f"   worst marginal ratio {worst_marg['marginal_ratio']:8.4f} at g={worst_marg['gap']:.2f}")
    print()

    print("-- 3d. cross-check against the two existing instruments ---------------")
    cc = eform3_crosscheck(0.5)
    print(f" Shq/2 = {cc['shq_half']:.6e} vs Lean floor 187/1440 y^2 = "
          f"{cc['lean_shq_half_lower']:.6e} -> {cc['shq_half_respects_lean_floor']}")
    print(f" separated damage = {cc['separated_damage_measured']:.6e} vs Lean cap "
          f"1228/10000 y^2 = {cc['lean_separated_damage_cap']:.6e} -> "
          f"{cc['separated_respects_lean_cap']}")
    print(f" Lean margin {cc['lean_margin']:.4f}x, measured margin "
          f"{cc['measured_margin']:.4f}x, budget fraction "
          f"{cc['far_field_budget_fraction']:.4f} (FAR-FIELD-EXCHANGE: 0.406)")
    print()

    print("-- 4. theta = 1 ------------------------------------------------------")
    tc = theta_one_counterexample()
    print(f" {tc['m']} coincident points at s={tc['s']:.5f}: damage={tc['damage_total']:.6e} "
          f"> Shq/2={tc['shq_half']:.6e}")
    print(f"   theta=1   slack={tc['theta_one_slack']:.6e}   "
          f"retention margin={tc['retention_margin_theta_one']:.6e}")
    print(f"   theta=.995 slack={tc['theta_eform3_slack']:.6e}   "
          f"retention margin={tc['retention_margin_theta_eform3']:.6e}")
    print()

    print("-- 5. scans ----------------------------------------------------------")
    for res in (lattice_scan(), cluster_embedded_scan(), random_scan()):
        print(f" {res.name}: {res.n_configs} configs, violations={res.violations}, "
              f"worst slack={res.worst_slack:.6e}, worst c={res.worst_c:.4e}")
    print()
    print(SHARPEST_STATEMENT)
    print("NAMED GAPS")
    for g in NAMED_GAPS:
        print("  - " + g)


if __name__ == "__main__":  # pragma: no cover
    report()
