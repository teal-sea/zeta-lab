"""The finite-to-infinite budget bridge, as a TWO-SIDED estimate.

`cluster_universal.py` closed the periodic family: the infinite lattice
`{(j s, y)}` has an exact per-pair budget (Poisson, closed form,
:func:`cluster_universal.b_infty`) and a measured per-pair cap, with

    sup rho = cap/b_inf = 0.9286   over s in [0.3, 20] mean gaps,
                                   y in (0, 1/2],

i.e. the infinite lattice closes with >= 7.1% relative room.  What it did
NOT deliver is the transfer of that verdict to a finite cluster of m
pairs, and it recorded WHY: the finite-size correction has **no uniform
sign** (per-pair margins at m = 4 / m = 32 straddle the limit at the
resonance).  So there is no one-sided comparison lemma to look for.  The
tractable statement is a two-sided estimate

    |b_m(s, y) - b_inf(s, y)|  <=  E(m, s, y),

and this module derives one, measures how tight it is, and reports what
it does and does not buy.

**Why it is elementary.**  The kernel `c2 = autocorr` (the
autocorrelation of the window `g(u) = cos(sqrt2 u) 1_{|u| <= 1/2}`) is
supported in `[-1, 1]`, so the dual sum in `b_inf` runs over the finitely
many Bragg frequencies `|2 pi k / s| < 1`.  Nothing diverges on the
infinite side; the whole finite-vs-infinite question is the bookkeeping
of pair interactions that a finite cluster is MISSING at its two ends.

**1. Both sides in one line.**  The budget of a pair set P is exactly
(`paper_joint.PaperJoint.budget`, `joint_universal.budget_terms`)

    budget(P) = sum_r slack(y_r) + sum_{i != j} T(t_i - t_j, y_i, y_j).

For the finite lattice `P_m = {(j s, y) : 0 <= j < m}` the double sum
depends only on the difference `d = |i - j|`, which occurs `m - d` times:

    b_m(s, y) := budget(P_m)/m
               = slack(y) + (2/m) sum_{d=1}^{m-1} (m - d) T(d s, y, y),
    b_inf(s, y) = slack(y) + 2 sum_{d=1}^{inf} T(d s, y, y)

(the second is `b_perpair_direct`; `b_infty` is its Poisson closed form).
Subtracting is the whole derivation:

    b_m - b_inf = -(2/m) sum_{d=1}^{m-1} d T(d s, y, y)
                  - 2 sum_{d >= m} T(d s, y, y).                    (*)

Read (*) as the audit's boundary story made arithmetic: the pair at
lattice site j is missing its neighbours at distance > j on one side and
> m-1-j on the other; summing the misses over j is exactly the weight `d`
on `T(d s)`, i.e. an O(1)-per-end-pair effect divided by m.

**2. The estimate.**  `cluster_universal.t_decay_constant` already
derived |T(dt, y1, y2)| <= C_T / dt^2 uniformly over depths in (0, 1/2]
by two integrations by parts (the corner of c2 at 0 and the edge at 1
supply the boundary terms), with **C_T = 27.4970** — closed-form except
for one quadrature, re-checked here (:func:`c_t_reuse_check`).  Feeding
it into (*) with the two elementary bounds

    sum_{d=1}^{m-1} 1/d = H_{m-1},
    sum_{d >= m} 1/d^2 <= sum_{d >= m} 1/((d-1/2)(d+1/2)) = 1/(m-1/2)
                          (telescoping; no zeta value needed)

gives the fully symbolic

    E_crude(m, s) = (2 C_T / s^2) [ H_{m-1}/m + 1/(m - 1/2) ].

It is DEPTH-FREE (C_T is uniform in y), decays like log m / m, and is
valid for every s > 0 and every y in (0, 1/2].

The `log m` is not slack in the bookkeeping — it is real, and it is the
audit's one correction.  The double integration by parts gives

    T(dt) ~ -(8 / (A^2 dt^2)) [ h'(0+) - h'(1-) cos(dt) ],
    h(w) = c2(w) cosh(y w)^2,

so `d T(d s)` carries a NON-oscillating `1/d` piece from `h'(0+)`
(the corner of c2 at the origin, which is the window's jump
autocorrelated against itself).  Its partial sums grow like `log m`.
Hence :func:`leading_coefficient`: writing L for the bracket,

    b_m - b_inf  ~  (16 / (A^2 s^2 m)) * L * log m,
    L = c2'(0+)                    generically  (negative),
    L = c2'(0+) - c2'(1-) cosh(y)^2  when s in 2 pi Z  (positive),

because at commensurate spacing `cos(d s) = 1` for every d and the
second term stops averaging away.  **That sign flip is the mechanism
behind the crossing that killed the one-sided lemma**: at the resonances
the finite cluster's budget sits ABOVE the limit, off resonance BELOW.
Measured against (*), the fitted `log m / m` coefficient agrees with the
derived L to a few percent at every probe (:func:`rate_record`).

**3. A sharpened variant.**  `E_crude` throws away everything about the
first few interactions, where `C_T/dt^2` is loosest.  Since T is
elementary (`paper_chain.PaperChain.T`, a closed-form combination of the
window transform), one may keep the first D terms exactly:

    E_hybrid(m, s, y; D) = (2/m) sum_{d<=min(m-1,D)} d |T(d s, y, y)|
                         + (2 C_T/(m s^2)) (H_{m-1} - H_{min(m-1,D)})
                         + [exact tail head to D] + 2 C_T/(s^2 (D+1/2))
                                                     or 2 C_T/(s^2 (m-1/2)).

Every constant is closed form except the one quadrature inside C_T.
D = 8 by default: it is a choice of statement, not a fit — the estimate
holds for every D.

**4. What the bridge buys, and where it does not.**  With
`sup rho = 0.9286` the finite cluster inherits the infinite verdict once
`E <= (1 - rho) b_inf`.  The resulting `m0` is single-digit over most of
the range but NOT uniformly:

    s = 5, 10, 20 gaps:  m0 = 2 (nothing to check)
    s = 1.5, 3 gaps:     m0 = 2-4 (pointwise rho = 0)
    s = 2.0 gaps:        m0 = 78  (the resonance: rho = 0.88, little room)
    s = 1.0 gaps:        m0 = 260 (the budget FLOOR b_inf = 0.0245)

so the periodic-family bridge is **not** closed by this estimate alone;
it is closed outside two thin regions, and inside them the finite cases
are only checked at a ladder of m (:func:`small_m_ladder`), not at every
m < m0.  Three named gaps, all stated rather than papered over:

  (G1) the estimate bounds the BUDGET side only, and the cap side is
       measured to go the WRONG way.  At matched grid step the finite
       per-pair cap does not sit below the periodic-limit cap: at
       s = 2 gaps it RISES with m (0.1127 / 0.1156 / 0.1184 / 0.1205 at
       m = 4/8/16/32), and at s = 1 gap, where the periodic instrument
       reports total shielding (cap = 0), the finite per-pair cap falls
       only slowly (0.0651 / 0.0488 / 0.0384 / 0.0325 / 0.0293 at
       m = 4..64) and shows no sign of reaching 0.  The periodic cap is
       one period of an exactly periodic field with cross-cell charges
       dropped; the finite cap is a different instrument, and nothing
       here shows the second converges to the first.  A verdict transfer
       therefore does NOT follow from the budget bridge alone.
  (G2) the m < m0 cases are checked on a ladder of m values, not
       exhaustively.
  (G3) grid resolution is load-bearing on the cap side, so the two caps
       must be read at one step: at the argmax (s = 2.002 gaps,
       y = 0.4999) cap_inf is 0.125799 / 0.124008 / 0.120620 at step
       0.005 / 0.004 / 0.002 against b_inf = 0.129891, i.e. rho =
       0.9685 / 0.9547 / 0.9286.  The recorded sup rho = 0.9286 is a
       step-0.002 number.

       What (G1) and (G3) cost together is visible at that argmax: the
       finite ladder (coarse instrument) has per-pair margins
       +0.02890 / +0.01752 / +0.00760 / +0.00037 / -0.00264 / -0.00685
       at m = 2 / 4 / 8 / 16 / 24 / 64 — it goes NEGATIVE from m = 24.
       The budget side is not the cause: b_m falls 0.150154 -> 0.130079
       toward b_inf = 0.129891 exactly as the estimate says.  The cause
       is the cap side, whose finite per-pair value RISES past the
       limit instrument's (0.124864 at m = 4 to 0.136926 at m = 64,
       against cap_inf = 0.125799 at the same step).

Nothing here computes a proportion and nothing here is evidence about
RH.  Run
``.venv/bin/python hunts/frontier_math/truncation_bridge.py`` (~2 min;
``--quick`` skips the cap-side probe).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from paper_chain import A, MEAN_GAP, PaperChain, phipap  # noqa: E402
from paper_joint import PaperJoint  # noqa: E402
from joint_universal import THETA_FULL  # noqa: E402
from cluster_universal import (  # noqa: E402
    C2_EDGE_SLOPE, RHO_SUP_RECORD, b_infty, periodic_cap, t_decay_constant,
    t_decay_check,
)

#: the supremum of cap/budget over the periodic family, from
#: `cluster_universal.RHO_SUP_RECORD` — the room the bridge must fit in.
RHO_SUP = RHO_SUP_RECORD["rho"]

#: default split point of the sharpened estimate: the first D interaction
#: distances are kept exactly.  A choice of statement (the estimate holds
#: for every D >= 0), not a fitted parameter.
D_SPLIT = 8

_PC = PaperChain()


# ---------------------------------------------------------------------------
# 1. both sides of the bridge, exactly
# ---------------------------------------------------------------------------


def pair_term(dt, y: float):
    """``T(dt, y, y)`` vectorised: ``W(dt, 0) + W(dt, 2y)``.

    Identical to :meth:`paper_chain.PaperChain.T` at equal depths (pinned
    in the tests); vectorised because the ladders need thousands of it.
    """
    dt = np.asarray(dt, float)
    v1 = phipap(dt + 0j)
    v2 = phipap(dt + 2j * y)
    return 2 * ((v1.real**2 - v1.imag**2) + (v2.real**2 - v2.imag**2)) / A**2


def b_finite(m: int, s: float, y: float) -> float:
    """``b_m(s, y)`` — the exact per-pair budget of ``{(j s, y)}_{j<m}``.

    ``slack(y) + (2/m) sum_{d=1}^{m-1} (m-d) T(d s, y, y)``: the O(m^2)
    double sum of :meth:`paper_joint.PaperJoint.budget` collapsed by
    translation invariance to O(m) terms.  Exact, no quadrature.
    """
    if m < 1:
        raise ValueError("m >= 1")
    if m == 1:
        return _PC.slack(y)
    d = np.arange(1, m)
    return _PC.slack(y) + (2.0 / m) * float(((m - d) * pair_term(d * s, y)).sum())


def b_finite_via_instrument(m: int, s: float, y: float) -> float:
    """The same number through `PaperJoint.budget` — the O(m^2) route,
    kept as the cross-check that the collapse above is the same object."""
    pj = PaperJoint(step=0.005, G=60.0)
    return pj.budget([(j * s, y) for j in range(m)]) / m


def b_limit(s: float, y: float) -> float:
    """``b_inf(s, y)``: the Poisson closed form, re-exported from
    `cluster_universal.b_infty` (finite Bragg sum, `|2 pi k/s| < 1`)."""
    return b_infty(s, y)


def b_limit_direct(s: float, y: float, J: int = 20000) -> float:
    """``slack(y) + 2 sum_{d<=J} T(d s)`` — the sum the Poisson step
    replaces, kept so the two can be checked against each other."""
    d = np.arange(1, J + 1)
    return _PC.slack(y) + 2 * float(pair_term(d * s, y).sum())


def discrepancy(m: int, s: float, y: float) -> float:
    """``b_m - b_inf``, signed (the sign is the point: it flips)."""
    return b_finite(m, s, y) - b_limit(s, y)


def discrepancy_via_identity(m: int, s: float, y: float,
                             J: int = 20000) -> float:
    """The right-hand side of (*): ``-(2/m) sum_{d<m} d T(ds)
    - 2 sum_{d>=m} T(ds)``, summed to J.  Must reproduce
    :func:`discrepancy` to the truncation tail."""
    out = 0.0
    if m > 1:
        d = np.arange(1, m)
        out -= (2.0 / m) * float((d * pair_term(d * s, y)).sum())
    d = np.arange(m, J + 1)
    out -= 2 * float(pair_term(d * s, y).sum())
    return out


# ---------------------------------------------------------------------------
# 2. the derived estimate
# ---------------------------------------------------------------------------


def harmonic(n: int) -> float:
    """``H_n = sum_{k<=n} 1/k`` (exact partial sum, n small here)."""
    return float(sum(1.0 / k for k in range(1, n + 1)))


def inverse_square_tail_bound(m: int) -> float:
    """``sum_{d >= m} 1/d^2 <= 1/(m - 1/2)`` for m >= 1.

    Elementary and closed form: ``1/d^2 <= 1/((d-1/2)(d+1/2))
    = 1/(d-1/2) - 1/(d+1/2)``, which telescopes.  Used instead of
    trigamma so the statement carries no special function.
    """
    return 1.0 / (m - 0.5)


def E_crude(m: int, s: float, y: float | None = None) -> float:
    """``E_crude(m, s) = (2 C_T/s^2) [H_{m-1}/m + 1/(m-1/2)]``.

    Depth-free: `y` is accepted and ignored, because C_T is uniform over
    depths in (0, 1/2].  Every constant is closed form except the single
    quadrature inside C_T (:func:`cluster_universal.t_decay_constant`).
    """
    del y
    C_T = t_decay_constant()
    return (2 * C_T / s**2) * (harmonic(m - 1) / m + inverse_square_tail_bound(m))


def E_hybrid(m: int, s: float, y: float, D: int = D_SPLIT) -> float:
    """The sharpened estimate: first ``D`` interactions kept exactly.

    Bounds the two sums of (*) term by term, using the closed-form
    |T(d s, y, y)| while d <= D and C_T/(d s)^2 beyond.  Holds for every
    D >= 0 (D = 0 returns exactly :func:`E_crude` up to the tail split);
    D is a choice of statement, not a fitted parameter.
    """
    C_T = t_decay_constant()
    total = 0.0
    head = min(m - 1, D)
    if head >= 1:
        d = np.arange(1, head + 1)
        total += (2.0 / m) * float((d * np.abs(pair_term(d * s, y))).sum())
    if m - 1 > head:
        total += (2 * C_T / (m * s**2)) * (harmonic(m - 1) - harmonic(head))
    if m <= D:
        d = np.arange(m, D + 1)
        total += 2 * float(np.abs(pair_term(d * s, y)).sum())
        total += 2 * C_T / (s**2 * (D + 0.5))
    else:
        total += 2 * C_T * inverse_square_tail_bound(m) / s**2
    return total


def c_t_reuse_check(pinned: float = 27.4970, tol: float = 5e-4) -> dict:
    """Re-check of the constant this module borrows.

    Two things: that `t_decay_constant()` still returns the value
    `cluster_universal` reports, and that its own measurement
    (`t_decay_check`) still finds |T| dt^2 below it.
    """
    C_T = t_decay_constant()
    tc = t_decay_check()
    return {"C_T": C_T, "pinned": pinned, "matches_pinned": abs(C_T - pinned) < tol,
            "worst_quotient": tc["worst_quotient"], "holds": tc["holds"]}


# ---------------------------------------------------------------------------
# 3. the rate, and the structural story behind it
# ---------------------------------------------------------------------------


def is_resonant(s: float, tol: float = 1e-9) -> bool:
    """``s in 2 pi Z`` — commensurate spacing, where cos(d s) = 1 for all
    d and the edge term stops averaging away."""
    k = round(s / MEAN_GAP)
    return k >= 1 and abs(s - k * MEAN_GAP) < tol * max(1.0, s)


def leading_coefficient(s: float, y: float) -> dict:
    """The derived coefficient of ``log m / m`` in ``b_m - b_inf``.

    From ``T(dt) ~ -(8/(A^2 dt^2)) [h'(0+) - h'(1-) cos(dt)]`` with
    ``h = c2 cosh(y .)^2``, ``h'(0+) = c2'(0+) = -(1+cos sqrt2)/2`` and
    ``h'(1-) = c2'(1-) cosh(y)^2``:

        b_m - b_inf  ~  (16 L / (A^2 s^2)) * log m / m,
        L = h'(0+) - h'(1-) * [1 if s in 2 pi Z else 0],

    the bracket collapsing off resonance because sum_d cos(d s)/d stays
    bounded there while sum_d 1/d does not.
    """
    hp0 = -C2_EDGE_SLOPE
    hp1 = -C2_EDGE_SLOPE * math.cosh(y) ** 2
    L = hp0 - (hp1 if is_resonant(s) else 0.0)
    return {"L": L, "coefficient": 16 * L / (A**2 * s**2),
            "resonant": is_resonant(s)}


def rate_record(s: float, y: float, ms=(8, 16, 32, 64, 128, 256)) -> dict:
    """Two readings of the convergence rate.

    ``exponent``: least-squares slope of log|b_m - b_inf| against log m
    (the naive power-law reading; a pure 1/m boundary term would give 1,
    a log-corrected one gives slightly less over any finite window).

    ``fitted_log_coefficient``: the coefficient of log m / m read off the
    increments of m|b_m - b_inf| between successive doublings, compared
    with the DERIVED :func:`leading_coefficient`.  This is the sharp
    test of the structural story; the exponent alone cannot distinguish
    1/m from log m / m.
    """
    ms = tuple(ms)
    ds = np.array([abs(discrepancy(m, s, y)) for m in ms])
    lm = np.log(np.array(ms, float))
    slope, _ = np.polyfit(lm, np.log(ds), 1)
    prod = np.array(ms, float) * np.array([discrepancy(m, s, y) for m in ms])
    # m|d| ~ a + b log m: slope of the product against log m
    b_fit, _ = np.polyfit(lm, prod, 1)
    der = leading_coefficient(s, y)
    ratio = b_fit / der["coefficient"] if der["coefficient"] else math.nan
    return {"s": s, "y": y, "ms": ms, "exponent": float(-slope),
            "fitted_log_coefficient": float(b_fit),
            "derived_log_coefficient": der["coefficient"],
            "fit_over_derived": float(ratio), "resonant": der["resonant"],
            "signs": [float(np.sign(discrepancy(m, s, y))) for m in ms]}


# ---------------------------------------------------------------------------
# 4. validation of the estimate on the grid
# ---------------------------------------------------------------------------

#: the spacing grid: [0.3, 20] mean gaps, dense on the near-integer
#: resonances where `cluster_universal` found the cap peaks.
S_GRID = (0.3, 0.5, 0.8, 1.0, 1.2, 1.5, 1.9, 1.95, 2.0, 2.002, 2.05, 2.5,
          3.0, 3.05, 4.0, 5.0, 6.0, 7.0, 10.0, 14.0, 20.0)
Y_GRID = (0.02, 0.1, 0.3, 0.49)
M_GRID = (2, 4, 8, 16, 32, 64)


def bridge_grid(s_grid=S_GRID, ys=Y_GRID, ms=M_GRID, D: int = D_SPLIT,
                inflate: float = 1.0) -> dict:
    """Does E bound |b_m - b_inf| everywhere on the grid, and by how much?

    ``inflate`` is the planted control: multiplying the measured
    discrepancy by a factor > 1/worst_ratio must make the estimate fail,
    which is what gives the check its power.
    """
    worst_c = {"ratio": -1.0}
    worst_h = {"ratio": -1.0}
    rows = []
    for x in s_grid:
        s = x * MEAN_GAP
        for y in ys:
            bi = b_limit(s, y)
            for m in ms:
                dm = abs(b_finite(m, s, y) - bi) * inflate
                ec, eh = E_crude(m, s), E_hybrid(m, s, y, D)
                rec = {"s_gaps": x, "y": y, "m": m, "abs_disc": dm,
                       "E_crude": ec, "E_hybrid": eh,
                       "ratio_crude": dm / ec, "ratio_hybrid": dm / eh}
                rows.append(rec)
                if rec["ratio_crude"] > worst_c["ratio"]:
                    worst_c = {"ratio": rec["ratio_crude"], **rec}
                if rec["ratio_hybrid"] > worst_h["ratio"]:
                    worst_h = {"ratio": rec["ratio_hybrid"], **rec}
    return {"n": len(rows), "rows": rows,
            "worst_crude": worst_c, "worst_hybrid": worst_h,
            "crude_holds": worst_c["ratio"] <= 1.0,
            "hybrid_holds": worst_h["ratio"] <= 1.0,
            "headroom_crude": 1.0 / worst_c["ratio"],
            "headroom_hybrid": 1.0 / worst_h["ratio"]}


# ---------------------------------------------------------------------------
# 5. the payoff: m0 and the small-m ladder
# ---------------------------------------------------------------------------


def m0_from_room(s: float, y: float, room: float, D: int = D_SPLIT,
                 m_cap: int = 100000) -> dict:
    """Smallest m with E(m, s, y) <= room, for both estimates.

    ``room`` is the per-pair margin the infinite lattice has spare.  Two
    ways to supply it are used below: the UNIFORM room
    ``(1 - RHO_SUP) b_inf`` (worst case over the whole family) and the
    POINTWISE room ``b_inf - cap_inf`` at this (s, y).
    """
    out = {"room": room, "m0_crude": None, "m0_hybrid": None}
    if room <= 0:
        return out
    for m in range(2, m_cap + 1):
        if out["m0_crude"] is None and E_crude(m, s) <= room:
            out["m0_crude"] = m
        if out["m0_hybrid"] is None and E_hybrid(m, s, y, D) <= room:
            out["m0_hybrid"] = m
        if out["m0_crude"] and out["m0_hybrid"]:
            break
    return out


def m0_uniform(s_gaps: float, y: float, rho_sup: float = RHO_SUP) -> dict:
    """m0 against the uniform room ``(1 - sup rho) b_inf``."""
    s = s_gaps * MEAN_GAP
    bi = b_limit(s, y)
    rec = m0_from_room(s, y, (1 - rho_sup) * bi)
    return {"s_gaps": s_gaps, "y": y, "b_inf": bi, **rec}


def m0_pointwise(s_gaps: float, y: float, theta: float = THETA_FULL,
                 step: float = 0.004) -> dict:
    """m0 against the POINTWISE room ``b_inf - cap_inf(s, y)``.

    Much smaller wherever the lattice is fully shielded (cap = 0), which
    is most of the range; the uniform version pays the resonance
    everywhere.  The cap here is the measured band-cell instrument of
    `cluster_universal.periodic_cap` — measured grade, not derived.
    """
    s = s_gaps * MEAN_GAP
    bi = b_limit(s, y)
    cap = periodic_cap(s, y, theta, step)["cap"]
    rec = m0_from_room(s, y, bi - cap)
    return {"s_gaps": s_gaps, "y": y, "b_inf": bi, "cap_inf": cap,
            "rho": cap / bi if bi > 0 else math.inf, **rec}


def small_m_ladder(s_gaps: float, y: float,
                   ms=(2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64),
                   theta: float = THETA_FULL,
                   pj: PaperJoint | None = None) -> dict:
    """Direct finite verdicts at a ladder of m, for the m < m0 region.

    The existing instrument (`PaperJoint.verdict`) on the actual finite
    cluster — budget and cap both finite, no bridge involved.  A ladder,
    NOT every m below m0: gap (G2) in the module docstring.
    """
    pj = pj or PaperJoint(step=0.005, G=60.0)
    s = s_gaps * MEAN_GAP
    rows = []
    for m in ms:
        rec = pj.verdict([(j * s, y) for j in range(m)], theta)
        rows.append({"m": m, "budget_pp": rec["budget"] / m,
                     "cap_pp": rec["cap"] / m,
                     "margin_pp": rec["margin"] / m})
    return {"s_gaps": s_gaps, "y": y, "rows": rows,
            "min_margin_pp": min(r["margin_pp"] for r in rows),
            "all_close": all(r["margin_pp"] > 0 for r in rows)}


def cap_side_probe(s_gaps: float, y: float, ms=(4, 8, 16, 32),
                   theta: float = THETA_FULL,
                   pj: PaperJoint | None = None,
                   step: float | None = None) -> dict:
    """Gap (G1), measured: is the finite per-pair cap below the limit?

    The bridge derived above is a BUDGET statement.  Transferring a
    verdict also needs the cap side, for which no derived finite-size
    estimate exists here.  This records the measurement — including
    where it goes the wrong way.

    ``step`` defaults to the finite instrument's own grid step so the two
    caps are like for like; the periodic cap is strongly step-dependent
    (`cluster_universal.RHO_SUP_RECORD` records 0.9547 / 0.9286 / 0.9154
    at step 0.004 / 0.002 / 0.001), so a mismatched comparison measures
    the grid, not the cluster.  ``rho_inf`` is reported at the same step
    for exactly that reason.
    """
    pj = pj or PaperJoint(step=0.005, G=60.0)
    s = s_gaps * MEAN_GAP
    cap_inf = periodic_cap(s, y, theta, step or pj.step)["cap"]
    b_inf = b_limit(s, y)
    rows = []
    for m in ms:
        cap = pj.cap([(j * s, y) for j in range(m)], theta)["cap"] / m
        rows.append({"m": m, "cap_pp": cap, "excess": cap - cap_inf})
    return {"s_gaps": s_gaps, "y": y, "cap_inf": cap_inf,
            "step": step or pj.step, "b_inf": b_inf,
            "rho_inf": cap_inf / b_inf if b_inf > 0 else math.inf,
            "rows": rows,
            "all_below_limit": all(r["excess"] <= 1e-12 for r in rows),
            "worst_excess": max(r["excess"] for r in rows)}


# ---------------------------------------------------------------------------
# audit
# ---------------------------------------------------------------------------


def audit(quick: bool = False) -> None:
    print("= the constant this module reuses (cluster_universal's C_T) =")
    ct = c_t_reuse_check()
    print(f"  C_T = {ct['C_T']:.4f} (pinned {ct['pinned']}, matches: "
          f"{ct['matches_pinned']}); measured worst |T| dt^2 / C_T = "
          f"{ct['worst_quotient']:.4f} ({'holds' if ct['holds'] else 'FAILS'})")

    print("= both sides, and the identity (*) =")
    for x, y in ((2.0, 0.49), (2.05, 0.49), (1.0, 0.49), (0.3, 0.1)):
        s = x * MEAN_GAP
        bi, bd = b_limit(s, y), b_limit_direct(s, y)
        d16 = discrepancy(16, s, y)
        d16i = discrepancy_via_identity(16, s, y)
        print(f"  s={x:5} y={y}: b_inf {bi:+.8f} (direct {bd:+.8f}, "
              f"defect {abs(bi-bd):.1e}); b_16 - b_inf = {d16:+.3e} "
              f"(identity {d16i:+.3e}, defect {abs(d16-d16i):.1e})")

    print("= the rate: log m / m, with the derived coefficient =")
    for x, y in ((2.0, 0.49), (2.05, 0.49), (1.0, 0.49), (3.0, 0.3),
                 (5.0, 0.1)):
        r = rate_record(x * MEAN_GAP, y)
        print(f"  s={x:5} y={y} resonant={str(r['resonant']):5}: "
              f"exponent {r['exponent']:.3f}; fitted log-coef "
              f"{r['fitted_log_coefficient']:+.5f} vs derived "
              f"{r['derived_log_coefficient']:+.5f} "
              f"(ratio {r['fit_over_derived']:.3f}); signs "
              f"{set(r['signs'])}")

    print("= E on the grid (must bound the measured discrepancy) =")
    g = bridge_grid()
    wc, wh = g["worst_crude"], g["worst_hybrid"]
    print(f"  {g['n']} points; crude holds: {g['crude_holds']}, worst ratio "
          f"{wc['ratio']:.4f} at s={wc['s_gaps']} y={wc['y']} m={wc['m']} "
          f"(headroom x{g['headroom_crude']:.2f})")
    print(f"  hybrid (D={D_SPLIT}) holds: {g['hybrid_holds']}, worst ratio "
          f"{wh['ratio']:.4f} at s={wh['s_gaps']} y={wh['y']} m={wh['m']} "
          f"(headroom x{g['headroom_hybrid']:.2f})")

    print("= planted control: inflate the discrepancy, E must fail =")
    factor = 1.0 / g["worst_hybrid"]["ratio"] * 1.05
    gi = bridge_grid(inflate=factor)
    print(f"  inflate x{factor:.3f}: crude holds {gi['crude_holds']}, "
          f"hybrid holds {gi['hybrid_holds']} (worst hybrid ratio "
          f"{gi['worst_hybrid']['ratio']:.4f}) — the check has power: "
          f"{not gi['hybrid_holds']}")

    print("= m0 against the UNIFORM room (1 - sup rho) b_inf, sup rho = "
          f"{RHO_SUP} =")
    for x in (0.3, 1.0, 1.5, 2.0, 2.002, 3.0, 5.0, 10.0, 20.0):
        r = m0_uniform(x, 0.49)
        print(f"  s={x:6} gaps: b_inf {r['b_inf']:.6f}, room "
              f"{r['room']:.6f} -> m0_crude {r['m0_crude']}, m0_hybrid "
              f"{r['m0_hybrid']}")

    if not quick:
        print("= m0 against the POINTWISE room b_inf - cap_inf (measured "
              "cap) =")
        for x in (0.3, 1.0, 1.5, 2.0, 2.002, 3.0, 5.0):
            r = m0_pointwise(x, 0.49)
            print(f"  s={x:6} gaps: rho {r['rho']:.4f}, room "
                  f"{r['room']:.6f} -> m0_crude {r['m0_crude']}, m0_hybrid "
                  f"{r['m0_hybrid']}")

        print("= the m < m0 region, checked directly on a ladder of m =")
        for x, y in ((1.0, 0.49), (2.0, 0.49), (2.002, 0.4999)):
            lad = small_m_ladder(x, y)
            print(f"  s={x} y={y}: min per-pair margin "
                  f"{lad['min_margin_pp']:+.5f} over m in "
                  f"{[r['m'] for r in lad['rows']]}, all close: "
                  f"{lad['all_close']}")

        print("= gap (G1)/(G3): the cap side, measured only, at MATCHED "
              "grid step =")
        for x, y in ((2.0, 0.49), (1.0, 0.49), (2.002, 0.4999)):
            cp = cap_side_probe(x, y)
            print(f"  s={x} y={y} step {cp['step']}: cap_inf "
                  f"{cp['cap_inf']:.6f} (rho_inf {cp['rho_inf']:.4f}); finite "
                  "per-pair caps "
                  + ", ".join(f"m={r['m']}: {r['cap_pp']:.6f}"
                              for r in cp["rows"])
                  + f"  all below limit: {cp['all_below_limit']} "
                    f"(worst excess {cp['worst_excess']:+.2e})")


if __name__ == "__main__":
    audit(quick="--quick" in sys.argv)
