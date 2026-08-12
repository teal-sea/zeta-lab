"""Rational weak-duality certificate for the bucket-floor LP reading.

WHAT THIS IS.  ``kernel_pairing.floors_on_a_ladder`` reads the g-kernel
bucket floor c_u(g) = 5.021179e-6 at nu = H_PINNED off a scipy ``linprog``
call (``cg_transplant.bucket_floor``).  That number is "scipy said so".
This module converts it into a statement a Lean 4 file can check by pure
rational arithmetic: an explicit dual-feasible point with exact rational
coordinates whose dual objective F_RAT is, by weak duality, a lower bound
for the LP value — no simplex run, no floating point, only finitely many
comparisons of fractions.

THE PRIMAL (from ``cg_transplant.bucket_floor``; x in R^6, x >= 0):

    minimise   g(a) x1 + g(b) x2 + 0 x3 + h x4 + 0 x5 + j x6
    subject to x1 + x2 + x3 + x4 + x5           =  nu
               a x2 + b x3 + c x4 + d x5        <= 1
               2 x3 - x6                        <= nu

with h = min g on [c, d] and j = min g on [2b, 2c], g the Montgomery-
Taylor kernel (``cg_transplant.g_kernel``).  Edges (a, b, c, d) are the
n = 600001 HardenedGTable optimum recovered in this session (pinned
below; ``recover_edges()`` re-derives them in ~4 min).

THE DUAL POINT.  Multipliers y (equality, free) and u1, u2 <= 0 (the two
<= rows).  Dual feasibility is one inequality per primal column:

    col 1:  y                 <= g(a)
    col 2:  y + a u1          <= g(b)
    col 3:  y + b u1 + 2 u2   <= 0
    col 4:  y + c u1          <= h
    col 5:  y + d u1          <= 0
    col 6:  -u2               <= j

and then for every feasible x >= 0,

    cost(x) >= y (sum x1..x5) + u1 (a x2 + .. + d x5) + u2 (2 x3 - x6)
            >= y nu + u1 * 1 + u2 * nu     =: F,

using u1, u2 <= 0 against the <= rows.  That two-line chain is the whole
argument; it is what the Lean file will replay.

DIRECTION OF THE KERNEL BOUNDS (this is the sign bookkeeping).  The four
kernel numbers g(a), g(b), h, j sit in the COST VECTOR of a minimisation
over x >= 0.  Replacing any of them by something smaller can only lower
the objective, so a bound established for the lowered cost is a fortiori
a bound for the true cost:

    cost_true(x) >= cost_rational(x) >= F_RAT      whenever
    r_a <= g(a),  r_b <= g(b),  r_h <= min g on [c,d],
    r_j <= min g on [2b,2c].

Hence all four bounds needed are LOWER bounds.  (r_a, r_b enter columns
1-2 directly; r_h, r_j are lower bounds on interval minima, i.e. "g >= r
on the whole interval", which is the natural one-sided statement for
interval arithmetic.)  Note h and j appear on the right of dual rows 4
and 6, so shrinking them TIGHTENS dual feasibility — the dual point
below is feasible against the rational r_h, r_j, not just the sampled
table values, and that is checked exactly.

THE CERTIFICATE (all exact rationals, stated in full below):

    nu  = 6725007037 / 10^10          (the pinned decimal for H_PINNED)
    a, b, c, d = exact binary rationals of the recovered edge floats
    r_a = 147223/10^7    <= g(a)  = 0.0147223943...   (margin 9.4e-8)
    r_b = 250294/10^9    <= g(b)  = 0.00025029401...  (margin 1.0e-11)
    r_h = 185/10^6       <= min g on [c, d]           (margin  >= 4.0e-6)
    r_j = 398/10^6       <= min g on [2b, 2c]         (margin  >= 4.5e-6)
    u1  = -212/900565,  u2 = -79/700438,  y = 2351506773321/(5*10^15)

    F_RAT = y nu + u1 + u2 nu
          = 15836524170563975879104102066119
            / 3153949737350000000000000000000000000
          = 5.021172019015776e-06,

a shortfall of 7.0e-12 against the scipy reading 5.021179e-6 — a valid
lower bound need not be the optimum, and this one gives up 1.4e-6 of the
value in relative terms.

WHAT IS EXACT AND WHAT IS NOT.  ``audit()`` checks the dual feasibility
inequalities and the value identity for F_RAT entirely in ``fractions.
Fraction`` — that part is finite rational arithmetic end to end.  The
four kernel lower bounds are checked here numerically (mpmath dps 40 at
the points; a 600001-point numpy grid plus an analytic slope bound on
the intervals) — those four inequalities about an explicit sin/cos
expression are exactly the lemmas the future Lean file must supply; on
the Python side they are measured with stated margins, not established.
Nothing in this file claims the LP models anything about zeta: the
bucket floor's own standing is recorded in ``cg_transplant.py`` (the
transplant was withdrawn) and ``kernel_pairing.py``.

SLOPE BOUND USED FOR THE INTERVAL MINIMA (kept crude so Lean can copy
it).  With d1 = sqrt2 - 2 pi u, d2 = sqrt2 + 2 pi u, A = sin(d1/2)/d1,
B = sin(d2/2)/d2, g = (A+B)^2/(1-cos sqrt2):

    |A| <= 1/|d1|,   |A'| <= pi/|d1| + 2 pi/d1^2      (same for B),
    |g'| <= 2 (|A|+|B|) (|A'|+|B'|) / (1 - cos sqrt2),

and on u >= 1 both |d1| = 2 pi u - sqrt2 and d2 = 2 pi u + sqrt2 are
increasing, so their values at the interval's left endpoint bound the
whole interval.  1 - cos sqrt2 >= 0.844.  This gives M = 0.56 on [c, d]
and M = 0.21 on [2b, 2c] (measured grid slopes: 0.094 and 0.039, so the
analytic bound is ~6x slack).  A grid of spacing s then gives
min g >= (grid min) - M s on the interval.

Run from the repo root:
    .venv/bin/python hunts/frontier_math/lp_certificate.py        (~15 s)
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cg_transplant import g_kernel, optimize_edges  # noqa: E402
from reconnect import H_PINNED, HardenedGTable  # noqa: E402

# ---------------------------------------------------------------------------
# Pinned floating-point data from this session's n = 600001 run
# ---------------------------------------------------------------------------

#: optimize_edges(H_PINNED, table=HardenedGTable(n=600001)) — the edges
#: behind the ladder reading c_u(g) = 5.021179e-6 (kernel_pairing.py).
EDGES = (0.934579827137746, 1.0395927961701252,
         1.3539506700128414, 1.9978157969309793)

#: bucket_floor at those edges/table: the scipy primal optimum.
FLOOR_SCIPY = 5.021179065914518e-06

#: HardenedGTable(n=600001).minimum on [c, d] and [2b, 2c] (the values
#: the scipy cost vector actually used; already one-sided).
H_TABLE = 0.00016521710212901943
J_TABLE = 0.00037824516810093214

#: scipy dual at the optimum: (eqlin.marginals[0], *ineqlin.marginals).
DUAL_SCIPY = (0.0004703013651243636,
              -0.00023540777175094668,
              -0.00011278657072480917)

# ---------------------------------------------------------------------------
# The rational certificate — every constant exact
# ---------------------------------------------------------------------------

#: nu as the pinned decimal (H_PINNED = 0.6725007037 exactly).
NU_R = Fraction(6725007037, 10**10)

#: the edges as exact binary rationals (Fraction(float) is exact).
A_R, B_R, C_R, D_R = (Fraction(x) for x in EDGES)

#: rational LOWER bounds on the four kernel numbers (direction argued in
#: the module docstring; margins measured in audit()).
R_A = Fraction(147223, 10**7)   # <= g(a)
R_B = Fraction(250294, 10**9)   # <= g(b)
R_H = Fraction(185, 10**6)      # <= min g on [c, d]
R_J = Fraction(398, 10**6)      # <= min g on [2b, 2c]

#: the dual point (limit_denominator(10^6) of the scipy dual, y then
#: re-derived exactly and rounded DOWN at denominator 5*10^15 — see
#: rationalize_dual()).
U1 = Fraction(-212, 900565)
U2 = Fraction(-79, 700438)
Y = Fraction(2351506773321, 5 * 10**15)

#: F_RAT = Y*NU_R + U1 + U2*NU_R, the exact rational lower bound.
F_RAT = Fraction(15836524170563975879104102066119,
                 3153949737350000000000000000000000000)

#: the ladder reading this bounds, as a rational for exact gap reporting.
TARGET = Fraction(5021179, 10**12)


# ---------------------------------------------------------------------------
# Recompute-and-check: the scipy side
# ---------------------------------------------------------------------------

def solve_lp_with_dual(nu: float, a: float, b: float, c: float, d: float,
                       h: float, j: float):
    """bucket_floor's exact LP, plus the HiGHS dual multipliers."""
    from scipy.optimize import linprog
    cobj = np.array([float(g_kernel(np.array([a]))[0]),
                     float(g_kernel(np.array([b]))[0]), 0.0, h, 0.0, j])
    Aeq = np.array([[1., 1., 1., 1., 1., 0.]])
    Aub = np.array([[0., a, b, c, d, 0.],
                    [0., 0., 2., 0., 0., -1.]])
    res = linprog(cobj, A_ub=Aub, b_ub=np.array([1.0, nu]),
                  A_eq=Aeq, b_eq=np.array([nu]),
                  bounds=[(0, None)] * 6, method="highs")
    y = float(res.eqlin.marginals[0])
    u1, u2 = (float(v) for v in res.ineqlin.marginals)
    dual_obj = y * nu + u1 * 1.0 + u2 * nu
    return res, (y, u1, u2), dual_obj


def strong_duality_check(tol: float = 1e-12):
    """Re-solve the pinned LP; primal and dual objectives must agree.

    Also recomputes the table minima H_TABLE/J_TABLE from a fresh
    HardenedGTable(n=600001) so the pinned cost vector is not taken on
    faith.  Returns a dict of readings; raises AssertionError on drift.
    """
    a, b, c, d = EDGES
    t = HardenedGTable(n=600001)
    h, j = t.minimum(c, d), t.minimum(2 * b, 2 * c)
    assert abs(h - H_TABLE) < 1e-15 and abs(j - J_TABLE) < 1e-15, \
        (h, j, "table minima drifted from the pinned session values")
    res, dual, dual_obj = solve_lp_with_dual(H_PINNED, a, b, c, d, h, j)
    assert res.success
    gap = res.fun - dual_obj
    assert abs(gap) < tol, ("strong duality gap", gap)
    assert abs(res.fun - FLOOR_SCIPY) < 1e-14, (res.fun, FLOOR_SCIPY)
    return {"primal": res.fun, "dual": dual_obj, "gap": gap,
            "multipliers": dual, "h": h, "j": j, "x": res.x}


def recover_edges():
    """Re-derive EDGES from scratch (~4 min): the kernel_pairing path."""
    table = HardenedGTable(n=600001)
    floor, edges = optimize_edges(H_PINNED, table=table)
    return floor, edges


# ---------------------------------------------------------------------------
# Rationalization: float dual -> exact-feasible rational dual
# ---------------------------------------------------------------------------

def rationalize_dual(den: int, dual=DUAL_SCIPY, y_den: int = 10**16):
    """Turn the float dual into an exactly feasible rational one.

    u1, u2 are limit_denominator(den) snaps, clamped to u <= 0 and
    u2 >= -R_J (dual row 6).  y is then NOT snapped: it is set to the
    exact rational minimum of the five upper bounds the remaining dual
    rows place on it, floored at denominator y_den so the stated
    constant is short.  Feasibility therefore holds by construction in
    Q; the only question the audit re-asks is the arithmetic itself.
    Returns (y, u1, u2, F) with F = y*NU_R + u1 + u2*NU_R exact.
    """
    _, u1f, u2f = dual
    u1 = min(Fraction(u1f).limit_denominator(den), Fraction(0))
    u2 = min(Fraction(u2f).limit_denominator(den), Fraction(0))
    if u2 < -R_J:
        u2 = -R_J
    y_cap = min(R_A,
                R_B - A_R * u1,
                -B_R * u1 - 2 * u2,
                R_H - C_R * u1,
                -D_R * u1)
    y = Fraction(math.floor(y_cap * y_den), y_den)
    return y, u1, u2, y * NU_R + u1 + u2 * NU_R


def dual_feasibility_exact(y: Fraction, u1: Fraction, u2: Fraction):
    """The six column inequalities + sign conditions, in Q. Returns list."""
    return [
        ("col1: y <= r_a", y <= R_A),
        ("col2: y + a*u1 <= r_b", y + A_R * u1 <= R_B),
        ("col3: y + b*u1 + 2*u2 <= 0", y + B_R * u1 + 2 * u2 <= 0),
        ("col4: y + c*u1 <= r_h", y + C_R * u1 <= R_H),
        ("col5: y + d*u1 <= 0", y + D_R * u1 <= 0),
        ("col6: -u2 <= r_j", -u2 <= R_J),
        ("sign: u1 <= 0", u1 <= Fraction(0)),
        ("sign: u2 <= 0", u2 <= Fraction(0)),
    ]


# ---------------------------------------------------------------------------
# The four kernel lower bounds (numeric side; the future Lean lemmas)
# ---------------------------------------------------------------------------

def g_mp(u, dps: int = 40):
    """Montgomery-Taylor kernel via mpmath at dps digits."""
    import mpmath as mp
    with mp.workdps(dps):
        s2 = mp.sqrt(2)
        uu = mp.mpf(u)
        d1 = s2 - 2 * mp.pi * uu
        d2 = s2 + 2 * mp.pi * uu
        A = mp.sin(d1 / 2) / d1
        B = mp.sin(d2 / 2) / d2
        return (A + B) ** 2 / (1 - mp.cos(s2))


def slope_bound(lo: float) -> float:
    """Analytic upper bound for |g'| on [lo, inf) restricted to u >= 1.

    |g'| <= 2 (1/m1 + 1/m2)(pi/m1 + 2 pi/m1^2 + pi/m2 + 2 pi/m2^2)
            / (1 - cos sqrt2),
    with m1 = 2 pi lo - sqrt2, m2 = 2 pi lo + sqrt2 (both increasing in
    u, so endpoint values bound the interval), 1 - cos sqrt2 >= 0.844.
    Inflated by 1.001 to absorb the float rounding of this formula.
    """
    assert lo >= 1.0
    m1 = 2 * math.pi * lo - math.sqrt(2)
    m2 = 2 * math.pi * lo + math.sqrt(2)
    amp = 1 / m1 + 1 / m2
    der = math.pi / m1 + 2 * math.pi / m1**2 + math.pi / m2 + 2 * math.pi / m2**2
    return 1.001 * 2 * amp * der / 0.844


def interval_lower_bound(lo: float, hi: float, n: int = 600001):
    """Grid minimum minus slope*spacing: a one-sided bound for min g.

    numpy doubles on the grid (relative error ~1e-15, absorbed many
    times over by the M*s margin); returns (bound, grid_min, argmin, M, s).
    """
    x = np.linspace(lo, hi, n)
    v = g_kernel(x)
    i = int(v.argmin())
    s = float(x[1] - x[0])
    M = slope_bound(lo)
    return float(v[i]) - M * s, float(v[i]), float(x[i]), M, s


def kernel_bound_checks(dps: int = 40):
    """Measure the four lower bounds R_A, R_B, R_H, R_J with margins.

    Point bounds at dps-digit precision; interval bounds by grid + slope.
    Returns a list of (name, rational_bound, reference_value, margin,
    note) and raises if any margin is not positive.
    """
    a, b, c, d = EDGES
    ga, gb = g_mp(a, dps), g_mp(b, dps)
    out = [
        ("r_a <= g(a)", R_A, float(ga), float(ga - float(R_A)),
         f"g(a) at dps={dps}"),
        ("r_b <= g(b)", R_B, float(gb), float(gb - float(R_B)),
         f"g(b) at dps={dps}"),
    ]
    for name, lo, hi, r in (("r_h <= min g on [c,d]", c, d, R_H),
                            ("r_j <= min g on [2b,2c]", 2 * b, 2 * c, R_J)):
        bound, gmin, argmin, M, s = interval_lower_bound(lo, hi)
        out.append((name, r, bound, bound - float(r),
                    f"grid min {gmin:.8e} at u={argmin:.8f} "
                    f"(endpoint: {'yes' if min(argmin - lo, hi - argmin) < s else 'no'}), "
                    f"M={M:.3f}, spacing={s:.2e}, M*s={M * s:.2e}"))
    for name, r, ref, margin, note in out:
        assert margin > 0, (name, margin, "kernel bound margin not positive")
    return out


# ---------------------------------------------------------------------------
# The end-to-end audit
# ---------------------------------------------------------------------------

def audit(skip_scipy: bool = False):
    """Check the whole certificate; exact in Q except the kernel lemmas.

    Order: (1) the stated F_RAT is exactly Y*NU_R + U1 + U2*NU_R and is
    positive; (2) the stated dual point is exactly feasible in Q against
    the rational data; (3) the four kernel lower bounds hold numerically
    with positive margins (these are the future Lean lemmas — measured
    here, not established); (4) unless skipped, scipy reproduces the
    pinned primal/dual with strong duality, and the primal optimum sits
    above float(F_RAT).  Raises AssertionError on any failure.
    """
    print("= rational weak-duality certificate for c_u(g) =")
    print(f"  edges a,b,c,d = {EDGES}")
    print(f"  nu = {NU_R} = {float(NU_R)}")

    # (1) the value identity, exact
    f_check = Y * NU_R + U1 + U2 * NU_R
    assert f_check == F_RAT, "stated F_RAT is not Y*nu + U1 + U2*nu"
    assert F_RAT > 0
    print(f"  (1) F_RAT identity holds exactly in Q: F_RAT = "
          f"{F_RAT.numerator}/{F_RAT.denominator}")
    print(f"      = {float(F_RAT):.15e}; gap to ladder reading "
          f"{float(TARGET):.6e}: {float(F_RAT - TARGET):+.3e}")

    # (2) exact dual feasibility
    rows = dual_feasibility_exact(Y, U1, U2)
    for name, ok in rows:
        assert ok, f"exact dual feasibility failed at {name}"
    print(f"  (2) dual point y={Y}, u1={U1}, u2={U2}")
    print(f"      all {len(rows)} inequalities hold exactly in Q")

    # (3) kernel bounds, numeric with stated margins
    print("  (3) kernel lower bounds (numeric; the future Lean lemmas):")
    for name, r, ref, margin, note in kernel_bound_checks():
        print(f"      {name}: bound={r} ({float(r):.6e}), "
              f"reference={ref:.10e}, margin={margin:.3e}")
        print(f"          [{note}]")

    # (4) scipy cross-check
    if not skip_scipy:
        sd = strong_duality_check()
        assert sd["primal"] >= float(F_RAT), \
            "scipy primal optimum fell below the rational bound"
        print(f"  (4) scipy re-solve: primal={sd['primal']:.15e}, "
              f"dual={sd['dual']:.15e}, gap={sd['gap']:.2e}")
        print(f"      primal >= float(F_RAT): "
              f"{sd['primal']:.9e} >= {float(F_RAT):.9e}")

    print("  conclusion: for every x >= 0 meeting the two constraint rows")
    print("  with the rational data above, cost(x) >= F_RAT, provided the")
    print("  four kernel inequalities hold — finite rational arithmetic")
    print("  plus four one-variable trig lemmas.  The LP's own standing")
    print("  (withdrawn transplant) is unchanged; see cg_transplant.py.")
    return {"F_RAT": F_RAT, "gap": F_RAT - TARGET}


def rationalization_ladder(dens=(10**6, 10**9, 10**12)):
    """The bound at several snap denominators (the stated one is 10^6)."""
    out = {}
    for den in dens:
        y, u1, u2, f = rationalize_dual(den)
        rows = dual_feasibility_exact(y, u1, u2)
        out[den] = {"y": y, "u1": u1, "u2": u2, "F": f,
                    "feasible": all(ok for _, ok in rows)}
    return out


if __name__ == "__main__":
    audit()
    print("= rationalization ladder (all exact-feasible) =")
    for den, rec in rationalization_ladder().items():
        print(f"  den={den:.0e}: F={float(rec['F']):.15e} "
              f"feasible={rec['feasible']}")
