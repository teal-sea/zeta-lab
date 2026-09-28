"""Hunt R-828C8B, the ceiling procedure applied to Erdos's minimum overlap problem.

Runs end to end with:

    .venv/bin/python hunts/r_828c8b/probe.py            # ~2 min
    .venv/bin/python hunts/r_828c8b/probe.py --quick    # ~20 s

Four fronts, in the order the issue (#111) asks for them.

  A. The discrete truth.  M(n) computed exhaustively for small n by bitmask
     search, so the continuous relaxation below is anchored to something that
     is not a relaxation.

  B. The upper-bound family, which is where the published record lives.
     Haugland's 0.382002 (1996) and 0.380926 (2016) are step-function
     constructions.  A step function with m pieces is a point in a compact
     m-dimensional polytope and its value is a max of finitely many
     quadratics, so "push the parameterisation to its own limit" is here a
     literal instruction: solve the m-piece minimax for growing m and watch
     where the value stops moving.

  C. The acceptance step.  The value of an m-piece construction is a finite
     sum of products of the pieces.  If the pieces are rational the value is
     rational, so the accepted object can be re-evaluated in exact arithmetic
     with no floating point anywhere.  We do that, and we report the size of
     the correction that exact re-evaluation applies to the float value.

  D. The lower-bound family, which is where the convex program lives.  White
     (arXiv:2201.05704) gets 0.379005 by Fourier-analysing the problem into a
     convex program.  We reconstruct the averaging skeleton such a bound must
     have, compute the bound the plainest weight gives (exactly), and record
     the two obstructions that stop the reconstruction from reaching 0.379005
     inside this budget.

Nothing here is evidence for or against RH (docs/08).  The reserved word for
enclosure-carrying claims belongs to zeta/rigor.py and the Lean arm and is not
used here.

THE OBJECT
----------
For n >= 1 let A subset {1..2n} with |A| = n and B its complement.  For an
integer shift k set

    M_k(A) = #{(a,b) in A x B : a - b = k},

M(n) = min_A max_k M_k(A), and C = lim_n M(n)/n (the limit exists).

Rescale by n.  A step function f : [0,2] -> [0,1] with integral 1 plays the
part of 1_A; g = 1_{[0,2]} - f plays 1_B; the overlap at real shift t is

    h_f(t) = int f(x) g(x - t) dx,

and C = inf_f sup_t h_f(t) over measurable f.  Every explicit f therefore
gives an upper bound on C and no explicit f gives a lower bound: that
asymmetry is the whole reason the two published records were obtained by two
unrelated methods.
"""

from __future__ import annotations

import argparse
import itertools
import json
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent

# The published record, as of the literature check run 2026-08-23.  Recorded
# here as reference values to compare against, not as anything this file
# verifies.
PUBLISHED = {
    "upper_haugland_1996": 0.382002,
    "upper_haugland_2016": 0.380926,
    "lower_white_2022": 0.379005,
    "lower_augmented_program": 0.37912,
}


# ---------------------------------------------------------------------------
# A. the discrete truth: M(n) by exhaustive bitmask search
# ---------------------------------------------------------------------------

def max_overlap_bitmask(a_mask: int, n2: int) -> int:
    """max_k M_k(A) for A given as a bitmask over positions 0..n2-1."""
    b_mask = ((1 << n2) - 1) ^ a_mask
    best = 0
    for k in range(-(n2 - 1), n2):
        if k >= 0:
            shifted = (b_mask << k) & ((1 << n2) - 1)
        else:
            shifted = b_mask >> (-k)
        c = bin(a_mask & shifted).count("1")
        if c > best:
            best = c
    return best


def minimum_overlap_exact(n: int) -> dict:
    """M(n) by exhaustive search over all C(2n, n) splits.

    Symmetry used: position 0 may be assumed to lie in A (complementing A
    with B leaves max_k M_k unchanged because M_k(B) = M_{-k}(A)).
    """
    n2 = 2 * n
    best = n2
    witness = None
    for rest in itertools.combinations(range(1, n2), n - 1):
        mask = 1
        for p in rest:
            mask |= 1 << p
        v = max_overlap_bitmask(mask, n2)
        if v < best:
            best = v
            witness = mask
    return {"n": n, "M": best, "M_over_n": best / n, "witness_mask": witness}


# ---------------------------------------------------------------------------
# B. the upper-bound family: the m-piece minimax
# ---------------------------------------------------------------------------
#
# Let f be constant f_i on bin i = 0..m-1 of [0,2], bin width 2/m, with
# 0 <= f_i <= 1 and (2/m) sum f_i = 1.  Then h_f is piecewise linear in t
# with breakpoints exactly at the grid points t = 2j/m, so
#
#     sup_t h_f(t) = max_j h_j,   h_j = (2/m) * ( L_j(f) - q_j(f) ),
#
# where q_j = sum_i f_i f_{i-j} is the autocorrelation at lag j and
# L_j = sum over the overlap window of f_i is the linear part.  The window is
# what breaks translation invariance; without it the value would be 1/2.
#
# CLAIM (piecewise linearity).  h_f = f * gcheck is the correlation of two
# functions constant on a common grid of width w, hence a sum of terms
# (indicator of bin) correlated with (indicator of bin), each of which is a
# tent of half-width w centred on a grid point.  A sum of tents on a common
# grid is piecewise linear with breakpoints on the grid.  So the max over
# real t is attained at some t = 2j/m.  This is checked numerically in
# check_grid_sufficiency() below rather than assumed.


def overlaps(f: np.ndarray) -> np.ndarray:
    """h_j for j = -(m-1) .. (m-1), given the m bin heights."""
    m = len(f)
    g = 1.0 - f
    # np.correlate(f, g, "full")[i] = sum_k f[k] g[k - (m-1) + i]
    corr = np.correlate(f, g, "full")  # length 2m-1, index i <-> j = i-(m-1)
    return (2.0 / m) * corr


def overlaps_fine(f: np.ndarray, sub: int = 8) -> np.ndarray:
    """h at sub-grid shifts, by refining f by an integer factor and reusing
    the same machinery.  Used only to check that the grid max is the true max."""
    fr = np.repeat(f, sub)
    return overlaps(fr)


def check_grid_sufficiency(f: np.ndarray, sub: int = 8) -> float:
    """max over the sub-grid minus max over the grid.  Should be ~0."""
    return float(overlaps_fine(f, sub).max() - overlaps(f).max())


def _epigraph_solve(f0: np.ndarray, maxiter: int = 300) -> tuple[np.ndarray, float]:
    """min_f max_j h_j(f) by SLSQP on the epigraph, analytic jacobians."""
    m = len(f0)
    target = m / 2.0

    def unpack(z):
        return z[:m], z[m]

    def obj(z):
        return z[m]

    def obj_jac(z):
        gj = np.zeros(m + 1)
        gj[m] = 1.0
        return gj

    def cons_f(z):
        f, s = unpack(z)
        return s - overlaps(f)          # >= 0

    def cons_jac(z):
        f, s = unpack(z)
        # d h_j / d f_i = (2/m) * ( 1_{i in window_j} - (f_{i-j} + f_{i+j}) )
        J = np.zeros((2 * m - 1, m + 1))
        idx = np.arange(m)
        for i_row in range(2 * m - 1):
            j = i_row - (m - 1)
            lo, hi = max(0, j), min(m, m + j)
            lin = np.zeros(m)
            if hi > lo:
                lin[lo:hi] = 1.0
            quad = np.zeros(m)
            a = idx - j
            ok = (a >= 0) & (a < m)
            quad[ok] += f[a[ok]]
            b = idx + j
            ok2 = (b >= 0) & (b < m)
            quad[ok2] += f[b[ok2]]
            J[i_row, :m] = -(2.0 / m) * (lin - quad)
            J[i_row, m] = 1.0
        return J

    z0 = np.concatenate([f0, [overlaps(f0).max()]])
    bounds = [(0.0, 1.0)] * m + [(0.0, 1.0)]
    constraints = [
        {"type": "ineq", "fun": cons_f, "jac": cons_jac},
        {"type": "eq",
         "fun": lambda z: np.array([z[:m].sum() - target]),
         "jac": lambda z: np.concatenate([np.ones(m), [0.0]])[None, :]},
    ]
    res = minimize(obj, z0, jac=obj_jac, bounds=bounds, constraints=constraints,
                   method="SLSQP", options={"maxiter": maxiter, "ftol": 1e-12})
    f = np.clip(res.x[:m], 0.0, 1.0)
    # repair the mass constraint after clipping, then report the honest value
    f = _repair_mass(f, target)
    return f, float(overlaps(f).max())


def _repair_mass(f: np.ndarray, target: float) -> np.ndarray:
    """Project onto {0<=f<=1, sum f = target} by a bisection on a shift."""
    lo, hi = -1.0, 1.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        s = np.clip(f + mid, 0.0, 1.0).sum()
        if s < target:
            lo = mid
        else:
            hi = mid
    return np.clip(f + 0.5 * (lo + hi), 0.0, 1.0)


def upsample(f: np.ndarray, factor: int) -> np.ndarray:
    return np.repeat(f, factor)


def ceiling_sweep(ms: list[int], starts: int, rng: np.random.Generator,
                  seed_from: np.ndarray | None = None) -> list[dict]:
    """The ceiling procedure: solve the m-piece minimax for growing m."""
    rows = []
    carried = seed_from
    for m in ms:
        t0 = time.time()
        inits = []
        if carried is not None and m % len(carried) == 0:
            inits.append(upsample(carried, m // len(carried)))
        # the naive split, A = the first half
        blk = np.zeros(m)
        blk[: m // 2] = 1.0
        inits.append(blk)
        # a smooth ramp, the shape Haugland-style constructions resemble
        x = (np.arange(m) + 0.5) / m
        inits.append(_repair_mass(np.clip(1.2 - 1.4 * x, 0, 1), m / 2))
        # random restarts are cheap at small m and dominate the cost at large
        # m, where the upsampled carry is already a good start
        n_rand = max(1, starts // max(1, m // 32))
        for _ in range(n_rand):
            inits.append(_repair_mass(rng.random(m), m / 2))

        best_f, best_v = None, np.inf
        for f0 in inits:
            f, v = _epigraph_solve(np.asarray(f0, dtype=float))
            if v < best_v:
                best_f, best_v = f, v
        elapsed = time.time() - t0
        rows.append({
            "m": m,
            "value": best_v,
            "seconds": elapsed,
            "n_starts": len(inits),
            "grid_sufficiency_defect": check_grid_sufficiency(best_f),
            "f": [float(x) for x in best_f],
        })
        carried = best_f
        print(f"  m={m:4d}  value={best_v:.9f}  {elapsed:6.2f}s  "
              f"gap_to_haugland2016={best_v - PUBLISHED['upper_haugland_2016']:+.6f}",
              flush=True)
    return rows


# ---------------------------------------------------------------------------
# C. the acceptance step, in exact arithmetic
# ---------------------------------------------------------------------------

def exact_value(f_rational: list[Fraction], m: int) -> Fraction:
    """max_j h_j computed in Q, with no floating point anywhere."""
    g = [Fraction(1) - x for x in f_rational]
    best = Fraction(0)
    for j in range(-(m - 1), m):
        acc = Fraction(0)
        for i in range(m):
            k = i - j
            if 0 <= k < m:
                acc += f_rational[i] * g[k]
        val = Fraction(2, m) * acc
        if val > best:
            best = val
    return best


def rationalise(f: np.ndarray, denom: int) -> list[Fraction]:
    """Round each bin height to a multiple of 1/denom, then repair the mass
    constraint exactly in Q so the accepted object is genuinely feasible."""
    m = len(f)
    num = [int(round(x * denom)) for x in f]
    num = [min(max(v, 0), denom) for v in num]
    target = m * denom // 2          # sum of numerators for (2/m) sum f = 1
    # nudge numerators, largest-residual first, until the mass is exact
    while sum(num) != target:
        diff = target - sum(num)
        step = 1 if diff > 0 else -1
        order = np.argsort(-(f * denom - np.array(num)) * step)
        moved = False
        for i in order:
            if 0 <= num[i] + step <= denom:
                num[i] += step
                moved = True
                break
        if not moved:
            raise RuntimeError("cannot repair mass at this denominator")
    return [Fraction(v, denom) for v in num]


# ---------------------------------------------------------------------------
# D. the lower-bound family: the averaging skeleton
# ---------------------------------------------------------------------------
#
# Any lower bound on inf_f sup_t h_f(t) has to survive every f, so it cannot
# be a construction.  The one move available is averaging: for any probability
# density w on the shift axis,
#
#     sup_t h_f(t)  >=  int w(t) h_f(t) dt  =  <f, w*1_{[0,2]}> - <f, w*f>.
#
# The first term is linear in f and easy.  The second is the quadratic term
# and is the entire difficulty: bounding it is what a Fourier argument buys.
#
# We compute two things.
#
#   D1  The plainest weight, w uniform on the whole shift range [-2,2].  Then
#       int w h = (1/4) int int f(x) g(y) = 1/4 exactly, for every f.  So
#       C >= 1/4.  Exact, unconditional, and 0.129 below the published bound.
#
#   D2  The obstruction that stops the naive Fourier bound.  Writing
#       <f, w*f> = int what(xi) |fhat(xi)|^2 and using |fhat|^2 <= ... with
#       0 <= f <= 1 gives <f, w*f> <= (sup what) ||f||_2^2 <= sup what.  But
#       w >= 0 with int w = 1 forces what(0) = 1, so sup what = 1 always and
#       the bound reads sup h >= <f, w*1> - 1 <= 0.  Vacuous for every w.
#       This is measured below rather than only argued: we evaluate both sides
#       for a family of weights and show the bound never leaves the negatives.
#
#   D3  What the dual could give if the quadratic term were handled: for a
#       given w, the honest quantity is min_f int w h, a nonconvex quadratic
#       minimisation.  We evaluate it from above by local minimisation, which
#       is an upper estimate of the best bound that weight could ever yield.
#       Reported as MEASURED and explicitly not a proof.


def uniform_average_bound_exact() -> Fraction:
    """D1: the exact value of the uniform-weight averaging bound."""
    # int_{-2}^{2} h_f(t) dt = (int f)(int g) = 1 * 1 = 1; the shift range has
    # length 4; so the average is 1/4 for every admissible f.
    return Fraction(1, 4)


def naive_fourier_bound_is_vacuous(rng: np.random.Generator, m: int = 64,
                                   n_weights: int = 200) -> dict:
    """D2: measure sup_xi what over random admissible weights, and the value
    of the resulting bound.  what(0) = 1 for every w >= 0 with int w = 1, so
    the bound <f, w*1> - sup what can never be positive."""
    worst = -np.inf
    sup_hats = []
    bounds = []
    for _ in range(n_weights):
        w = rng.random(4 * m)
        w /= w.sum()
        hat = np.fft.rfft(w).real          # unnormalised: hat[0] = sum w = 1
        sup_hat = float(np.abs(np.fft.rfft(w)).max())
        sup_hats.append(sup_hat)
        # <f, w*1> <= int f = 1 for any admissible f, so the bound is at most
        # 1 - sup_hat <= 0.
        b = 1.0 - sup_hat
        bounds.append(b)
        worst = max(worst, b)
    return {
        "n_weights": n_weights,
        "min_sup_what": float(np.min(sup_hats)),
        "max_bound": float(worst),
        # 1e-12 is float slack on what(0) = sum w = 1, not signal
        "any_positive": bool(worst > 1e-12),
    }


def dual_potential(rng: np.random.Generator, m: int, w_kind: str,
                   starts: int = 12) -> dict:
    """D3: for a fixed weight profile w on the shift grid, estimate
    min_f sum_j w_j h_j(f) from above by local minimisation."""
    n_shifts = 2 * m - 1
    js = np.arange(n_shifts) - (m - 1)
    t = 2.0 * js / m
    if w_kind == "uniform":
        w = np.ones(n_shifts)
    elif w_kind == "tent":
        w = np.maximum(0.0, 1.0 - np.abs(t) / 2.0)
    elif w_kind == "gauss":
        w = np.exp(-(t ** 2) / 0.5)
    elif w_kind == "edge":
        w = np.abs(t) / 2.0
    else:
        raise ValueError(w_kind)
    w = w / w.sum()

    target = m / 2.0

    def val(f):
        return float(w @ overlaps(f))

    best = np.inf
    for s in range(starts):
        f0 = _repair_mass(rng.random(m), target) if s else np.concatenate(
            [np.ones(m // 2), np.zeros(m - m // 2)])
        res = minimize(
            lambda z: val(np.clip(z, 0, 1)),
            f0, method="SLSQP",
            bounds=[(0.0, 1.0)] * m,
            constraints=[{"type": "eq",
                          "fun": lambda z: np.array([z.sum() - target]),
                          "jac": lambda z: np.ones((1, m))}],
            options={"maxiter": 250, "ftol": 1e-12},
        )
        f = _repair_mass(np.clip(res.x, 0, 1), target)
        best = min(best, val(f))
    return {"weight": w_kind, "m": m, "upper_estimate_of_dual_value": best}


# ---------------------------------------------------------------------------
# the guard, and its power
# ---------------------------------------------------------------------------
#
# Every number in front B and front C rests on one step: that
#
#     sup over real t of h_f(t)  =  max over the integer shift grid.
#
# If the shift enumeration is wrong the reported value is too SMALL, which is
# the dangerous direction here: an upper bound on C that is too small is a
# claimed improvement on Haugland.  So the enumeration deserves a guard, and
# the guard deserves a mutant.
#
# GUARD.  grid_sufficiency_defect(f, evaluator) evaluates h_f on a shift grid
# refined by a factor of 8 using the full reference correlation, and subtracts
# the maximum the evaluator under test reported.  A sound evaluator gives 0.
#
# The mutants below are the enumeration bugs that would produce a too-small
# value.  Run with `--mutant`.


def reference_sup(f: np.ndarray, sub: int = 8) -> float:
    return float(overlaps_fine(f, sub).max())


def grid_sufficiency_defect(f: np.ndarray, evaluator, sub: int = 8) -> float:
    return reference_sup(f, sub) - float(evaluator(f))


def _eval_sound(f):
    return overlaps(f).max()


def _eval_nonneg_shifts_only(f):
    m = len(f)
    return overlaps(f)[m - 1:].max()


def _eval_every_other_shift(f):
    return overlaps(f)[::2].max()


def _eval_interior_only(f):
    m = len(f)
    return overlaps(f)[m // 2: -(m // 2)].max()


MUTANTS = {
    "sound (negative control)": _eval_sound,
    "enumerate only shifts j >= 0": _eval_nonneg_shifts_only,
    "enumerate every other shift": _eval_every_other_shift,
    "drop the outer half of the shift range": _eval_interior_only,
}


def mutant_run(rng: np.random.Generator, m: int = 24, trials: int = 40) -> dict:
    """Demonstrate the guard's power: each planted enumeration fault must
    make the defect strictly positive on at least one admissible f."""
    fs = [_repair_mass(rng.random(m), m / 2) for _ in range(trials)]
    rows = []
    for label, ev in MUTANTS.items():
        defects = [grid_sufficiency_defect(f, ev) for f in fs]
        rows.append({
            "mutant": label,
            "max_defect": float(np.max(defects)),
            "n_trials_with_positive_defect": int(sum(d > 1e-12 for d in defects)),
            "fired": bool(np.max(defects) > 1e-12),
        })
        print(f"  {label:42s}  max_defect={np.max(defects):.6f}  "
              f"fired={np.max(defects) > 1e-12}", flush=True)
    sound = rows[0]
    planted = rows[1:]
    fired = [r["mutant"] for r in planted if r["fired"]]
    missed = [r["mutant"] for r in planted if not r["fired"]]
    demonstrated = (not sound["fired"]) and bool(fired)
    print(f"  guard power demonstrated: {demonstrated}  "
          f"({len(fired)}/{len(planted)} planted faults caught)")
    if missed:
        print(f"  known miss: {missed}")
    return {
        "m": m, "trials": trials, "rows": rows,
        "guard_power_demonstrated": demonstrated,
        "caught": fired,
        "known_misses": missed,
    }


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--mutant", action="store_true",
                    help="run only the guard demonstration")
    args = ap.parse_args()

    rng = np.random.default_rng(0x828C8B)

    if args.mutant:
        print("GUARD: grid_sufficiency_defect, and the enumeration faults it "
              "must catch")
        res = mutant_run(rng)
        path = HERE / "guard_mutants.json"
        path.write_text(json.dumps(res, indent=2) + "\n")
        print(f"wrote {path}")
        return
    out: dict = {
        "hunt": "r_828c8b",
        "run_id": "f0bbb14a-833d-456a-befa-2e4f74ba6947",
        "issue": "https://github.com/teal-sea/zeta-lab/issues/111",
        "published_reference_values": PUBLISHED,
        "environment": {
            "python": sys.version.split()[0],
            "numpy": np.__version__,
            "platform": platform.platform(),
        },
        "quick": bool(args.quick),
    }

    print("A. discrete truth: M(n) by exhaustive search")
    t0 = time.time()
    n_max = 8 if args.quick else 10
    discrete = []
    for n in range(2, n_max + 1):
        r = minimum_overlap_exact(n)
        discrete.append(r)
        print(f"  n={n:2d}  M(n)={r['M']}  M(n)/n={r['M_over_n']:.4f}", flush=True)
    out["A_discrete"] = {"rows": discrete, "seconds": time.time() - t0}

    print("\nB. the ceiling: the m-piece minimax")
    ms = [4, 8, 16, 32] if args.quick else [4, 8, 16, 32, 64, 128]
    starts = 4 if args.quick else 10
    rows = ceiling_sweep(ms, starts, rng)
    out["B_ceiling"] = {
        "rows": [{k: v for k, v in r.items() if k != "f"} for r in rows],
        "best_f_by_m": {str(r["m"]): r["f"] for r in rows},
    }

    best_row = min(rows, key=lambda r: r["value"])
    print(f"\n  ceiling of this parameterisation at m<={max(ms)}: "
          f"{best_row['value']:.9f} (m={best_row['m']})")

    print("\nC. the acceptance step in exact arithmetic")
    acc = []
    for r in rows[-3:]:
        m = r["m"]
        f = np.array(r["f"])
        for denom in (2 * m, 20 * m):
            try:
                fr = rationalise(f, denom)
            except RuntimeError as exc:
                acc.append({"m": m, "denom": denom, "error": str(exc)})
                continue
            t1 = time.time()
            ev = exact_value(fr, m)
            acc.append({
                "m": m,
                "denom": denom,
                "exact_value_float": float(ev),
                "exact_value_num": str(ev.numerator),
                "exact_value_den": str(ev.denominator),
                "float_value": r["value"],
                "rounding_penalty": float(ev) - r["value"],
                "seconds": time.time() - t1,
            })
            print(f"  m={m:4d} denom={denom:6d}  exact={float(ev):.9f}  "
                  f"penalty_vs_float={float(ev) - r['value']:+.3e}", flush=True)
    out["C_exact_acceptance"] = acc
    valid = [a for a in acc if "exact_value_float" in a]
    if valid:
        best_exact = min(valid, key=lambda a: a["exact_value_float"])
        out["C_best_exact_upper_bound"] = best_exact
        print(f"  best exact upper bound on C: {best_exact['exact_value_float']:.9f}"
              f"  = {best_exact['exact_value_num']}/{best_exact['exact_value_den']}")

    print("\nD. the lower-bound family")
    d1 = uniform_average_bound_exact()
    print(f"  D1 uniform-weight averaging bound (exact): C >= {d1} = {float(d1)}")
    d2 = naive_fourier_bound_is_vacuous(rng, m=32 if args.quick else 64)
    print(f"  D2 naive Fourier bound: min sup|what| over {d2['n_weights']} weights "
          f"= {d2['min_sup_what']:.6f}; best resulting bound = {d2['max_bound']:.6f}; "
          f"any positive = {d2['any_positive']}")
    d3 = []
    for kind in ("uniform", "tent", "gauss", "edge"):
        r = dual_potential(rng, 32 if args.quick else 48, kind,
                           starts=6 if args.quick else 12)
        d3.append(r)
        print(f"  D3 weight={kind:8s} upper estimate of min_f <w,h> = "
              f"{r['upper_estimate_of_dual_value']:.6f}", flush=True)
    out["D_lower"] = {
        "D1_uniform_exact": {"num": d1.numerator, "den": d1.denominator,
                             "float": float(d1)},
        "D2_naive_fourier_vacuous": d2,
        "D3_dual_potential": d3,
    }

    (HERE / "results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"\nwrote {HERE / 'results.json'}")


if __name__ == "__main__":
    main()
