"""ARM B: window asymptotics for the depth-1 damage kernel.

Bounded question (support run 5418c63e, parent run 872d7dce / hunt r_c7f779):

    D(a, s) = -Re ghat(a + i s)^2,   ghat(z) = int_{-1/2}^{1/2} cos(sqrt2 t) e^{zt} dt.

A *depth-1 damage window* is a maximal interval of `s` on which `D(1, s) > 0`.
Locate the window edges out to `s ~ 1e5`; decide whether the window centres
minus `2 pi d` drift linearly, converge to a constant, or do something else;
and decide whether every `2 pi d` lies inside a window, reporting the minimum
distance from `2 pi d` to the nearest edge.

Run:  .venv/bin/python hunts/support_5418c63e/probe_arm_b.py [--quick]

`--quick` scans to s = 2000 instead of 1e5 (a few seconds).  The full run is
a couple of minutes.  Writes results.json next to this file.

Nothing here bears on RH (docs/08).  Everything below is *measured* in double
precision with mpmath spot checks at 50 digits, except the asymptotic series,
which is *derived* and then checked numerically.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import os
import sys
import time

import mpmath as mp
import numpy as np

SQ2 = math.sqrt(2.0)
# ghat(z) = [alpha z sinh(z/2) + beta cosh(z/2)] / (z^2 + 2)   -- exact, derived
# in the docstring of `asymptotics()` below.
ALPHA = 2 * math.cos(1 / SQ2)
BETA = 2 * SQ2 * math.sin(1 / SQ2)

HERE = os.path.dirname(os.path.abspath(__file__))
TWO_PI = 2 * math.pi


# --------------------------------------------------------------------------
# the kernel


def ghat_closed(z):
    """`[alpha z sinh(z/2) + beta cosh(z/2)] / (z^2+2)`, vectorised."""
    return (ALPHA * z * np.sinh(z / 2) + BETA * np.cosh(z / 2)) / (z * z + 2)


def damage(a, s):
    """`D(a,s) = -Re ghat(a+is)^2`.  `s` may be an array."""
    z = a + 1j * np.asarray(s, dtype=float)
    g = ghat_closed(z)
    return -(g * g).real


def damage_scalar(a, s):
    z = complex(a, s)
    g = (ALPHA * z * cmath.sinh(z / 2) + BETA * cmath.cosh(z / 2)) / (z * z + 2)
    return float(-(g * g).real)


def damage_mp(a, s, dps=50):
    """High-precision `D(a,s)` by the two-term form of `gram_form._ghat`,
    a *different code path* from `ghat_closed` (no algebraic recombination)."""
    with mp.workdps(dps):
        z = mp.mpf(a) + 1j * mp.mpf(s)
        n2 = mp.sqrt(2)
        zp, zm = z + 1j * n2, z - 1j * n2
        g = mp.sinh(zp / 2) / zp + mp.sinh(zm / 2) / zm
        return -(g * g).real


# --------------------------------------------------------------------------
# the derived asymptotics


def asymptotics():
    """The large-`s` expansion of `D(a,s)`, derived, returned as coefficients.

    Writing `nu = sqrt2`, `sinh(zp/2) + sinh(zm/2) = 2 cos(nu/2) sinh(z/2)` and
    `sinh(zm/2) - sinh(zp/2) = -2i cosh(z/2) sin(nu/2)`, so putting the two
    terms over the common denominator `z^2 + nu^2` gives the *exact* form

        ghat(z) = [alpha z sinh(z/2) + beta cosh(z/2)] / (z^2 + 2),
        alpha = 2 cos(1/sqrt2),  beta = 2 sqrt2 sin(1/sqrt2) = 2 A.

    Squaring and using `sinh^2 = (cosh z - 1)/2`, `cosh^2 = (cosh z + 1)/2`:

        ghat^2 = [ (alpha^2/2) z^2 (cosh z - 1) + alpha beta z sinh z
                   + (beta^2/2)(cosh z + 1) ] / (z^2+2)^2.

    Expanding `(z^2+2)^{-2} = z^{-4}(1 - 4 z^{-2} + ...)` and then `z^{-n}` for
    `z = a + i s` in powers of `1/s`, and taking `D = -Re ghat^2`:

        D(a,s) = (alpha^2/2)(cosh a cos s - 1) / s^2
               + alpha C sin s / s^3
               + (E cos s + F) / s^4  +  O(s^-5),

        C = beta cosh a - alpha a sinh a,
        E = cosh a (alpha^2 - beta^2)/2 + 3 alpha beta sinh a
            - (3 alpha^2 a^2 / 2)(cosh a) ... (a = 1 substituted below),
        F = -(alpha^2 + beta^2)/2 + (3 alpha^2 a^2/2).

    Only `a = 1` is needed here, and the `a=1` coefficients are what this
    function returns.  The leading term is `2 pi`-periodic with maxima exactly
    at `s in 2 pi Z`, confirming the caller's hint; the `1/s^3` term is the
    first correction and it is an *odd* (sin) perturbation, which shifts the
    whole profile rather than widening it.
    """
    a = 1.0
    ch, sh = math.cosh(a), math.sinh(a)
    c2 = ALPHA ** 2 / 2
    C = BETA * ch - ALPHA * a * sh
    # 1/s^4 coefficients, with a = 1 (see derivation in the module notes)
    E = ch * (ALPHA ** 2 - BETA ** 2) / 2 + 3 * ALPHA * BETA * sh
    F = -(ALPHA ** 2 + BETA ** 2) / 2
    return {"c2": c2, "C": C, "E": E, "F": F, "cosh_a": ch, "sinh_a": sh}


def damage_asym(s, order=4):
    k = asymptotics()
    t = k["c2"] * (k["cosh_a"] * np.cos(s) - 1) / s ** 2
    if order >= 3:
        t = t + ALPHA * k["C"] * np.sin(s) / s ** 3
    if order >= 4:
        t = t + (k["E"] * np.cos(s) + k["F"]) / s ** 4
    return t


def predicted_edge_shift():
    """Edge law derived from the expansion.  Returns `(w0, K, W2)`.

    Put `s = 2 pi d + x` and multiply `D` by `s^2`; the root equation for the
    window edges becomes, with `S = 2 pi d + x` and `c2 = alpha^2/2`,

        f(x) = c2 (cosh1 cos x - 1) + alpha C sin x / S + (E cos x + F)/S^2 = 0.

    **`S` is the running variable, not `2 pi d`.**  Expanding `1/S` about
    `1/s` (`s := 2 pi d`) produces an extra `-alpha C x sin x / s^2`, which is
    the same order as the `E, F` term and must be kept; dropping it gives a
    width constant 43% too large (that error was made and caught here).

    Zeroth order: `cos x0 = sech 1`, i.e. `x0 = +/- w0`, `w0 = arccos(sech 1)`.

    First order: `dx = -(alpha C / s) sin x0 / (-c2 cosh1 sin x0)
                     = alpha C / (c2 cosh1 s) =: K/s`, **the same at both
    edges** because the `sin x0` cancels.  So at this order the window keeps
    its width and *translates* by `K/s`.

    Second order: with `f0'' = -c2`, `f1' = alpha C / cosh1` and the effective
    `f2(x0) = E sech1 + F - alpha C w0 tanh1`, the bracket

        Geff = -(c2/2) K^2 + (alpha C / cosh1) K + E sech1 + F
               - alpha C w0 tanh1

    is *even* in `x0`, so the two second-order shifts are `+/- Geff/(c2 sinh1)`:
    they cancel in the centre and add in the width.  Hence

        centre(d) - 2 pi d = K/s + O(s^-3)          (no 1/s^2 term)
        half_width(d)      = w0 + W2/s^2 + O(s^-3),  W2 = Geff/(c2 sinh1)
        margin(d)          = w0 - K/s + W2/s^2 + O(s^-3).
    """
    k = asymptotics()
    ch, sh = k["cosh_a"], k["sinh_a"]
    c2 = k["c2"]
    w0 = math.acos(1.0 / ch)
    K = ALPHA * k["C"] / (c2 * ch)
    Geff = (-(c2 / 2) * K ** 2 + (ALPHA * k["C"] / ch) * K
            + k["E"] / ch + k["F"] - ALPHA * k["C"] * w0 * math.tanh(1.0))
    W2 = Geff / (c2 * sh)
    return w0, K, W2


# --------------------------------------------------------------------------
# the exact rational form ON the lattice


def lattice_cubic():
    """`D(1, s)` restricted to `s in 2 pi Z` is an explicit rational function.

    At `s = 2 pi d` we have `cos s = 1`, `sin s = 0`, so `cosh z = cosh 1` and
    `sinh z = sinh 1` are *real* at `z = 1 + i s`.  Then

        ghat^2 = [ p' z^2 + q' z + r' ] / (z^2+2)^2,
        p' = (alpha^2/2)(cosh 1 - 1),  q' = alpha beta sinh 1,
        r' = (beta^2/2)(cosh 1 + 1),

    and with `z = 1 + is`, `|(z^2+2)^2| ^2 = (s^4 - 2 s^2 + 9)^2`, taking
    `-Re` gives the **exact identity**

        D(1, 2 pi d) = P(s) / (s^4 - 2 s^2 + 9)^2,     s = 2 pi d,
        P(s) = p u^3 - (3p - 3q + r) u^2 - (5p + 2q - 10r) u - 9(p+q+r),
        u = s^2,

    with the constants in closed form

        p = (1 + cos sqrt2)(cosh 1 - 1)
        q = 2 sqrt2 sin(sqrt2) sinh 1
        r = 2 (1 - cos sqrt2)(cosh 1 + 1).

    `s^4 - 2s^2 + 9 = (s^2-1)^2 + 8 > 0`, so the sign of `D` on the lattice is
    the sign of the cubic `P` in `u = s^2`.  Numerically its coefficients are

        P(u) = 0.62777 u^3 + 3.67360 u^2 + 33.22460 u - 73.83674,

    i.e. **every coefficient but the constant is positive**, so `P` is strictly
    increasing on `u >= 0` and has exactly one nonnegative root,
    `u* = 1.77074902` (`s* = 1.33069494`).  Since `u = (2 pi d)^2 >= 4 pi^2 =
    39.478 > u*` for every integer `d >= 1`,

        D(1, 2 pi d) > 0  for every d >= 1,

    *derived*, with no horizon.  (`d = 0` is the exception: `D(1,0) < 0`.  It
    does not arise in `P(T,y)`, whose sum runs over `p != q`.)
    """
    p = (1 + math.cos(SQ2)) * (math.cosh(1) - 1)
    q = 2 * SQ2 * math.sin(SQ2) * math.sinh(1)
    r = 2 * (1 - math.cos(SQ2)) * (math.cosh(1) + 1)
    coeffs = [p, -(3 * p - 3 * q + r), -(5 * p + 2 * q - 10 * r),
              -9 * (p + q + r)]
    return p, q, r, coeffs


def damage_on_lattice(s):
    p, q, r, co = lattice_cubic()
    u = s * s
    P = ((co[0] * u + co[1]) * u + co[2]) * u + co[3]
    return P / (u * u - 2 * u + 9) ** 2


# --------------------------------------------------------------------------
# root finding


def bisect(a, lo, hi, iters=100):
    flo = damage_scalar(a, lo)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if mid == lo or mid == hi:
            break
        fm = damage_scalar(a, mid)
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return 0.5 * (lo + hi)


def scan_sign_changes(a, s0, s1, step, chunk=2_000_000):
    """Every bracketing interval of a sign change of `D(a, .)` on [s0, s1]."""
    brackets = []
    n_total = int(math.ceil((s1 - s0) / step)) + 1
    prev_s = None
    prev_v = None
    start = 0
    while start < n_total:
        n = min(chunk, n_total - start)
        idx = np.arange(start, start + n, dtype=np.float64)
        s = s0 + idx * step
        v = damage(a, s)
        if prev_s is not None:
            s = np.concatenate(([prev_s], s))
            v = np.concatenate(([prev_v], v))
        sgn = np.signbit(v)
        flips = np.nonzero(sgn[1:] != sgn[:-1])[0]
        for i in flips:
            brackets.append((float(s[i]), float(s[i + 1])))
        prev_s, prev_v = float(s[-1]), float(v[-1])
        start += n
    return brackets


# --------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--step", type=float, default=0.002)
    args = ap.parse_args()

    a = 1.0
    s_max = 2000.0 if args.quick else 100_000.0
    s_min = 1e-6
    t0 = time.time()

    out = {
        "question": "depth-1 damage windows: edges, centre drift, and whether "
                    "every 2*pi*d lies inside one",
        "kernel": "D(1,s) = -Re ghat(1+is)^2",
        "grade": "measured (double precision scan, mpmath dps=50 spot checks); "
                 "the asymptotic series is derived and checked",
        "scan": {"s_min": s_min, "s_max": s_max, "step": args.step},
    }

    # -- 0. code-path cross-check of the vectorised kernel ------------------
    xchk = 0.0
    for s in (0.5, 6.5, 61.0, 617.0, 6171.0, 61713.0, 99999.5):
        d1 = damage_scalar(a, s)
        d2 = float(damage_mp(a, s))
        xchk = max(xchk, abs(d1 - d2) / abs(d2))
    out["kernel_cross_check_worst_rel"] = xchk
    print(f"kernel closed form vs mpmath two-term form: worst rel {xchk:.3e}")

    # and against the tree's own implementation, read-only
    try:
        sys.path.insert(0, os.path.join(HERE, "..", "frontier_math"))
        import gram_form  # noqa: E402
        gchk = 0.0
        for s in (0.5, 6.5, 61.0, 617.0, 6171.0, 61713.0):
            for aa in (0.0, 0.5, 1.0, 2.0):
                ref = gram_form.damage(aa, s)
                gchk = max(gchk, abs(damage_scalar(aa, s) - ref)
                           / max(1e-300, abs(ref)))
        out["vs_gram_form_damage_worst_rel"] = gchk
        print(f"closed form vs hunts/frontier_math/gram_form.damage: "
              f"worst rel {gchk:.3e}")
    except Exception as exc:            # pragma: no cover - convenience only
        out["vs_gram_form_damage_worst_rel"] = f"unavailable: {exc}"

    # -- 1. the derived asymptotics, checked --------------------------------
    k = asymptotics()
    w0, K, W2 = predicted_edge_shift()
    rows = []
    for s in (30.0, 100.0, 1000.0, 10_000.0, 100_000.0):
        d = damage_scalar(a, s)
        rows.append({"s": s, "D": d,
                     "rel_err_order2": abs(damage_asym(s, 2) - d) / abs(d),
                     "rel_err_order3": abs(damage_asym(s, 3) - d) / abs(d),
                     "rel_err_order4": abs(damage_asym(s, 4) - d) / abs(d)})
    out["asymptotics"] = {
        "form": "D(1,s) = (alpha^2/2)(cosh1 cos s - 1)/s^2 + alpha C sin s/s^3 "
                "+ (E cos s + F)/s^4 + O(s^-5)",
        "alpha": ALPHA, "beta": BETA,
        "C": k["C"], "E": k["E"], "F": k["F"],
        "leading_half_width_w0": w0,
        "leading_half_width_w0_closed_form": "arccos(sech 1)",
        "predicted_shift_coefficient_K": K,
        "predicted_width_coefficient_W2": W2,
        "predicted_shift": "centre(d) - 2*pi*d = K/s + O(s^-3), s = 2*pi*d",
        "predicted_width": "half_width(d) = w0 + W2/s^2 + O(s^-3)",
        "checks": rows,
    }
    print(f"derived: w0 = arccos(sech 1) = {w0:.12f}, K = {K:.12f}, "
          f"W2 = {W2:.12f}")

    # -- 1b. the exact lattice cubic ---------------------------------------
    p_, q_, r_, co = lattice_cubic()
    lat_chk = []
    for d in (1, 2, 3, 10, 100, 4000, 15915, 10 ** 6, 10 ** 9):
        s = TWO_PI * d
        ex = damage_scalar(a, s) if d <= 10 ** 6 else None
        rat = damage_on_lattice(s)
        row = {"d": d, "s": s, "D_rational": rat}
        if ex is not None:
            row["D_direct"] = ex
            row["rel"] = abs(ex - rat) / abs(ex)
        lat_chk.append(row)
    # discriminant of a u^3 + b u^2 + c u + e
    A_, B_, C_, E_ = co
    disc = (18 * A_ * B_ * C_ * E_ - 4 * B_ ** 3 * E_ + B_ ** 2 * C_ ** 2
            - 4 * A_ * C_ ** 3 - 27 * A_ ** 2 * E_ ** 2)
    rts = np.roots(co)
    real_rts = sorted(float(t.real) for t in rts if abs(t.imag) < 1e-9)
    u_star = real_rts[-1]
    s_star = math.sqrt(u_star) if u_star > 0 else 0.0
    out["lattice_cubic"] = {
        "identity": "D(1, 2*pi*d) = P(s)/(s^4-2s^2+9)^2 with "
                    "P(s) = p u^3 - (3p-3q+r) u^2 - (5p+2q-10r) u - 9(p+q+r), "
                    "u = s^2",
        "p_closed_form": "(1+cos sqrt2)(cosh 1 - 1)", "p": p_,
        "q_closed_form": "2 sqrt2 sin(sqrt2) sinh 1", "q": q_,
        "r_closed_form": "2 (1-cos sqrt2)(cosh 1 + 1)", "r": r_,
        "cubic_coefficients_in_u": co,
        "coefficients_positive_except_constant":
            bool(co[0] > 0 and co[1] > 0 and co[2] > 0 and co[3] < 0),
        "strictly_increasing_on_u_ge_0_so_one_nonneg_root": True,
        "u_at_d_equals_1": TWO_PI ** 2,
        "discriminant": disc,
        "n_real_roots": len(real_rts),
        "largest_real_root_u": u_star,
        "s_star": s_star,
        "s_star_over_2pi": s_star / TWO_PI,
        "conclusion": "leading coefficient p > 0 and the cubic has one real "
                      "root, so D(1, 2*pi*d) > 0 for every s = 2*pi*d > "
                      "%.12f, i.e. for every integer d >= 1, with no horizon"
                      % s_star,
        "checks": lat_chk,
    }
    print(f"lattice cubic: one real root at s* = {s_star:.9f} "
          f"(= {s_star/TWO_PI:.6f} periods); disc = {disc:.6e}")
    print(f"  => D(1, 2*pi*d) > 0 for every d >= 1, derived, no horizon")

    # -- 2. the scan --------------------------------------------------------
    print(f"scanning D(1,s) on [{s_min}, {s_max}] at step {args.step} ...")
    brackets = scan_sign_changes(a, s_min, s_max, args.step)
    roots = np.array([bisect(a, lo, hi) for lo, hi in brackets])
    print(f"  {len(roots)} sign changes in {time.time()-t0:.1f}s")

    # windows = maximal intervals where D > 0.  D alternates sign across the
    # simple roots, so the window left-edges are the roots at which D turns
    # positive: index 0 if D < 0 at s_min, index 1 otherwise.
    d_at_start = damage_scalar(a, s_min)
    out["D_at_s_min"] = d_at_start
    out["window_open_at_s_min"] = bool(d_at_start > 0)
    first = 1 if d_at_start > 0 else 0
    windows = [(float(roots[i]), float(roots[i + 1]))
               for i in range(first, len(roots) - 1, 2)]
    # sanity: D must be positive at every window midpoint and negative between
    mids = np.array([0.5 * (l + r) for l, r in windows])
    out["window_midpoints_all_positive"] = bool((damage(a, mids) > 0).all())
    gaps = np.array([0.5 * (windows[i][1] + windows[i + 1][0])
                     for i in range(len(windows) - 1)])
    out["window_gaps_all_negative"] = bool((damage(a, gaps) < 0).all())
    out["n_sign_changes"] = int(len(roots))
    out["n_windows"] = len(windows)

    # expected: exactly 2 sign changes per 2*pi period at large s
    out["sign_changes_per_2pi"] = len(roots) / (s_max / TWO_PI)

    # -- 3. lattice points vs windows --------------------------------------
    W = np.array(windows)  # (n, 2)
    lefts, rights = W[:, 0], W[:, 1]
    d_max = int(math.floor(s_max / TWO_PI))
    lattice_rows = []
    worst_margin = None
    outside = []
    for d in range(0, d_max + 1):
        s = TWO_PI * d
        if s > s_max or s < s_min:
            if d == 0:
                lattice_rows.append({"d": 0, "s": 0.0,
                                     "D": damage_scalar(a, 0.0),
                                     "inside": bool(damage_scalar(a, 0.0) > 0),
                                     "note": "d=0 is excluded from P by p!=q"})
                continue
            continue
        j = int(np.searchsorted(lefts, s) - 1)
        inside = bool(0 <= j < len(W) and lefts[j] < s < rights[j])
        if not inside:
            outside.append(d)
            lattice_rows.append({"d": d, "s": s, "D": damage_scalar(a, s),
                                 "inside": False})
            continue
        L, R = float(lefts[j]), float(rights[j])
        centre = 0.5 * (L + R)
        margin = min(s - L, R - s)
        rec = {"d": d, "s": s, "left": L, "right": R, "centre": centre,
               "half_width": 0.5 * (R - L), "centre_minus_2pid": centre - s,
               "margin": margin, "inside": True}
        if worst_margin is None or margin < worst_margin[0]:
            worst_margin = (margin, d)
        if d in (1, 2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 4000,
                 8000, 15915) or d <= 5:
            lattice_rows.append(rec)
        if d == 0:
            continue
    # keep the full arrays for the fit
    all_d, all_off, all_margin, all_hw = [], [], [], []
    for d in range(1, d_max + 1):
        s = TWO_PI * d
        if s > s_max:
            break
        j = int(np.searchsorted(lefts, s) - 1)
        if not (0 <= j < len(W) and lefts[j] < s < rights[j]):
            continue
        L, R = float(lefts[j]), float(rights[j])
        all_d.append(d)
        all_off.append(0.5 * (L + R) - s)
        all_margin.append(min(s - L, R - s))
        all_hw.append(0.5 * (R - L))
    all_d = np.array(all_d, dtype=float)
    all_off = np.array(all_off)
    all_margin = np.array(all_margin)
    all_hw = np.array(all_hw)

    out["lattice"] = {
        "d_max": d_max,
        "n_checked": int(all_d.size),
        "n_outside_any_window": len(outside),
        "first_d_outside": outside[0] if outside else None,
        "d_outside_list_head": outside[:20],
        "min_margin": float(all_margin.min()),
        "argmin_margin_d": int(all_d[int(np.argmin(all_margin))]),
        "max_margin": float(all_margin.max()),
        "margin_at_largest_d": float(all_margin[-1]),
        "rows": lattice_rows,
    }

    # -- 4. the drift verdict ----------------------------------------------
    s_lat = TWO_PI * all_d
    prod = all_off * s_lat          # should tend to K if offset ~ K/s
    slope_fit = np.polyfit(all_d, all_off, 1)  # linear-in-d test
    tail = all_d > max(10.0, 0.1 * all_d[-1])
    out["drift"] = {
        "verdict": None,   # filled below
        "offset_first": {"d": int(all_d[0]), "offset": float(all_off[0])},
        "offset_last": {"d": int(all_d[-1]), "offset": float(all_off[-1])},
        "offset_times_s_first": float(prod[0]),
        "offset_times_s_last": float(prod[-1]),
        "offset_times_s_tail_mean": float(prod[tail].mean()),
        "offset_times_s_tail_std": float(prod[tail].std()),
        "predicted_K": K,
        "linear_fit_slope_per_d": float(slope_fit[0]),
        "linear_fit_intercept": float(slope_fit[1]),
        "half_width_first": float(all_hw[0]),
        "half_width_last": float(all_hw[-1]),
        "half_width_w0_predicted": w0,
        "half_width_minus_w0_times_s2_last":
            float((all_hw[-1] - w0) * (TWO_PI * all_d[-1]) ** 2),
    }
    # classify
    lin = abs(slope_fit[0]) * all_d[-1]
    if lin > 1e-3 and abs(prod[-1] - K) > 0.5 * abs(K):
        verdict = "linear drift"
    elif abs(prod[tail].mean() - K) < 0.05 * abs(K):
        verdict = ("bounded, converging to 0 like K/s with "
                   "K = %.9f; the constant offset is 0" % K)
    else:
        verdict = "bounded but not matching the predicted K/s law"
    out["drift"]["verdict"] = verdict

    # -- 4b. the margin law -------------------------------------------------
    # the offset is positive, so the nearest edge is the LEFT one and
    #     margin(d) = half_width(d) - offset(d)  ~  w0 - K/s.
    pred = w0 - K / s_lat + W2 / s_lat ** 2
    hw_pred = w0 + W2 / s_lat ** 2
    out["margin_law"] = {
        "law": "margin(d) = half_width - offset = w0 - K/s + W2/s^2 + O(s^-3)",
        "w0": w0, "K": K, "W2": W2,
        "worst_abs_err_half_width_d_ge_10":
            float(np.abs(all_hw - hw_pred)[all_d >= 10].max()),
        "half_width_minus_w0_times_s2_at_d_1000":
            float((all_hw[999] - w0) * s_lat[999] ** 2)
            if all_d.size > 999 else None,
        "worst_abs_err_vs_law_d_ge_10":
            float(np.abs(all_margin - pred)[all_d >= 10].max()),
        "worst_abs_err_vs_law_all_d": float(np.abs(all_margin - pred).max()),
        "monotone_increasing_in_d":
            bool((np.diff(all_margin) > 0).all()),
        "first_ten": [{"d": int(all_d[i]), "margin": float(all_margin[i]),
                       "law": float(pred[i]),
                       "half_width": float(all_hw[i]),
                       "offset": float(all_off[i])}
                      for i in range(min(10, all_d.size))],
    }

    # -- 5. mpmath confirmation of the edges at selected d ------------------
    conf = []
    for d in [1, 2, 5, 100, 1000, min(d_max, 15915)]:
        s = TWO_PI * d
        j = int(np.searchsorted(lefts, s) - 1)
        if not (0 <= j < len(W) and lefts[j] < s < rights[j]):
            continue
        L, R = float(lefts[j]), float(rights[j])
        with mp.workdps(50):
            twopi_d = 2 * mp.pi * d
            f = lambda x: damage_mp(1.0, x, dps=50)
            Lm = mp.findroot(f, mp.mpf(L))
            Rm = mp.findroot(f, mp.mpf(R))
            conf.append({
                "d": d,
                "left_double": L, "left_mp": mp.nstr(Lm, 20),
                "right_double": R, "right_mp": mp.nstr(Rm, 20),
                "left_err": float(abs(Lm - L)), "right_err": float(abs(Rm - R)),
                "centre_minus_2pid_mp": mp.nstr((Lm + Rm) / 2 - twopi_d, 15),
                "margin_mp": mp.nstr(min(twopi_d - Lm, Rm - twopi_d), 15),
            })
    out["mp_confirmation"] = conf

    # -- 5b. the width constant W2, beyond the double-precision floor -------
    # half_width - w0 is ~W2/s^2, which is 4.5e-12 at d = 1e5: too small for
    # the double scan, so the edges are re-found at dps=60.
    w2_rows = []
    with mp.workdps(60):
        w0_mp = mp.acos(1 / mp.cosh(1))
        for d in (1000, 10_000, 100_000):
            s0 = 2 * mp.pi * d
            f = lambda t: damage_mp(1.0, s0 + t, dps=60)
            xp = mp.findroot(f, w0_mp)
            xm = mp.findroot(f, -w0_mp)
            hw = (xp - xm) / 2
            w2_rows.append({
                "d": d,
                "half_width_minus_w0": mp.nstr(hw - w0_mp, 10),
                "times_s2": mp.nstr((hw - w0_mp) * s0 * s0, 12),
                "derived_W2": W2,
                "offset_times_s": mp.nstr((xp + xm) / 2 * s0, 12),
            })
    out["W2_high_precision_check"] = w2_rows
    print("W2 check at dps=60: " + ", ".join(
        f"d={r['d']}: {r['times_s2']}" for r in w2_rows)
        + f"   derived {W2:.9f}")

    # -- 6. the small-s region, listed in full ------------------------------
    out["small_s_sign_changes"] = [float(r) for r in roots if r < 25.0]

    out["elapsed_s"] = time.time() - t0
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(out, fh, indent=2)

    # -- report -------------------------------------------------------------
    print()
    print(f"sign changes: {out['n_sign_changes']}  "
          f"(= {out['sign_changes_per_2pi']:.6f} per 2*pi period)")
    print(f"D(1,0) = {damage_scalar(a,0.0):.9f}  -> d=0 is NOT in a window")
    print(f"multiples of 2*pi with d>=1 checked: {int(all_d.size)}; "
          f"outside a window: {len(outside)}")
    print(f"min margin over d>=1: {all_margin.min():.9f} at d="
          f"{int(all_d[int(np.argmin(all_margin))])}")
    print(f"margin at d={int(all_d[-1])}: {all_margin[-1]:.9f}   "
          f"(w0 = {w0:.9f})")
    print(f"centre - 2*pi*d : {all_off[0]:.6e} at d={int(all_d[0])} -> "
          f"{all_off[-1]:.6e} at d={int(all_d[-1])}")
    print(f"(centre - 2*pi*d)*s : {prod[0]:.6f} -> {prod[-1]:.6f}   "
          f"predicted K = {K:.6f}")
    print(f"linear-in-d fit slope: {slope_fit[0]:.3e} per d")
    print(f"verdict: {verdict}")
    print(f"elapsed {out['elapsed_s']:.1f}s -> results.json")


if __name__ == "__main__":
    main()
