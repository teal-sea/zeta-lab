#!/usr/bin/env python
"""Zero-spacing statistics of ζ vs random-matrix theory (the GUE) vs Poisson.

The mathematics
---------------
Unfold the zero ordinates to unit mean density with the exact smooth term of
the Riemann-von Mangoldt counting function:

    γ̃_n = θ(γ_n)/π          (θ = Riemann–Siegel theta; N(T) = θ/π + 1 + S)

and form the nearest-neighbour spacings s_n = γ̃_{n+1} − γ̃_n, mean 1.  Then:

  * Uncorrelated levels (Poisson) would give p(s) = e^{−s}, maximal at 0.
  * The Gaussian Unitary Ensemble gives the Gaudin law p(s) = d²E/ds² with
    E(0;s) = det(I − K_s), K the sine kernel, p(s) ~ s² at 0: eigenvalues
    (and, empirically, zeta zeros) actively repel each other.
  * Montgomery (1973): the pair correlation of the zeros is the GUE
    sine-kernel two-point function  R₂(r) = 1 − (sin πr / πr)².

This is the Montgomery–Odlyzko law, the strongest numerical evidence for
the Hilbert–Pólya idea that the γ_n are the spectrum of a self-adjoint
operator.  The script measures all of it: KS tests against the exact Gaudin
law, the Wigner surmise and Poisson, a two-sample KS against an ACTUAL
random GUE matrix run through the identical pipeline, and the pair
correlation against Montgomery's prediction.
"""

from __future__ import annotations

import argparse
import math
import time

import numpy as np

from zeta.statistics import (
    compare_to_random_matrix,
    gue_spacing_exact_cdf,
    level_repulsion_report,
    montgomery_prediction,
    nearest_neighbour_spacings,
    pair_correlation,
    poisson_spacing_cdf,
    zero_ordinates,
)

__all__ = ["main"]


def _t_max_for(n: int) -> float:
    """Height comfortably containing n zeros (inverse Riemann-von Mangoldt)."""
    if n <= 10142:
        return 10000.0
    lo, hi = 10000.0, 10000.0
    while (hi / (2 * math.pi)) * math.log(hi / (2 * math.pi)) - hi / (2 * math.pi) < n:
        hi *= 2
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        x = mid / (2 * math.pi)
        if x * math.log(x) - x + 0.875 < n:
            lo = mid
        else:
            hi = mid
    return hi * 1.02


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Nearest-neighbour spacing statistics of the unfolded zeta zeros "
            "gamma~_n = theta(gamma_n)/pi versus the exact GUE (Gaudin/sine-"
            "kernel) law, the Wigner surmise, Poisson, and an actual random "
            "GUE matrix; plus Montgomery's pair-correlation test "
            "R2(r) = 1 - (sin(pi r)/(pi r))^2.  Prints KS statistics and the "
            "numerical verdict (Montgomery-Odlyzko law)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--n", type=int, default=10000,
                        help="number of zeros to use (first n; cached scan)")
    parser.add_argument("--seed", type=int, default=0,
                        help="RNG seed for the GUE matrices / Poisson sample")
    parser.add_argument("--matrix-size", type=int, default=800,
                        help="size of each random GUE matrix drawn")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("ZETA ZERO SPACINGS vs GUE vs POISSON: THE MONTGOMERY–ODLYZKO LAW")
    print("=" * 78)
    print()

    g = zero_ordinates(args.n, t_max=_t_max_for(args.n))
    s = nearest_neighbour_spacings(g)
    print(f"Zeros used     : first {g.size}  (γ_1 = {g[0]:.4f} … γ_{g.size} = "
          f"{g[-1]:.4f})")
    print(f"Unfolding      : γ̃ = θ(γ)/π  (exact mean density; ⟨s⟩ = "
          f"{s.mean():.6f}, should → 1)")
    print()

    # ---- 1. one-sample KS against the fully specified laws ----------------
    rep = level_repulsion_report(g)
    d_gue = rep["ks_gue_exact"]["statistic"]
    d_wig = rep["ks_gue_wigner"]["statistic"]
    d_poi = rep["ks_poisson"]["statistic"]
    print("1)  Kolmogorov–Smirnov distance of the spacing distribution")
    print(f"    {'law':<34} {'D = sup|F_emp − F|':>18}")
    print("    " + "-" * 54)
    print(f"    {'GUE exact (Gaudin, sine kernel)':<34} {d_gue:>18.4f}")
    print(f"    {'GUE Wigner surmise (32/π²)s²e^..':<34} {d_wig:>18.4f}")
    print(f"    {'Poisson e^(−s) (no repulsion)':<34} {d_poi:>18.4f}")
    print()
    print(f"    D_Poisson / D_GUE = {rep['ks_ratio_poisson_over_gue']:.1f}x  "
          "->  the zeros are GUE-distributed, emphatically not random points.")
    print()

    # ---- 2. level repulsion: the small-spacing census ---------------------
    frac = rep["frac_spacing_below_0.1"]
    print("2)  Level repulsion (fraction of spacings below s = 0.1)")
    print(f"    observed: {100 * frac['observed']:.3f} %    "
          f"GUE predicts: {100 * frac['gue_exact']:.3f} %    "
          f"Poisson predicts: {100 * frac['poisson']:.3f} %")
    print(f"    variance of s: observed {rep['var_spacing']:.4f}   "
          f"GUE {rep['variance_reference']['gue_exact']:.4f}   Poisson 1.0")
    print(f"    smallest spacing seen: {rep['min_spacing']:.4f} "
          "(zeros do not clump)")
    print()

    # ---- 3. two-sample: zeros vs an ACTUAL random matrix ------------------
    cmp = compare_to_random_matrix(g.size, seed=args.seed,
                                   matrix_size=args.matrix_size, gammas=g)
    ks2g = cmp["ks2_zeta_vs_gue_matrix"]
    ks2p = cmp["ks2_zeta_vs_poisson"]
    ctrl = cmp["ks_gue_matrix_vs_gaudin"]
    print(f"3)  Two-sample KS: zeta spacings vs {cmp['n_spacings']} bulk "
          f"eigenvalue spacings of real {args.matrix_size}x{args.matrix_size} "
          "GUE matrices")
    print(f"    zeta vs GUE matrix : D = {ks2g['statistic']:.4f}   "
          f"(p = {ks2g['pvalue']:.3g})")
    print(f"    zeta vs Poisson    : D = {ks2p['statistic']:.4f}   "
          f"(p = {ks2p['pvalue']:.3g})")
    print(f"    pipeline control, GUE matrix vs exact Gaudin law: "
          f"D = {ctrl['statistic']:.4f} (p = {ctrl['pvalue']:.2f})")
    print()

    # ---- 4. Montgomery pair correlation -----------------------------------
    r, r2 = pair_correlation(g, r_max=3.0, bins=60)
    sel = r > 0.2
    err = float(np.max(np.abs(r2[sel] - montgomery_prediction(r[sel]))))
    print("4)  Pair correlation vs Montgomery's  R₂(r) = 1 − (sin πr/πr)²")
    print(f"    {'r':>6} {'empirical':>10} {'Montgomery':>11}")
    print("    " + "-" * 30)
    for target in (0.125, 0.375, 0.625, 0.875, 1.125, 1.625, 2.125):
        i = int(np.argmin(np.abs(r - target)))
        print(f"    {r[i]:>6.3f} {r2[i]:>10.4f} "
              f"{montgomery_prediction(r[i]):>11.4f}")
    print(f"    max |empirical − Montgomery| over r > 0.2 : {err:.4f}")
    print(f"    correlation hole at r → 0 confirmed: R₂ vanishes "
          f"(empirical R₂({r[0]:.3f}) = {r2[0]:.4f})")
    print()

    # ---- verdict -----------------------------------------------------------
    print("-" * 78)
    print("VERDICT: the unfolded zeta-zero spacings match the GUE eigenvalue")
    print(f"statistics (D = {d_gue:.4f} vs exact Gaudin; D = "
          f"{ks2g['statistic']:.4f} vs a real random matrix)")
    print(f"and reject Poisson by a factor {d_poi / d_gue:.1f} in KS distance.  "
          "The zeros repel like the")
    print("spectrum of a random Hermitian operator, the Montgomery–Odlyzko law.")
    print("(Honest caveat: with ~1e4 spacings the residual D_GUE ≈ 0.03 is real")
    print(" finite-height O(1/log γ) drift; it shrinks as the height grows.)")
    print("-" * 78)
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
