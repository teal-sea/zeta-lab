#!/usr/bin/env python
"""One command, the whole story: a guided tour of the Riemann zeta laboratory.

Runs an abbreviated version of every demo in scripts/01–05 with narration:

  Act 1  ζ continued past its series  (ζ(2) = π²/6, ζ(−1) = −1/12 from
         finite arithmetic via Euler–Maclaurin)
  Act 2  the theta modular relation → the functional equation ξ(s) = ξ(1−s)
  Act 3  the zeros: found by Hardy's Z, counted by the argument principle,
         RH verified up to T (Turing's method)
  Act 4  the explicit formula: the primes rebuilt from the zeros
  Act 5  GUE statistics: the zeros repel like random-matrix eigenvalues
  Act 6  heat flow on Ξ and the de Bruijn–Newman constant (RH ⟺ Λ = 0)

Total runtime is kept under ~90 s (well under, once caches are warm).
Each act names the full script that goes deeper.
"""

from __future__ import annotations

import argparse
import math
import time

import numpy as np
from mpmath import mp

__all__ = ["main"]

_T0 = time.time()


def _act(n: int, title: str) -> None:
    print()
    print(f"--- Act {n}: {title} " + "-" * max(0, 60 - len(title)))
    print()


def _tick(label: str = "") -> None:
    print(f"    [{time.time() - _T0:5.1f} s] {label}")


def act1_continuation(dps: int) -> None:
    from zeta.core import zeta, zeta_euler_maclaurin

    _act(1, "ζ beyond its series (scripts/01…)")
    print("  ζ(s) = Σ n^(−s) only converges for Re s > 1, but Euler–Maclaurin")
    print("  (comparing the Riemann SUM with the INTEGRAL) continues it everywhere:")
    print()
    z2 = zeta(2, dps=dps)
    with mp.workdps(dps):
        ref = mp.pi ** 2 / 6
    print(f"    ζ(2)  = {mp.nstr(z2, 20)}   (π²/6 = {mp.nstr(ref, 20)})")
    print(f"    ζ(−1) = {mp.nstr(zeta_euler_maclaurin(-1, dps=dps), 20)}"
          "                  <- '1+2+3+… = −1/12', from finite arithmetic")
    print(f"    ζ(0)  = {mp.nstr(zeta_euler_maclaurin(0, dps=dps), 20)}")


def act2_functional_equation(dps: int) -> None:
    from zeta.core import (functional_equation_defect, theta_mellin_xi,
                           completed_zeta, theta_modular_defect)

    _act(2, "theta modularity IS the functional equation (scripts/01)")
    d = theta_modular_defect(2, dps=dps)
    print(f"  Poisson summation:  θ(1/x) − √x·θ(x) at x=2:   |defect| = "
          f"{mp.nstr(abs(d), 3)}")
    lhs = completed_zeta(3, dps=dps)
    rhs = theta_mellin_xi(3, dps=dps)
    print("  Riemann's Mellin form Λ(s) = 1/(s(s−1)) + ∫_1^∞ (x^(s/2−1)+x^((1−s)/2−1))ω dx")
    print(f"      at s=3:  |Λ_direct − Λ_theta| = {mp.nstr(abs(lhs - rhs), 3)}")
    fd = functional_equation_defect(mp.mpc("0.3", "2"), dps=dps)
    print(f"  and therefore ξ(s) = ξ(1−s):  |ξ(0.3+2i) − ξ(0.7−2i)| = "
          f"{mp.nstr(abs(fd), 3)}")
    print("  The symmetry s ↦ 1−s is the modular flip x ↦ 1/x of a theta function.")


def act3_zeros(T: float) -> None:
    from zeta.zeros import verify_rh_up_to

    _act(3, f"the zeros, found and counted up to T = {T:g} (scripts/02)")
    res = verify_rh_up_to(T, dps=20)
    zs = res["zeros"]
    print("  Hardy's Z(t) = e^(iθ)ζ(1/2+it) is REAL, its sign changes are zeros")
    print("  of ζ on the critical line.  The argument principle counts every zero")
    print("  in the whole strip: N(T) = 1 + θ(T)/π + S(T).")
    print()
    shown = ", ".join(mp.nstr(z, 10) for z in zs[:5])
    print(f"    first ordinates γ_n : {shown}, …")
    print(f"    sign changes of Z   : {res['n_sign_changes']}")
    print(f"    strip count N(T)    : {res['N_T']}")
    verdict = ("EQUAL -> all zeros below T are simple and ON the line: "
               "RH verified up to T"
               if res["all_on_line"] else "NOT equal -> scan needs refining")
    print(f"    {verdict}")


def act4_primes(x: float, n_zeros: int) -> None:
    from zeta.explicit import (convergence_table, first_zeros, prime_spectrum,
                               psi_true, spectrum_peaks)

    _act(4, f"the primes rebuilt from {n_zeros} zeros (scripts/03)")
    g = first_zeros(n_zeros)
    print("  Von Mangoldt:  ψ₀(x) = x − Σ_ρ x^ρ/ρ − log 2π − ½log(1−x⁻²), where")
    print("  ψ(x) = Σ_{p^k ≤ x} log p.  Cosine waves, one per zero, building a staircase:")
    print()
    rows = convergence_table(x, g, counts=(0, 10, 100, n_zeros))
    print(f"    ψ({x:g}) exact = {psi_true(x):.5f}")
    for r in rows:
        print(f"      {r['n_zeros']:>5} zeros ->  ψ_rec = {r['psi_est']:>9.5f}   "
              f"error {r['error']:+.5f}")
    u = np.linspace(0.5, math.log(x), 3000)
    spec = prime_spectrum(g, u, window="gauss")
    peaks = spectrum_peaks(u, spec, n_peaks=8)
    det = sorted(p["nearest_n"] for p in peaks)
    ok = all(p["is_prime_power"] for p in peaks)
    print()
    print(f"    dual view: top 8 spectral peaks of −2Σcos(γu) sit at n = {det}")
    print(f"    all prime powers? {'YES' if ok else 'no'}, the zeros know the primes.")


def act5_gue(n: int) -> None:
    from zeta.statistics import level_repulsion_report, zero_ordinates

    _act(5, f"spacing statistics of {n} zeros vs GUE (scripts/04)")
    g = zero_ordinates(n)
    rep = level_repulsion_report(g)
    print("  Unfold to unit density (γ̃ = θ(γ)/π), take nearest-neighbour spacings,")
    print("  and compare with random-matrix (GUE) and with uncorrelated (Poisson) laws:")
    print()
    print(f"    KS distance to exact GUE law : {rep['ks_gue_exact']['statistic']:.4f}")
    print(f"    KS distance to Poisson       : {rep['ks_poisson']['statistic']:.4f}   "
          f"({rep['ks_ratio_poisson_over_gue']:.1f}x farther)")
    f = rep["frac_spacing_below_0.1"]
    print(f"    spacings below 0.1           : {100 * f['observed']:.3f} %  "
          f"(GUE {100 * f['gue_exact']:.3f} %, Poisson {100 * f['poisson']:.2f} %)")
    print("    The zeros repel like eigenvalues of a random Hermitian matrix:")
    print("    the Montgomery–Odlyzko law, the footprint of a hidden operator.")


def act6_heatflow() -> None:
    from zeta.heatflow import H_t, lambda_facts, polynomial_heat_flow, track_zeros
    from zeta.zeros import first_n_zeros

    _act(6, "heat flow on Ξ and the constant Λ (scripts/05)")
    g1 = first_n_zeros(1)[0]
    v = abs(H_t(2 * mp.mpf(g1), 0, dps=30))
    print(f"  H_t(z) = ∫ e^(tu²)Φ(u)cos(zu)du;  H₀(z) = (1/8)Ξ(z/2):  "
          f"|H₀(2γ₁)| = {mp.nstr(v, 3)}")
    tr = track_zeros([-0.05, 0.0, 0.05])
    mg = ", ".join(f"{m:.4f}" for m in tr["min_gap"])
    print(f"  flow the zeros: min gap at t = −0.05, 0, +0.05  ->  {mg}")
    print("  (backward flow squeezes zeros together, forward flow repels them)")
    toy = polynomial_heat_flow([-3.0, -1.0, 0.5, 2.0, 4.5],
                               [-0.6, -0.3, 0.0, 0.3, 0.6])
    print(f"  toy polynomial under the same flow: collision (roots go complex) at "
          f"sampled t = {toy['collision_t']}")
    lf = lambda_facts()
    print(f"  Λ := inf{{t : H_t has only real zeros}};  {lf['equivalence']};")
    print(f"  rigorously {lf['current_interval']} (Rodgers–Tao 2020; "
          "Platt–Trudgian 2021).  RH says Λ = 0:")
    print("  the zeta zeros sit exactly at the boundary of reality.")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "A guided ~90-second tour of the whole laboratory: analytic "
            "continuation, theta modularity -> functional equation, zero "
            "hunting + Turing verification of RH, primes rebuilt from zeros "
            "(explicit formula), GUE spacing statistics, and heat flow / the "
            "de Bruijn-Newman constant.  Each act names the full script."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--T", type=float, default=60.0,
                        help="height for the RH verification act")
    parser.add_argument("--x", type=float, default=50.0,
                        help="rebuild psi(x) at this x in the primes act")
    parser.add_argument("--zeros", type=int, default=500,
                        help="zeros used in the primes act")
    parser.add_argument("--n-stat", type=int, default=10000,
                        help="zeros used in the statistics act")
    parser.add_argument("--dps", type=int, default=25,
                        help="working precision for acts 1-2")
    args = parser.parse_args()

    print("=" * 78)
    print("THE RIEMANN ZETA FUNCTION: A LABORATORY TOUR IN SIX ACTS")
    print("=" * 78)
    print()
    print("  One thread runs through everything below: a single function ζ(s),")
    print("  its reflection symmetry, its zeros, and the primes they encode.")

    act1_continuation(args.dps)
    _tick("act 1 done")
    act2_functional_equation(args.dps)
    _tick("act 2 done")
    act3_zeros(args.T)
    _tick("act 3 done")
    act4_primes(args.x, args.zeros)
    _tick("act 4 done")
    act5_gue(args.n_stat)
    _tick("act 5 done")
    act6_heatflow()
    _tick("act 6 done")

    print()
    print("=" * 78)
    print("CURTAIN.  The primes are the spectrum of the zeros; the zeros behave")
    print("like the spectrum of an operator; and RH says that operator's heat")
    print("flow parameter Λ is exactly 0.  Go deeper with scripts/01…05.")
    print(f"Total runtime: {time.time() - _T0:.1f} s")
    print("=" * 78)


if __name__ == "__main__":
    main()
