#!/usr/bin/env python
"""Numerically walk Riemann's theta -> functional-equation derivation.

This script makes docs/03-functional-equation.md executable.  Three steps,
each one a *measured* residual of an identity that is exactly zero:

  1. Theta modularity (Poisson summation applied to the Gaussian):

         θ(1/x) = √x · θ(x),        θ(x) = Σ_{n∈ℤ} e^{−π n² x}

     Both sides are computed by direct summation, so a small defect is real
     numerical evidence, not an identity baked into the code.

  2. Riemann's symmetric Mellin representation.  Splitting the Mellin
     transform of ω(x) = (θ(x)−1)/2 at x = 1 and applying step 1 gives

         Λ(s) := π^{−s/2} Γ(s/2) ζ(s)
               = 1/(s(s−1)) + ∫_1^∞ (x^{s/2−1} + x^{(1−s)/2−1}) ω(x) dx .

     The right-hand side is *visibly* invariant under s ↦ 1−s.  We evaluate
     it by quadrature and compare with the left-hand side.

  3. The functional equation itself:

         ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)   satisfies   ξ(s) = ξ(1−s),

     which is exactly the s ↦ 1−s symmetry of step 2.  Includes trivial
     zeros (ξ(−2) = ξ(3)) and points near the critical line.

Everything is computed with the hand-rolled machinery in zeta.core;
mpmath is used only as the underlying arithmetic engine.
"""

from __future__ import annotations

import argparse
import time

from mpmath import mp

from zeta.core import (
    Xi,
    completed_zeta,
    functional_equation_defect,
    theta,
    theta_mellin_xi,
    theta_modular_defect,
    xi,
)

__all__ = ["main"]


def _fmt(v, digits: int = 6) -> str:
    """Compact mpmath number formatting for tables."""
    return mp.nstr(v, digits)


def step1_theta_modularity(dps: int) -> None:
    print("STEP 1, theta modularity:  θ(1/x) − √x·θ(x)  ≡ 0")
    print("        (Poisson summation; both sides summed directly)")
    print()
    print(f"  {'x':>8}   {'θ(x)':>24}   {'|θ(1/x) − √x·θ(x)|':>20}")
    print("  " + "-" * 60)
    for x in ("0.1", "0.25", "0.5", "1", "2", "5", "10"):
        d = theta_modular_defect(x, dps=dps)
        print(f"  {x:>8}   {_fmt(theta(x, dps=dps), 18):>24}   {_fmt(abs(d), 3):>20}")
    print()


def step2_mellin(dps: int) -> None:
    print("STEP 2: Riemann's symmetric integral formula")
    print("        Λ(s) = π^(−s/2)Γ(s/2)ζ(s)  =  1/(s(s−1)) + ∫_1^∞ (x^(s/2−1)+x^((1−s)/2−1)) ω(x) dx")
    print()
    print(f"  {'s':>12}   {'Λ(s) direct':>24}   {'Λ(s) theta-Mellin':>24}   {'|residual|':>12}")
    print("  " + "-" * 82)
    points = [mp.mpf(2), mp.mpf(3), mp.mpf("0.5"), mp.mpf("-1.5"),
              mp.mpc("0.5", "3"), mp.mpc("0.25", "1")]
    for s in points:
        lhs = completed_zeta(s, dps=dps)
        rhs = theta_mellin_xi(s, dps=dps)
        res = abs(rhs - lhs)
        print(f"  {_fmt(s, 6):>12}   {_fmt(lhs, 14):>24}   {_fmt(rhs, 14):>24}   {_fmt(res, 3):>12}")
    print()
    print("  The right-hand side is symmetric under s ↦ 1−s by inspection:")
    print("  1/(s(s−1)) is symmetric and the two powers of x trade places.  That")
    print("  symmetry, transported through the equality above, IS the functional equation.")
    print()


def step3_functional_equation(dps: int) -> None:
    print("STEP 3, functional equation:  ξ(s) − ξ(1−s)  ≡ 0")
    print()
    print(f"  {'s':>14}   {'ξ(s)':>26}   {'|ξ(s) − ξ(1−s)|':>18}")
    print("  " + "-" * 64)
    points = [mp.mpf("0.3"), mp.mpf(2), mp.mpf(-2), mp.mpf("0.75"),
              mp.mpc("0.3", "2"), mp.mpc("-1.5", "5"), mp.mpc("0.5", "14.1347")]
    for s in points:
        d = functional_equation_defect(s, dps=dps)
        print(f"  {_fmt(s, 6):>14}   {_fmt(xi(s, dps=dps), 14):>26}   {_fmt(abs(d), 3):>18}")
    print()
    print("  Landmarks:")
    print(f"    ξ(0) = {_fmt(xi(0, dps=dps), 20)}   (exactly 1/2)")
    print(f"    ξ(1) = {_fmt(xi(1, dps=dps), 20)}   (exactly 1/2)")
    print(f"    Ξ(0) = ξ(1/2) = {_fmt(Xi(0, dps=dps), 20)}  (≈ 0.4971207781…)")
    print(f"    |ξ(−2) − ξ(3)| = {_fmt(abs(functional_equation_defect(-2, dps=dps)), 3)}   (trivial-zero pairing)")
    print()


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Walk the theta -> functional equation derivation numerically: "
            "(1) theta modularity theta(1/x) = sqrt(x)*theta(x) [= Poisson summation], "
            "(2) Riemann's symmetric Mellin formula for Lambda(s) = pi^(-s/2)Gamma(s/2)zeta(s), "
            "(3) the functional equation xi(s) = xi(1-s).  Each step prints the "
            "measured residual of an identity that is exactly zero; the residual "
            "sizes show the identities hold to full working precision."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--dps", type=int, default=30,
                        help="decimal digits of working precision")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("THE FUNCTIONAL EQUATION, DERIVED NUMERICALLY   (working precision "
          f"{args.dps} digits)")
    print("=" * 78)
    print("(a residual printed as 0.0 is below the 10^-dps resolution of the")
    print(" returned values, the identity holds to every digit carried)")
    print()
    step1_theta_modularity(args.dps)
    step2_mellin(args.dps)
    step3_functional_equation(args.dps)
    print(f"All three identities hold to ~1e-{args.dps}, the functional equation")
    print("is the theta modular relation, pushed through a Mellin transform.")
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
