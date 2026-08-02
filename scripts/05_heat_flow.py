#!/usr/bin/env python
"""Heat flow on the Riemann Ξ function: watch the zeros move, and the
de Bruijn–Newman constant Λ.

The mathematics
---------------
With the super-exponentially decaying weight

    Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}

define the family

    H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(zu) du .

At t = 0 this IS the Riemann Ξ function: H₀(z) = (1/8)·Ξ(z/2), so the real
zeros of H₀ sit at z = 2γ_n.  Differentiating under the integral shows H_t
obeys the BACKWARD heat equation  ∂H/∂t = −∂²H/∂z²  (t increasing smooths).
Under this flow real zeros repel each other (min gap grows with t); run
backwards they attract, collide, and leave the real axis as conjugate pairs.

The de Bruijn–Newman constant is

    Λ := inf{ t : H_t has only real zeros },     RH  ⟺  Λ ≤ 0,

and Rodgers–Tao (2020) proved Λ ≥ 0, so RH ⟺ Λ = 0: "the Riemann
hypothesis, if true, is only barely so" (Newman).  Rigorous state of the
art: 0 ≤ Λ ≤ 0.2 (Rodgers–Tao; Platt–Trudgian sharpening Polymath15).

The script (1) certifies H₀ = Ξ/8 and the backward heat equation
numerically, (2) tracks the first zeros of H_t across your chosen t values
and prints the min-gap statistics (repulsion made visible), and (3) runs the
same flow on a plain polynomial, where a backward collision actually happens
in front of you.
"""

from __future__ import annotations

import argparse
import time

import numpy as np
from mpmath import mp

from zeta.heatflow import (
    H_t,
    heat_equation_residual,
    lambda_facts,
    polynomial_heat_flow,
    track_zeros,
)
from zeta.zeros import first_n_zeros

__all__ = ["main"]


def section_normalisation(dps: int) -> None:
    print("1)  H₀ is the Riemann Ξ function  (H₀(z) = (1/8)·Ξ(z/2), so zeros at 2γ_n)")
    gammas = first_n_zeros(3)
    with mp.workdps(dps):
        print(f"    {'n':>3} {'2·γ_n':>24} {'H_t(2γ_n, t=0)':>16}")
        print("    " + "-" * 48)
        for n, gam in enumerate(gammas, 1):
            v = H_t(2 * mp.mpf(gam), 0, dps=dps)
            print(f"    {n:>3} {mp.nstr(2 * mp.mpf(gam), 18):>24} "
                  f"{mp.nstr(abs(v), 3):>16}")
    res = heat_equation_residual(10, 0.2, dps=dps)
    print(f"    backward heat equation |∂H/∂t + ∂²H/∂z²| at (z,t)=(10,0.2): "
          f"{mp.nstr(res, 3)}")
    print("    (the + sign residual vanishes: ∂H/∂t = −∂²H/∂z², the BACKWARD flow)")
    print()


def section_track(t_values: list[float], z_max: float, n_zeros: int) -> None:
    print(f"2)  The first {n_zeros} zeros of H_t under the flow  "
          f"(z_max = {z_max:g})")
    res = track_zeros(t_values, z_max=z_max, n_zeros=n_zeros)
    ts = res["t_values"]
    Z = res["zeros"]
    print()
    header = "    " + f"{'zero #':>7}" + "".join(f"   t={t:+.3f}" for t in ts)
    print(header)
    print("    " + "-" * (7 + 11 * len(ts)))
    for j in range(Z.shape[1]):
        row = "".join(f" {Z[i, j]:>10.4f}" for i in range(len(ts)))
        print(f"    {j + 1:>7}" + row)
    print("    " + "-" * (7 + 11 * len(ts)))
    print("    min gap" + "".join(f" {v:>10.4f}" for v in res["min_gap"]))
    print("    spread " + "".join(f" {v:>10.4f}" for v in res["spread"]))
    print()
    mono = all(res["min_gap"][i] < res["min_gap"][i + 1]
               for i in range(len(ts) - 1))
    print(f"    min gap strictly increasing in t: {mono}  ->  forward flow "
          "REPELS the real zeros;")
    print("    backward flow squeezes them together (the road to a collision "
          "below t = Λ).")
    print()


def section_polynomial() -> None:
    roots = [-3.0, -1.0, 0.5, 2.0, 4.5]
    ts = [-0.6, -0.45, -0.3, -0.15, 0.0, 0.15, 0.3, 0.45, 0.6]
    print("3)  The same story on a toy: p(x) = Π(x − r), r = "
          f"{roots},  p_t = exp(−t d²/dx²) p")
    print("    (roots then obey dr_i/dt = +2 Σ_{j≠i} 1/(r_i − r_j) — "
          "Coulomb repulsion)")
    print()
    res = polynomial_heat_flow(roots, ts)
    print(f"    {'t':>7} {'min gap':>9} {'spread':>8} {'max |Im root|':>14}   state")
    print("    " + "-" * 56)
    for t, mg, sp, mi, ar in zip(res["t_values"], res["min_gap"],
                                 res["spread"], res["max_abs_imag"],
                                 res["all_real"]):
        state = "all roots real" if ar else "COMPLEX PAIR — left the axis!"
        mg_s = f"{mg:9.4f}" if np.isfinite(mg) else "      —  "
        print(f"    {t:>+7.2f} {mg_s} {sp:>8.4f} {mi:>14.4f}   {state}")
    print()
    print(f"    Backward collision detected at sampled t = {res['collision_t']} "
          "(real pair → complex pair),")
    print(f"    exactly the mechanism that defines Λ for H_t.  Root-ODE vs "
          f"exact-coefficient flow agree to {res['max_ode_error']:.1e}.")
    print()


def section_lambda() -> None:
    facts = lambda_facts()
    print("4)  What is rigorously known about Λ (published theorems, not "
          "computed here)")
    print(f"    definition : {facts['definition']}")
    print(f"    equivalence: {facts['equivalence']}   and Rodgers–Tao ⟹  "
          f"{facts['consequence'].split(':')[-1].strip()}")
    print(f"    best bounds: {facts['current_interval']}")
    for h in facts["history"]:
        if h["who"] in ("B. Rodgers, T. Tao", "D. J. Platt, T. S. Trudgian",
                        "H. Ki, Y.-O. Kim, J. Lee",
                        "D. H. J. Polymath (Polymath15, led by T. Tao)"):
            print(f"      • {h['bound']:<44} — {h['who']}")
    print("    Newman's conjecture Λ ≥ 0 is now a theorem: RH, if true, is "
          "\"only barely so\".")
    print()


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Show the zeros of H_t(z) = int_0^inf e^(t u^2) Phi(u) cos(zu) du "
            "moving under the (backward) heat flow dH/dt = -d2H/dz2.  At t=0, "
            "H_0(z) = (1/8) Xi(z/2), so the zeros are the zeta ordinates "
            "(z = 2 gamma_n).  Forward t repels real zeros (min gap grows); "
            "backward t attracts them toward collisions, which is what defines "
            "the de Bruijn-Newman constant Lambda (RH <=> Lambda = 0, with "
            "0 <= Lambda <= 0.2 rigorously known).  Includes an elementary "
            "polynomial root-repulsion illustration where a backward collision "
            "is actually reached."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--t", type=float, nargs="+", default=[-0.05, 0.0, 0.05],
                        help="heat-flow times t at which to locate the zeros")
    parser.add_argument("--z-max", type=float, default=105.0,
                        help="track zeros of H_t up to this z (2*gamma_10 = 99.5)")
    parser.add_argument("--n-zeros", type=int, default=10,
                        help="number of zeros of H_t to track")
    parser.add_argument("--dps", type=int, default=30,
                        help="working precision for the certification step")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("HEAT FLOW ON Ξ AND THE DE BRUIJN–NEWMAN CONSTANT")
    print("=" * 78)
    print()
    section_normalisation(args.dps)
    section_track(args.t, args.z_max, args.n_zeros)
    section_polynomial()
    section_lambda()
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
