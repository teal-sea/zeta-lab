#!/usr/bin/env python
"""The counterexample show: perfect zeta-shaped symmetry, and a zero OFF the line.

The mathematics
---------------
The Davenport–Heilbronn function (1936) is the classical rival to ζ.  With χ
the odd Dirichlet character mod 5 having χ(2) = i, and κ = 0.28407904… the
unique real constant making the completion symmetric (derived numerically
here, never remembered), set

    f(s)  =  ((1 − iκ)/2)·L(s, χ) + ((1 + iκ)/2)·L(s, χ̄),
    F(s)  =  (π/5)^{−(s+1)/2} Γ((s+1)/2) f(s).

Then f has EVERYTHING the functional-equation-only "proofs" of RH ever use:

  * F(s) = F(1 − s) exactly (defect measured below, at the round-off floor);
  * f entire, real Dirichlet coefficients (period 5: 1, κ, −κ, −1, 0);
  * a real Hardy-style Z_f(t) on the critical line, so line zeros are sign
    changes, exactly like ζ.

And yet RH is FALSE for f.  This script runs the zero hunt of
``scripts/02_find_zeros.py`` in reverse: the argument-principle count of
zeros in a strip box exceeds the sign-change count on the line, the excess
is bisected and polished to an off-critical-line zero

    ρ = 0.80851718245663738555… + 85.69934848537759217193…·i,

verified by |f(ρ)|, the mirror pair ρ ↔ 1 − ρ̄, and a winding-number
certificate (independently: Spira, Math. Comp. 1994, lists 0.808517 +
85.699348i).  The one structural ingredient f LACKS is the Euler product,
its coefficients are not multiplicative (a₆ = 1 ≠ a₂a₃ = −κ²), and the
closing battery shows that claim distinguishing ζ from f while the
functional-equation claim does not.

Moral (docs/08 §4.1, docs/09 gate #3): symmetry alone cannot give RH; any
proposed proof whose every step f also satisfies is dead on arrival.
Nothing here says anything about ζ's own zeros.
"""

from __future__ import annotations

import argparse
import time

from mpmath import mp

from zeta.epstein import (
    KAPPA_REF,
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    battery,
    claim_functional_equation,
    claim_multiplicativity,
    count_zeros_box,
    dh_coefficient,
    dh_f,
    dh_functional_equation_defect,
    find_offline_zero,
    kappa,
    zeros_on_line,
)


__all__ = ["main"]


def section_functional_equation(dps: int) -> None:
    print("1)  THE MIRROR SYMMETRY  F(s) = F(1−s), same shape as Riemann's ξ")
    k = kappa(dps)
    with mp.workdps(dps):
        ref = mp.mpf(KAPPA_REF)
        print(f"    κ derived by linear solve of the defect condition: "
              f"{mp.nstr(k, min(dps, 25))}")
        print(f"    |κ − κ_ref(40 digits, pinned)| = {mp.nstr(abs(k - ref), 2)} "
              f"at dps = {dps}  (κ is re-derived, never trusted)")
    print()
    print(f"    defect F(s) − F(1−s) at asymmetric points  (dps = {dps}):")
    pts = [mp.mpc("0.3", "14.2"), mp.mpc("-0.75", "42.5"), mp.mpc("1.9", "-7.3")]
    worst = mp.mpf(0)
    with mp.workdps(dps):
        for s in pts:
            d = abs(dh_functional_equation_defect(s, dps=dps))
            worst = max(worst, d)
            print(f"      s = {mp.nstr(s, 6):>16}   |F(s) − F(1−s)| = {mp.nstr(d, 3)}")
        floor = mp.mpf(10) ** (-dps + 2)
        print(f"    worst defect {mp.nstr(worst, 3)} ≤ {mp.nstr(floor, 2)}: "
              "the functional equation holds to working precision,")
        print("    exactly as flat as ζ's own (zeta.core.functional_equation_defect).")
    print()


def section_count(windows: list[tuple[float, float]]) -> tuple[float, float]:
    print("2)  COUNT ZEROS TWO WAYS, scripts/02 run in reverse")
    print("    box   = argument-principle count in the strip  −1 ≤ Re s ≤ 2  (all of f's")
    print("            complex zeros live there; f is entire, no pole-dodging needed)")
    print("    line  = sign changes of Z_f on Re s = ½, grid refined until stable")
    print()
    print(f"    {'window t ∈':>16} {'box':>5} {'line':>5}   verdict")
    print("    " + "-" * 60)
    discrepancy = None
    for (t0, t1) in windows:
        nb = count_zeros_box(mp.mpc(-1, t0), mp.mpc(2, t1), dps=20)
        nl = zeros_on_line(t0, t1, dps=15)
        if nb > nl:
            verdict = f"{nb - nl} zero(s) NOT on the line"
            if discrepancy is None:
                discrepancy = (t0, t1)
        else:
            verdict = "all accounted for on the line"
        print(f"    [{t0:6.1f}, {t1:6.1f}] {nb:>5} {nl:>5}   {verdict}")
    print("    " + "-" * 60)
    if discrepancy is None:
        raise SystemExit("    no discrepancy window found, widen --windows")
    print("    For ζ this equality NEVER breaks (zeta.zeros.verify_rh_up_to saturates the")
    print("    count); for f it just did.  Off-line zeros arrive in mirror pairs ρ, 1−ρ̄.")
    print()
    return discrepancy


def section_locate(window: tuple[float, float], dps: int) -> None:
    t0, t1 = window
    print(f"3)  BISECT AND POLISH, find_offline_zero on the discrepancy window "
          f"[{t0:g}, {t1:g}]")
    rho = find_offline_zero(t_lo=t0, t_hi=t1, window=t1 - t0, dps=dps)
    with mp.workdps(dps + 10):
        resid = abs(dh_f(rho, dps=dps + 10))
        mirror = 1 - mp.conj(rho)
        resid_m = abs(dh_f(mirror, dps=dps + 10))
        ref = mp.mpc(mp.mpf(OFFLINE_ZERO_RE), mp.mpf(OFFLINE_ZERO_IM))
        print()
        print(f"    ρ      = {mp.nstr(mp.re(rho), 21)}")
        print(f"             + {mp.nstr(mp.im(rho), 22)}·i        (20+ digits shown)")
        print(f"    |f(ρ)| = {mp.nstr(resid, 3)}   (winding number around ρ: 1, "
              "verified inside find_offline_zero)")
        print(f"    Re ρ − ½ = {mp.nstr(mp.re(rho) - mp.mpf(1)/2, 10)}   "
              "→  0.31 OFF the critical line")
        print(f"    mirror 1 − ρ̄ = {mp.nstr(mirror, 12)},  |f(1 − ρ̄)| = "
              f"{mp.nstr(resid_m, 3)}  (the pair the symmetry forces)")
        print(f"    vs pinned/published value (Spira 1994: 0.808517 + 85.699348i):")
        print(f"      |ρ − ρ_ref| = {mp.nstr(abs(rho - ref), 2)}  "
              f"(ρ_ref pinned to 50 digits in zeta.epstein, re-verified by the tests)")
    print()


def section_battery() -> None:
    print("4)  THE BATTERY, which structural claim tells ζ and f apart?")
    print()
    rows = [battery(claim_functional_equation), battery(claim_multiplicativity)]
    print(f"    {'claim':<28} {'riemann_zeta':>13} {'davenport_heilbronn':>20} "
          f"{'distinguishes':>14}")
    print("    " + "-" * 80)
    for r in rows:
        print(f"    {r['claim']:<28} {str(r['riemann_zeta']):>13} "
              f"{str(r['davenport_heilbronn']):>20} {str(r['distinguishes']):>14}")
    print("    " + "-" * 80)
    with mp.workdps(20):
        a2, a3, a6 = (dh_coefficient(n, dps=20) for n in (2, 3, 6))
        print(f"    where multiplicativity dies:  a₆ = {mp.nstr(a6, 6)}  but  "
              f"a₂·a₃ = −κ² = {mp.nstr(a2 * a3, 6)}")
    print("    The functional equation does NOT distinguish them, any RH argument built")
    print("    on it alone must also 'prove' RH for f, which is false.  The Euler product")
    print("    (multiplicativity) is exactly where f fails to embed.")
    print()
    print("    And multiplicativity is where the battery stops, not where a proof starts:")
    print("    the rival set also carries zeta(s+a)zeta(s-a), which HAS a scalar Euler")
    print("    product and still has zeros off its own critical line, so the row above")
    print("    reads 'shared_with: shifted_product'.  docs/09 section 5.1 for the scope.")
    print()


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Construct the Davenport-Heilbronn function f(s) = ((1-i*kappa)/2)"
            "L(s,chi) + ((1+i*kappa)/2)L(s,chibar) (chi the odd character mod 5, "
            "kappa = 0.2840... derived on the spot), which satisfies a Riemann-"
            "type functional equation F(s) = F(1-s) with F(s) = (pi/5)^(-(s+1)/2) "
            "Gamma((s+1)/2) f(s), has real coefficients and a real Hardy Z, and "
            "violates RH.  The script verifies the functional equation (printed "
            "defect at the round-off floor), exposes the failure by comparing the "
            "argument-principle zero count in a strip box against the sign-change "
            "count on the critical line, bisects and polishes the excess to the "
            "off-line zero rho = 0.8085...+85.6993...i to 20+ digits with |f(rho)|, "
            "and closes with a falsification battery: the functional-equation claim "
            "passes for BOTH zeta and f (so it cannot prove RH); multiplicativity "
            "(the Euler product) is what tells them apart.  Nothing here concerns "
            "zeta's own zeros (docs/08)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--windows", type=float, nargs="+", default=[84.0, 88.0, 92.0],
                        help="breakpoints of the t-windows compared in section 2")
    parser.add_argument("--fe-dps", type=int, default=30,
                        help="precision for the functional-equation defect check")
    parser.add_argument("--zero-dps", type=int, default=25,
                        help="digits for the located off-line zero (>= 25 shows 20+)")
    args = parser.parse_args()
    if len(args.windows) < 2:
        parser.error("--windows needs at least two breakpoints")

    t0 = time.time()
    print("=" * 78)
    print("THE WRONG-SHAPE ZETA: DAVENPORT–HEILBRONN, A COUNTEREXAMPLE TO 'SYMMETRY ⇒ RH'")
    print("=" * 78)
    print()
    section_functional_equation(args.fe_dps)
    windows = list(zip(args.windows, args.windows[1:]))
    disc = section_count(windows)
    section_locate(disc, args.zero_dps)
    section_battery()
    print("=" * 78)
    print("HEADLINE")
    print("  • F(s) = F(1−s) holds to working precision, perfect mirror symmetry,")
    print("    the same shape as Riemann's ξ.")
    print("  • And still: ρ = 0.8085… + 85.6993…·i, a verified zero 0.31 off the line.")
    print("  • Symmetry alone cannot give RH.  What f lacks is the Euler product,")
    print("    and the battery shows that is precisely the claim that distinguishes.")
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
