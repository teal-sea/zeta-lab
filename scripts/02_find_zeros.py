#!/usr/bin/env python
"""Find every non-trivial zero of ζ(s) up to height T, from scratch, and
verify the Riemann Hypothesis below T by the Backlund/Turing counting method.

The mathematics
---------------
Hardy's function

    Z(t) = e^{iθ(t)} ζ(1/2 + it),     θ(t) = arg Γ(1/4 + it/2) − (t/2)·log π

is real for real t with |Z(t)| = |ζ(1/2 + it)|, so every sign change of Z
certifies a zero of ζ ON the critical line.  Independently, the argument
principle applied to ξ on a rectangle gives the *exact* count of zeros in
the whole strip 0 < Im s < T, wherever their real parts are:

    N(T) = 1 + θ(T)/π + S(T),      S(T) = (1/π) arg ζ(1/2 + iT).

If the number of sign changes of Z on (0, T) equals N(T), every unit of the
strip count is accounted for by a simple critical-line zero — i.e. RH holds
up to height T, as a finite theorem, not statistics.
"""

from __future__ import annotations

import argparse
import time

from mpmath import mp

from zeta.zeros import (
    N_of_T,
    S_of_T,
    riemann_von_mangoldt,
    verify_rh_up_to,
)

__all__ = ["main"]


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Find every zeta zero with 0 < Im s < T via sign changes of Hardy's "
            "real function Z(t) = exp(i*theta(t)) zeta(1/2+it), count the zeros "
            "in the whole critical strip exactly with the argument principle "
            "N(T) = 1 + theta(T)/pi + S(T), and verify RH up to T by checking "
            "the two counts agree (Backlund/Turing method)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--T", type=float, default=100.0,
                        help="verify RH for all zeros with 0 < Im s < T")
    parser.add_argument("--dps", type=int, default=25,
                        help="decimal digits of working precision")
    parser.add_argument("--oracle", action="store_true",
                        help="cross-check the found ordinates against "
                             "mpmath.zetazero (independent implementation)")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print(f"ZERO HUNT AND TURING-STYLE RH VERIFICATION UP TO T = {args.T:g}")
    print("=" * 78)
    print()

    # ---- exact strip count from the argument principle --------------------
    exact = N_of_T(args.T, dps=args.dps)
    s_t = S_of_T(args.T, dps=args.dps)
    print("Argument-principle count of ALL zeros in the strip 0 < Im s < T")
    print("(no assumption about their real parts):")
    print(f"    N(T) = 1 + θ(T)/π + S(T) = {exact}")
    print(f"    S(T) = (1/π)·arg ζ(1/2+iT) = {mp.nstr(s_t, 10)}")
    print(f"    Riemann–von Mangoldt main term (T/2π)log(T/2π) − T/2π + 7/8 "
          f"= {riemann_von_mangoldt(args.T):.6f}")
    print()

    # ---- sign-change scan of Hardy's Z ------------------------------------
    print("Scanning Hardy's Z(t) for sign changes on (0, T) ...")
    res = verify_rh_up_to(args.T, verbose=False, dps=args.dps)
    zs = res["zeros"]
    print(f"    grid used: {res['n_samples']} samples;  sign changes found: "
          f"{res['n_sign_changes']}")
    print()

    print(f"The {len(zs)} zero ordinates γ_n (zeros are at s = 1/2 + iγ_n):")
    for i in range(0, len(zs), 4):
        row = "   ".join(f"γ_{i + j + 1:<3d}= {mp.nstr(z, 15):<18}"
                         for j, z in enumerate(zs[i:i + 4]))
        print("    " + row)
    print()

    if args.oracle:
        n_check = min(len(zs), 10)
        with mp.workdps(args.dps + 5):
            worst = max(
                abs(zs[k] - mp.im(mp.zetazero(k + 1))) for k in range(n_check)
            )
        print(f"Oracle check: first {n_check} ordinates vs mpmath.zetazero — "
              f"max |Δγ| = {mp.nstr(worst, 3)}")
        print()

    if res["gram_violations"]:
        print(f"Gram's law fails at Gram indices n = {res['gram_violations']} "
              "(harmless; the count still certifies)")
    else:
        print(f"Gram's law holds at every Gram point below T "
              f"(largest index n = {res['n_gram_max']}).")
    print()

    print("-" * 78)
    if res["all_on_line"]:
        print(f"TURING-STYLE CONFIRMATION:  sign changes ({res['n_sign_changes']}) "
              f"== N(T) ({res['N_T']}).")
        print(f"==> ALL {res['N_T']} zeros of ζ with 0 < Im s < {args.T:g} are "
              "SIMPLE and lie EXACTLY")
        print("    on the critical line Re s = 1/2.  RH is verified up to this "
              "height —")
        print("    a finite proof for this range, not a statistical statement.")
    else:
        print(f"COUNTS DISAGREE: {res['n_sign_changes']} sign changes vs "
              f"N(T) = {res['N_T']}.")
        print("The grid missed zeros (or a zero is off the line!). "
              "Nothing is proved; refine the scan.")
    print("-" * 78)
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
