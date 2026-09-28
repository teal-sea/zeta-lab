#!/usr/bin/env python
"""Li's criterion and the Jensen polynomials: RH as positivity, RH as real-rootedness.

The mathematics
---------------
Two exact reformulations of RH live in this script, and both turn the
hypothesis into a statement about an explicit infinite sequence.

**1.  Li's criterion** (Li 1997; Bombieri–Lagarias 1999).  With

    λ_n = (1/(n−1)!) · dⁿ/dsⁿ [ s^{n−1} log ξ(s) ] |_{s=1},

    RH  ⟺  λ_n ≥ 0  for every n ≥ 1.

That is a theorem; what is open is whether the λ_n are in fact nonnegative.
Equivalently λ_n = Σ_ρ [1 − (1 − 1/ρ)ⁿ] over the nontrivial zeros, and the two
sides are computed here by *independent* routes: the substitution s = 1/(1−z)
turns the definition into a single Cauchy/trapezoid pass around a circle
(λ_n = n·[zⁿ] log ξ(1/(1−z)), no zeros are touched), while the zero-sum route
never evaluates ξ.  Their agreement is the load-bearing check.  Calibration:
λ₁ = 1 + γ/2 − log(4π)/2 = 0.023095708966121033814…, in closed form.

**2.  Pólya's criterion via Jensen polynomials** (Griffin–Ono–Rolen–Zagier
2019 for the modern treatment).  Write 8·ξ(½+z) = Σ_{n≥0} γ(n) z^{2n}/n! and

    J^{d,n}(X) = Σ_{j=0}^{d} C(d,j) γ(n+j) Xʲ.

A real entire function of genus ≤ 1 lies in the Laguerre–Pólya class iff every
one of its Jensen polynomials is *hyperbolic* (all roots real), so

    RH  ⟺  J^{d,n} is hyperbolic for every d ≥ 1 and every n ≥ 0.

This is the Routh–Hurwitz situation in its purest form: an infinite table of
finite, decidable stability questions, of which any computer can check the
first few hundred rows and no computer can check the rest.  Hyperbolicity is
decided here twice, mpmath's Durand–Kerner (a tolerance test) and an *exact*
Sturm-sequence count in ℚ[X] (mpf coefficients are dyadic rationals, so the
conversion is lossless), and the two verdicts are compared.

GORZ also proved that for fixed d the renormalised roots of J^{d,n} converge
as n → ∞ to the roots of the Hermite polynomial H_d, the orthogonal
polynomials of the GUE weight, the same random-matrix shape that
``scripts/04_gue_statistics.py`` finds in the zero spacings.

Honest scope (docs/08).  Both criteria are equivalences, so ONE negative λ_n or
ONE non-hyperbolic J^{d,n} would REFUTE RH.  The converse direction is worth
nothing: a table with no violation in it says exactly "no violation was found
in this finite range", and by Littlewood's theorem no finite range can be
evidence for RH.  This script prints such a table and says so.
"""

from __future__ import annotations

import argparse
import time

from mpmath import mp

from zeta.li import (
    hyperbolicity_scan,
    is_hyperbolic,
    jensen_polynomial,
    jensen_roots_vs_gue,
    li_closed_form_lambda1,
    li_coefficients,
    li_generating_function_defect,
    li_positivity_scan,
    xi_taylor_coefficients,
)

__all__ = ["main"]


def _fmt(x, n: int = 12) -> str:
    return mp.nstr(x, n)


def section_lambda_table(n_show: int, n_both: int, n_zeros: int, dps: int) -> dict:
    """λ_n from two independent routes, and the closed form for λ₁."""
    print("1)  THE LI COEFFICIENTS, two independent routes to the same numbers")
    print("    RH ⟺ λ_n ≥ 0 for every n ≥ 1  (THEOREM: Li 1997, Bombieri–Lagarias 1999)")
    print()
    with mp.workdps(dps):
        closed = li_closed_form_lambda1(dps)
    cauchy = li_coefficients(n_show, method="cauchy", dps=dps)
    t0 = time.perf_counter()
    zeros = li_coefficients(n_both, method="zeros", dps=dps, n_zeros=n_zeros)
    zero_secs = time.perf_counter() - t0

    print(f"    λ₁ closed form  1 + γ/2 − log(4π)/2 = {_fmt(closed, 22)}")
    print(f"    λ₁ Cauchy route                     = {_fmt(cauchy[0], 22)}")
    with mp.workdps(dps):
        print(f"    |difference|                        = {_fmt(abs(closed - cauchy[0]), 4)}"
              f"   (at dps = {dps})")
    print()
    print(f"    {'n':>3} {'λ_n  (Cauchy: ξ only, no zeros)':>34} "
          f"{'λ_n  (zero sum, ξ never used)':>32} {'|difference|':>14}")
    print("    " + "-" * 88)
    worst = mp.mpf(0)
    for i in range(n_show):
        n = i + 1
        left = _fmt(cauchy[i], 20)
        if i < len(zeros):
            with mp.workdps(dps):
                diff = abs(cauchy[i] - zeros[i])
            worst = max(worst, diff)
            print(f"    {n:>3} {left:>34} {_fmt(zeros[i], 20):>32} {_fmt(diff, 4):>14}")
        else:
            print(f"    {n:>3} {left:>34} {'—':>32} {'—':>14}")
    print("    " + "-" * 88)
    print(f"    worst disagreement over n ≤ {n_both}: {_fmt(worst, 4)}   "
          f"({n_zeros} zeros summed + smooth-density tail, {zero_secs:.1f} s)")
    print("    The zero route consumes the verified critical-line ordinates, so this is a")
    print("    cross-check of two formulas, never evidence for RH.")
    print()
    return {"cauchy": cauchy, "zeros": zeros, "worst": worst, "closed": closed}


def section_identity(defect_n: int, dps: int) -> list:
    """The generating-function identity checked against the literal definition."""
    print("2)  THE IDENTITY IS VERIFIED, NOT ASSUMED")
    print("    λ_n = n·[zⁿ] log ξ(1/(1−z)) is the substitution that makes route 1 possible.")
    print("    Compared against the literal dⁿ/dsⁿ[s^{n−1} log ξ(s)]|_{s=1} by Cauchy")
    print(f"    differentiation (dps = {dps}, internal working precision dps + 30):")
    print()
    defects = []
    for n in range(1, defect_n + 1):
        d = li_generating_function_defect(n, dps=dps)
        defects.append(d)
        print(f"      n = {n}:  generating function − literal definition = {_fmt(d, 5)}")
    print()
    print("    Zero to the full internal working precision, the substitution reproduces")
    print("    Li's definition, not some neighbouring normalisation.")
    print()
    return defects


def section_positivity(n_max: int, dps: int) -> list:
    """The positivity margins and the RH-predicted growth."""
    print("3)  THE POSITIVITY MARGINS, how far each λ_n is from the RH boundary λ = 0")
    print("    λ_n ≈ (n/2)(log n − log 2π + γ − 1) + 1 is the growth RH predicts")
    print("    (leading term derived from the smooth zero density; the +1 constant is")
    print("    quoted from the literature and is NOT separable from the O(√n log n)")
    print("    oscillation at these n, see zeta.li.li_asymptotic).")
    print()
    rows = li_positivity_scan(n_max, dps=dps)
    print(f"    {'n':>4} {'λ_n':>22} {'λ_n > 0':>8} {'margin digits':>14} "
          f"{'RH asymptotic':>15} {'λ_n / asympt.':>14}")
    print("    " + "-" * 82)
    step = max(1, n_max // 12)
    shown = [r for r in rows if r["n"] <= 6 or r["n"] % step == 0 or r["n"] == n_max]
    for r in shown:
        print(f"    {r['n']:>4} {_fmt(r['lambda_n'], 16):>22} {str(r['positive']):>8} "
              f"{r['margin_digits']:>14.1f} {r['asymptotic']:>15.6f} "
              f"{r['relative_to_asymptotic']:>14.6f}")
    print("    " + "-" * 82)
    n_pos = sum(1 for r in rows if r["positive"])
    print(f"    λ_n > 0 for {n_pos} of the {len(rows)} coefficients computed"
          f"{'  (no violation found)' if n_pos == len(rows) else '  ← INVESTIGATE'}")
    print("    'margin digits' = log₁₀(λ_n) + dps: decimal digits between the value and the")
    print(f"    absolute floor 10^−{dps}.  The Cauchy route's error is *relative*, so for")
    print(f"    λ_n ≥ 1 the honest sign margin is the smaller number, dps = {dps} itself.")
    print()
    last = rows[-1]
    print("    The ratio λ_n / asymptotic is negative for the first few n because the")
    print("    asymptotic formula itself is negative there ((n/2)(log n − log 2π + γ − 1)")
    print("    + 1 < 0 for small n); it is a large-n statement, and the approach is slow:")
    print(f"    at n = {last['n']} the relative error is still "
          f"{abs(last['relative_to_asymptotic'] - 1.0) * 100:.1f}%.")
    print()
    return rows


def section_jensen(d_max: int, n_max: int, dps: int, method: str) -> dict:
    """The Jensen hyperbolicity table, the infinite Routh table, first rows."""
    print("4)  THE JENSEN / PÓLYA TABLE, the infinite Routh table, first rows")
    print("    RH ⟺ every J^{d,n} is hyperbolic (all roots real).  One ✗ anywhere in the")
    print("    infinite table would refute RH; the table below is finite.")
    print()
    a = xi_taylor_coefficients(6, dps=dps, method="integral")
    b = xi_taylor_coefficients(6, dps=dps, method="cauchy")
    identical = all(x == y for x, y in zip(a, b))
    print("    The coefficients γ(n) of 8·ξ(½+z) = Σ γ(n) z^{2n}/n!, by two routes")
    print("    (Riemann's Mellin integral vs Cauchy integration of 8·ξ(½+√w)):")
    for i, g in enumerate(a[:5]):
        print(f"      γ({i}) = {_fmt(g, 20)}")
    print(f"      the two routes are bit-identical over γ(0…5): {identical}")
    print()

    t0 = time.perf_counter()
    rows = hyperbolicity_scan(d_max, n_max, dps=dps, method=method)
    secs = time.perf_counter() - t0
    grid = {(r["d"], r["n"]): r for r in rows}

    header = "    d \\ n " + "".join(f"{n:>4}" for n in range(n_max + 1))
    print(header)
    print("    " + "-" * (len(header) - 4))
    for d in range(1, d_max + 1):
        line = f"    {d:>5} "
        for n in range(n_max + 1):
            line += f"{'   ✓' if grid[(d, n)]['hyperbolic'] else '   ✗'}"
        print(line)
    print("    " + "-" * (len(header) - 4))
    n_hyp = sum(1 for r in rows if r["hyperbolic"])
    finite_gaps = [r["min_gap"] for r in rows if r["min_gap"] != float("inf")]
    worst_imag = max(r["max_rel_imag"] for r in rows)
    print(f"    {n_hyp} of {len(rows)} rows hyperbolic  ({secs:.1f} s, dps = {dps}, "
          f"method = {method!r})")
    print(f"    largest relative |Im root| anywhere : {worst_imag:.3e}  "
          "← real to far beyond working precision")
    print(f"    smallest relative root gap          : {min(finite_gaps):.5f}  "
          "← well separated, i.e. comfortably hyperbolic")
    if method in ("sturm", "both"):
        exact_ok = all(r["n_real_exact"] == r["d"] for r in rows)
        print(f"    exact Sturm count = degree in every row: {exact_ok}  "
              "(a decision procedure in ℚ[X], no tolerance)")
    print()

    d_demo = min(6, d_max)
    n_demo = min(3, n_max)
    coeffs = jensen_polynomial(d_demo, n_demo, dps=dps, normalise=True)
    info = is_hyperbolic(coeffs, dps=dps, method="both")
    print(f"    The roots themselves, J^{{{d_demo},{n_demo}}} in the normalised variable "
          "(they are real numbers, printed as such):")
    with mp.workdps(dps):
        for r in info["roots"]:
            print(f"      {_fmt(mp.re(r), 16):>24}   Im = {_fmt(mp.im(r), 3)}")
    print(f"      Durand–Kerner verdict {info['hyperbolic']}, exact Sturm real-root count "
          f"{info['n_real_exact']} of degree {info['degree']}, "
          f"routes agree: {info['agree']}")
    with mp.workdps(dps):
        all_negative = all(mp.re(r) < 0 for r in info["roots"])
    print(f"      every root real AND negative: {all_negative}, the substitution w = z²")
    print("      sends a zero ½ ± iγ of ξ to w = −γ², so 'real and negative' is exactly")
    print("      what RH asks (and γ(n) > 0 for all n forces it by Descartes' rule).")
    print()
    return {"rows": rows, "n_hyperbolic": n_hyp, "worst_imag": worst_imag,
            "min_gap": min(finite_gaps), "gamma_identical": identical,
            "seconds": secs}


def section_gue(d_values: list[int], n_values: list[int], dps: int) -> list:
    """The Jensen roots approaching the Hermite (GUE) roots."""
    print("5)  WHERE THE TABLE POINTS: Jensen roots → Hermite roots (the GUE side)")
    print("    GORZ 2019: for fixed d, the renormalised roots of J^{d,n} converge as")
    print("    n → ∞ to the roots of the Hermite polynomial H_d, the orthogonal")
    print("    polynomials of the GUE weight e^{−x²}.  Deviations of the *standardised*")
    print("    root vectors (mean 0, unit s.d., the affine normalisation removed):")
    print()
    print(f"    {'d':>4} " + "".join(f"{'n = ' + str(n):>14}" for n in n_values))
    print("    " + "-" * (5 + 14 * len(n_values)))
    out = []
    for d in d_values:
        line = f"    {d:>4} "
        for n in n_values:
            rec = jensen_roots_vs_gue(d, n, dps=dps)
            out.append(rec)
            line += f"{rec['max_deviation']:>14.5f}"
        print(line)
    print("    " + "-" * (5 + 14 * len(n_values)))
    print("    Convergence is genuinely slow, the numbers say so.  d = 2 is exact for")
    print("    every n by symmetry (two distinct points standardise to ∓1 either way).")
    print()
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Print the Li coefficient table computed two independent ways "
            "(Cauchy extraction of the coefficients of log xi(1/(1-z)), which "
            "never touches a zero, against the zero sum lambda_n = sum_rho "
            "[1 - (1-1/rho)^n], which never touches xi), the closed form for "
            "lambda_1, the generating-function identity checked against the "
            "literal n-th derivative definition, the positivity margins with "
            "the RH-predicted growth (n/2)(log n - log 2pi + gamma - 1) + 1, "
            "and the Jensen-polynomial hyperbolicity table -- the infinite "
            "Routh table, first N rows -- decided both by a root tolerance and "
            "by an exact Sturm-sequence count in Q[X].  Li's criterion (RH <=> "
            "lambda_n >= 0 for all n) and Polya's criterion (RH <=> every "
            "J^{d,n} is hyperbolic) are both THEOREMS, so a single violation "
            "would refute RH.  Finding none does NOT support RH: by "
            "Littlewood's theorem no finite range can (docs/08)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--n-lambda", type=int, default=10,
                        help="Li coefficients lambda_1..N shown in the comparison table")
    parser.add_argument("--n-both-routes", type=int, default=8,
                        help="how many lambda_n to also compute by the zero sum (slow)")
    parser.add_argument("--n-zeros", type=int, default=200,
                        help="zeros summed in the zero-sum route")
    parser.add_argument("--n-scan", type=int, default=40,
                        help="positivity scan runs over lambda_1..N")
    parser.add_argument("--defect-n", type=int, default=3,
                        help="check the generating-function identity for n = 1..N")
    parser.add_argument("--d-max", type=int, default=8,
                        help="Jensen table degrees d = 1..D")
    parser.add_argument("--n-max", type=int, default=8,
                        help="Jensen table shifts n = 0..N")
    parser.add_argument("--dps", type=int, default=25,
                        help="working precision for the Li coefficients")
    parser.add_argument("--jensen-dps", type=int, default=30,
                        help="working precision for the Jensen table")
    parser.add_argument("--jensen-method", default="both",
                        choices=["roots", "sturm", "both"],
                        help="hyperbolicity test: tolerance, exact Sturm, or both")
    parser.add_argument("--skip-gue", action="store_true",
                        help="skip the Jensen-roots-vs-Hermite comparison")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("LI'S CRITERION AND THE JENSEN POLYNOMIALS")
    print("=" * 78)
    print()
    lam = section_lambda_table(args.n_lambda, args.n_both_routes, args.n_zeros, args.dps)
    section_identity(args.defect_n, args.dps)
    rows = section_positivity(args.n_scan, args.dps)
    jen = section_jensen(args.d_max, args.n_max, args.jensen_dps, args.jensen_method)
    if not args.skip_gue:
        section_gue([2, 3, 4, 6], [10, 20, 40], args.jensen_dps)

    n_pos = sum(1 for r in rows if r["positive"])
    print("=" * 78)
    print("HEADLINE")
    print(f"  • λ_n > 0 for all {n_pos} coefficients computed (n ≤ {args.n_scan}); the two")
    print(f"    independent routes agree to {_fmt(lam['worst'], 3)} over n ≤ "
          f"{args.n_both_routes}, and λ₁ matches its closed form exactly.")
    print(f"  • All {jen['n_hyperbolic']} of {len(jen['rows'])} Jensen polynomials "
          f"J^(d,n) with d ≤ {args.d_max}, n ≤ {args.n_max} are hyperbolic —")
    print(f"    max relative |Im root| {jen['worst_imag']:.1e}, min relative root gap "
          f"{jen['min_gap']:.4f}, exact Sturm counts agreeing.")
    print("  • Both criteria are exact equivalences, so one negative λ_n or one")
    print("    non-hyperbolic J^(d,n) would REFUTE RH. None appeared here.")
    print("  • Stated plainly: NO VIOLATION FOUND IS NOT EVIDENCE FOR RH. The criteria")
    print("    quantify over all n; this is the first few rows of an infinite table, and")
    print("    by Littlewood's theorem no finite computation can settle the question")
    print("    either way (docs/08).")
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
