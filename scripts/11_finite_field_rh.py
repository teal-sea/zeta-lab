#!/usr/bin/env python
"""The universe where RH is a THEOREM, curves over finite fields, checked by counting.

The mathematics
---------------
For a prime p > 3 and a, b in F_p with 4a³ + 27b² ≠ 0, let

    E : y² = x³ + a x + b      over F_p,
    N_n = #E(F_{pⁿ})           (points over the degree-n extension, plus ∞),
    a_p = p + 1 − N_1          (the trace of Frobenius).

The zeta function of the curve packages *every* count into one series,
Z(T) = exp(Σ_{n≥1} N_n Tⁿ/n), and Weil's theorem is that this
transcendental-looking object is a rational function with integer coefficients:

    Z(T) = (1 − a_p T + p T²) / ((1 − T)(1 − p T)).

Factor the numerator as (1 − αT)(1 − ᾱT).  Then α + ᾱ = a_p, αᾱ = p, and RH
for E is the single statement

    |α| = √p      ⟺      |a_p| ≤ 2√p      (Hasse 1934).

The equivalence is elementary: x² − a_p x + p has a genuine conjugate pair of
roots exactly when a_p² < 4p, and a conjugate pair of product p has modulus √p.
Substituting T = p^{−s} sends a numerator root T₀ = 1/α to

    s = log α / log p,     so     Re(s) = log|α| / log p = log √p / log p = 1/2.

**The √ in the point-count bound IS the ½ in Re(s) = ½.**  There is nothing
approximate about it: the eigenvalues sit on the circle |α| = √p by a theorem,
not by measurement.

Why this universe has an RH at all: the zeros come from an *operator*.
Frobenius φ : x ↦ x^p acts on the étale cohomology of the curve, its fixed
points are exactly the F_p-points, and the Lefschetz fixed-point formula reads

    N_n = pⁿ + 1 − (αⁿ + ᾱⁿ) = Σ_i (−1)ⁱ Tr(Frob^n | Hⁱ).

That is not left as formalism here.  The script builds F_{p²} = F_p[t]/(t²−n)
explicitly and counts the solutions of y² = x³+ax+b over it by brute
enumeration, no zeta function, no eigenvalues, no Weil theory, and compares
with p² + 1 − (α² + ᾱ²).  A number obtained by counting in a field with p²
elements, predicted exactly by the second power sum of two complex numbers.

The three ingredients (docs/11 §1) are: a **space** (the curve, with a ground
field beneath it, so that E × E is a genuine surface), an **operator**
(Frobenius, with the counts as traces), and a **positivity input**
(Castelnuovo–Severi applied to the graph of Frobenius on E × E, symmetry alone
never suffices; that is what zeta.epstein demonstrates on the analytic side).
Over Spec Z the first is missing and the third has nowhere to live: Z ⊗_Z Z = Z,
so the "square" of Spec Z is one-dimensional.  **Nothing here is evidence for RH
over the integers.**  It is the blueprint, made concrete so the gap is visible.
"""

from __future__ import annotations

import argparse
import math
import random
import textwrap
import time
from fractions import Fraction

from mpmath import mp

from zeta.finitefield import (
    count_points,
    count_points_bruteforce,
    count_points_fp2,
    critical_line_check,
    curve_survey,
    frobenius_eigenvalues,
    frobenius_power_traces,
    gauss_trace,
    point_counts_over_extensions,
    quadratic_nonresidue,
    random_curve,
    sato_tate_histogram,
    survey_summary,
    trace_of_frobenius,
    weil_conjecture_facts,
    zeta_function_values,
    zeta_functional_equation_defect,
    zeta_log_series_defect,
    zeta_numerator,
)

__all__ = ["main"]

DEFAULT_PRIMES = (5, 13, 31, 101, 503, 1009, 2003, 4001, 10007, 20011)


def _fmt(x, n: int = 12) -> str:
    return mp.nstr(x, n)


def section_one_curve(p: int, seed: int, dps: int) -> dict:
    """One curve worked in full: counts, zeta function, functional equation."""
    a, b = random_curve(p, random.Random(seed))
    n1 = count_points(a, b, p)
    n1_bf = count_points_bruteforce(a, b, p)
    ap = trace_of_frobenius(a, b, p)
    num = zeta_numerator(a, b, p)

    print(f"1)  ONE CURVE, WORKED IN FULL:  E : y² = x³ + {a}x + {b}  over F_{p}")
    print()
    print(f"    N₁ = #E(F_{p})                      = {n1}   "
          f"(brute-force double loop agrees: {n1 == n1_bf})")
    print(f"    a_p = p + 1 − N₁                     = {ap}")
    print(f"    zeta numerator  1 − a_p T + p T²     = "
          f"[{num[0]}, {num[1]}, {num[2]}]  (ascending powers of T)")
    print(f"      = det(1 − Frob·T | H¹_ét): the only interesting cohomology")
    print()

    # exact rational abscissa: 1/(10p) is well inside the radius of convergence
    # 1/p, and using a Fraction keeps the point itself free of round-off.
    T = Fraction(1, 10 * p)
    z = zeta_function_values(a, b, p, T, dps=dps)
    fe = zeta_functional_equation_defect(a, b, p, T, dps=dps)
    ls = zeta_log_series_defect(a, b, p, n_max=60, T=T, dps=dps)
    print(f"    Z(T) at the exact rational T = 1/(10p) = {float(T):.6g}")
    print(f"      rational formula  (1−a_pT+pT²)/((1−T)(1−pT)) = {_fmt(z, 20)}")
    print(f"      |Z(T) − exp(Σ_{{n≤60}} N_n Tⁿ/n)|             = {_fmt(ls, 4)}")
    print("        ← the DEFINITION of the zeta function of a variety, checked against")
    print("          Weil's rational formula: counting in every extension = one integer a_p")
    print(f"      |Z(1/(pT)) − Z(T)|                           = {_fmt(fe, 4)}")
    print("        ← the functional equation.  Under T = p^{−s} it reads s ↔ 1 − s:")
    print("          the exact analogue of ξ(s) = ξ(1−s), mirror axis Re(s) = ½.")
    print()
    return {"a": a, "b": b, "p": p, "a_p": ap, "N_1": n1,
            "log_series_defect": ls, "fe_defect": fe}


def section_survey(primes: tuple[int, ...], n_curves: int, seed: int,
                   dps: int) -> dict:
    """Sweep curves over many primes; the Hasse bound holds every time."""
    print("2)  THE SURVEY, the Hasse bound |a_p| ≤ 2√p, checked on every curve")
    print("    The comparison is the exact integer test a_p² ≤ 4p; the ratio is reported")
    print("    for information only, so 'satisfied' can never be a floating-point artefact.")
    print()
    t0 = time.perf_counter()
    rows = curve_survey(p_list=primes, n_curves_per_p=n_curves, seed=seed, dps=dps)
    secs = time.perf_counter() - t0
    print(f"    {'p':>7} {'curves':>7} {'2√p':>12} {'max |a_p|':>10} "
          f"{'max |a_p|/2√p':>14} {'violations':>11} {'max |Re s − ½|':>16}")
    print("    " + "-" * 82)
    for p in primes:
        sub = [r for r in rows if r["p"] == p]
        print(f"    {p:>7} {len(sub):>7} {2 * math.sqrt(p):>12.4f} "
              f"{max(abs(r['a_p']) for r in sub):>10} "
              f"{max(r['ratio'] for r in sub):>14.6f} "
              f"{sum(1 for r in sub if not r['satisfied']):>11} "
              f"{max(r['max_deviation_from_half'] for r in sub):>16.3e}")
    print("    " + "-" * 82)
    summary = survey_summary(rows)
    print(f"    {summary['n_curves']} curves over {len(summary['primes'])} primes "
          f"({min(summary['primes'])} … {max(summary['primes'])}), {secs:.2f} s")
    print(f"    Hasse violations                       : {summary['violations']}")
    print(f"    closest approach to the bound |a_p|/2√p : {summary['max_ratio']:.6f}")
    print(f"    worst | |α|/√p − 1 |                    : "
          f"{summary['max_alpha_abs_relative_defect']:.3e}")
    print(f"    worst |Re(s) − ½|                       : "
          f"{summary['max_deviation_from_half']:.3e}   (pure log/sqrt round-off)")
    print()
    print("    Zero violations, and NOT because the sample was lucky.  Hasse's theorem")
    print("    forbids anything else; a violation here would mean a bug in this module.")
    print()
    return {"rows": rows, "summary": summary, "seconds": secs}


def section_eigenvalues(primes: tuple[int, ...], rows: list, dps: int) -> list:
    """The Frobenius eigenvalues, their modulus, and the s-coordinates."""
    print("3)  THE FROBENIUS EIGENVALUES, α = a_p/2 + i√(4p − a_p²)/2,  and |α| = √p")
    print("    One curve per prime (the one closest to the Hasse bound in the survey).")
    print()
    print(f"    {'p':>7} {'a_p':>7} {'α = Re + i·Im':>34} {'|α|':>16} {'√p':>16} "
          f"{'||α| − √p|':>12}")
    print("    " + "-" * 98)
    picks = []
    for p in primes:
        sub = [r for r in rows if r["p"] == p]
        best = max(sub, key=lambda r: r["ratio"])
        picks.append(best)
        alpha, _ = frobenius_eigenvalues(best["a"], best["b"], p, dps=dps)
        chk = critical_line_check(best["a"], best["b"], p, dps=dps)
        with mp.workdps(dps):
            sq = mp.sqrt(p)
            astr = f"{_fmt(mp.re(alpha), 10)} + {_fmt(mp.im(alpha), 10)}i"
            print(f"    {p:>7} {best['a_p']:>7} {astr:>34} {_fmt(abs(alpha), 14):>16} "
                  f"{_fmt(sq, 14):>16} {chk['abs_alpha_defect']:>12.1e}")
    print("    " + "-" * 98)
    print("    |α| = √p is not a fit and not a measurement: αᾱ = p exactly (the constant")
    print("    term of x² − a_p x + p), and ᾱ is the complex conjugate of α because")
    print("    4p − a_p² > 0 by Hasse.  The printed defect is mpmath round-off, nothing more.")
    print()

    print("    Now the same fact in s-coordinates.  Put T = p^{−s}; a numerator root")
    print("    T₀ = 1/α lands at s = log(α)/log(p):")
    print()
    print(f"    {'p':>7} {'Re(s) as returned':>26} {'|Re(s) − ½| (unrounded)':>26} "
          f"{'Im(s) = ±arg(α)/log p':>24}")
    print("    " + "-" * 88)
    worst = 0.0
    for best in picks:
        chk = critical_line_check(best["a"], best["b"], best["p"], dps=dps)
        worst = max(worst, chk["max_deviation_from_half"])
        with mp.workdps(dps):
            print(f"    {best['p']:>7} {_fmt(chk['re_s'][0], 20):>26} "
                  f"{chk['max_deviation_from_half']:>26.3e} "
                  f"{_fmt(chk['im_s'][0], 16):>24}")
    print("    " + "-" * 88)
    print(f"    worst |Re(s) − ½| over these primes: {worst:.3e}")
    print("    Re(s) = ½ EXACTLY.  The ½ is log(√p)/log(p); the square root in the")
    print("    point-count bound is the critical line.  (The Im(s) are defined only mod")
    print("    2π/log p, p^{−s} is periodic, so these zeros live on a CIRCLE, not a line.")
    print("    That periodicity is exactly the structure Spec Z is missing, docs/11.)")
    print()
    return picks


def section_lefschetz(picks: list, n_max: int, fp2_max_p: int, dps: int) -> dict:
    """N_n as traces of powers of one 2x2 operator, checked by brute force in F_{p²}."""
    print("4)  LEFSCHETZ, counting solutions IS linear algebra")
    print("    N_n = pⁿ + 1 − (αⁿ + ᾱⁿ) = Tr(Frob^n|H⁰) − Tr(Frob^n|H¹) + Tr(Frob^n|H²).")
    print("    The power sums come from the exact integer recursion t_n = a_p t_{n−1} −")
    print("    p t_{n−2} (t₀ = 2, t₁ = a_p), so every N_n below is an exact integer.")
    print()
    demo = [r for r in picks if r["p"] <= fp2_max_p]
    if not demo:
        demo = picks[:1]
    for best in demo[:3]:
        p, a, b = best["p"], best["a"], best["b"]
        traces = frobenius_power_traces(a, b, p, n_max)
        counts = point_counts_over_extensions(a, b, p, n_max)
        print(f"    E : y² = x³ + {a}x + {b} over F_{p}   (a_p = {best['a_p']})")
        print(f"      {'n':>3} {'t_n = αⁿ + ᾱⁿ':>22} {'N_n = pⁿ + 1 − t_n':>26}")
        for n in range(1, n_max + 1):
            print(f"      {n:>3} {traces[n - 1]:>22} {counts[n - 1]:>26}")
        print()

    print("    THE CHECK THAT MAKES IT REAL.  F_{p²} is built explicitly as")
    print("    F_p[t]/(t² − n) with n a quadratic non-residue, and the solutions of")
    print("    y² = x³ + ax + b are counted there by literal enumeration, no zeta")
    print("    function, no eigenvalues, no Weil theory:")
    print()
    print(f"    {'p':>7} {'non-residue':>12} {'N₂ by enumeration':>20} "
          f"{'p² + 1 − (α² + ᾱ²)':>22} {'equal':>7} {'ms':>8}")
    print("    " + "-" * 76)
    all_equal = True
    n_checked = 0
    for best in [r for r in picks if r["p"] <= fp2_max_p]:
        p, a, b = best["p"], best["a"], best["b"]
        t0 = time.perf_counter()
        n2 = count_points_fp2(a, b, p, method="table")
        dt = time.perf_counter() - t0
        pred = point_counts_over_extensions(a, b, p, 2)[1]
        all_equal &= n2 == pred
        n_checked += 1
        print(f"    {p:>7} {quadratic_nonresidue(p):>12} {n2:>20} {pred:>22} "
              f"{str(n2 == pred):>7} {dt * 1e3:>8.1f}")
    print("    " + "-" * 76)
    print(f"    all {n_checked} agree: {all_equal}")
    print("    A number obtained by brute-force counting in a field with p² elements is")
    print("    predicted, exactly, by the second power sum of two complex eigenvalues.")
    print("    The operator interpretation is REAL, not formal.")
    print()
    return {"all_equal": all_equal, "n_checked": n_checked}


def section_oracle(primes: tuple[int, ...]) -> dict:
    """Gauss's theorem for y² = x³ − x: a_p with no point counting at all."""
    print("5)  AN INDEPENDENT ORACLE: Gauss, with no point counting at all")
    print("    For y² = x³ − x: if p ≡ 3 (mod 4) the curve is supersingular and a_p = 0;")
    print("    if p ≡ 1 (mod 4) write p = A² + B² with A odd, B even, sign of A fixed by")
    print("    A + B ≡ 1 (mod 4), then a_p = 2A.  A sum of two squares, nothing else.")
    print()
    print(f"    {'p':>7} {'p mod 4':>8} {'Gauss a_p':>11} {'counted a_p':>12} {'agree':>7}")
    print("    " + "-" * 50)
    ok = True
    for p in primes:
        g = gauss_trace(p)
        c = trace_of_frobenius(-1, 0, p)
        ok &= g == c
        print(f"    {p:>7} {p % 4:>8} {g:>11} {c:>12} {str(g == c):>7}")
    print("    " + "-" * 50)
    print(f"    every prime agrees: {ok}")
    print()
    return {"agree": ok}


def section_sato_tate(p: int) -> dict:
    """The vertical Sato–Tate law: 'GUE statistics' in the proven universe."""
    print("6)  THE STATISTICS OF THE PROVEN UNIVERSE, vertical Sato–Tate")
    print("    Over ALL p² − p nonsingular curves mod p, the normalised traces")
    print("    a_p/(2√p) all lie in [−1, 1], that IS RH, and their distribution tends")
    print("    to the semicircle (2/π)√(1−x²) as p → ∞.  THEOREM (Birch 1968, via the")
    print("    Eichler–Selberg trace formula); this is the fixed-p, all-curves statement,")
    print("    not the horizontal Sato–Tate conjecture (one curve, varying p).")
    print()
    h = sato_tate_histogram(p, n_bins=20)
    print(f"    p = {h['p']}:  {h['n_curves']} curves  (= p² − p)")
    print(f"      Hasse violations                 : {h['hasse_violations']}")
    print(f"      max |a_p|                        : {h['max_abs_a_p']}  "
          f"(bound 2√p = {2 * math.sqrt(p):.3f})")
    print(f"      Σ a_p                            : {h['sum_a_p']}  "
          "(exactly 0, quadratic twisting negates a_p)")
    print(f"      Σ a_p²                           : {h['second_moment_exact']}")
    print(f"      closed form (p−1)²(p+1)          : {h['second_moment_closed_form']}  "
          f"→ identical: {h['second_moment_exact'] == h['second_moment_closed_form']}")
    print(f"      distinct traces / Hasse interval : {h['distinct_traces']} / "
          f"{h['hasse_interval_size']}  (equal: every admissible integer occurs, Deuring)")
    print(f"      moments ⟨x^{{2k}}⟩, k = 1,2,3      : "
          + ", ".join(f"{m:.7f}" for m in h["moments"]))
    print(f"      semicircle limits C_k/4^k        : "
          + ", ".join(f"{m:.7f}" for m in h["semicircle_moments"]))
    print(f"      sup |density − semicircle|       : {h['sup_deviation']:.4f}  "
          "(20 bins; convergence is slow and not monotone in p)")
    print()
    return h


def section_gap() -> dict:
    """What exists here, and what is missing over Spec Z."""
    facts = weil_conjecture_facts()
    print("7)  WHAT IS MISSING OVER Spec Z")
    print(f"    status of RH for curves over F_q : {facts['status']}")
    print()
    print("    The three ingredients that make the proof work here (docs/11 §1):")
    for key, label in (("space", "a space"), ("operator", "an operator"),
                       ("positivity", "positivity")):
        for line in textwrap.wrap(f"{label}: {facts['ingredients'][key]}", width=70):
            print(f"      {line}")
        print()
    for line in textwrap.wrap(facts["what_is_missing_over_Z"], width=72):
        print(f"    {line}")
    print()
    for line in textwrap.wrap(facts["honest_scope"], width=72):
        print(f"    {line}")
    print()
    return facts


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Exercise the one Riemann Hypothesis that has been PROVED: for an "
            "elliptic curve y^2 = x^3 + ax + b over F_p the zeta function "
            "Z(T) = (1 - a_p T + p T^2)/((1-T)(1-pT)) has numerator roots "
            "1/alpha with |alpha| = sqrt(p) (Hasse 1934, Weil 1948, Deligne "
            "1974), which under T = p^{-s} says exactly Re(s) = 1/2.  The "
            "script surveys curves over many primes and verifies the Hasse "
            "bound |a_p| <= 2 sqrt(p) on every one of them by an exact integer "
            "comparison, prints the Frobenius eigenvalues with their modulus "
            "against sqrt(p), converts to s-coordinates to display Re(s) = 1/2, "
            "runs the Lefschetz check N_2 = p^2 + 1 - (alpha^2 + alphabar^2) "
            "against a brute-force enumeration of the curve over an explicitly "
            "constructed F_{p^2}, cross-checks a_p against Gauss's two-squares "
            "theorem, and shows the vertical Sato-Tate semicircle.  Headline: "
            "in this universe RH is a theorem, and here it is, holding, for "
            "every curve we checked.  Nothing here is evidence for RH over the "
            "integers -- Spec Z has no base, so Weil's positivity argument has "
            "nowhere to live (docs/11)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--primes", type=int, nargs="+", default=list(DEFAULT_PRIMES),
                        help="primes to survey")
    parser.add_argument("--curves-per-prime", type=int, default=40,
                        help="distinct nonsingular curves drawn per prime")
    parser.add_argument("--seed", type=int, default=20260801,
                        help="seed for the curve sampler (reproducible)")
    parser.add_argument("--dps", type=int, default=30,
                        help="mpmath working precision for eigenvalues and s-coordinates")
    parser.add_argument("--demo-prime", type=int, default=101,
                        help="prime for the single fully worked curve")
    parser.add_argument("--extensions", type=int, default=5,
                        help="how many N_n = #E(F_{p^n}) to tabulate")
    parser.add_argument("--fp2-max-p", type=int, default=200,
                        help="run the brute-force F_{p^2} count for p up to this (O(p^2))")
    parser.add_argument("--sato-tate-p", type=int, default=1009,
                        help="prime for the all-curves Sato-Tate histogram")
    parser.add_argument("--skip-sato-tate", action="store_true",
                        help="skip the vertical Sato-Tate section")
    args = parser.parse_args()

    primes = tuple(sorted(set(int(p) for p in args.primes)))
    t0 = time.time()
    print("=" * 78)
    print("RH IS A THEOREM HERE:  CURVES OVER FINITE FIELDS")
    print("=" * 78)
    print()
    section_one_curve(args.demo_prime, args.seed, args.dps)
    surv = section_survey(primes, args.curves_per_prime, args.seed, args.dps)
    picks = section_eigenvalues(primes, surv["rows"], args.dps)
    lef = section_lefschetz(picks, args.extensions, args.fp2_max_p, args.dps)
    oracle = section_oracle(primes)
    st = None
    if not args.skip_sato_tate:
        st = section_sato_tate(args.sato_tate_p)
    section_gap()

    s = surv["summary"]
    print("=" * 78)
    print("HEADLINE")
    print(f"  • In this universe RH is a THEOREM, and here it is, holding, for every one")
    print(f"    of the {s['n_curves']} curves checked across {len(s['primes'])} primes "
          f"({min(s['primes'])} … {max(s['primes'])}): {s['violations']} Hasse violations.")
    print(f"  • Every Frobenius eigenvalue sits on the circle |α| = √p: worst measured")
    print(f"    | |α|/√p − 1 | = {s['max_alpha_abs_relative_defect']:.1e}, and in "
          f"s-coordinates |Re(s) − ½| ≤ {s['max_deviation_from_half']:.1e}:")
    print("    both are round-off, not error; the identity αᾱ = p is exact.")
    print(f"  • The Lefschetz prediction for N₂ matched a brute-force count over F_{{p²}} "
          f"in all {lef['n_checked']} cases ({lef['all_equal']}):")
    print("    counting solutions really is the trace of the square of one 2×2 operator.")
    print(f"  • Gauss's two-squares formula reproduced a_p for y² = x³ − x on every prime "
          f"({oracle['agree']}).")
    if st is not None:
        print(f"  • All {st['n_curves']} curves mod {st['p']} obey the bound, with "
              f"Σa_p² = (p−1)²(p+1) exactly and the")
        print("    normalised traces filling the semicircle: GUE statistics, in the proven case.")
    print("  • And none of it transfers: Z ⊗_Z Z = Z, so Spec Z has no base, E × E has no")
    print("    analogue, and the positivity input has nowhere to live (docs/11).")
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
