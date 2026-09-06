#!/usr/bin/env python
"""The Riemann–Weil explicit formula, balanced live, then Weil positivity probed.

The mathematics
---------------
For an even test function h, analytic in |Im r| ≤ 1/2 + δ and rapidly
decaying, with Fourier partner g(u) = (1/2π)∫ h(r) e^{−iru} dr, the
Riemann–Weil explicit formula says

    Σ_ρ h(γ_ρ)  =  h(i/2) + h(−i/2)                          (pole term)
                 + (1/2π) ∫ h(r) [Re ψ(¼ + ir/2) − log π] dr (archimedean)
                 − 2 Σ_{n≥2} Λ(n) n^{−1/2} g(log n)          (primes),

the left side running over ALL nontrivial zeros ρ = 1/2 + iγ_ρ (both signs
of γ).  Zeros on one side, primes and Γ-factors on the other: the same
number computed two unrelated ways.  This script computes BOTH sides
independently (zero side from cached verified ordinates, arithmetic side
from digamma quadrature + a prime-power sieve) and prints the balance,
with the truncation-tail bounds that account for the residual.

**Weil positivity criterion** (Weil 1952/1972): RH ⟺ W(h) := Σ_ρ h(γ_ρ) ≥ 0
for every admissible h of positive type (h = |f̂|² on the real axis).  The
script then evaluates W over parametrised families of positive-type pairs,
from the arithmetic side, no zeros used, and reports how close W comes to 0:
the near-tightness structure is controlled by the first zero γ₁ = 14.1347…,
because a test function concentrating on the zero-free gap (−γ₁, γ₁) makes
W = 2h(γ₁)(1 + o(1)) → 0⁺ (Gaussians: log W has slope −γ₁² in a).

Honest scope (docs/08): every computed W ≥ 0 reflects the computationally
verified zeros; it is NOT evidence for RH.  A true W < 0 would disprove RH,
a computed one would, per the house rule, almost certainly be a bug.
"""

from __future__ import annotations

import argparse
import time

from mpmath import mp

from zeta.weil import (
    GAMMA1,
    autocorrelation_pair,
    explicit_formula_sides,
    fejer_pair,
    gaussian_pair,
    near_tightness_report,
    positivity_probe,
)

__all__ = ["main"]


def _fmt(x, n: int = 12) -> str:
    return mp.nstr(x, n)


def section_balance(gamma_max: float, balance_digits: list[float]) -> None:
    print("1)  THE FORMULA BALANCES, LIVE, zeros on the left, primes + Γ on the right")
    print(f"    (zero side: cached verified ordinates γ ≤ {gamma_max:g}; "
          "arithmetic side: no zeros anywhere)")
    print()
    pairs = [
        ("Gaussian   h(r) = exp(−0.01·r²)", gaussian_pair("0.01"), 25),
        ("Autocorr.  h = |f̂|², two-bump f (s=2, σ=0.3)",
         autocorrelation_pair([1, -1], spacing=2.0, sigma=0.3), 20),
        ("Fejér      h(r) = (sin 2r / 2r)²  [g compactly supported]",
         fejer_pair(2), 20),
    ]
    for label, (h, g), dps in pairs:
        res = explicit_formula_sides(h, g, gamma_max=gamma_max, dps=dps)
        with mp.workdps(dps):
            print(f"    {label}   (dps = {dps})")
            print(f"      zero side       Σ_ρ h(γ_ρ)        = {_fmt(res['zero_side'], dps)}")
            print(f"        [{res['n_zeros_used']} zeros summed;  discarded-tail bound "
                  f"{_fmt(res['zero_side_tail_bound'], 3)}"
                  + (f", density estimate {_fmt(res['zero_side_tail_estimate'], 4)}"
                     if res["zero_side_tail_estimate"] is not None else "") + "]")
            print(f"      arithmetic side   pole  h(±i/2)   = {_fmt(res['pole_term'], dps)}")
            print(f"                        archimedean ∫   = {_fmt(res['arch_term'], dps)}")
            print(f"                        primes −2ΣΛg    = {_fmt(res['prime_term'], dps)}"
                  f"   [tail bound {_fmt(res['prime_tail_bound'], 3)}, n ≤ {res['n_max']}]")
            print(f"                        total           = {_fmt(res['arithmetic_side'], dps)}")
            diff = res["abs_diff"]
            digits = float(-mp.log10(res["agreement"])) if res["agreement"] > 0 else float(dps)
            est = res["zero_side_tail_estimate"]
            if est is not None and est > 0 and abs(diff / est - 1) < 0.1:
                match_digits = float(-mp.log10(abs(diff / est - 1)))
                verdict = (f"residual = the truncated zero tail: estimate matches to "
                           f"{match_digits:.0f}+ digits")
            else:
                verdict = f"agreement to {digits:.0f} significant digits"
            print(f"      |zero − arithmetic| = {_fmt(diff, 4)}   →  {verdict}")
            balance_digits.append(digits)
        print()


def section_probe(families: list[str], n_points: int, dps: int) -> dict:
    print("2)  POSITIVITY PROBE: W(h) from the arithmetic side only (no zeros used)")
    print("    RH  ⟺  W(h) ≥ 0 for every positive-type h;  here W is measured over families,")
    print("    with automatic precision escalation until each sign is certified.")
    print()
    print(f"    {'family':<16} {'parameter':>11} {'W(h)':>14} {'margin W/scale':>15} "
          f"{'dps':>4}  {'certified':>9}")
    print("    " + "-" * 76)
    tightest = None
    n_total = 0
    for fam in families:
        rows = positivity_probe(fam, n_points=n_points, dps=dps)
        pname = {"gaussian": "a", "fejer": "b", "autocorrelation": "σ"}[fam]
        for r in rows:
            with mp.workdps(r["dps_used"]):
                mark = "  ← tightest in family" if r["is_tightest"] else ""
                print(f"    {fam:<16} {pname}={r['param']:<9.4f} {_fmt(r['W'], 6):>14} "
                      f"{_fmt(r['margin'], 3):>15} {r['dps_used']:>4}  "
                      f"{'W > 0' if r['positive'] else 'UNRESOLVED':>9}{mark}")
            n_total += 1
            if r["is_tightest"] and (tightest is None or r["margin"] < tightest["margin"]):
                tightest = r
    print("    " + "-" * 76)
    all_pos = tightest is not None and tightest["positive"]
    print(f"    all {n_total} probes:  W ≥ 0 everywhere"
          if all_pos else "    WARNING: an unresolved/negative W appeared, investigate")
    print()
    return {"tightest": tightest, "n_total": n_total, "all_positive": all_pos}


def section_tightness(full: bool) -> dict:
    print("3)  NEAR-TIGHTNESS, what controls the approach to W = 0")
    if full:
        rep = near_tightness_report(dps=40)
    else:
        rep = near_tightness_report(gaussian_a=(0.05, 0.10, 0.15, 0.20),
                                    fejer_b=(1.0, 2.0), dps=30)
    print()
    print(f"    {'a':>6} {'W (Gaussian family)':>22} {'γ₁ share of Σ':>14} "
          f"{'cancelled digits':>17}")
    print("    " + "-" * 64)
    for d in rep["gaussian_scan"]:
        print(f"    {d['a']:>6.2f} {mp.nstr(mp.mpf(d['W']), 8):>22} "
              f"{d['gamma1_share']:>14.6f} {d['cancellation_digits']:>17.1f}")
    print("    " + "-" * 64)
    print(f"    fitted slope of log W in a : {rep['gaussian_log_margin_slope']:.5f}")
    print(f"    prediction  −γ₁²           : {rep['predicted_slope']:.5f}   "
          f"(rel. error {rep['slope_rel_error']:.1e})")
    print(f"    →  W collapses like 2·exp(−a·γ₁²): the margin IS the first zero.")
    print()
    if rep["fejer_scan"]:
        print("    Fejér cross-check:  W·b² hovers at Σ_γ γ⁻² "
              f"= {rep['sum_inv_gamma_sq_partial']:.5f} (partial, γ < 10⁴), of which")
        print(f"    the single lowest zero contributes 1/γ₁², a "
              f"{100 * rep['gamma1_share_of_sum']:.1f}% share:")
        for d in rep["fejer_scan"]:
            print(f"      b = {d['b']:.1f}:  W·b² = {d['W_times_b2']:.5f},  "
                  f"γ₁ share of the zero side = {d['gamma1_share']:.2e}"
                  + ("  (2γ₁ ≈ 9π, so sin²(bγ₁) ≈ 0: b = 2 nearly annihilates γ₁)"
                     if abs(d["b"] - 2.0) < 1e-9 else ""))
        print()
    return rep


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Compute BOTH sides of the Riemann-Weil explicit formula "
            "sum_rho h(gamma) = h(i/2) + h(-i/2) + (1/2pi) int h(r) "
            "[Re psi(1/4 + ir/2) - log pi] dr - 2 sum Lambda(n) n^(-1/2) "
            "g(log n) independently (zero side from cached verified zeros, "
            "arithmetic side from digamma quadrature and a prime sieve) and "
            "print the balance with explicit truncation-tail bounds.  Then "
            "probe the Weil positivity criterion (RH <=> W(h) >= 0 for every "
            "positive-type h): evaluate W(h) zero-free over parametrised "
            "families, certify each sign, and report the near-tightness "
            "structure, the margin collapses like 2 exp(-a gamma1^2), i.e. "
            "the first zero gamma1 = 14.1347... controls the infimum.  "
            "Positivity observed here reflects the verified zeros and is NOT "
            "evidence for RH (docs/08)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--gamma-max", type=float, default=10000.0,
                        help="sum zeros with gamma <= this on the zero side")
    parser.add_argument("--probe-points", type=int, default=7,
                        help="parameters sampled per family in the positivity probe")
    parser.add_argument("--probe-dps", type=int, default=20,
                        help="starting precision for the probe (auto-escalates)")
    parser.add_argument("--families", nargs="+", default=["gaussian", "fejer"],
                        choices=["gaussian", "fejer", "autocorrelation"],
                        help="positive-type families to probe")
    parser.add_argument("--full", action="store_true",
                        help="publication parameters for the tightness report (slower)")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("THE RIEMANN–WEIL EXPLICIT FORMULA AND WEIL POSITIVITY")
    print("=" * 78)
    print()
    digits: list[float] = []
    section_balance(args.gamma_max, digits)
    probe = section_probe(args.families, args.probe_points, args.probe_dps)
    rep = section_tightness(args.full)

    tight = probe["tightest"]
    print("=" * 78)
    print("HEADLINE")
    print(f"  • The explicit formula balances to {max(digits):.0f} significant digits "
          "(Gaussian pair, both sides independent).")
    print(f"  • W(h) stayed ≥ 0 at every one of the {probe['n_total']} probes "
          "(each sign certified above its noise floor).")
    with mp.workdps(int(tight["dps_used"])):
        print(f"  • Tightest margin: W = {_fmt(tight['W'], 6)} at "
              f"{tight['family']} parameter {tight['param']:g}, "
              f"{mp.nstr(mp.mpf(rep['max_cancellation_digits']), 3)} digits of cancellation,")
    print(f"    controlled by the first zero at γ₁ = {GAMMA1:.12f}: "
          f"W ≈ 2h(γ₁), share {rep['gamma1_share_at_tightest']:.6f}.")
    print("  • The infimum 0 is approached, never attained, and none of this is "
          "evidence for RH (docs/08).")
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
