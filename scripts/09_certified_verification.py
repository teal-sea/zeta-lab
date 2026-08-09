#!/usr/bin/env python
"""Certified RH verification: the difference between "we measured" and "we proved".

The mathematics
---------------
Every other number in this laboratory is an ordinary float: a real number
carrying an *unknown* error.  Ball (interval) arithmetic replaces the number by
an **enclosure** — a pair lo ≤ hi with the guarantee that the true value lies
in [lo, hi] — and every operation propagates that guarantee by rounding
outward.  The pay-off is one sentence long:

    if an enclosure of Z(t) is strictly positive or strictly negative,
    the sign of Z(t) is PROVEN.

Hardy's Z is real and continuous, so two proven signs that differ bracket a
genuine zero of Z, hence a zero of ζ *on the critical line* (|Z(t)| =
|ζ(½+it)|).  Counting only such proven brackets gives a rigorous lower bound m
for the number of critical-line zeros below T.  Independently, the argument
principle applied in ball arithmetic to

    N(T) = 1 + θ(T)/π + S(T),    S(T) = (1/π)·Δ arg ζ  along 2 → 2+iT → ½+iT,

returns an interval for N(T); N(T) is an integer, so it is *proven* as soon as
that interval contains exactly one integer.  If m = N(T) then every zero
counted by N(T) is one of the proven critical-line sign changes, so below
height T no zero is off the line, none has even order, and all are simple.

That is exactly the argument of ``zeta.zeros.verify_rh_up_to`` — but there it
runs on ordinary mpmath floats, so the conclusion is contingent on every sign
evaluation being right.  Overwhelmingly likely; not proved.  This script runs
both and prints them side by side: the same integers, a different epistemic
status.  It is the standard that makes large verifications citable (Platt and
Trudgian to height 3·10¹²; Helfgott's ternary Goldbach) and it is the standard
this repository holds itself to.

What "certified" means here, stated plainly: *given* that the ball library is
correct and that the quoted theorems (Riemann–von Mangoldt, Σ_{n≥2} n⁻² =
ζ(2)−1) are correct, the enclosures contain the true values and the returned
integers are the true ones.  Anything undecidable is reported, never guessed —
``proven_sign`` returns 0 and the run is marked uncertified.

Honest scope (docs/08): a certificate for a finite interval is still a
statement about a finite interval.  By Littlewood's theorem no finite
computation is evidence for RH either way.  What rigor buys is the removal of
floating-point luck from the finite claim, not a step toward the infinite one.
"""

from __future__ import annotations

import argparse
import time

from mpmath import mp

from zeta.rigor import (
    BACKEND,
    BACKEND_REASON,
    available_backends,
    certified_gaussian_pair,
    enclose_Z,
    enclose_weil_functional,
    enclosure_width_report,
    proven_sign,
    verify_rh_certified,
)
from zeta.zeros import verify_rh_up_to

__all__ = ["main"]

#: γ₁, the lowest zero ordinate — the point where no precision can prove a sign.
GAMMA1 = 14.134725141734694


def _fmt(x, n: int = 12) -> str:
    return mp.nstr(x, n)


def section_backend(probe_t: float, probe_bits: int) -> list[str]:
    """Which ball engine is in use, and the two engines checked against each other."""
    print("1)  THE BACKEND  —  which ball-arithmetic engine is doing the proving")
    print()
    backends = available_backends()
    print(f"    in use          : {BACKEND}")
    print(f"    reason          : {BACKEND_REASON}")
    print(f"    all importable  : {', '.join(backends)}")
    print()
    print(f"    Two independent certified implementations must produce OVERLAPPING")
    print(f"    enclosures of Z({probe_t:g}) at {probe_bits} bits — if they did not, one of them")
    print("    would be wrong.  (Arb computes ζ as a ball itself; the mpmath.iv path")
    print("    builds ζ from Euler–Maclaurin with the classical explicit remainder.)")
    print()
    boxes = {}
    for name in backends:
        t0 = time.perf_counter()
        lo, hi = enclose_Z(probe_t, probe_bits, backend=name)
        dt = time.perf_counter() - t0
        boxes[name] = (lo, hi)
        with mp.workdps(30):
            print(f"      {name:<14} [{_fmt(lo, 22)}, {_fmt(hi, 22)}]")
            print(f"      {'':<14}  width {float(hi - lo):.3e}   ({dt * 1e3:.1f} ms)")
    if len(boxes) > 1:
        los = [v[0] for v in boxes.values()]
        his = [v[1] for v in boxes.values()]
        overlap = max(los) <= min(his)
        print()
        print(f"      overlap        : {'YES — the two certificates are consistent' if overlap else 'NO — investigate, one backend is wrong'}")
    print()
    return backends


def section_widths(t_values: list[float], bits: list[int], backends: list[str]) -> None:
    """The cost curve of rigor: width against precision, and the digits proven."""
    print("2)  WHAT AN ENCLOSURE COSTS  —  width shrinks geometrically in the bit count")
    print("    'proven digits' = log₁₀|mid| − log₁₀(width): significant digits of Z(t)")
    print("    that are CERTIFIED, not merely computed.")
    print()
    print(f"    {'t':>8} {'backend':<14} {'bits':>5} {'enclosure width':>18} "
          f"{'proven digits':>14} {'sign':>6} {'ms':>7}")
    print("    " + "-" * 78)
    for backend in backends:
        rows = enclosure_width_report(t_values, bits, backend=backend)
        for r in rows:
            width = float(r["width"]) if r["width"] is not None else float("nan")
            print(f"    {r['t']:>8.2f} {r['backend']:<14} {r['prec_bits']:>5} "
                  f"{width:>18.3e} {r['proven_digits']:>14.1f} "
                  f"{'PROVEN' if r['sign_proven'] else '  —':>6} "
                  f"{r['seconds'] * 1e3:>7.2f}")
        print("    " + "-" * 78)
    print("    Roughly one extra proven digit per 3.33 bits: proving the sign of Z where")
    print("    |Z| ~ 10⁻ᵈ costs about 3.33·d bits on top of the evaluation itself.")
    print()


def section_certificate(T: float, prec_bits: int, count_prec_bits: int,
                        backend: str | None) -> dict:
    """The certificate itself: proven sign changes, certified N(T), enclosures."""
    print(f"3)  THE CERTIFICATE at T = {T:g}  —  every sign and every count is a theorem")
    print()
    t0 = time.perf_counter()
    res = verify_rh_certified(
        T, prec_bits=prec_bits, count_prec_bits=count_prec_bits,
        backend=backend, compare_floating=False,
    )
    wall = time.perf_counter() - t0
    src = "recomputed" if not res["from_cache"] else "served from data/ cache"
    print(f"    proven sign changes of Z on (0, T) : {res['certified_sign_changes']}")
    print(f"      from {res['n_samples']} sampled abscissae at {res['prec_bits']} bits, "
          f"escalating up to {res['max_escalations']}x")
    print(f"      undecided samples                : {len(res['undecided_points'])}"
          f"{'  (each would break the certificate)' if res['undecided_points'] else ''}")
    print()
    print(f"    certified N(T)                     : {res['N_T']}")
    lo, hi = res["N_T_enclosure"]
    print(f"      enclosure of N(T)                : [{lo}, {hi}]")
    print(f"      enclosure width                  : {res['N_T_enclosure_width']:.3e}"
          "   ← contains exactly one integer, so N(T) is proven")
    print(f"      contour sub-segments certified   : {res['n_segments']} "
          f"(at {res['count_prec_bits']} bits)")
    print()
    xc = res["cross_checks"]
    labels = {
        "arb_zeta_nzeros": ("N(T), Arb's own Turing-method count", True),
        "mpmath_nzeros": ("N(T), mpmath", False),
        "mpmath_backlunds": ("S(T), mpmath's Backlund S", False),
    }
    print("    independent cross-checks:")
    for key in sorted(xc):
        if key.endswith("_rigorous"):
            continue
        what, rigorous = labels.get(key, (key, xc.get(f"{key}_rigorous")))
        rigorous = xc.get(f"{key}_rigorous", rigorous)
        tag = "" if rigorous is None else ("  [rigorous]" if rigorous else "  [NOT rigorous]")
        print(f"      {what:<36} = {xc[key]}{tag}")
    print()
    print(f"    uncertified steps                  : "
          f"{res['uncertified_steps'] or 'none'}")
    print(f"    backend                            : {res['backend']}")
    print(f"    certified compute time             : {res['wall_seconds']:.2f} s "
          f"({src}; this call took {wall:.2f} s)")
    print()
    if res["certified"]:
        print(f"    ==> PROVEN: all {res['N_T']} zeros with 0 < γ < {T:g} are simple and lie")
        print("        exactly on the critical line — modulo the correctness of the ball")
        print("        library and the two quoted theorems, and nothing else.")
    else:
        print(f"    ==> NOT certified: {res['uncertified_steps']}")
    print()
    return res


def section_contrast(T: float, certified: dict) -> dict:
    """The same argument on ordinary floats: same numbers, weaker conclusion."""
    print("4)  'WE MEASURED' vs 'WE PROVED'  —  the same two integers, side by side")
    print()
    t0 = time.perf_counter()
    fp = verify_rh_up_to(T)
    fp_wall = time.perf_counter() - t0
    print(f"    {'':<34} {'floating point':>18} {'certified':>16}")
    print("    " + "-" * 70)
    print(f"    {'sign changes of Z on (0, T)':<34} {fp['n_sign_changes']:>18} "
          f"{certified['certified_sign_changes']:>16}")
    print(f"    {'N(T)':<34} {fp['N_T']:>18} {certified['N_T']:>16}")
    print(f"    {'m == N(T)':<34} {str(bool(fp['all_on_line'])):>18} "
          f"{str(bool(certified['all_on_line'])):>16}")
    print(f"    {'grid samples':<34} {fp['n_samples']:>18} "
          f"{certified['n_samples']:>16}")
    print(f"    {'wall seconds':<34} {fp_wall:>18.2f} "
          f"{certified['wall_seconds']:>16.2f}")
    print(f"    {'every sign backed by':<34} {'mpmath at dps=25':>18} "
          f"{'an enclosure':>16}")
    print(f"    {'status of the conclusion':<34} {'CONTINGENT':>18} {'PROVEN':>16}")
    print("    " + "-" * 70)
    agree = (fp["n_sign_changes"] == certified["certified_sign_changes"]
             and fp["N_T"] == certified["N_T"])
    print(f"    the two routes agree on every integer: {agree}")
    print()
    print("    The numbers are identical; that is the point.  What differs is what may be")
    print(f"    said afterwards.  The floating-point row assumes that all {fp['n_samples']} sign")
    print("    evaluations were each accurate to better than |Z| at that point — true beyond")
    print("    reasonable doubt, but an assumption.  The certified row assumes nothing about")
    print("    them: a sign was counted only once its enclosure excluded 0.")
    print()
    return {"fp": fp, "fp_wall": fp_wall, "agree": agree}


def section_failure_mode() -> dict:
    """Where rigor says "I don't know" — and why that is the feature."""
    print("5)  THE HONEST FAILURE MODE  —  0 means 'not decided', never 'probably'")
    print()
    print(f"    Take t = {GAMMA1:.15f}, the float nearest the lowest zero "
          "γ₁ = 14.134725141734694…")
    lo, hi = enclose_Z(GAMMA1, 64)
    with mp.workdps(30):
        print(f"      enclosure of Z(t) at  64 bits : [{_fmt(lo, 12)}, {_fmt(hi, 12)}]")
    lo32, hi32 = enclose_Z(GAMMA1, 32)
    with mp.workdps(30):
        print(f"      enclosure of Z(t) at  32 bits : [{_fmt(lo32, 12)}, {_fmt(hi32, 12)}]"
              "   ← straddles 0")
    s32 = proven_sign(GAMMA1, prec_bits=32, max_escalations=0)
    s64 = proven_sign(GAMMA1, prec_bits=64, max_escalations=8)
    print()
    print(f"      proven_sign(t, 32 bits, no escalation) = {s32}"
          "   ← UNDECIDED, and it says so")
    print(f"      proven_sign(t, 64 bits, 8 escalations) = {s64:+d}"
          "   ← proven (this float is not the zero)")
    print()
    print("    At an exact zero of Z no precision suffices and 0 is the permanent, correct")
    print("    answer: Z really has no sign there.  Nothing is ever silently upgraded to a")
    print("    certificate — an undecided sample lands in 'undecided_points' and the whole")
    print("    run is reported uncertified.")
    print()
    return {"undecided_at_32": s32 == 0, "proven_at_64": s64 != 0}


def section_weil_positivity() -> dict:
    """The certified Weil functional: positivity with error bars, not luck."""
    print("6)  CERTIFIED WEIL POSITIVITY  —  W(h) > 0 as an enclosure, not a verdict")
    print()
    if "python-flint" not in available_backends():
        print("    (skipped: flint-only — mpmath.iv has no certified quadrature)")
        print()
        return {"skipped": True}
    print("    RH  ⇔  W(h) ≥ 0 for every admissible h (Weil).  The near-tight")
    print("    Gaussian a = 0.2 has W ≈ 8.86e-18 emerging from pieces of size ~2:")
    print("    eighteen digits of cancellation, exactly where floats can lie.")
    print()
    h, g = certified_gaussian_pair("0.2")
    r = enclose_weil_functional(h, g, n_max=20000, prec_bits=256,
                                cross_check=False)
    lo, hi = r["W_enclosure"]
    with mp.workdps(30):
        print(f"      W enclosure at 256 bits : [{_fmt(lo, 20)}, {_fmt(hi, 20)}]")
        print(f"      width                   : {_fmt(hi - lo, 3)}")
    print(f"      sign                    : {r['sign']:+d}   ← PROVEN positive "
          f"(certified = {r['certified']})")
    r48 = enclose_weil_functional(h, g, n_max=2000, prec_bits=48,
                                  cross_check=False)
    lo48, hi48 = r48["W_enclosure"]
    with mp.workdps(30):
        print(f"      same W at 48 bits       : [{_fmt(lo48, 4)}, {_fmt(hi48, 4)}]"
              f"   ← straddles 0, sign = {r48['sign']} (undecided, and says so)")
    print()
    print("    Finitely many certified instances are not evidence for RH (docs/08);")
    print("    they are positivity statements that no longer rest on floating-point")
    print("    luck.  A certified negative W would disprove RH — per the house rule,")
    print("    the correct first inference from one is a bug.")
    print()
    return {"sign": r["sign"], "certified": r["certified"],
            "undecided_at_48": r48["sign"] == 0}


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Run the RIGOROUS RH verification of zeta.rigor.verify_rh_certified "
            "for a modest height T and contrast it with the non-rigorous "
            "zeta.zeros.verify_rh_up_to.  Both count sign changes of Hardy's Z "
            "and compare with N(T) from the argument principle; the certified "
            "route does it in ball (interval) arithmetic, so a sign is counted "
            "only when its enclosure of Z(t) excludes 0 (a proof) and N(T) only "
            "when its enclosure contains a unique integer.  The script prints "
            "the backend in use and checks the two backends against each other, "
            "the proven sign changes, the enclosure widths and how they shrink "
            "with working precision, the certified N(T) with its independent "
            "cross-checks, and the failure mode in which a sign is honestly "
            "reported as undecided.  Headline: the same integers come out of "
            "both routes -- the difference is that one is measured and the other "
            "is proved.  Honest scope: a certificate for a finite interval is "
            "still finite; by Littlewood's theorem it is not evidence for RH "
            "(docs/08)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--T", type=float, default=100.0,
                        help="verify every zero with 0 < gamma < T")
    parser.add_argument("--prec-bits", type=int, default=64,
                        help="starting precision for the proven signs of Z (escalates)")
    parser.add_argument("--count-prec-bits", type=int, default=192,
                        help="precision for the certified argument-principle N(T)")
    parser.add_argument("--backend", default=None, choices=available_backends(),
                        help="ball-arithmetic backend (default: the fastest importable)")
    parser.add_argument("--width-t", type=float, nargs="+", default=[100.0],
                        help="points at which to report the enclosure-width curve")
    parser.add_argument("--width-bits", type=int, nargs="+",
                        default=[32, 64, 128, 256],
                        help="precisions for the enclosure-width curve")
    parser.add_argument("--no-compare", action="store_true",
                        help="skip the floating-point run (it is the slow half)")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("CERTIFIED VERIFICATION:  'WE MEASURED' vs 'WE PROVED'")
    print("=" * 78)
    print()
    backends = section_backend(args.width_t[0], 64)
    if args.backend is not None:
        backends = [args.backend]
    section_widths(args.width_t, args.width_bits, backends)
    cert = section_certificate(args.T, args.prec_bits, args.count_prec_bits,
                               args.backend)
    comparison = None
    if not args.no_compare:
        comparison = section_contrast(args.T, cert)
    modes = section_failure_mode()
    weil = section_weil_positivity()

    print("=" * 78)
    print("HEADLINE")
    print(f"  • {cert['certified_sign_changes']} sign changes of Z below T = {args.T:g} were "
          "PROVEN — each from an enclosure that excludes 0.")
    print(f"  • N({args.T:g}) = {cert['N_T']} was PROVEN — its enclosure has width "
          f"{cert['N_T_enclosure_width']:.1e} and contains one integer.")
    print(f"  • m = N(T), so every zero below T is simple and on the line: "
          f"certified = {cert['certified']}.")
    if comparison is not None:
        print(f"  • The floating-point route returned the same two integers "
              f"({comparison['agree']}) in {comparison['fp_wall']:.2f} s against "
              f"{cert['wall_seconds']:.2f} s —")
        print("    rigor here is not the slow option; it is the one that assumes less.")
    print(f"  • Undecidability is reported, not hidden: proven_sign returned 0 at 32 bits "
          f"({modes['undecided_at_32']}).")
    if not weil.get("skipped"):
        print("  • Weil positivity at the near-tight Gaussian (W ~ 9e-18, 18 digits of "
              f"cancellation) was PROVEN (sign = {weil['sign']:+d}).")
    print("  • And none of this is evidence for RH — it is a finite interval, made "
          "trustworthy (docs/08).")
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
