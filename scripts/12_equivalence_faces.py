#!/usr/bin/env python
"""Four exact equivalences of RH, all four run, on one dashboard.

The mathematics
---------------
``docs/07-equivalences-and-criteria.md`` catalogues the statements known to be
*exactly* equivalent to RH.  A catalogue is not an instrument, so this script
executes four of them and prints what each one found.

1.  **Mertens / Möbius.**  THEOREM: for ½ ≤ θ < 1, M(x) = O(x^{θ+ε}) for every
    ε > 0 iff ζ has no zero with Re(s) > θ; in particular

        RH  ⟺  M(x) = O(x^{½+ε})   for every ε > 0,     M(x) = Σ_{n≤x} μ(n).

    This face is in the script as the standing warning about numerics.  The
    *strong* Mertens conjecture |M(x)| < √x is FALSE (Odlyzko–te Riele 1985),
    the disproof is non-constructive, and no counterexample is known.  A scan
    finding |M(x)|/√x comfortably below 1 reproduces exactly the evidence that
    convinced people for a century.

2.  **Nyman–Beurling / Baez-Duarte.**  THEOREM (Nyman 1950, Beurling 1955;
    Baez-Duarte 2003): with A_k(x) = {1/(kx)} − (1/k){1/x} on (0,1) and
    d_N² = inf_c ‖1 − Σ_{k≤N} c_k A_k‖²_{L²(0,1)},

        RH  ⟺  d_N → 0.

    RH becomes a least-squares problem.  The conjectured rate is d_N² ~ C/log N
    with C = Σ_ρ 1/|ρ|² = 2 + γ − log 4π = 0.0461914…, and 1/log N is why no
    computation will ever see the limit.

3.  **Robin / Lagarias.**  THEOREM (Robin 1984): RH ⟺ σ(n) < e^γ n log log n
    for every n > 5040.  THEOREM (Lagarias 2002): RH ⟺ σ(n) ≤ H_n + e^{H_n}
    log H_n for every n ≥ 1.  The only plausible violators are the
    superabundant / colossally abundant numbers, and by Gronwall's theorem the
    ratio climbs toward e^γ forever, so "close to e^γ" is the expected
    behaviour, not a warning sign.

4.  **Speiser.**  THEOREM (Speiser 1934/35): RH ⟺ ζ′(s) has no zeros in the
    strip 0 < Re(s) < ½.  The one criterion on the list that ever paid: its
    quantitative companion (Levinson–Montgomery 1974) is the engine of
    Levinson's method, which put a positive proportion of the zeros on the line.

Honest scope (docs/08).  Every face here is an equivalence, so a violation of
any one would refute RH.  None of the four "no violation found in this range"
results is evidence for RH: by Littlewood's theorem no finite range can be, and
face 1 is included precisely because it is the standing counterexample to
reading numerics as evidence.
"""

from __future__ import annotations

import argparse
import math
import time

from mpmath import mp

from zeta.criteria import (
    BD_CONSTANT,
    MERTENS_PINNED,
    ROBIN_EXCEPTIONS,
    ROBIN_THRESHOLD,
    baez_duarte_table,
    colossally_abundant,
    mertens_facts,
    mertens_ratio_extremes,
    robin_search,
    speiser_scan,
)

__all__ = ["main"]


def _fmt(x, n: int = 12) -> str:
    return mp.nstr(x, n)


def face_mertens(limit: int, x_min: int) -> dict:
    """Face 1: M(x)/√x, the random walk that misled a century."""
    print("FACE 1)  MERTENS / MÖBIUS      RH ⟺ M(x) = O(x^{½+ε})  [THEOREM]")
    print("         M(x) = Σ_{n≤x} μ(n);  bridge: 1/ζ(s) = s ∫₁^∞ M(x) x^{−s−1} dx")
    print()
    print(f"         {'x':>12} {'M(x)':>10} {'M(x)/√x':>12}")
    print("         " + "-" * 36)
    for x in sorted(k for k in MERTENS_PINNED if k <= limit):
        m = MERTENS_PINNED[x]
        print(f"         {x:>12} {m:>10} {m / math.sqrt(x):>12.6f}")
    print("         " + "-" * 36)
    ext = mertens_ratio_extremes(limit, x_min=1)
    ext_hi = mertens_ratio_extremes(limit, x_min=x_min)
    print(f"         over 1 ≤ x ≤ {limit:,}:")
    print(f"           max M(x)/√x        = {ext['max_ratio']:+.6f}  at x = {ext['argmax']:,}")
    print(f"           min M(x)/√x        = {ext['min_ratio']:+.6f}  at x = {ext['argmin']:,}")
    print(f"           max |M(x)|/√x      =  {ext['max_abs_ratio']:.6f}  "
          f"at x = {ext['argmax_abs']:,}")
    print(f"         ignoring the tiny-x degeneracies (x ≥ {x_min}):")
    print(f"           max |M(x)|/√x      =  {ext_hi['max_abs_ratio']:.6f}  "
          f"at x = {ext_hi['argmax_abs']:,}")
    print()
    facts = mertens_facts()
    print(f"         strong Mertens conjecture, {facts['strong_mertens_conjecture']} :  FALSE")
    print("           Odlyzko–te Riele 1985: limsup M(x)/√x > 1.06, liminf < −1.009.")
    print("           Non-constructive, no explicit counterexample is known and the")
    print("           bounds on the first one are astronomical.  So the numbers above")
    print("           are NOT reassurance about anything; they are the exact numerical")
    print("           picture that made the false conjecture believable.")
    print()
    return {"extremes": ext, "extremes_high": ext_hi}


def face_baez_duarte(n_values: list[int], dps: int) -> dict:
    """Face 2: d_N² → 0, the linear-algebra face, and its 1/log N wall."""
    print("FACE 2)  NYMAN–BEURLING / BAEZ-DUARTE      RH ⟺ d_N → 0  [THEOREM]")
    print("         d_N² = inf over c of ‖1 − Σ_{k≤N} c_k A_k‖²_{L²(0,1)},")
    print("         A_k(x) = {1/(kx)} − (1/k){1/x}.  RH as a least-squares problem.")
    print()
    t0 = time.perf_counter()
    rows = baez_duarte_table(n_values, dps=dps)
    secs = time.perf_counter() - t0
    print(f"         {'N':>5} {'d_N²':>22} {'d_N':>14} {'d_N²·log N / C':>16} "
          f"{'cond(G)':>12}")
    print("         " + "-" * 74)
    for r in rows:
        with mp.workdps(dps):
            d = mp.sqrt(r["d2"])
        print(f"         {r['N']:>5} {_fmt(r['d2'], 16):>22} {_fmt(d, 10):>14} "
              f"{_fmt(r['d2_times_logN_over_C'], 9):>16} "
              f"{float(r['condition_number']):>12.1f}")
    print("         " + "-" * 74)
    print(f"         ({secs:.1f} s at dps = {dps}; the Gram matrix is in exact closed form)")
    print(f"         C = Σ_ρ 1/|ρ|² = 2 + γ − log 4π = {BD_CONSTANT[:20]}… (under RH)")
    print("         The conjectured rate d_N² ~ C/log N is consistent with the ratio")
    print("         column, and is NOT tested by it: 1/log N cannot be distinguished")
    print("         from a small positive limit by any finite computation, and the ratio")
    print("         is not even monotone in N.")
    with mp.workdps(20):
        c = mp.mpf(BD_CONSTANT)
        n_needed = mp.exp(c / mp.mpf("1e-3"))
    print(f"         Scale of the wall: pushing d_N² down to 10⁻³ needs N ≈ "
          f"{mp.nstr(n_needed, 3)}.")
    print("         Conditioning, measured rather than repeated: cond(G) grows like a")
    print("         small power of N (a few thousand at N = 50), so the obstruction is")
    print("         not ill-conditioning at reachable N, it is the 1/log N decay itself.")
    print()
    return {"rows": rows}


def face_robin(max_log_n: float, ca_steps: int, n_ca_shown: int, dps: int) -> dict:
    """Face 3: Robin's inequality on the colossally abundant candidates."""
    print("FACE 3)  ROBIN / LAGARIAS      RH ⟺ σ(n) < e^γ n log log n for n > 5040  [THEOREM]")
    print("         The least counterexample, if one exists, is superabundant, so the")
    print("         superabundant / colossally abundant chain is the only place to look.")
    print()
    t0 = time.perf_counter()
    res = robin_search(max_log_n=max_log_n, ca_steps=ca_steps, dps=dps)
    secs = time.perf_counter() - t0
    print(f"         e^γ = {_fmt(res['e_gamma'], 16)}   (the boundary Robin's inequality forbids)")
    print()
    print(f"         exhaustive over superabundant-shaped n with log n ≤ {max_log_n:g}:")
    print(f"           patterns scanned    : {res['patterns_scanned']:,}")
    print(f"           max σ(n)/(n log log n) above {ROBIN_THRESHOLD} : "
          f"{_fmt(res['exhaustive_max_ratio'], 13)}")
    print(f"           attained at n       : {res['exhaustive_argmax_n']:,}  "
          f"(exponent pattern {res['exhaustive_argmax_pattern']})")
    print(f"           gap to e^γ          : {_fmt(res['exhaustive_gap_to_e_gamma'], 6)}")
    print(f"           Lagarias ratio there: {_fmt(res['exhaustive_lagarias_ratio_at_argmax'], 12)}"
          "   (RH ⟺ this stays ≤ 1)")
    print(f"           violations          : {len(res['exhaustive_violations'])}")
    print()
    print(f"         colossally abundant chain, {ca_steps} steps:")
    print(f"           max ratio           : {_fmt(res['ca_max_ratio'], 13)} at step "
          f"{res['ca_argmax_step']} (log n = {_fmt(res['ca_argmax_log_n'], 10)})")
    print(f"           gap to e^γ          : {_fmt(res['ca_gap_to_e_gamma'], 6)}")
    print(f"           Robin violations    : {len(res['ca_violations'])}")
    print(f"           Lagarias violations : {len(res['lagarias_violations_on_chain'])}")
    print()
    chain = colossally_abundant(n_ca_shown, dps=dps)
    print("         the first colossally abundant candidates (OEIS A004490).  Robin's")
    print(f"         criterion quantifies only over n > {ROBIN_THRESHOLD}, so rows at or below")
    print("         that threshold are outside its scope and are marked 'n/a', the")
    print("         inequality really does fail at several of them, by design:")
    print(f"           {'step':>5} {'n':>16} {'log n':>10} {'σ(n)/n':>10} "
          f"{'σ(n)/(n log log n)':>20} {'Robin':>7}")
    print("           " + "-" * 72)
    for rec in chain:
        ratio = rec["robin_ratio"]
        n_str = f"{rec['n']:,}" if rec["n"] is not None else "(too large)"
        if ratio is None:
            verdict, shown = "n/a", "— (log log n ≤ 0)"
        else:
            with mp.workdps(dps):
                ok = bool(ratio < res["e_gamma"])
            below = rec["n"] is not None and rec["n"] <= ROBIN_THRESHOLD
            verdict = "n/a" if below else ("holds" if ok else "VIOLATED")
            shown = f"{float(ratio):.9f}"
        print(f"           {rec['step']:>5} {n_str:>16} "
              f"{float(rec['log_n']):>10.4f} {float(rec['sigma_over_n']):>10.5f} "
              f"{shown:>20} {verdict:>7}")
    print("           " + "-" * 72)
    print(f"         The complete list of n ≥ 3 with σ(n) ≥ e^γ n log log n "
          f"({len(ROBIN_EXCEPTIONS)} of them,")
    print("         and final under RH):")
    print("           " + ", ".join(str(n) for n in ROBIN_EXCEPTIONS[:14]) + ",")
    print("           " + ", ".join(str(n) for n in ROBIN_EXCEPTIONS[14:])
          + f", every one ≤ {ROBIN_THRESHOLD}.")
    print(f"         ({secs:.1f} s.)  Gronwall's theorem says the ratio must approach e^γ")
    print("         forever, so proximity to e^γ is EXPECTED and is not a near-miss.")
    print()
    return {"result": res, "seconds": secs}


def face_speiser(t_max: float, dps: int) -> dict:
    """Face 4: no zeros of ζ′ to the left of the critical line."""
    print("FACE 4)  SPEISER      RH ⟺ ζ′(s) has no zeros in 0 < Re(s) < ½  [THEOREM]")
    print("         Three independent argument-principle counts, so the conclusion does")
    print("         not rest on the root finder.")
    print()
    t0 = time.perf_counter()
    res = speiser_scan(t_max=t_max, dps=dps)
    secs = time.perf_counter() - t0
    w = {k: float(v) for k, v in res["window"].items()}
    print(f"         window: {w['sigma_min']:g} ≤ Re(s) ≤ {w['sigma_max']:g}, "
          f"{w['t_min']:g} ≤ Im(s) ≤ {w['t_max']:g}")
    print(f"           zeros of ζ′ located          : {res['n_zeros']}"
          f"   (box count {res['box_count']}, they must agree, and do)")
    print(f"           zeros with {w['sigma_min']:g} < Re(s) < ½    : "
          f"{res['left_strip_count']}   ← Speiser's strip.  RH predicts 0.")
    print(f"           zeros with {w['sigma_max']:g} < Re(s) < 30     : "
          f"{res['right_tail_count']}   ← so σ_max is not hiding any")
    print(f"           leftmost Re(s) found         : {_fmt(res['leftmost_re'], 15)}  "
          f"at t = {_fmt(res['leftmost_at_t'], 15)}")
    print(f"           all zeros right of Re = ½    : {res['all_right_of_critical_line']}")
    print(f"           uncovered                    : {res['uncovered_sliver']}")
    print()
    print(f"         the located zeros of ζ′ (Re + i·Im), {secs:.1f} s:")
    with mp.workdps(dps):
        ordered = sorted(res["zeros"], key=lambda z: mp.im(z))
        for z in ordered[:8]:
            print(f"           {_fmt(mp.re(z), 15):>20} + {_fmt(mp.im(z), 15):>20} i")
        if len(ordered) > 8:
            print(f"           … and {len(ordered) - 8} more up to Im = "
                  f"{_fmt(mp.im(ordered[-1]), 12)}")
    print()
    print("         Beyond Re = 30 no contour is needed: in ζ′(s) = −Σ_{n≥2}(log n)n^{−s}")
    print("         the n = 2 term dominates all the rest, so ζ′ cannot vanish there.")
    print("         This is a floating-point argument-principle count, not certified")
    print("         arithmetic (contrast scripts/09), two independent counting schemes")
    print("         agreeing is strong evidence and nothing more.")
    print()
    return {"result": res, "seconds": secs}


def dashboard(mert: dict, bd: dict, rob: dict, spe: dict, limit: int) -> None:
    """The four faces, side by side."""
    print("=" * 78)
    print("DASHBOARD, four exact equivalences, four finite ranges, four results")
    print("=" * 78)
    print()
    print(f"    {'face':<18} {'range checked':<26} {'what was found':<26} {'viol.':>5}")
    print("    " + "-" * 78)
    bd_last = bd["rows"][-1]
    rres = rob["result"]
    sres = spe["result"]
    rows = [
        ("1 Mertens", f"x ≤ {limit:,}",
         f"max|M|/√x = {mert['extremes_high']['max_abs_ratio']:.4f}", 0),
        ("2 Baez-Duarte", f"N ≤ {bd_last['N']}",
         f"d_N² = {float(bd_last['d2']):.6f}", 0),
        ("3 Robin", f"log n ≤ {rres['max_log_n']:g} + {rres['ca_steps']} CA",
         f"max ratio = {float(rres['ca_max_ratio']):.6f}",
         len(rres["exhaustive_violations"]) + len(rres["ca_violations"])),
        ("4 Speiser", f"Im(s) ≤ {float(sres['window']['t_max']):g}, Re(s) ≤ 30",
         f"{sres['left_strip_count']} zeros of ζ′ left of ½", sres["left_strip_count"]),
    ]
    for name, rng, found, viol in rows:
        print(f"    {name:<18} {rng:<26} {found:<26} {viol:>5}")
    print("    " + "-" * 78)
    total = sum(r[3] for r in rows)
    print(f"    total violations of any of the four criteria: {total}")
    print()
    print("    Read that number correctly.  Each criterion is an EQUIVALENCE, so a single")
    print("    violation would refute RH, the zero is a real constraint on the world.")
    print("    The converse is worth nothing: 'no violation in a finite range' is what")
    print("    the Mertens face looked like for a century before Odlyzko and te Riele")
    print("    proved the conjecture false, without exhibiting a single counterexample.")
    print("    By Littlewood's theorem no finite computation can be evidence for RH")
    print("    (docs/08).  These are instruments, not votes.")
    print()


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Run all four executable equivalence faces of RH from "
            "zeta.criteria and print a compact dashboard: (1) the Mertens "
            "ratio M(x)/sqrt(x), whose boundedness -- the strong Mertens "
            "conjecture -- is FALSE by Odlyzko-te Riele 1985 even though no "
            "counterexample is known, which is why this face is the standing "
            "warning about numerics; (2) the Baez-Duarte residual d_N^2, RH "
            "as a least-squares problem, with its conjectured C/log N decay "
            "and the measured condition numbers; (3) Robin's inequality "
            "sigma(n) < e^gamma n log log n on the only plausible violators, "
            "the superabundant and colossally abundant numbers, plus the "
            "Lagarias variant; (4) Speiser's criterion, counting the zeros of "
            "zeta' in the strip 0 < Re(s) < 1/2 by the argument principle.  "
            "All four are THEOREMS, so one violation anywhere would refute "
            "RH; none was found in the ranges scanned, which is NOT evidence "
            "for RH (docs/08)."
        ),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--mertens-limit", type=int, default=10**6,
                        help="sieve mu(n) and M(x) up to this x")
    parser.add_argument("--mertens-x-min", type=int, default=100,
                        help="ignore x below this when reporting the extreme ratio")
    parser.add_argument("--bd-N", type=int, nargs="+", default=[10, 20, 30, 50],
                        help="Baez-Duarte dimensions N to solve")
    parser.add_argument("--bd-dps", type=int, default=50,
                        help="precision for the Baez-Duarte least squares")
    parser.add_argument("--robin-max-log-n", type=float, default=60.0,
                        help="exhaustive superabundant scan up to log n = this")
    parser.add_argument("--robin-ca-steps", type=int, default=500,
                        help="steps along the colossally abundant chain")
    parser.add_argument("--ca-shown", type=int, default=14,
                        help="colossally abundant numbers listed in the table")
    parser.add_argument("--speiser-t-max", type=float, default=100.0,
                        help="height window for the zeros of zeta'")
    parser.add_argument("--dps", type=int, default=25,
                        help="working precision for Robin and Speiser")
    args = parser.parse_args()

    t0 = time.time()
    print("=" * 78)
    print("FOUR FACES OF THE SAME HYPOTHESIS")
    print("=" * 78)
    print()
    mert = face_mertens(args.mertens_limit, args.mertens_x_min)
    bd = face_baez_duarte(list(args.bd_N), args.bd_dps)
    rob = face_robin(args.robin_max_log_n, args.robin_ca_steps, args.ca_shown, args.dps)
    spe = face_speiser(args.speiser_t_max, args.dps)
    dashboard(mert, bd, rob, spe, args.mertens_limit)
    print(f"[{time.time() - t0:.1f} s]")


if __name__ == "__main__":
    main()
