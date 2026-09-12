"""Does an *effective* (explicit, computable) version of the Siegel-Walfisz
input actually used in UPPER_BOUND.md Section 7 exist, and if so, does it
bind against the measured S(N) in results_delta_sq.json, replacing
delta_sq_sw_bind.py's labeled convention constant (=1) with a real one?

Section 7 does not use (SW) (UPPER_BOUND.md Section 1 item 3, "uniformly for
q <= L^B") at a growing modulus. It uses only the q=1 case: "Using (SW) with
q=1 gives, for every fixed H, max_{t<=N}|Delta(t)| <<_H N L^{-H}." At q=1
there is no reduced residue class and no Dirichlet character other than the
principal one; psi(t;1,1) is just psi(t), and the classical unconditional
statement behind this line is not really Siegel-Walfisz at all -- it is the
zero-free-region-derived prime number theorem remainder for zeta(s) alone,

    psi(x) = x + O(x * exp(-c1 * sqrt(log x))),                          (*)

proved effectively (an explicit, computable c1 and threshold x0) since de la
Vallee Poussin (1899), decades before Siegel's theorem (1935) or the
Siegel-Walfisz theorem (1936). The general (SW) statement is ineffective
only because, for q > 1 ranging over an unbounded set as N -> infinity, it
cannot rule out a Landau-Siegel zero attached to some real primitive
character mod q in that range, and Siegel's theorem (used to exclude that)
supplies no computable constant. No real character enters at q=1: the
classical zero-free region for zeta(s) is proved by the elementary "3-4-1"
inequality alone, with no auxiliary L(s, chi) and no Siegel-zero case split.
See SW_EFFECTIVE.md for the full argument, its scope, and what it does and
does not settle; this script only carries out the numeric side of it.

(*) is a strictly stronger statement than "for every fixed H, <<_H N L^{-H}"
-- exp(-c1 sqrt(log x)) beats every fixed power of log x -- so it implies
Section 7's max_{t<=N}|Delta(t)| <<_H N L^{-H} line as a corollary, for any
H, with no extra ineffective input. Squaring and summing over ~N terms the
way (29) does gives, on the same convention basis as delta_sq_sw_bind.py's
N^3 L^{-2H} (assumed constant 1),

    T_N <bound> = N^3 * exp(-2 * c1 * sqrt(log N)),                      (**)

again under an explicit, labeled convention: the leading constant K in
|Delta(t)| <= K * t * exp(-c1 sqrt(log t)) is taken to be K=1, for the same
reason delta_sq_sw_bind.py took its convention constant to be 1 -- it is the
simplest value that turns the O-notation into a number, not a value derived
from any specific theorem. What is NOT a convention here, unlike in
delta_sq_sw_bind.py, is c1's existence and effectiveness: an explicit c1 is
known to exist in the literature (Rosser-Schoenfeld 1962; McCurley 1984;
Kadiri 2005; Mossinghoff-Trudgian 2015; Platt-Trudgian 2021;
Broadbent-Kadiri-Lumley-Ng-Wilk 2021, among others, some giving the sharper
Vinogradov-Korobov-type saving exp(-c(log x)^{3/5}/(log log x)^{1/5}) in
place of the sqrt(log x) exponent used here for simplicity). This script has
no network or library access to pull a citation-checked numeric digit for
c1 from any of those papers, so instead of asserting one, it solves, at
each ladder N, for the threshold c1*(N) at which (**) under the K=1
convention exactly equals the measured S(N):

    N^3 exp(-2 c1*(N) sqrt(log N)) = S(N)
    c1*(N) = (3 log N - log S(N)) / (2 sqrt(log N)).

Because (**) is strictly decreasing in c1, the convention-(**) bound exceeds
(binds against) measured S(N) at a given N iff the true c1 is below
c1*(N); it is violated there iff the true c1 is above c1*(N). The smallest
c1*(N) over the ladder is the binding constraint: any c1 below that value
makes (**) exceed S(N) at every ladder cutoff. The published constants this
script cannot verify here are, as far as they can be recalled without a
checked citation, of order a few tenths up to about 1 in this normalization
-- well below the computed thresholds below -- so it is likely, but NOT
confirmed against a primary source in this run, that the real effective
bound binds comfortably everywhere S(N) is measured. Pinning an exact,
citation-checked (c1, K, x0) and rerunning this comparison with it in place
of the swept range is the residual task; see SW_EFFECTIVE.md.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/delta_sq_sw_effective_bind.py
Reads hunts/prime_pair_error/results_delta_sq.json
Writes hunts/prime_pair_error/results_delta_sq_sw_effective_bind.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Illustrative sweep only, not a citation: spans the rough order of magnitude
# of c1 values that appear across the classical-to-modern literature on
# explicit zero-free regions for zeta(s), from very conservative early
# constants up to sharper modern ones, in the exp(-c1 sqrt(log x))
# normalization used in (*)/(**) above.
C1_SWEEP = [0.05, 0.1, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 2.5, 3.0]


def main() -> int:
    src_path = HERE / "results_delta_sq.json"
    src = json.loads(src_path.read_text())

    ladder = src["ladder"]
    rows_by_N = {row["N"]: row for row in src["rows"]}
    missing = [N for N in ladder if N not in rows_by_N]
    if missing:
        raise SystemExit(f"results_delta_sq.json ladder/rows mismatch: {missing}")

    out_rows = []
    for N in ladder:
        S_N = rows_by_N[N]["S_N"]
        L = math.log(N)
        sqrtL = math.sqrt(L)
        c1_star = (3 * math.log(N) - math.log(S_N)) / (2 * sqrtL)

        per_c1 = []
        for c1 in C1_SWEEP:
            bound = N**3 * math.exp(-2 * c1 * sqrtL)
            per_c1.append(
                {
                    "c1": c1,
                    "bound_under_K_equals_1_convention": bound,
                    "ratio_measured_S_N_over_bound": S_N / bound,
                    "bound_exceeds_measured_S_N": bound > S_N,
                }
            )

        out_rows.append(
            {
                "N": N,
                "L_log_N": L,
                "measured_S_N": S_N,
                "c1_star_threshold": c1_star,
                "per_c1": per_c1,
            }
        )

    min_c1_star = min(row["c1_star_threshold"] for row in out_rows)
    binding_N = min(out_rows, key=lambda row: row["c1_star_threshold"])["N"]

    binds_at_c1 = {
        c1: all(
            row["per_c1"][C1_SWEEP.index(c1)]["bound_exceeds_measured_S_N"]
            for row in out_rows
        )
        for c1 in C1_SWEEP
    }

    verdict = (
        "Unlike delta_sq_sw_bind.py's target -- the general O_H(N^3 L^{-2H}) "
        "corollary, whose implied constant Section 7's proof never names or "
        "claims is effective -- the q=1 statement Section 7 actually derives "
        "this corollary from reduces to the classical zero-free-region "
        "prime number theorem remainder for zeta(s) alone, which has been "
        "effective (an explicit, computable c1 and threshold) since de la "
        "Vallee Poussin, with no Siegel-zero case split because no real "
        "Dirichlet character enters at q=1. So an effective bound DOES "
        "exist here, in contrast to the recurrence this task was framed to "
        "expect. What this script cannot do without network or library "
        "access is pull a citation-checked numeric value for that "
        "constant; instead it reports the threshold c1*(N) at each ladder "
        "point above which the convention-K=1 bound (**) would be violated "
        "by the measured S(N), and sweeps an illustrative range of c1 "
        f"values. The binding constraint is c1 < {min_c1_star:.5f} "
        f"(at N={binding_N}): any true effective c1 below that value "
        "makes (**) exceed measured S(N) at every ladder cutoff. Published "
        "explicit zero-free-region constants, as far as can be recalled "
        "here without a verified citation, are of order a few tenths to "
        "about 1 in this normalization, comfortably under that threshold, "
        "so it is likely -- not confirmed in this run -- that the real "
        "effective bound binds everywhere on the ladder, unlike the "
        "convention-1 L^{-2H} bound at H=4 and H=8 in "
        "results_delta_sq_sw_bind.json, which was violated there."
    )

    out = {
        "what_is_evaluated": (
            "The q=1 case of (SW) as Section 7 actually uses it: "
            "max_{t<=N}|Delta(t)| <<_H N L^{-H} for every fixed H, derived "
            "there from the stronger unconditional statement "
            "psi(x) = x + O(x exp(-c1 sqrt(log x))), effective since de la "
            "Vallee Poussin (1899) because q=1 involves no Dirichlet "
            "character other than the principal one and so no Siegel-zero "
            "ineffectivity. This is a materially different question from "
            "the general (SW) statement uniform over growing q <= L^B "
            "(q > 1), which is used elsewhere in this hunt (e.g. "
            "UPPER_BOUND.md Section 5, SW_MOMENT_SPLICE.md) and DOES carry "
            "genuine Siegel-zero ineffectivity; this script and "
            "SW_EFFECTIVE.md do not claim to resolve that case."
        ),
        "convention": (
            "T_N's bound under (29) is evaluated as N^3 * exp(-2 c1 "
            "sqrt(log N)), i.e. |Delta(t)| <= K t exp(-c1 sqrt(log t)) "
            "squared and summed over ~N terms, with the leading constant "
            "K fixed at the labeled convention K=1 -- for the same reason "
            "delta_sq_sw_bind.py used a convention constant of 1: it is "
            "the simplest value turning O(...) into a number, not a value "
            "any cited theorem produces. Unlike that script's c(H), c1's "
            "existence and effectiveness are not a convention; only its "
            "numeric value is swept here rather than cited, for lack of "
            "network or library access to a primary source in this run."
        ),
        "source_measured_S_N": "hunts/prime_pair_error/results_delta_sq.json, key 'rows'",
        "c1_sweep": C1_SWEEP,
        "rows": out_rows,
        "min_c1_star_threshold_over_ladder": min_c1_star,
        "min_c1_star_threshold_at_N": binding_N,
        "bound_exceeds_measured_S_N_at_every_cutoff_by_c1": binds_at_c1,
        "verdict": verdict,
        "what_this_is_not": (
            "This does not make the N^3 L^{-2H}-type bound useful for the "
            "unconditional upper-bound goal: Section 7 already notes this "
            "component is a full power of N short of the unproved target "
            "(31), N^{2+eps}, and that gap is exactly as large whether or "
            "not the constant in front of it is known. Effectiveness and "
            "sufficiency are different questions; this script and "
            "SW_EFFECTIVE.md answer only the first, for the q=1 term "
            "Section 7 actually uses. Nothing here bears on RH."
        ),
    }

    out_path = HERE / "results_delta_sq_sw_effective_bind.json"
    out_path.write_text(json.dumps(out, indent=1))

    print("q=1 case of (SW): effective since de la Vallee Poussin, no Siegel-zero issue.")
    print("threshold c1*(N) (convention K=1) at which (**) is violated by measured S(N):")
    for row in out_rows:
        print(f"  N={row['N']:>9}  S(N)={row['measured_S_N']:.6e}  c1*={row['c1_star_threshold']:.5f}")
    print()
    print(f"binding constraint: true c1 < {min_c1_star:.5f} binds at every ladder cutoff (K=1 convention)")
    print("bound_exceeds_measured_S_N_at_every_cutoff, by swept c1:")
    for c1 in C1_SWEEP:
        print(f"  c1={c1}: {binds_at_c1[c1]}")
    print()
    print("no citation-checked numeric c1 is asserted here; see SW_EFFECTIVE.md.")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
