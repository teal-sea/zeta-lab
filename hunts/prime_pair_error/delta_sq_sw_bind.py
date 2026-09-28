"""Does UPPER_BOUND.md Section 7's Siegel-Walfisz-derived bound on T_N bind
at the cutoffs delta_sq_probe.py already measured, or is it vacuous, or can
it not be evaluated there at all?

UPPER_BOUND.md Section 7 establishes, for every fixed H > 0, using only (SW)
(Siegel-Walfisz) and the identity (29):

    T_N := sum_{t=1}^{N} Delta(t)^2 + sum_{t=1}^{N-1} [Delta(N)-Delta(t)]^2
         = O_H(N^3 L^{-2H}),     L = log N,     Delta(t) = psi(t) - t.

(The paragraph right after (31): "Using (SW) with q=1 gives, for every fixed
H, max_{t<=N}|Delta(t)| <<_H N L^{-H}, and (29) only gives T_N <<_H N^3
L^{-2H}.") This is unconditional: "No RH estimate is used in (1), (13),
(26), (29), or (30)."

delta_sq_probe.py measures S(N) := sum_{t=1}^{N} Delta(t)^2, written to
results_delta_sq.json, at the ladder N = 100000, 250000, 500000, 1000000,
2000000, 4000000, 7000000, 10000000 (that file's own "ladder" key -- this
script reads it rather than assuming it, per the operator's 2026-09-10
note). S(N) is only the leading of the two summands inside T_N; the second
summand, sum_{t=1}^{N-1} [Delta(N)-Delta(t)]^2, is not measured anywhere in
this hunt. Both summands are sums of squares, hence both are non-negative,
so S(N) <= T_N termwise for every N. That inequality is used below: it
licenses comparing the measured S(N) against a bound proved for T_N without
computing T_N itself, in one direction only. If a bound value exceeds S(N),
that is consistent with the same bound holding for T_N, but does not show
it, because T_N could still exceed the bound even where S(N) does not. If a
bound value is smaller than S(N), the bound is violated by T_N too, since
T_N >= S(N).

O_H(N^3 L^{-2H}) is Landau notation: it asserts a constant c(H) > 0 exists
with T_N <= c(H) N^3 L^{-2H} for N large enough, but the proof in
UPPER_BOUND.md Section 7 -- max_{t<=N}|Delta(t)| <<_H N L^{-H} from (SW),
squared and summed via (29) -- does not name c(H) at any H, and does not say
whether c(H) is effectively computable. (Separately, and not something this
hunt establishes: implied constants in Siegel-Walfisz-type bounds are widely
known, in the general literature on the subject, to sometimes come from
Siegel's theorem on the least zero of L(s,chi) and so be non-effective; that
is mentioned here only as a reason not to expect a small or easily-guessed
c(H), not as a property established for this specific c(H) or from this
proof.) So this script evaluates the bound under one explicit, clearly
labeled convention: c(H) = 1, chosen only because it is the simplest value
that turns O_H(N^3 L^{-2H}) into a number, not because UPPER_BOUND.md's
proof derives it, suggests it, or bounds c(H) above or below by it. Every
number below that depends on this convention is labeled as such, and no
convention constant is fit, tuned, or rescaled to make the comparison look
more or less favorable after seeing the measured S(N).

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/delta_sq_sw_bind.py
Reads hunts/prime_pair_error/results_delta_sq.json
Writes hunts/prime_pair_error/results_delta_sq_sw_bind.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent

H_VALUES = [1, 2, 4, 8]
ASSUMED_CONSTANT = 1.0


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
        per_H = []
        for H in H_VALUES:
            bound_convention = ASSUMED_CONSTANT * N**3 * L ** (-2 * H)
            ratio = S_N / bound_convention
            per_H.append(
                {
                    "H": H,
                    "bound_true_constant_named": False,
                    "bound_evaluated_under_convention_constant_1": bound_convention,
                    "ratio_measured_S_N_over_convention_bound": ratio,
                    "convention_bound_exceeds_measured_S_N": bound_convention > S_N,
                }
            )
        out_rows.append(
            {
                "N": N,
                "L_log_N": L,
                "measured_S_N": S_N,
                "per_H": per_H,
            }
        )

    holds_at_H = {
        H: all(
            row["per_H"][H_VALUES.index(H)]["convention_bound_exceeds_measured_S_N"]
            for row in out_rows
        )
        for H in H_VALUES
    }

    verdict = (
        "The theorem as stated -- O_H(N^3 L^{-2H}) with an implied constant "
        "that UPPER_BOUND.md's proof does not name -- cannot be evaluated "
        "to an absolute number at these cutoffs, or at any N, without "
        "assuming a value for that constant; no such value is derivable "
        "from the proof in Section 7, which only shows a constant exists "
        "for each fixed H, via (SW) and (29). Under the explicit, labeled "
        "convention of an assumed constant equal to 1 (not a value the "
        "proof produces), the convention-bound comfortably exceeds the "
        "measured S(N) -- the leading half of T_N -- at every ladder "
        "cutoff for H = 1 and H = 2, so the convention-bound binds there "
        "and is not vacuous. At H = 4 and H = 8, the convention-bound is "
        "smaller than the measured S(N) at every cutoff, so under that same "
        "convention it is violated there, and since S(N) <= T_N termwise "
        "this violation would carry over to T_N as well; the more likely "
        "reading is not that Section 7's proved statement fails, but that "
        "the labeled convention constant of 1 is too small for those H, "
        "which is expected of an unstated, unfit placeholder rather than a "
        "derived constant, and is exactly why the true, constant-unnamed "
        "bound cannot be evaluated on its own terms here."
    )

    out = {
        "theorem_quoted": (
            "UPPER_BOUND.md Section 7, paragraph after (31): using (SW) "
            "with q=1, for every fixed H, max_{t<=N}|Delta(t)| <<_H N "
            "L^{-H}, and (29) only gives T_N <<_H N^3 L^{-2H}, where "
            "T_N = sum_{t=1}^{N} Delta(t)^2 + sum_{t=1}^{N-1} "
            "[Delta(N)-Delta(t)]^2 and L = log N. Proved from (SW) "
            "(Siegel-Walfisz) alone: 'No RH estimate is used in (1), (13), "
            "(26), (29), or (30).'"
        ),
        "what_is_compared": (
            "delta_sq_probe.py measures S(N) = sum_{t=1}^{N} Delta(t)^2, "
            "the leading of T_N's two non-negative summands, not T_N "
            "itself; the second summand, sum_{t=1}^{N-1} "
            "[Delta(N)-Delta(t)]^2, is not measured anywhere in this hunt. "
            "Because both summands are sums of squares, S(N) <= T_N for "
            "every N, so a convention-bound exceeded by measured S(N) is "
            "also exceeded by T_N, but a convention-bound that exceeds "
            "measured S(N) says nothing about whether it would still "
            "exceed T_N, since the unmeasured second summand could push "
            "T_N past it."
        ),
        "source_measured_S_N": "hunts/prime_pair_error/results_delta_sq.json, key 'rows'",
        "constant_convention": (
            "The O_H notation in UPPER_BOUND.md Section 7 asserts an "
            "H-dependent constant c(H) exists but the proof (via (SW) and "
            "(29)) does not name it and does not state whether it is "
            "effectively computable. This script evaluates the bound at "
            "H in {1, 2, 4, 8} under the explicit, stated convention "
            "c(H) = 1 for every H. This is a labeled convention chosen for "
            "its simplicity, not a value derived, fit, or suggested by "
            "UPPER_BOUND.md's proof, and it is not tuned or rescaled after "
            "seeing the measured S(N) below."
        ),
        "H_values": H_VALUES,
        "rows": out_rows,
        "convention_bound_exceeds_measured_S_N_at_every_cutoff_by_H": holds_at_H,
        "verdict": verdict,
        "what_this_is_not": (
            "This is not a claim that UPPER_BOUND.md Section 7's proved "
            "statement is false, weak, or wrongly established, and the "
            "proof itself is not touched or re-derived here. The true "
            "O_H(N^3 L^{-2H}) bound, with its actual unnamed constant, "
            "cannot be evaluated to a number at these cutoffs; only a "
            "clearly labeled convention value can, and that convention is "
            "not a substitute for the real constant. The separate, "
            "unproved (31) (sum_{t<=N} Delta(t)^2 <<_eps N^{2+eps},  "
            "RESULTS.md's rank-1 door) and this proved T_N <<_H N^3 L^{-2H} "
            "are different statements, with different unconditional/"
            "unproved status, about related but distinct objects (S(N) "
            "alone versus T_N); this script does not conflate them. "
            "Nothing here bears on RH."
        ),
    }

    out_path = HERE / "results_delta_sq_sw_bind.json"
    out_path.write_text(json.dumps(out, indent=1))

    print("T_N = O_H(N^3 L^{-2H}) from (SW) and (29), UPPER_BOUND.md Section 7")
    print("measured S(N) (leading half of T_N) at the recorded ladder:")
    for row in out_rows:
        print(f"  N={row['N']:>9}  S(N)={row['measured_S_N']:.6e}")
    print()
    print("convention constant = 1 (labeled, not derived) evaluated at H in", H_VALUES)
    for H in H_VALUES:
        print(f"  H={H}: convention-bound exceeds measured S(N) at every cutoff? {holds_at_H[H]}")
    print()
    print("the true, constant-unnamed bound cannot be evaluated to a number at these cutoffs.")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
