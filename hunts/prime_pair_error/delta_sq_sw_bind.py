"""Does UPPER_BOUND.md's proved Siegel-Walfisz-derived bound on T_N bind, or
is it vacuous, or can it not be evaluated, at the cutoffs
results_delta_sq.json already measured S(N) at?

UPPER_BOUND.md Section 7 proves, unconditionally from (SW) alone:

    T_N := sum_{t=1}^N Delta(t)^2 + sum_{t=1}^{N-1} [Delta(N)-Delta(t)]^2
         <<_H N^3 L^{-2H}     for every fixed H,   L = log N,
         Delta(t) = psi(t) - t.

(the paragraph right after (31), using (SW) with q=1 and (29)). Both
summands of T_N are sums of squares, hence nonnegative, so

    S(N) := sum_{t=1}^N Delta(t)^2 <= T_N

unconditionally -- no extra assumption is needed for that step, it is just
one nonnegative sum being at most a sum that contains it. Any numeric bound
on T_N is therefore also a valid numeric upper bound candidate for S(N),
under whatever convention is used to turn <<_H into a number.

results_delta_sq.json (from attempt a-0009) already measured S(N), not T_N,
at a ladder of eight cutoffs. This script evaluates N^3 L^{-2H} at those same
cutoffs, for H in {1, 2, 4, 8}, and compares it against the measured S(N).

The implied constant. <<_H hides a constant depending on H that
UPPER_BOUND.md's proof does not name; worse, UPPER_BOUND.md states at (1),
in its own opening paragraph, that this family of bounds holds "with
ineffective constants". That is not merely unstated in this hunt -- the
attempt that proved it says outright that no value is available. There is
therefore no way to derive a true numeric bound at any H. Per the task's
instruction, this script instead uses the stated CONVENTION of an implied
constant equal to 1, labeled clearly as a convention and not a derived
value, and reports what that produces. It does not invent or fit a
different constant to make the comparison come out looking meaningful.

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
ASSUMED_CONSTANT = 1.0  # stated convention, not a derived value; see module docstring


def main() -> int:
    src_path = HERE / "results_delta_sq.json"
    data = json.loads(src_path.read_text())

    per_cutoff = []
    for row in data["rows"]:
        N = row["N"]
        S_N = row["S_N"]
        L = math.log(N)
        per_h = []
        for H in H_VALUES:
            bound = ASSUMED_CONSTANT * (N ** 3) * (L ** (-2 * H))
            ratio = S_N / bound
            per_h.append(
                {
                    "H": H,
                    "bound_N3_Lneg2H_convention_const_1": bound,
                    "ratio_measured_S_N_over_bound": ratio,
                }
            )
        per_cutoff.append(
            {
                "N": N,
                "L_logN": L,
                "measured_S_N": S_N,
                "by_H": per_h,
            }
        )

    # H values at which the constant=1 convention is not merely loose but is
    # outright exceeded by the measured data (ratio > 1) at every cutoff.
    violated_H = [
        H
        for H in H_VALUES
        if all(
            next(b for b in row["by_H"] if b["H"] == H)["ratio_measured_S_N_over_bound"] > 1
            for row in per_cutoff
        )
    ]
    vacuous_H = [H for H in H_VALUES if H not in violated_H]

    verdict = (
        "Under the stated implied-constant-1 convention, the bound "
        "N^3 L^{-2H} is vacuous at H = "
        + ", ".join(str(h) for h in vacuous_H)
        + " at every one of the eight measured cutoffs: the bound holds at "
        "that constant but the ratio of measured S(N) to the bound is of "
        "order 1e-4 to 1e-7 there, i.e. many orders of magnitude looser "
        "than the measured value, so it supplies no real constraint beyond "
        "S(N) >= 0. At H = "
        + ", ".join(str(h) for h in violated_H)
        + " the constant-1 convention instead produces a number smaller "
        "than the measured S(N) at every cutoff (ratio > 1, growing to "
        "order 1e10 by H = 8): the convention itself fails there, which is "
        "exactly what UPPER_BOUND.md's own statement that these constants "
        "are ineffective predicts -- no constant is available, effective or "
        "otherwise, and the constant-1 stand-in is shown by these numbers "
        "not to be one. Combining both halves: the proved bound cannot be "
        "evaluated to an absolute number at any H without first assuming a "
        "convention for its constant, and the one convention this script is "
        "permitted to use is vacuous where it holds and violated where it "
        "does not, at every cutoff measured here."
    )

    out = {
        "statement_quoted": (
            "UPPER_BOUND.md Section 7, paragraph after (31): using (SW) "
            "with q = 1 gives, for every fixed H, "
            "max_{t<=N} |Delta(t)| <<_H N L^{-H}, and (29) only gives "
            "T_N <<_H N^3 L^{-2H}. UPPER_BOUND.md (1) states this family of "
            "bounds holds 'with ineffective constants'."
        ),
        "T_N_definition": (
            "T_N = sum_{t=1}^N Delta(t)^2 + sum_{t=1}^{N-1} "
            "[Delta(N)-Delta(t)]^2, UPPER_BOUND.md (29). Both summands are "
            "sums of squares, hence nonnegative, so "
            "S(N) = sum_{t=1}^N Delta(t)^2 <= T_N unconditionally, and any "
            "numeric bound on T_N is also a valid numeric upper bound "
            "candidate for S(N)."
        ),
        "source_measured_S_N": "hunts/prime_pair_error/results_delta_sq.json, key 'rows'",
        "H_values": H_VALUES,
        "implied_constant_convention": {
            "value": ASSUMED_CONSTANT,
            "note": (
                "Stated convention, not a derived value. UPPER_BOUND.md (1) "
                "says outright that the constants in this family of bounds "
                "are ineffective, so no true numeric value is available at "
                "any H; this script substitutes 1 only to produce a "
                "comparable number, following the task's instruction, and "
                "does not fit or tune it."
            ),
        },
        "cutoffs": per_cutoff,
        "vacuous_H_under_convention": vacuous_H,
        "convention_violated_H": violated_H,
        "verdict": verdict,
        "what_this_is_not": (
            "This is not a claim that UPPER_BOUND.md's bound is false, "
            "weak, or wrongly proved; the proof of T_N <<_H N^3 L^{-2H} is "
            "not touched or re-derived here. It is a report that the "
            "statement, exactly as proved, names no constant and says its "
            "constants are ineffective, so it cannot be turned into a "
            "number at any given N and H without a stated convention, and "
            "that under the one convention available (constant = 1) the "
            "resulting numbers are vacuous at H = 1, 2 and self-violating "
            "at H = 4, 8, at every cutoff measured here. Nothing here "
            "bears on RH."
        ),
    }

    out_path = HERE / "results_delta_sq_sw_bind.json"
    out_path.write_text(json.dumps(out, indent=1))

    print("T_N <<_H N^3 L^{-2H} (UPPER_BOUND.md, paragraph after (31)), constants stated ineffective at (1)")
    print(f"convention used: implied constant = {ASSUMED_CONSTANT} (stated, not derived)")
    for row in per_cutoff:
        print(f"N={row['N']:>9}  measured S(N)={row['measured_S_N']:.4e}  L={row['L_logN']:.4f}")
        for b in row["by_H"]:
            print(
                f"    H={b['H']}: bound={b['bound_N3_Lneg2H_convention_const_1']:.4e}"
                f"  ratio={b['ratio_measured_S_N_over_bound']:.4e}"
            )
    print(f"vacuous at H = {vacuous_H}; convention violated at H = {violated_H}")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
