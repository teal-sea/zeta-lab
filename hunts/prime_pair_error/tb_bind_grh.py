"""Conditional (GRH-for-L(s, chi_3)) exploration of Theorem B's shape.

tb_bind.py established that Theorem B (RESULTS.md Section 18),

    For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}),

cannot be evaluated against the measured E(N) in results.json, because
Theta_chi is unconditionally only known to satisfy 1/2 <= Theta_chi <= 1,
the Omega carries no explicit constant (the proof is a contradiction from
Landau's oscillation theorem applied to a Mellin transform with a pole, not
a construction), and the bound is proved only "along an unbounded sequence"
of N, not exhibited.

This script does NOT evaluate Theorem B. It evaluates a different, weaker,
CONDITIONAL statement: what Theorem B's shape becomes if Theta_chi = 1/2 is
assumed, i.e. GRH for L(s, chi_3) (this is exactly the illustrative case
RESULTS.md Section 18 itself uses under "What it says and does not say"),
giving

    E(N) = Omega(N^{2 - eps})   for every eps > 0.

Even granting that assumption, two of the three gaps tb_bind.py found are
untouched:

  - the Omega still carries no explicit constant or threshold N0 (assuming
    Theta_chi = 1/2 says nothing about the implied constant, which comes
    from a separate, non-constructive step of the proof);
  - the bound is still only asserted "along an unbounded sequence" of N,
    not exhibited, so there is still no licensed set of N to test it at.

So there is still no number to compare the measured E(N) against, and the
only thing available to compare is SHAPE: does the six-point measured E(N)
in results.json grow at a rate that is at least consistent with an exponent
approaching 2? That is a much weaker question than whether N^{2-eps} is a
valid lower bound at these specific N (which the missing constant and
missing sequence make impossible to check either way), and this script asks
only that weaker question, and only for the assumed-GRH exponent, not for
Theorem B itself.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/tb_bind_grh.py
Reads hunts/prime_pair_error/results.json
Writes hunts/prime_pair_error/results_tb_bind_grh.json
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent

# Small and explicit. eps only has to be positive for the statement to hold
# for "every eps > 0"; 0.01 is chosen so the illustrated exponent 2 - eps is
# close to the eps -> 0 limit (2) while still being a genuine positive eps,
# not a stand-in for eps = 0. Any other small positive choice would move the
# illustrated exponent by a comparably small amount; nothing here tunes eps
# to make an observed exponent look closer or further from 2 - eps.
EPS = 0.01
ASSUMED_THETA_CHI = 0.5
CONDITIONAL_EXPONENT = 1 + 2 * ASSUMED_THETA_CHI - EPS  # = 2 - eps = 1.99


def main() -> int:
    results_path = HERE / "results.json"
    data = json.loads(results_path.read_text())

    cutoffs = []
    for row in data["decomposition"]:
        cutoffs.append(
            {
                "N": row["N"],
                "measured_E_N": row["E"],
            }
        )

    Ns = np.array([row["N"] for row in cutoffs], dtype=float)
    Es = np.array([row["measured_E_N"] for row in cutoffs], dtype=float)

    # Observed log-log slope of the six measured points, the same
    # least-squares-over-a-finite-ladder method delta_sq_probe.py uses for
    # S(N). This is an observed slope over six points spanning N = 1e3 to
    # 1e7, not an asymptotic exponent, and it is not derived from, or a
    # substitute for, Theorem B's proof.
    slope, intercept = np.polyfit(np.log(Ns), np.log(Es), 1)

    for row in cutoffs:
        n = row["N"]
        row["N_to_the_2_minus_eps_unnormalized"] = n ** CONDITIONAL_EXPONENT
        row["measured_E_N_over_N_to_the_2_minus_eps"] = (
            row["measured_E_N"] / n ** CONDITIONAL_EXPONENT
        )

    shape_note = (
        f"Observed log-log exponent over the six measured points is "
        f"{slope:.4f}. The conditional (assumed Theta_chi = 1/2) exponent "
        f"Theorem B's shape would need is 2 - eps = {CONDITIONAL_EXPONENT:.4f} "
        f"with eps = {EPS}. The observed exponent sitting close to, at, or "
        f"above that value is a statement about six measured points over a "
        f"finite range, not about the asymptotic rate the conditional "
        f"statement makes a claim about, and it does not stand in for the "
        f"missing implied constant or the unexhibited unbounded sequence, "
        f"either of which the conditional statement (like Theorem B itself) "
        f"still needs before any numeric inequality could be checked."
    )

    out = {
        "theorem_b_quoted": (
            "For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}). "
            "(RESULTS.md Section 18.)"
        ),
        "what_this_is": (
            "A conditional exploration only: it assumes GRH for L(s, chi_3), "
            "i.e. Theta_chi = 1/2, exactly the illustrative case RESULTS.md "
            "Section 18 itself uses under 'What it says and does not say'. "
            "This is NOT an evaluation of Theorem B, which is unconditional "
            "and makes no such assumption. Nothing here changes, weakens, "
            "or measures the unconditional statement."
        ),
        "conditional_assumption": "Theta_chi = 1/2 (GRH for L(s, chi_3))",
        "eps_chosen": EPS,
        "eps_choice_reason": (
            "0.01: small and explicit, close to the eps -> 0 limit of the "
            "illustrated exponent (2) while remaining a genuine positive "
            "eps as the statement 'for every eps > 0' requires. Not fit or "
            "tuned against the measured E(N) below."
        ),
        "conditional_bound_shape": "N^{2 - eps}",
        "conditional_exponent": CONDITIONAL_EXPONENT,
        "source": "hunts/prime_pair_error/results.json, key 'decomposition'",
        "cutoffs": cutoffs,
        "observed_loglog_exponent_leastsquares": float(slope),
        "observed_loglog_intercept": float(intercept),
        "shape_comparison_note": shape_note,
        "bound_evaluated": False,
        "why_still_not_evaluated": (
            "Assuming Theta_chi = 1/2 only removes one of the three gaps "
            "tb_bind.py found (Theta_chi's value). The other two remain "
            "exactly as tb_bind.py described them: the proof's Omega "
            "carries no explicit constant or threshold N0 (that gap is "
            "independent of Theta_chi's value), and the conclusion is "
            "proved only along an unbounded sequence of N that is never "
            "exhibited, so there is still no licensed N at which to check "
            "a numeric inequality, conditionally or otherwise. What can be "
            "compared is shape only: does the measured E(N)'s observed "
            "growth rate sit near the conditional exponent 2 - eps. That is "
            "the comparison this script makes; it is not a binding numeric "
            "inequality and not a statement about Theorem B itself."
        ),
        "verdict": (
            "This conditional (GRH-for-L(s, chi_3)) exploration cannot "
            "produce a numeric bound to compare against the measured E(N) "
            "either, for the same missing-constant and missing-sequence "
            "reasons tb_bind.py found for the unconditional Theorem B; only "
            "the growth-rate shape is comparable, and that comparison is "
            "recorded above as an observed exponent, not as a value that "
            "binds or is vacuous. This script makes no claim about whether "
            "Theorem B itself binds or is vacuous at these cutoffs."
        ),
        "what_this_is_not": (
            "This is not an evaluation of Theorem B as stated in RESULTS.md "
            "Section 18, which is unconditional; it explores only the "
            "GRH-for-L(s, chi_3) illustrative case Section 18 itself names. "
            "It is not a claim that the observed exponent settles anything "
            "about the conditional or unconditional statement at any N, "
            "eventually or otherwise: an exponent measured over six points "
            "on a finite range is not an asymptotic rate. Nothing here "
            "bears on RH."
        ),
    }

    out_path = HERE / "results_tb_bind_grh.json"
    out_path.write_text(json.dumps(out, indent=1))

    print("Conditional exploration: assume Theta_chi = 1/2 (GRH for L(s, chi_3))")
    print(f"conditional shape: E(N) = Omega(N^{{2 - eps}}), eps = {EPS}")
    print(f"conditional exponent: {CONDITIONAL_EXPONENT:.4f}")
    print()
    print("measured E(N) at the recorded cutoffs:")
    for row in cutoffs:
        print(f"  N={row['N']:>9}  E(N)={row['measured_E_N']:.6e}")
    print()
    print(f"observed log-log exponent (least squares, six points): {slope:.4f}")
    print()
    print("no numeric bound evaluated: the implied constant and the")
    print("unbounded sequence of N are still unspecified even under this")
    print("assumption; only growth-rate shape is compared above.")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
