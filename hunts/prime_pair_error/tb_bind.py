"""Does Theorem B's lower bound (RESULTS.md Section 18) bind at the cutoffs
results.json already measured, or is it vacuous, or can it not be evaluated
there at all?

Theorem B, quoted in full from RESULTS.md Section 18:

    For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}). With Chou,
    Haag, Huryn and Ledoan's Theorem 2, E(N) = Omega(N^{1 + 2 max(Theta,
    Theta_chi) - eps}).

with Theta_chi = sup Re rho' over the non-trivial zeros of L(s, chi_3), and
the proof (Section 18) ending: "The conclusion is along that sequence, not
an eventual lower bound for all N."

This script reads the measured E(N) already on record in results.json (the
first pass's cutoffs, up to 1e7) and checks whether Theorem B's bound can be
evaluated there at all, before asking whether it binds or is vacuous.

It cannot. Three separate quantities the statement needs are all missing,
none of them a matter of more computation:

1. Theta_chi itself. Unconditionally only 1/2 <= Theta_chi <= 1 is known
   (Section 17's "Standard facts", F5, plus the classical zero-free region);
   its exact value is open, and nowhere in this hunt is it computed,
   approximated, or bounded more tightly than that. RESULTS.md only ever
   substitutes the hypothetical value Theta_chi = 1/2 (the GRH case, Section
   18, "What it says and does not say"). Substituting an assumed value to
   get a number would be evaluating a different, GRH-conditional statement,
   not Theorem B, which is unconditional.

2. The implied constant. Theorem B's proof (Section 18) derives the bound
   from Landau's oscillation theorem applied to a Mellin transform with a
   pole: "If I(x) were O(x^{1+Theta_chi-eps'}) the left side would converge
   absolutely and be analytic ... where the right side has a pole; so
   I(x) = Omega(...)". That is a proof by contradiction from an analyticity
   argument, not a construction, and it supplies no explicit constant c or
   threshold N0 with |E(N)| >= c N^{1+2Theta_chi-eps} for N >= N0. Omega
   notation with no stated constant is not a number at any given N; there is
   nothing here to divide the measured E(N) by.

3. The sequence. The proof's own conclusion is explicit that the bound holds
   "along an unbounded sequence" of N produced by the contradiction argument,
   "not an eventual lower bound for all N." That sequence is not exhibited,
   and there is no way to test whether any of results.json's cutoffs
   (1000; 10000; 100000; 1000000; 3000000; 10000000) belongs to it. Even
   with Theta_chi and a constant in hand, the bound would still only be a
   licensed comparison at unspecified N, not at these six.

None of this is a defect introduced here: it is what Theorem B, read
exactly as stated in Section 18, is. Assuming a value for Theta_chi,
supplying our own constant, or treating "along a sequence" as "for all N"
would be evaluating a stronger, different statement and calling it Theorem
B. This script does not do that. It reports what is missing and writes the
measured E(N) values alongside it, so the gap is on record next to the data
it cannot yet be compared to.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/tb_bind.py
Reads hunts/prime_pair_error/results.json
Writes hunts/prime_pair_error/results_tb_bind.json
"""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main() -> int:
    results_path = HERE / "results.json"
    data = json.loads(results_path.read_text())

    cutoffs = []
    for row in data["decomposition"]:
        cutoffs.append(
            {
                "N": row["N"],
                "measured_E_N": row["E"],
                "measured_E_N_over_N2log2N": row.get("E_over_N2log2N"),
            }
        )

    missing = [
        {
            "quantity": "Theta_chi",
            "definition": (
                "sup Re rho' over the non-trivial zeros of L(s, chi_3), as "
                "defined in RESULTS.md Section 17"
            ),
            "why_missing": (
                "Unconditionally only 1/2 <= Theta_chi <= 1 is known (the "
                "classical zero-free region and the non-vanishing of L(s, "
                "chi_3) on Re s = 1); its exact value is open. Nothing in "
                "this hunt computes, approximates, or further bounds it. "
                "RESULTS.md Section 18 only ever substitutes the "
                "hypothetical GRH value 1/2 to illustrate the shape of the "
                "statement; using that value here would evaluate a "
                "GRH-conditional statement, not the unconditional Theorem B."
            ),
        },
        {
            "quantity": "the implied constant (and threshold N0) in the Omega",
            "definition": (
                "the c > 0 and N0 such that |E(N)| >= c N^{1+2 Theta_chi-eps} "
                "for N >= N0, which Omega notation asserts exist without "
                "naming"
            ),
            "why_missing": (
                "Theorem B's proof (RESULTS.md Section 18) is a proof by "
                "contradiction from Landau's oscillation theorem: assuming "
                "I(x) = O(x^{1+Theta_chi-eps'}) would make a Mellin "
                "transform analytic where it is known to have a pole, a "
                "contradiction. That argument shows a bound cannot fail to "
                "hold; it does not construct a constant, so it supplies no "
                "number to evaluate at a given N."
            ),
        },
        {
            "quantity": "the unbounded sequence of N along which the bound holds",
            "definition": (
                "the specific N's produced by the contradiction argument, "
                "as opposed to all sufficiently large N"
            ),
            "why_missing": (
                "RESULTS.md Section 18 states this explicitly: 'The "
                "conclusion is along that sequence, not an eventual lower "
                "bound for all N.' That sequence is not exhibited by the "
                "proof, so there is no way to check whether any of the "
                "cutoffs measured in results.json (1000, 10000, 100000, "
                "1000000, 3000000, 10000000) is a member of it."
            ),
        },
    ]

    verdict = (
        "Theorem B's bound cannot be evaluated at the cutoffs results.json "
        "measured, or at any specific N: the statement is an unconditional "
        "existence claim (Omega, with no stated constant) that Theta_chi "
        "and an infinite unspecified sequence of N enter into, and none of "
        "Theta_chi, the implied constant, or that sequence is available "
        "unconditionally, in this hunt or otherwise. This is not a question "
        "of insufficient precision or a cutoff too small: no numeric value "
        "for the bound exists to compare against the measured E(N) above, "
        "so no ratio, no 'binds', and no 'vacuous' verdict can be computed "
        "from Theorem B as stated. The bound cannot be evaluated at these "
        "cutoffs."
    )

    out = {
        "theorem_b_quoted": (
            "For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}). "
            "With Chou, Haag, Huryn and Ledoan's Theorem 2, "
            "E(N) = Omega(N^{1 + 2 max(Theta, Theta_chi) - eps}). "
            "(RESULTS.md Section 18.)"
        ),
        "source": "hunts/prime_pair_error/results.json, key 'decomposition'",
        "cutoffs": cutoffs,
        "bound_evaluated": False,
        "bound": None,
        "ratio_measured_over_bound": None,
        "missing": missing,
        "verdict": verdict,
        "what_this_is_not": (
            "This is not a claim that Theorem B is false, weak, or wrongly "
            "proved; the proof in RESULTS.md Section 18 is not touched or "
            "re-derived here. It is a report that the statement, exactly as "
            "proved, does not fix enough unconditional information to be "
            "turned into a number at any given N, so it cannot be compared "
            "against measured E(N) at all, whether the outcome would have "
            "been described as binding or as vacuous. Nothing here bears "
            "on RH."
        ),
    }

    out_path = HERE / "results_tb_bind.json"
    out_path.write_text(json.dumps(out, indent=1))

    print("Theorem B: E(N) = Omega(N^{1 + 2 Theta_chi - eps}) for every eps > 0")
    print("measured E(N) at the recorded cutoffs:")
    for row in cutoffs:
        print(f"  N={row['N']:>9}  E(N)={row['measured_E_N']:.6e}")
    print()
    print("bound cannot be evaluated: Theta_chi, the implied constant, and")
    print("the unbounded sequence of N are all unspecified in the theorem")
    print("as stated, and none is computed anywhere in this hunt.")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
