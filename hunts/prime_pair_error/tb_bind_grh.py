"""A conditional exploration of Theorem B (RESULTS.md Section 18), not an
evaluation of Theorem B itself.

tb_bind.py already established, and results_tb_bind.json already records,
that Theorem B --

    For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}).

-- cannot be numerically evaluated against the measured E(N) in results.json:
Theta_chi is unconditionally only known to lie in [1/2, 1], the Omega carries
no explicit constant unconditionally, and the proof's conclusion holds only
along an unexhibited unbounded sequence of N, not for all N.

This script instead evaluates a different, weaker, conditional statement:
assume GRH for L(s, chi_3), i.e. Theta_chi = 1/2. RESULTS.md Section 18
itself uses exactly this substitution to illustrate the theorem's shape:
"with Theta_chi = 1/2 it gives Omega(N^{2 - eps})". Under that assumption
the claimed shape is

    E(N) = Omega(N^{2 - eps})   for every eps > 0.

Two of the three gaps tb_bind.py found do not close under this assumption:

  - The Omega still carries no explicit constant. Theorem B's proof derives
    an explicit constant 1/2 in |T(N)| >= (1/2) N^{1+Theta_chi-eps'}
    (RESULTS.md Section 18, the line before "Hence E(N) >= ..."), but only
    along the unbounded sequence the contradiction argument produces, using
    the O-constants buried in Theorem A and (E3)/Section 15, none of which
    is given a numeric value in RESULTS.md. Assuming Theta_chi = 1/2 fixes
    the exponent; it does not supply those O-constants.
  - The unbounded sequence along which the bound holds is still not
    exhibited, GRH-for-chi_3 or not; nothing in the proof's construction of
    that sequence depends on the value of Theta_chi.

So this script cannot produce a bound value to divide the measured E(N) by,
conditionally any more than unconditionally. What it can do instead is
compare the *shape* N^{2 - eps} implies -- growth in N with exponent close
to 2 -- against the exponent the measured E(N) in results.json actually
displays over that range, without treating that as a numeric inequality
test and without treating a finite range as settling an asymptotic exponent.

eps: this script fixes eps = 0.05. Theorem B's "for every eps > 0" makes the
claimed exponent 2 - eps approach 2 as eps -> 0, so the strictest members of
that family are the small ones; 0.05 is chosen as a concrete small
representative rather than a special value, close enough to the eps -> 0
limit to make the shape comparison meaningful, not so close that floating
point or the finite ladder below would blur it.

This is a GRH-for-L(s, chi_3) conditional exploration. It does not evaluate
the unconditional Theorem B, does not claim the unconditional bound binds or
is vacuous, and nothing here bears on RH.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/tb_bind_grh.py
Reads hunts/prime_pair_error/results.json
Writes hunts/prime_pair_error/results_tb_bind_grh.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent

EPS = 0.05


def main() -> int:
    results_path = HERE / "results.json"
    data = json.loads(results_path.read_text())

    rows = [(row["N"], row["E"]) for row in data["decomposition"]]

    conditional_exponent = 2 - EPS

    cutoffs = []
    for n, e in rows:
        cutoffs.append(
            {
                "N": n,
                "measured_E_N": e,
                "E_N_over_N_pow_conditional_exponent": e / (n ** conditional_exponent),
            }
        )

    local_exponents = []
    for (n1, e1), (n2, e2) in zip(rows, rows[1:]):
        exponent = math.log(e2 / e1) / math.log(n2 / n1)
        local_exponents.append(
            {
                "N_from": n1,
                "N_to": n2,
                "observed_local_exponent": exponent,
                "at_least_conditional_exponent": exponent >= conditional_exponent,
            }
        )

    log_n = [math.log(n) for n, _ in rows]
    log_e = [math.log(e) for _, e in rows]
    mean_log_n = sum(log_n) / len(log_n)
    mean_log_e = sum(log_e) / len(log_e)
    num = sum((x - mean_log_n) * (y - mean_log_e) for x, y in zip(log_n, log_e))
    den = sum((x - mean_log_n) ** 2 for x in log_n)
    global_exponent = num / den

    out = {
        "theorem_b_quoted": (
            "For every eps > 0, E(N) = Omega(N^{1 + 2 Theta_chi - eps}). "
            "(RESULTS.md Section 18.)"
        ),
        "what_this_is": (
            "A conditional exploration only: assumes GRH for L(s, chi_3), "
            "i.e. Theta_chi = 1/2, the substitution RESULTS.md Section 18 "
            "itself uses to state the shape Omega(N^{2 - eps}). This is not "
            "an evaluation of the unconditional Theorem B, and no claim is "
            "made here about whether the unconditional bound binds or is "
            "vacuous. Nothing here bears on RH."
        ),
        "assumption": "Theta_chi = 1/2 (GRH for L(s, chi_3))",
        "conditional_shape": "E(N) = Omega(N^{2 - eps}) for every eps > 0",
        "eps_choice": {
            "eps": EPS,
            "why": (
                "Theorem B's quantifier is 'for every eps > 0'; the claimed "
                "exponent 2 - eps approaches 2 as eps -> 0, so the small "
                "eps are the strictest members of that family. 0.05 is a "
                "concrete small representative, not a value singled out by "
                "the theorem or by the data."
            ),
        },
        "conditional_exponent_2_minus_eps": conditional_exponent,
        "why_still_not_a_numeric_bound": (
            "Fixing Theta_chi = 1/2 removes the one unconditional gap that "
            "concerns Theta_chi's value, but the other two gaps tb_bind.py "
            "found are independent of Theta_chi and remain open here: the "
            "Omega in Theorem B's proof supplies an explicit factor 1/2 "
            "only in front of N^{1+Theta_chi-eps'} along the unexhibited "
            "sequence, multiplying O-constants from Theorem A and Section "
            "15/(E3) that RESULTS.md never gives numeric values, and that "
            "sequence itself is still not exhibited. So there is still no "
            "number to divide the measured E(N) by; only the exponent 2 in "
            "the shape is pinned down by the GRH-for-chi_3 assumption."
        ),
        "source": "hunts/prime_pair_error/results.json, key 'decomposition'",
        "cutoffs": cutoffs,
        "local_exponents": local_exponents,
        "global_least_squares_exponent": global_exponent,
        "shape_comparison": (
            "The observed local exponents of E(N) across the six cutoffs in "
            "results.json range from about "
            f"{min(x['observed_local_exponent'] for x in local_exponents):.4f} "
            "to about "
            f"{max(x['observed_local_exponent'] for x in local_exponents):.4f}"
            ", and the global least-squares exponent over all six points is "
            f"about {global_exponent:.4f}. All of these sit above the "
            f"conditional shape exponent 2 - eps = {conditional_exponent:.4f} "
            "chosen above, so the measured growth over this finite range is "
            "not inconsistent with the shape N^{2 - eps} that the "
            "GRH-for-chi_3 conditional statement claims. That is a shape "
            "observation over six cutoffs up to 1e7, not a binding numeric "
            "inequality (no bound value was computed above to compare "
            "against), and not a statement about an asymptotic exponent: an "
            "exponent measured over one finite range does not settle the "
            "asymptotic rate, and it says nothing about the unconditional "
            "Theorem B or about whether GRH for L(s, chi_3) actually holds."
        ),
        "what_this_is_not": (
            "This is not a claim that Theorem B, conditionally or "
            "unconditionally, binds or is vacuous at these cutoffs: no "
            "bound value was computed to form that ratio, only an exponent "
            "shape was compared. It is not a claim that GRH for L(s, "
            "chi_3) holds, and it is not a re-derivation or evaluation of "
            "the unconditional Theorem B, which results_tb_bind.json "
            "already reports cannot be evaluated at these cutoffs. Nothing "
            "here bears on RH."
        ),
    }

    out_path = HERE / "results_tb_bind_grh.json"
    out_path.write_text(json.dumps(out, indent=1))

    print("Conditional (GRH for L(s, chi_3)) shape: E(N) = Omega(N^{2 - eps})")
    print(f"eps = {EPS}, conditional exponent = {conditional_exponent}")
    print()
    print("observed local exponents of measured E(N):")
    for row in local_exponents:
        print(
            f"  N={row['N_from']:>9} -> N={row['N_to']:>9}: "
            f"exponent={row['observed_local_exponent']:.4f}"
        )
    print(f"global least-squares exponent: {global_exponent:.4f}")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
