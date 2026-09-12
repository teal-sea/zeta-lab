"""
Gate 3 Harness: The Counterexample Battery

This script runs Fable's fully completed Gate 3 battery.
A claimed property of the Riemann Zeta function must not be shared by
imposter functions (Davenport-Heilbronn, Epstein zeta functions, and the
symmetric shifted product zeta(s+a)zeta(s-a)).
If an imposter satisfies the claim, the claim cannot prove the Riemann Hypothesis.

The third imposter is the one to read the scope note for: it has a genuine
scalar Euler product, which the other two lack, and it still has zeros off its
own critical line. It is outside the Selberg class, so a claim it shares is
shown to be blind to a shift rather than shown to be irrelevant to RH. The
construction and the caveat are in docs/09 section 5.1.
"""

import functools
import pprint

from zeta.epstein import (
    battery,
    claim_euler_product_positivity,
    claim_functional_equation,
    claim_multiplicativity,
)

def _report(verdict):
    pprint.pprint(verdict)
    if verdict["distinguishes"]:
        print("✅ The claim successfully isolates the Riemann Zeta function.")
    else:
        shared = ", ".join(verdict["shared_with"]) or "(none)"
        print(f"❌ FAILED: also true of {shared}. The claim proves nothing on its own.")
    if verdict["undefined_for"]:
        print(f"   not evaluable on: {', '.join(verdict['undefined_for'])}")


def run_gate_3_battery():
    print("--- GATE 3: THE COUNTEREXAMPLE BATTERY ---")

    print("\nClaim 1: The function satisfies the Functional Equation F(s) = F(1-s)")
    _report(battery(claim_functional_equation))

    print("\nClaim 2: The Dirichlet coefficients are strictly multiplicative (Euler Product)")
    _report(battery(claim_multiplicativity))
    print("   Note: this verdict changed when the shifted product joined the rival")
    print("   set. Multiplicativity separates zeta from every rival that lacks an")
    print("   Euler product, and from none that has one.")

    print("\nClaim 3: The coefficients of log F are non-negative (Euler-product positivity)")
    print("   read to n <= 200; the same claim read to n <= 40 names a different rival")
    _report(battery(functools.partial(claim_euler_product_positivity, n_max=200)))

if __name__ == "__main__":
    run_gate_3_battery()
