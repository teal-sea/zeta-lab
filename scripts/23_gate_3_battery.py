"""
Gate 3 Harness: The Counterexample Battery

This script runs Fable's fully completed Gate 3 battery.
A claimed property of the Riemann Zeta function must not be shared by
imposter functions (Davenport-Heilbronn and Epstein zeta functions).
If an imposter satisfies the claim, the claim cannot prove the Riemann Hypothesis.
"""

from zeta.epstein import battery, claim_functional_equation, claim_multiplicativity
import pprint

def run_gate_3_battery():
    print("--- GATE 3: THE COUNTEREXAMPLE BATTERY ---")
    
    print("\nClaim 1: The function satisfies the Functional Equation F(s) = F(1-s)")
    res1 = battery(claim_functional_equation)
    pprint.pprint(res1)
    if res1["distinguishes"]:
        print("✅ The claim successfully isolates the Riemann Zeta function.")
    else:
        print("❌ FAILED: The imposters also pass this claim. It proves nothing.")

    print("\nClaim 2: The Dirichlet coefficients are strictly multiplicative (Euler Product)")
    res2 = battery(claim_multiplicativity)
    pprint.pprint(res2)
    if res2["distinguishes"]:
        print("✅ The claim successfully isolates the Riemann Zeta function.")
    else:
        print("❌ FAILED: The imposters also pass this claim. It proves nothing.")

if __name__ == "__main__":
    run_gate_3_battery()
