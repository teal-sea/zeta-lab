"""
Landau Problem 1: Legendre's Conjecture via the Explicit Formula

Legendre's Conjecture states there is always a prime between n^2 and (n+1)^2.

We attack this using zeta/weil.py. 
We construct a test function g(u) that is strictly supported in the 
intervals [-B, -A] and [A, B], where A = log(n^2) and B = log((n+1)^2).

Because g(u) is zero everywhere else, the prime sum in the Riemann-Weil 
explicit formula ONLY evaluates primes inside the Legendre gap!

W(h) = pole + arch_term - 2 * sum( Lambda(k) k^{-1/2} g(log k) )

By computing W(h) (the arithmetic side) and the zero side, we can measure 
the exact amplitude of the Riemann zeros required to guarantee the existence 
of a prime in this interval.
"""

import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# The pair lives in the library now (zeta.weil.legendre_pair) so the funnel's
# LegendreWeilGenerator and this demo share one implementation and one test
# suite; this script is the human-readable tour of the same instrument.
from zeta.weil import explicit_formula_sides, legendre_pair

if __name__ == "__main__":
    n = 10
    print(f"--- Attacking Legendre's Conjecture for n = {n} ---")
    print(f"Target Interval: [{n**2}, {(n+1)**2}]")
    
    h, g = legendre_pair(n)
    
    # We use a relatively high gamma_max to resolve the sharp bumps
    gamma_max = 500.0
    print(f"Evaluating Weil Explicit Formula (summing {gamma_max} zeros)...")
    
    results = explicit_formula_sides(h, g, gamma_max=gamma_max, n_max=(n+1)**2 + 10, dps=25)
    
    print("\n--- Explicit Formula Output ---")
    print(f"Zero Side:       {results['zero_side']}")
    print(f"Arithmetic Side: {results['arithmetic_side']}")
    print(f"Prime Term (The Legendre Signal): {results['prime_term']}")
    print(f"Agreement Error: {float(results['agreement']):.2e}")
    
    print("\n--- Analysis ---")
    if results['prime_term'] < -1e-10:
        print(">> The prime term is strictly negative: the interval carries")
        print(">> Lambda-mass (prime_term = -2*sum, so negative means primes present).")
        print(">> Honest scope: this detects primes the sieve already lists, for n")
        print(">> where Legendre is finitely verified. It is an instrument, not a proof;")
        print(">> the funnel's LegendreWeilGenerator files it as 'known'.")
    else:
        print(">> The prime term is 0. No primes detected (or precision failed).")
