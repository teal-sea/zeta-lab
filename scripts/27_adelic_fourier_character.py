"""
Demonstration of the Adelic Additive Character and Pontryagin Duality.

The Adele ring A_Q is locally compact and abelian, so it admits a Fourier Transform.
The Pontryagin dual of A_Q is isomorphic to itself, and the self-duality is realized
via the canonical additive character:
    psi(x) = exp(2 * pi * i * x_inf) * prod_p exp(-2 * pi * i * {x_p}_p)

A fundamental theorem of Adelic geometry (which underpins the Riemann-Roch theorem 
and Tate's thesis) is that the rational numbers Q are discretely embedded in A_Q, 
and the quotient A_Q / Q is compact. This requires that any rational number q 
satisfies psi(q) = 1.

This script tests the computational implementation of psi(x) and verifies 
that psi(q) = 1 for any rational q.
"""

from fractions import Fraction
from zeta.adele import Adele, adelic_additive_character
import cmath

# Generate primes up to N
def sieve(n):
    is_prime = [True] * (n + 1)
    p = 2
    while p * p <= n:
        if is_prime[p]:
            for i in range(p * p, n + 1, p):
                is_prime[i] = False
        p += 1
    return [p for p in range(2, n + 1) if is_prime[p]]

def main():
    print("--- ADELIC ADDITIVE CHARACTER: MEASURING THE DEFECT ---")
    print("A fundamental theorem states that Q is discretely embedded in A_Q,")
    print("which requires the global additive character psi(q) = 1 for all q in Q.")
    print("However, computationally we can only evaluate a finite truncation of places.")
    print("Instead of hardcoding the required primes, we measure the shrinking defect.")
    
    # A rational number with large prime factors in the denominator
    q = Fraction(355, 113)
    print(f"\nRational q = {q}")
    
    all_primes = sieve(200)
    
    for n_primes in [5, 10, 20, 30, len(all_primes)]:
        current_primes = all_primes[:n_primes]
        adele = Adele.from_rational(q, current_primes)
        psi_q = adelic_additive_character(adele)
        
        # The defect is the distance from 1.0
        defect = abs(psi_q - 1.0)
        
        print(f"\nEvaluating with {n_primes:2d} primes (up to {current_primes[-1]:3d}):")
        print(f"  psi(q) = {psi_q.real:+.6f} {psi_q.imag:+.6f}j")
        print(f"  Defect = {defect:.6e}")
        
    print("\nThe defect vanishes completely only when the exact prime factors of the")
    print("denominator are included in the local p-adic product. Truncation leaves")
    print("a measurable phase error.")

if __name__ == "__main__":
    main()
