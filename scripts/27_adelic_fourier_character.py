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

def main():
    print("--- ADELIC ADDITIVE CHARACTER AND Q-TRIVIALITY ---")
    
    # Primes needed for the denominators
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 113]
    
    test_cases = [
        Fraction(1, 1),
        Fraction(1, 2),
        Fraction(3, 4),
        Fraction(-15, 7),
        Fraction(120, 11),
        Fraction(1, 1024),
        Fraction(355, 113) # Good rational approximation of pi
    ]
    
    for q in test_cases:
        adele = Adele.from_rational(q, primes)
        
        # Calculate psi(q)
        psi_q = adelic_additive_character(adele)
        
        print(f"\nRational q = {q}")
        print(f"  Adelic character psi(q) = {psi_q.real:+.8f} {psi_q.imag:+.8f}j")
        
        # Verify it's exactly 1 (up to floating point precision)
        error = abs(psi_q - 1.0)
        print(f"  Error margin            = {error:.8e}")
        
        assert error < 1e-12, f"Character failed Q-triviality for {q}!"

    print("\nAdelic additive character psi(q) = 1 computationally verified for all rational test cases.")
    print("Q is discretely embedded in A_Q.")

if __name__ == "__main__":
    main()
