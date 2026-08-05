"""
Demonstration of Artin's Product Formula over the Adeles.

By embedding a rational number q into the Adele ring A_Q and taking the product
of its absolute values over all places (the real place and all p-adic places),
we get exactly 1. 

This is the foundational symmetry that enables Connes' Spectral Realization 
of the Riemann zeros.
"""

from fractions import Fraction
from zeta.adele import PAdic, Adele, check_product_formula

def main():
    print("--- ARTIN'S PRODUCT FORMULA OVER THE ADELES ---")
    
    # We will test a few rational numbers. 
    # We only need primes that divide the numerator or denominator.
    # To be safe, we'll just supply the first few primes.
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    test_cases = [
        Fraction(1, 1),
        Fraction(2, 1),
        Fraction(3, 4),
        Fraction(-15, 7),
        Fraction(120, 11),
        Fraction(1, 1024)
    ]
    
    for q in test_cases:
        adele = Adele.from_rational(q, primes)
        
        # Display the local norms
        print(f"\nRational q = {q}")
        print(f"  Real norm |q|_inf = {abs(adele.real_part)}")
        
        for p, padic in adele.padic_parts.items():
            norm_p = padic.norm()
            if norm_p != 1.0:
                print(f"  p-adic norm |q|_{p}  = {norm_p}")
                
        # The global norm should be exactly 1
        global_norm = adele.norm()
        print(f"  -> Global Adelic Norm: {global_norm}")
        
        # Rigorous check
        assert abs(global_norm - 1.0) < 1e-12, f"Product formula failed for {q}!"

    print("\nProduct formula holds computationally for all test cases.")

if __name__ == "__main__":
    main()
