"""
Demonstration of Tate's Thesis and the Idelic Global Zeta Function.

Tate proved that the Riemann Zeta function is the Mellin transform of a 
Schwartz-Bruhat function over the Adeles, integrated against the Haar measure 
on the Ideles (the multiplicative group of the Adeles).

By choosing the standard test function (the indicator function of Z_p for every 
finite prime p, and the Gaussian exp(-pi x^2) for the real place), the local 
zeta integrals perfectly reproduce the Euler factors of the Riemann Zeta function.

This script demonstrates that evaluating the local integrals over Q_p^* computationally
reconstructs the true global Zeta function for Re(s) > 1.
"""

import math
from mpmath import mp
from zeta.adele import global_euler_product

# Generate some primes for the product
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
    print("--- TATE'S LOCAL INTEGRALS -> GLOBAL ZETA ---")
    
    # We'll use the first 10,000 primes for a decent approximation
    primes = sieve(104729) # 104729 is the 10,000th prime
    
    # Let's test at s = 2, where Zeta(2) = pi^2 / 6
    s_test = 2.0 + 0j
    exact_zeta = math.pi**2 / 6.0
    
    print(f"\nEvaluating Tate's Local Zeta Integrals over Q_p^* for all p up to {primes[-1]}...")
    partial_zeta = global_euler_product(s_test, primes)
    
    print(f"  s = {s_test.real}")
    print(f"  Adelic Euler Product (10,000 primes) = {partial_zeta.real:.8f}")
    print(f"  Analytic Zeta(2) (pi^2 / 6)          = {exact_zeta:.8f}")
    
    error = abs(exact_zeta - partial_zeta.real)
    print(f"  Error margin                         = {error:.8e}")
    
    # Check s = 4, where Zeta(4) = pi^4 / 90
    s_test2 = 4.0 + 0j
    exact_zeta2 = math.pi**4 / 90.0
    partial_zeta2 = global_euler_product(s_test2, primes)
    
    print(f"\n  s = {s_test2.real}")
    print(f"  Adelic Euler Product (10,000 primes) = {partial_zeta2.real:.8f}")
    print(f"  Analytic Zeta(4) (pi^4 / 90)         = {exact_zeta2:.8f}")
    
    error2 = abs(exact_zeta2 - partial_zeta2.real)
    print(f"  Error margin                         = {error2:.8e}")

    print("\nConclusion: The Adelic geometry accurately synthesizes the Riemann Zeta function.")

if __name__ == "__main__":
    main()
