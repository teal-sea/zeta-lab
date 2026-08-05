"""
Detector-Strength Audit: The Mertens Alarm against Davenport-Heilbronn

Mathematics provides many statements equivalent to the Riemann Hypothesis.
One of the most famous is the bound on the Mertens function:
    M(x) = sum_{n <= x} mu(n)
RH is equivalent to M(x) growing no faster than x^(1/2 + epsilon).

For the Davenport-Heilbronn (DH) function, RH is FALSE. The first offline zero
has real part ~ 0.8085. Therefore, the DH-Mertens function MUST grow as fast as 
x^0.8085. The ratio M_DH(x) / sqrt(x) MUST explode to infinity.

But does it explode FAST ENOUGH to be a computationally useful detector?
Let's compute it and find out!
"""

import sys
import math
from zeta.epstein import dh_coefficient

def audit_mertens(limit=100000):
    print(f"Auditing Mertens / Mobius detector up to n = {limit}")
    
    # 1. Precompute DH coefficients a_n
    # DH is periodic mod 5, so this is fast.
    print("Precomputing DH Dirichlet coefficients...")
    a = [0] * (limit + 1)
    for n in range(1, limit + 1):
        a[n] = float(dh_coefficient(n, dps=15))
        
    # 2. Compute the DH Mobius function mu_DH(n)
    # Defined by L(s) * (1/L(s)) = 1
    # So sum_{d|n} a_d * mu_DH(n/d) = 0 for n > 1
    # mu_DH(n) = - sum_{d|n, d<n} a_{n/d} * mu_DH(d) (since a_1 = 1)
    
    print("Computing DH Mobius inversion mu_DH(n)...")
    mu = [0.0] * (limit + 1)
    mu[1] = 1.0
    
    # O(N log N) sieve-like computation
    for d in range(1, limit + 1):
        if mu[d] == 0:
            continue
        # add mu[d] * a[k] to the n = d*k term
        for k in range(2, limit // d + 1):
            n = d * k
            mu[n] -= mu[d] * a[k]
            
    # 3. Compute M_DH(x) and audit the ratio
    print("Auditing the Mertens Ratio M_DH(x) / sqrt(x) ...")
    M = 0.0
    max_ratio = 0.0
    
    print("-" * 60)
    print(f"{'n':>10} | {'M_DH(n)':>15} | {'Ratio M / sqrt(n)':>20}")
    print("-" * 60)
    
    for n in range(1, limit + 1):
        M += mu[n]
        ratio = abs(M) / math.sqrt(n)
        
        if ratio > max_ratio:
            max_ratio = ratio
            
        if n in [10, 100, 1000, 10000, 50000, 100000, 500000, 1000000] or n == limit:
            print(f"{n:10d} | {M:15.2f} | {ratio:20.5f}")

    print("-" * 60)
    print(f"Max ratio reached: {max_ratio:.5f}")
    
    if max_ratio < 2.0:
        print("\nVERDICT: MERTENS IS A WEAK DETECTOR.")
        print("Even though the ratio is mathematically guaranteed to explode to infinity,")
        print(f"by n={limit} it hasn't even breached {max_ratio:.2f}.")
        print("Waiting for Mertens to catch the imposter is a computational dead end.")
    else:
        print("\nVERDICT: MERTENS IS A STRONG DETECTOR!")
        print("The ratio exploded early, successfully catching the imposter.")

if __name__ == "__main__":
    audit_mertens(1000000)
