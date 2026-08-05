"""
Discovery Lab 4: The Transcendental Antisymmetric Matrix

Taking the user's intuition:
1. We must inject a transcendental number (ln p) to bypass the algebraic lock.
2. The Riemann zeros are complex numbers: 1/2 + i*gamma.

If we shift the zeros by 1/2, we are looking for purely imaginary eigenvalues: i*gamma.
In linear algebra, a real matrix has purely imaginary eigenvalues IF AND ONLY IF it is Antisymmetric (M = -M^T).
This mathematically means "time-reversal symmetry is broken", which perfectly aligns with the GUE quantum chaos statistics!

We will build a directed arithmetic graph:
- Edge from u to v if v = u * p.
- Weight is +ln(p) going forward, and -ln(p) going backward.
"""

import math
import numpy as np

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

def get_primes(limit):
    return [p for p in range(2, limit + 1) if is_prime(p)]

def build_antisymmetric_matrix(N):
    """
    Builds an antisymmetric matrix where M_{u, v} = ln(p) and M_{v, u} = -ln(p)
    if v = u * p for some prime p.
    """
    primes = get_primes(N)
    M = np.zeros((N, N))
    
    for u in range(1, N + 1):
        for p in primes:
            v = u * p
            if v <= N:
                # Transcendental injection + Antisymmetry
                weight = math.log(p)
                M[u-1, v-1] = weight
                M[v-1, u-1] = -weight
                
    return M

if __name__ == "__main__":
    N = 100
    print(f"Building Transcendental Antisymmetric Matrix (N={N})...")
    
    M = build_antisymmetric_matrix(N)
    
    # Eigenvalues of a real antisymmetric matrix are purely imaginary: 0 + i*gamma
    evals = np.linalg.eigvals(M)
    
    # Extract the imaginary parts (the gammas)
    gammas = np.imag(evals)
    
    # Filter positive gammas and sort
    positive_gammas = [g for g in gammas if g > 1e-5]
    positive_gammas.sort()
    
    print("\nThe Frequencies (Gammas) of our New Matrix:")
    for i, g in enumerate(positive_gammas[:15]):
        print(f"Mode {i+1:2d}: {g:7.3f}")
        
    print("\nCompare to the first 15 Riemann Zeros:")
    print("14.135, 21.022, 25.011, 30.425, 32.935, 37.586, 40.919, 43.327, 48.005...")
