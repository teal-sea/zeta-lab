"""
Discovery Lab 6: The Polya-Hilbert Prototype

We combine all four structural rules we discovered:
1. Arithmetic Edges (Edges exist only if v = u * p)
2. Logarithmic Distances (Grid points are x_n = ln(n))
3. First-Derivative (Operator scales by 1 / distance)
4. Antisymmetry (M = -M^T to break time-reversal symmetry)

We will build the Hamiltonian H = x*p (which is -i x d/dx) 
on this exact topological space.
"""

import math
import numpy as np
from zeta.zeros import first_n_zeros

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

def get_primes(limit):
    return [p for p in range(2, limit + 1) if is_prime(p)]

def build_polya_hilbert_operator(N):
    primes = get_primes(N)
    M = np.zeros((N, N))
    
    # Grid points: x_n = ln(n). We use max(1, n) to avoid ln(1)=0 issues if needed,
    # but x_1 = 0 is geometrically correct (the origin).
    x = np.array([math.log(n) if n > 1 else 0.0 for n in range(1, N + 1)])
    
    for u in range(1, N + 1):
        for p in primes:
            v = u * p
            if v <= N:
                # Distance is always ln(p)
                dist = math.log(p)
                
                # H = x * (d/dx)
                # We use the average x coordinate of the edge
                x_avg = (x[u-1] + x[v-1]) / 2.0
                
                # The derivative weight is 1 / dx
                # So the operator weight is x_avg / dx
                weight = x_avg / dist
                
                # Antisymmetry forces the eigenvalues onto the imaginary axis (critical line)
                M[u-1, v-1] = weight
                M[v-1, u-1] = -weight
                
    return M

if __name__ == "__main__":
    N = 400
    print(f"Building the Polya-Hilbert Prototype Matrix (N={N})...")
    
    M = build_polya_hilbert_operator(N)
    
    print("Computing the eigenvalues...")
    evals = np.linalg.eigvals(M)
    
    # Extract the imaginary parts (the gammas)
    gammas = np.imag(evals)
    
    # Filter positive gammas and sort
    positive_gammas = [g for g in gammas if g > 1e-5]
    positive_gammas.sort()
    
    print("\nThe Frequencies (Gammas) of the Prototype:")
    for i, g in enumerate(positive_gammas[:20]):
        print(f"Mode {i+1:2d}: {g:7.3f}")
        
    print("\nCompare to the first 20 Riemann Zeros:")
    target_zeros = [float(z) for z in first_n_zeros(20)]
    for i, z in enumerate(target_zeros):
        print(f"Mode {i+1:2d}: {z:7.3f}")
