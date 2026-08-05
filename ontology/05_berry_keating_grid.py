"""
Discovery Lab 5: The Berry-Keating Grid

The Berry-Keating heuristic proposes the classical Hamiltonian H = xp.
Quantized, this is H = -i (x d/dx + 1/2).
Since it has a derivative, it acts on a continuous space. 

But what if we discretize this operator onto a graph? 
We will build a finite difference approximation of H = xp on different "grids"
(integers, primes, and prime logarithms) and see which one produces a 
spectrum closest to the Riemann zeros.

Because H has a first derivative, the finite difference matrix will naturally 
be ANTISYMMETRIC! (f'(x) ~ f(x+1) - f(x-1) gives a +1 and -1 off-diagonal).
"""

import math
import numpy as np
from zeta.zeros import first_n_zeros

def get_primes(limit):
    def is_prime(n):
        if n < 2: return False
        for i in range(2, int(math.sqrt(n)) + 1):
            if n % i == 0: return False
        return True
    return [p for p in range(2, limit + 1) if is_prime(p)]

def build_xp_operator(grid):
    """
    Builds the discretized H = -i(x d/dx + 1/2) operator on a given 1D grid.
    We drop the -i to keep the matrix real and antisymmetric (so eigenvalues are i*gamma).
    """
    N = len(grid)
    M = np.zeros((N, N))
    
    for i in range(1, N - 1):
        # x-coordinate
        x = grid[i]
        
        # Grid spacings
        dx_plus = grid[i+1] - grid[i]
        dx_minus = grid[i] - grid[i-1]
        dx_avg = (dx_plus + dx_minus) / 2.0
        
        # We need an antisymmetric operator. 
        # A simple antisymmetric derivative is (f_{i+1} - f_{i-1}) / (2 * dx_avg)
        # We scale by x for the "x" in "xp"
        weight = x / (2.0 * dx_avg)
        
        M[i, i+1] = weight
        M[i, i-1] = -weight
        
    return M

def analyze_spectrum(M, title):
    evals = np.linalg.eigvals(M)
    gammas = np.imag(evals)
    positive_gammas = [g for g in gammas if g > 1e-5]
    positive_gammas.sort()
    
    print(f"\n--- {title} ---")
    for i, g in enumerate(positive_gammas[:5]):
        print(f"Mode {i+1:2d}: {g:7.3f}")

if __name__ == "__main__":
    N = 100
    print("Testing the Berry-Keating (xp) Operator on different Geometric Grids...")
    
    target_zeros = [float(z) for z in first_n_zeros(5)]
    print("\nTARGET RIEMANN ZEROS:")
    for i, g in enumerate(target_zeros):
        print(f"Mode {i+1:2d}: {g:7.3f}")
    
    # 1. The Integer Grid
    grid_int = np.arange(1, N + 1, dtype=float)
    M_int = build_xp_operator(grid_int)
    analyze_spectrum(M_int, "Integer Grid (x_n = n)")
    
    # 2. The Prime Grid
    primes = get_primes(550)[:N] # Get first N primes
    grid_prime = np.array(primes, dtype=float)
    M_prime = build_xp_operator(grid_prime)
    analyze_spectrum(M_prime, "Prime Grid (x_n = p_n)")
    
    # 3. The Transcendental Prime Grid (Deninger's Orbits)
    grid_log_prime = np.log(grid_prime)
    M_log_prime = build_xp_operator(grid_log_prime)
    analyze_spectrum(M_log_prime, "Transcendental Prime Grid (x_n = ln p_n)")
