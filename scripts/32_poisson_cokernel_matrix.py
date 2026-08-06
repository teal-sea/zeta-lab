"""
Script 32: Poisson-Summation Cokernel Matrix (with p-adic tensor factors)

Builds a computational model of the Poisson-summation map on a truncated 
Adelic Schwartz space.

Basis functions are tensor products f = f_real * f_padic.
- f_real is an odd function (e.g. x * exp(-(x/s_j)^2))
- f_padic is the indicator of the fractional ideal p^{-k} Z_p.

For q in Q*, f_padic(q) = 1 if the denominator of q divides d (where d 
encodes the p-adic scales p^k). Otherwise 0.

This structurally encodes the arithmetic of the primes into the matrix, 
addressing Fable's critique that the previous version was just a smooth 
mesh perturbation.
"""

import math
import numpy as np
from fractions import Fraction

def generate_q_mesh(cutoff, primes):
    """
    Generate the truncated rational mesh Q*.
    """
    Q = set()
    max_n = max(3, int(cutoff * 5))
    for n in range(1, max_n + 1):
        Q.add(Fraction(n, 1))
        for p in primes:
            Q.add(Fraction(n, p))
            if p**2 <= cutoff * 3:
                Q.add(Fraction(n, p**2))
    # Return as list of Fractions to preserve exact denominators
    return sorted(list(Q))

def count(cutoff, primes, svd_tol=1e-8):
    Q_fracs = generate_q_mesh(cutoff, primes)
    
    # Rows: sample points in the Adele class space
    rows = int(cutoff * 10) + 10
    X = np.linspace(0.1, cutoff * 2, rows)
    
    # Cols: basis functions (j, d)
    # j is the real basis scale index
    # d is the p-adic indicator (denominator limit)
    real_basis_count = int(cutoff * 2) + 2
    
    # D is the set of allowable denominators
    D = [1] + list(primes)
    cols = real_basis_count * len(D)
    
    M = np.zeros((rows, cols))
    
    col_idx = 0
    for d in D:
        for j in range(real_basis_count):
            s_j = 0.5 + j * 0.3
            for i, x in enumerate(X):
                val = 0.0
                for q_frac in Q_fracs:
                    # p-adic factor: 1 if denom(q) divides d, else 0
                    if d % q_frac.denominator == 0:
                        q_float = float(q_frac)
                        arg = q_float * x
                        if arg < 15.0:  # avoid exp underflow
                            val += arg * math.exp(-(arg / s_j)**2)
                M[i, col_idx] = val
            col_idx += 1
            
    # Compute numerical rank
    s = np.linalg.svd(M, compute_uv=False)
    rank = np.sum(s > svd_tol)
    
    # dim(coker) = Rows - Rank
    coker_dim = rows - rank
    return coker_dim

if __name__ == "__main__":
    from zeta.spectral_gate import counting_gate
    
    primes = [2, 3, 5, 7, 11]
    decoys = [4, 6, 8, 9, 10]
    
    cutoffs = [2.0, 3.0, 4.0]
    
    print("Building Poisson Cokernel Matrices (with p-adic tensor factors)...")
    print("Running Counting Gate...\n")
    
    verdict = counting_gate(count, primes, decoys, cutoffs)
    
    print("--- Counting Gate Verdict ---")
    print(f"Logarithmic: {verdict.logarithmic} (Growth Ratio: {verdict.growth_ratio:.3f})")
    print(f"Predictive: {verdict.predictive} (Error: {verdict.prediction:.1%})")
    print(f"Arithmetic Dependent: {verdict.arithmetic_dependent} (Ablation: {verdict.ablation:.1%})")
    
    if not verdict.passed:
        print("\nFailures:")
        for f in verdict.failures:
            print("- " + f)
        print("\n>> FABLE'S VERDICT: The matrix route is officially closed. Arithmetic is completely absent from the spectrum.")
    else:
        print("\n>> FABLE'S VERDICT OVERTURNED: The p-adic tensor factors forced the matrix to recognize the arithmetic!")
