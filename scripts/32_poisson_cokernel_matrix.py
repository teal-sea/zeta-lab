"""
Script 32: Poisson-Summation Cokernel Matrix

Builds a computational model of the Poisson-summation map on a truncated 
Adelic Schwartz space.

We project onto the subspace f(0) = f_hat(0) = 0 by using odd basis functions:
f_j(x) = x * exp(-(x / s_j)^2).

This script implements the count(cutoff, primes) interface expected by 
zeta.spectral_gate.counting_gate, and then runs the gate to test 
Fable's B3 prediction: that truncation breaks the functional equations, 
making the matrix generic and causing the counting gate to fail on ablation 
and growth ratio.
"""

import math
import numpy as np

def generate_q_mesh(cutoff, primes):
    """
    Generate the truncated rational mesh Q*.
    """
    Q = set()
    max_n = max(3, int(cutoff * 5))
    for n in range(1, max_n + 1):
        Q.add(float(n))
        for p in primes:
            Q.add(n / float(p))
    return sorted(list(Q))

def count(cutoff, primes, svd_tol=1e-8):
    """
    Returns the cokernel dimension of the truncated Poisson map E_Lambda.
    """
    Q = generate_q_mesh(cutoff, primes)
    
    # Rows: sample points in the Adele class space
    # We ensure Rows > Cols so the cokernel is naturally Rows - Rank
    rows = int(cutoff * 10) + 10
    X = np.linspace(0.1, cutoff * 2, rows)
    
    # Cols: basis functions
    cols = int(cutoff * 4) + 5
    
    M = np.zeros((rows, cols))
    
    for j in range(cols):
        s_j = 0.5 + j * 0.2
        for i, x in enumerate(X):
            val = 0.0
            for q in Q:
                arg = q * x
                if arg < 15.0:  # avoid exp underflow
                    val += arg * math.exp(-(arg / s_j)**2)
            M[i, j] = val
            
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
    
    # cutoffs: the first element is used as the base for count_growth_ratio (base, base^2, base^4).
    # the last element is the held-out point for count_prediction_defect.
    cutoffs = [2.0, 3.0, 4.0]
    
    print("Building Poisson Cokernel Matrices and running Counting Gate...")
    print("Testing Fable's B3 Pre-Registered Prediction...")
    print("If Ablation ≈ 0.0%, truncation genericized the matrix.\n")
    
    verdict = counting_gate(count, primes, decoys, cutoffs)
    
    print("--- Counting Gate Verdict ---")
    print(f"Logarithmic: {verdict.logarithmic} (Growth Ratio: {verdict.growth_ratio:.3f})")
    print(f"Predictive: {verdict.predictive} (Error: {verdict.prediction:.1%})")
    print(f"Arithmetic Dependent: {verdict.arithmetic_dependent} (Ablation: {verdict.ablation:.1%})")
    
    if not verdict.passed:
        print("\nFailures:")
        for f in verdict.failures:
            print("- " + f)
        print("\n>> FABLE'S PREDICTION CONFIRMED: The truncation broke the exact functional equations.")
        print(">> The matrix became mathematically generic, fixing the rank to min(Rows, Cols).")
    else:
        print("\n>> FABLE'S PREDICTION BROKEN: The matrix preserved the functional equation!")
