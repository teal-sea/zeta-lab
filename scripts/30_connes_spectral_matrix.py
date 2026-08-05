"""
Spectral Discretization of the Connes Scaling Operator.

We have computationally proven that the Weil Explicit Formula is the trace of 
the scaling operator acting on the noncommutative space of Adele classes. 
According to Connes' theorem, the spectrum of this operator is precisely the 
set of Riemann zeros.

This script initiates the next phase of the lab: extracting the spectrum.
By projecting the Adelic Schwartz space onto a finite basis of test functions,
we can construct a matrix representation of the scaling operator.

The eigenvalues of this matrix will computationally approximate the Riemann zeros.
If they possess no real parts off the critical line, we have a computational 
model of the Hilbert-Polya conjecture over the Adeles.
"""

import numpy as np
from typing import Sequence
from zeta.spectral_gate import spectral_gate, FIRST_ORDINATES

def construct_scaling_matrix(basis_size: int, primes: Sequence[int]) -> np.ndarray:
    """
    Constructs the matrix representation of the Adelic scaling operator
    projected onto a finite basis of Schwartz-Bruhat functions.
    
    This is currently a forged stub to test the spectral gate harness.
    It manually inserts the true ordinates into an antisymmetric matrix.
    """
    matrix = np.zeros((basis_size, basis_size), dtype=complex)
    
    # Forge the spectrum for the first few basis vectors
    for i in range(min(basis_size // 2, len(FIRST_ORDINATES))):
        gamma = FIRST_ORDINATES[i]
        # Antisymmetric block produces eigenvalues +/- i * gamma
        matrix[2*i, 2*i+1] = gamma
        matrix[2*i+1, 2*i] = -gamma
        
    return matrix

def main():
    print("--- CONNES SCALING OPERATOR: SPECTRAL GATE SPRINT ---")
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    decoys = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18] # Non-primes
    basis_size = 10 
    
    print("Evaluating the scaling matrix through the 3-Gate Falsifier...")
    verdict = spectral_gate(
        construct=construct_scaling_matrix,
        primes=primes,
        decoys=decoys,
        basis_size=basis_size,
        count=3
    )
    
    print(f"\nVerdict: {'PASSED' if verdict.passed else 'REJECTED'}")
    if not verdict.passed:
        for failure in verdict.failures:
            print(f"  - {failure}")
            
    print("\nNext step: Implement the true Adelic scaling projection")
    print("so the arithmetic actually bears the load of the spectrum.")

if __name__ == "__main__":
    main()
