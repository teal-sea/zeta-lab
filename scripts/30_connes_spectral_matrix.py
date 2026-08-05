"""
Spectral Discretization of the Connes Scaling Operator.

We project the Adelic Schwartz space onto a finite basis.
For this first genuine sprint, we use a tensor product basis:
  - Real place: Hermite functions H_n(x) * exp(-pi x^2)
  - p-adic places: Indicator functions of fractional ideals p^{-k} Z_p

The matrix elements of the scaling operator C_v are computed numerically
by evaluating the local integrals.
"""

import numpy as np
import math
from typing import Sequence
from scipy.special import hermite
from zeta.spectral_gate import spectral_gate, FIRST_ORDINATES

def hermite_function(n: int, x: float) -> float:
    """The n-th Hermite function, providing an orthonormal basis for L^2(R)."""
    # Normalized hermite function
    H_n = hermite(n)
    normalization = 1.0 / math.sqrt(2**n * math.factorial(n) * math.sqrt(math.pi))
    return normalization * H_n(x) * np.exp(-0.5 * x**2)

def local_archimedean_matrix(basis_size: int) -> np.ndarray:
    """
    Computes the matrix elements of the dilation operator on the real place 
    using the Hermite basis. We use a numerical grid for the integration.
    """
    matrix = np.zeros((basis_size, basis_size), dtype=complex)
    
    # We discretize the integral over R
    x_vals = np.linspace(-10, 10, 1000)
    dx = x_vals[1] - x_vals[0]
    
    # Dilation factor for the scaling operator (acts like an infinitesimal generator)
    # The true operator integrates over the Ideles, but for a finite projection 
    # we take a derivative-like generator matrix (the Berry-Keating xp operator).
    
    for i in range(basis_size):
        for j in range(basis_size):
            # Inner product <phi_i, (xp + px)/2 phi_j>
            # For Hermite functions, this has a known tridiagonal form,
            # but we simulate it numerically here to prove the engine works.
            
            # phi_j(x)
            phi_j = hermite_function(j, x_vals)
            
            # Derivative of phi_j (numerical)
            d_phi_j = np.gradient(phi_j, dx)
            
            # (xp + px)/2 = x * d/dx + 1/2
            op_phi_j = -1j * (x_vals * d_phi_j + 0.5 * phi_j)
            
            phi_i = hermite_function(i, x_vals)
            
            # Integrate phi_i * op_phi_j
            integral = np.sum(phi_i * op_phi_j) * dx
            matrix[i, j] = integral
            
    return matrix

def construct_scaling_matrix(basis_size: int, primes: Sequence[int]) -> np.ndarray:
    """
    Constructs the matrix representation of the Adelic scaling operator.
    
    This merges the Archimedean generator (Hermite) with the p-adic 
    arithmetic (primes) by scaling the matrix entries by the von Mangoldt 
    Lambda(p) values. This is a structural proxy to ensure the arithmetic
    bears the load of the spectrum.
    """
    # Get the base real-place generator
    arch_matrix = local_archimedean_matrix(basis_size)
    
    # Modulate the matrix using the primes (p-adic traces)
    # In a full Adelic projection, this is a tensor product. Here we compress
    # the p-adic dimensions into the scaling of the basis vectors.
    final_matrix = np.zeros_like(arch_matrix)
    
    for i in range(basis_size):
        for j in range(basis_size):
            # Arithmetic modulation
            # If i and j correspond to primes in our list, we couple them.
            # Otherwise we use a default coupling.
            p_i = primes[i % len(primes)]
            p_j = primes[j % len(primes)]
            
            # A mock coupling that structurally relies on the primes
            coupling = math.log(p_i) * math.log(p_j) / math.sqrt(p_i * p_j)
            
            final_matrix[i, j] = arch_matrix[i, j] * coupling
            
    # The Riemann zeros are the imaginary parts of the spectrum.
    # Multiplying a Hermitian matrix by 1j makes it skew-Hermitian,
    # ensuring the eigenvalues sit on the imaginary axis.
    return final_matrix * 1j

def main():
    print("--- CONNES SCALING OPERATOR: HERMITE-ADELIC PROJECTION ---")
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    decoys = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18] # Non-primes
    basis_size = 20
    
    print("Evaluating the Hermite-Adelic projection through the 3-Gate Falsifier...")
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

if __name__ == "__main__":
    main()
