"""
Discovery Lab 11: Quantum Chaos & The Music of the Primes
Testing the Montgomery-Odlyzko Law (GUE Random Matrices)

Compares the statistical spacing of Riemann zeros to the energy levels
of a heavy atomic nucleus (Gaussian Unitary Ensemble).
"""

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

def wigner_surmise_gue(s):
    """The GUE spacing distribution (Wigner surmise approx)."""
    return (32 / np.pi**2) * (s**2) * np.exp(-(4 / np.pi) * (s**2))

def generate_gue_eigenvalues(N):
    """Generate eigenvalues of a random NxN GUE matrix."""
    # GUE: H = (A + A^dagger) / 2 where A has complex gaussian entries
    A = np.random.randn(N, N) + 1j * np.random.randn(N, N)
    H = (A + A.conj().T) / 2.0
    eigvals = np.linalg.eigvalsh(H)
    return eigvals

def normalize_spacings(eigenvalues):
    """Normalize spacings so the mean spacing is 1."""
    spacings = np.diff(np.sort(eigenvalues))
    mean_spacing = np.mean(spacings)
    return spacings / mean_spacing

def plot_quantum_chaos():
    print("Initializing Quantum Chaos GUE Model...")
    
    # 1. Generate GUE Eigenvalue spacings
    N_matrix = 1000
    gue_eigs = generate_gue_eigenvalues(N_matrix)
    gue_spacings = normalize_spacings(gue_eigs)
    
    # 2. Known first Riemann zeros (using a precomputed sample or mpmath)
    import mpmath
    mpmath.mp.dps = 15
    print("Computing first 400 Riemann zeros for spectral analysis...")
    zeros = [float(mpmath.zetazero(i).imag) for i in range(1, 401)]
    
    # Normalize zero spacings: s_n = (gamma_n+1 - gamma_n) * (log(gamma_n / 2pi) / 2pi)
    zero_spacings = []
    for i in range(len(zeros)-1):
        delta = zeros[i+1] - zeros[i]
        density = np.log(zeros[i] / (2 * np.pi)) / (2 * np.pi)
        zero_spacings.append(delta * density)
        
    zero_spacings = np.array(zero_spacings)
    # The analytical density log(t/2pi)/2pi is asymptotic, for small zeros mean spacing is slightly off
    # We rescale manually for this small sample to match mean=1 exactly
    zero_spacings = zero_spacings / np.mean(zero_spacings)
    
    # Plotting
    s_vals = np.linspace(0, 3, 200)
    p_vals = wigner_surmise_gue(s_vals)
    
    plt.figure(figsize=(10, 6))
    
    # Histogram of GUE spacings
    plt.hist(gue_spacings, bins=40, density=True, alpha=0.5, color='blue', label='GUE Matrix Eigenvalues')
    
    # Histogram of Riemann Zero spacings
    plt.hist(zero_spacings, bins=30, density=True, alpha=0.6, color='crimson', label='Riemann Zeros')
    
    # Analytical GUE curve
    plt.plot(s_vals, p_vals, 'k-', linewidth=2, label='GUE Prediction (Wigner Surmise)')
    
    plt.title("The Music of the Primes: Quantum Chaos (GUE) vs Riemann Zeros")
    plt.xlabel("Normalized Spacing (s)")
    plt.ylabel("Probability Density P(s)")
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plot_path = "figures/11_quantum_chaos_gue.png"
    import os
    if not os.path.exists("figures"):
        os.makedirs("figures")
    plt.savefig(plot_path)
    print(f"Saved Quantum Chaos plot to {plot_path}")

if __name__ == "__main__":
    plot_quantum_chaos()
