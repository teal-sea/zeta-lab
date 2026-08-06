"""
Discovery Lab 10: Geometric Dust Torus (Symphony of Polygons)
Testing the 2026 Geometric Riemann Hypothesis Reformulation

Constructs a Hamiltonian H = -Laplacian + V on a discrete torus,
where V is the "geometric dust" accumulated from regular polygons.

Using the exact Phase Embedding from the paper:
Phi(n) = sqrt(n) * exp(i * sqrt(n * pi))
Wrapped onto T^2 as:
theta_1(n) = sqrt(n * pi) mod 2*pi
theta_2(n) = sqrt(n) mod 2*pi
"""

import numpy as np

def geometric_dust(n):
    """Area remainder between a circle of radius n and an inscribed regular n-gon."""
    if n == 1 or n == 2:
        return 0.0
    return np.pi * (n**2) - 0.5 * (n**3) * np.sin(2 * np.pi / n)

def torus_laplacian(N, dx=1.0):
    """Constructs the discrete Laplacian on an N x N periodic grid."""
    size = N * N
    L = np.zeros((size, size), dtype=float)
    
    def idx(i, j):
        return (i % N) * N + (j % N)
        
    for i in range(N):
        for j in range(N):
            k = idx(i, j)
            L[k, idx(i+1, j)] = -1.0 / (dx**2)
            L[k, idx(i-1, j)] = -1.0 / (dx**2)
            L[k, idx(i, j+1)] = -1.0 / (dx**2)
            L[k, idx(i, j-1)] = -1.0 / (dx**2)
            L[k, k] = 4.0 / (dx**2)
    return L

def torus_distance_sq(t1, t2, target_t1, target_t2):
    """Squared geodesic distance on [0, 2pi) x [0, 2pi) torus."""
    d1 = abs(t1 - target_t1)
    d1 = min(d1, 2*np.pi - d1)
    
    d2 = abs(t2 - target_t2)
    d2 = min(d2, 2*np.pi - d2)
    
    return d1**2 + d2**2

def build_dust_potential(N, M, sigma=0.5):
    """Builds a potential V on the torus using Phase Embedding."""
    V = np.zeros((N, N), dtype=float)
    
    # Grid coordinates on [0, 2pi)
    theta_grid = np.linspace(0, 2*np.pi, N, endpoint=False)
    
    for n in range(3, M+1):
        dust = geometric_dust(n)
        
        # Exact phase embedding from paper
        theta1_n = np.sqrt(n * np.pi) % (2 * np.pi)
        theta2_n = np.sqrt(n) % (2 * np.pi)
        
        # Gaussian smoothing onto the discrete grid
        for i in range(N):
            for j in range(N):
                d_sq = torus_distance_sq(theta_grid[i], theta_grid[j], theta1_n, theta2_n)
                V[i, j] += dust * np.exp(-d_sq / (2 * sigma**2))
                
    # Flatten to diagonal potential matrix
    size = N * N
    P = np.zeros((size, size), dtype=float)
    for i in range(N):
        for j in range(N):
            k = i * N + j
            P[k, k] = V[i, j]
    return P

def evaluate_geometric_rh():
    print("Initializing EXACT Phase Embedding Geometric Dust Torus...")
    N = 50  # Super-high grid size for maximum resolution
    M = 300  # Enormous number of polygons to accumulate geometric dust
    dx = 2 * np.pi / N
    
    L = torus_laplacian(N, dx)
    P = build_dust_potential(N, M, sigma=0.2)
    H = L + P
    
    print(f"Diagonalizing {N*N}x{N*N} Hamiltonian...")
    eigvals = np.linalg.eigvalsh(H)
    
    # The Geometric RH requires all eigenvalues to be real and >= 1/4
    min_eig = np.min(eigvals)
    print(f"Minimum Eigenvalue: {min_eig:.4f} (Must be >= 0.25 for Geometric RH)")
    
    # Known Riemann zeros (imaginary parts)
    t_vals = [14.1347, 21.0220, 25.0108, 30.4249, 32.9351, 37.5862, 40.9187]
    target = np.array([0.25 + t**2 for t in t_vals])
    
    lam = np.sort(eigvals)[:len(target)]
    
    # Linear calibration (alpha * lam + beta = 1/4 + t^2)
    A = np.vstack([lam, np.ones_like(lam)]).T
    alpha, beta = np.linalg.lstsq(A, target, rcond=None)[0]
    
    calibrated = alpha * lam + beta
    error = np.abs(calibrated - target) / target * 100
    
    print("\nSpectral Calibration against Riemann Zeros:")
    print(f"Alpha: {alpha:.4f}, Beta: {beta:.4f}")
    for i in range(len(target)):
        print(f"Zero {i+1}: Target {target[i]:.2f} | Torus Model {calibrated[i]:.2f} | Error: {error[i]:.2f}%")

if __name__ == "__main__":
    evaluate_geometric_rh()
