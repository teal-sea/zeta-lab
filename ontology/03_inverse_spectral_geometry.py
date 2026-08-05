"""
Discovery Lab 3: Inverse Spectral Geometry

Instead of guessing the geometry and hoping it plays the Riemann zeros,
we will work backwards. We know the exact frequencies the instrument 
must play (the zeros). 

We will use numerical optimization to mathematically "forge" a matrix 
whose eigenvalues perfectly match the first N Riemann zeros. 
Then, we will inspect the matrix to see what shape it took.

This is Inverse Spectral Geometry: "Hearing the shape of the drum" in reverse.
"""

import numpy as np
from scipy.optimize import minimize
from zeta.zeros import first_n_zeros

def build_symmetric_matrix(params, N):
    """Reconstruct a symmetric N x N matrix from its upper triangular elements."""
    matrix = np.zeros((N, N))
    idx = 0
    for i in range(N):
        for j in range(i, N):
            matrix[i, j] = params[idx]
            matrix[j, i] = params[idx]  # Mirror for symmetry
            idx += 1
    return matrix

def spectral_loss(params, N, target_eigenvalues):
    """
    Computes how far the current matrix's eigenvalues are from the Riemann zeros.
    """
    matrix = build_symmetric_matrix(params, N)
    
    # Compute eigenvalues
    evals = np.linalg.eigvalsh(matrix)
    
    # Sort just in case, though eigvalsh already sorts them
    evals = np.sort(evals)
    
    # We compare the absolute values (magnitudes) since zeros are frequencies
    loss = np.sum((np.abs(evals) - target_eigenvalues)**2)
    
    # Add a small L1 regularization to encourage a sparse (graph-like) matrix
    l1_penalty = 0.01 * np.sum(np.abs(params))
    
    return loss + l1_penalty

def forge_instrument(num_zeros=15):
    print(f"Fetching the first {num_zeros} Riemann zeros...")
    target_zeros = np.array([float(z) for z in first_n_zeros(num_zeros)])
    print("Target Frequencies:", np.round(target_zeros, 2))
    
    # We can mathematically guarantee a matrix has these eigenvalues 
    # using the Spectral Theorem: M = O * D * O^T 
    # where D is the diagonal matrix of the zeros, and O is an orthogonal matrix.
    
    print("\nForging the acoustic matrix (using the Spectral Theorem)...")
    
    # 1. Create the diagonal matrix of frequencies
    D = np.diag(target_zeros)
    
    # 2. Generate a random Orthogonal matrix O to 'scramble' the geometry
    random_mat = np.random.randn(num_zeros, num_zeros)
    Q, R = np.linalg.qr(random_mat)
    
    # 3. Forge the final matrix
    forged_matrix = Q @ D @ Q.T
    
    print("\n✅ Successfully forged a matrix that perfectly plays the Riemann zeros!")
    
    evals = np.linalg.eigvalsh(forged_matrix)
    print("\nForged Spectrum vs Target Spectrum:")
    for i in range(num_zeros):
        print(f"Mode {i+1:2d}: Forged {abs(evals[i]):.3f} | Target {target_zeros[i]:.3f}")
        
    print("\nWhat does the forged matrix look like? (Top left 5x5 corner)")
    np.set_printoptions(precision=2, suppress=True, linewidth=100)
    print(forged_matrix[:5, :5])
    
    print("\nBut here is the problem: this matrix is unstructured noise.")
    print("The holy grail is finding a matrix that produces this spectrum")
    print("where the matrix itself is built OUT OF THE PRIME NUMBERS (like our acoustic graph).")

if __name__ == "__main__":
    forge_instrument(num_zeros=15)
