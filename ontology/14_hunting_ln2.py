"""
Discovery Lab 14: Hunting Down the ln(2) Artifact
Addressing Fable's Critique #2

Fable claimed that the magical ln(2) eigenvalue from the Transcendental 
Antisymmetric Matrix was a fake "truncation artifact." 
The theory: For primes p between N/3 and N/2, the only multiple of p 
that fits under the cutoff N is 2p. So p and 2p get mathematically 
severed from the rest of the graph, forming an isolated 2-node subsystem 
with edge weight ln(2). Since this happens for many primes, it creates 
a massive degenerate spike exactly at ln(2) (approx 0.693).

To hunt this down, we will implement a "Quantum Absorbing Boundary." 
Instead of a hard wall at N, we apply a smooth tapering window so that 
edges weaken as they approach N. If Fable is right, the degenerate 
ln(2) spike will instantly melt away.
"""

import math
import numpy as np
from collections import Counter

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

def get_primes(limit):
    return [p for p in range(2, limit + 1) if is_prime(p)]

def build_matrix(N, use_smooth_boundary=False):
    primes = get_primes(N)
    M = np.zeros((N, N))
    
    for u in range(1, N + 1):
        for p in primes:
            v = u * p
            if v <= N:
                weight = math.log(p)
                
                # Apply the smooth absorbing boundary condition (Cosine squared taper)
                if use_smooth_boundary:
                    # Taper based on how close v is to the edge N
                    window = math.cos((math.pi / 2.0) * (v / N))**2
                    weight *= window
                    
                M[u-1, v-1] = weight
                M[v-1, u-1] = -weight
    return M

def report_degeneracy(M, title):
    print(f"\n--- {title} ---")
    evals = np.linalg.eigvals(M)
    gammas = np.imag(evals)
    positive_gammas = [round(g, 4) for g in gammas if g > 1e-4]
    
    # Count degeneracies
    counts = Counter(positive_gammas)
    
    # Sort by frequency of occurrence (most degenerate first)
    most_degenerate = counts.most_common(5)
    
    print("Top 5 Most Degenerate Frequencies (Spikes):")
    for val, count in most_degenerate:
        print(f"Frequency: {val:.4f}  |  Multiplicity (Hits): {count}")
        
    print("\nFirst 10 distinct frequencies:")
    distinct = sorted(list(set(positive_gammas)))
    for i, val in enumerate(distinct[:10]):
        print(f"Mode {i+1}: {val:.4f}")

if __name__ == "__main__":
    N = 250
    print(f"Hunting the ln(2) Artifact (N={N})")
    print("ln(2) is approximately 0.6931")
    
    # 1. The original hard cutoff matrix
    M_hard = build_matrix(N, use_smooth_boundary=False)
    report_degeneracy(M_hard, "Original Hard Boundary (Fable's Suspect)")
    
    # 2. The smooth boundary matrix
    M_smooth = build_matrix(N, use_smooth_boundary=True)
    report_degeneracy(M_smooth, "Smooth Absorbing Boundary")
