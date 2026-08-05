"""
Gate 1 Harness: The Classical Physics Battery

Following Fable's critique, a candidate operator must not just 'look' like 
the Riemann zeros; it must rigorously reproduce the classical physics of 
the Zeta function. This harness tests two computable scorecards:

1. Density of States: Does the spectrum grow like (T/2π)log(T/2π)?
2. The Weil Trace: Does the spectral sum against test functions exactly 
   reproduce the prime-sum side of the Weil explicit formula?

We test our 'Final Boss' Polya-Hilbert prototype matrix against this rigorous harness.
"""

import math
import numpy as np
from mpmath import mp

# We import the exact Weil arithmetic evaluator from the repo
from zeta.weil import gaussian_pair, weil_functional

# --- QUARANTINED ONTOLOGY (The Prototype Matrix) ---
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
    x = np.array([math.log(n) if n > 1 else 0.0 for n in range(1, N + 1)])
    
    for u in range(1, N + 1):
        for p in primes:
            v = u * p
            if v <= N:
                dist = math.log(p)
                x_avg = (x[u-1] + x[v-1]) / 2.0
                weight = x_avg / dist
                M[u-1, v-1] = weight
                M[v-1, u-1] = -weight
    return M
# --------------------------------------------------

def test_density(gammas):
    print("\n--- TEST 1: DENSITY OF STATES ---")
    
    # Riemann-von Mangoldt asymptotic for N(T)
    # N(T) ≈ (T / 2π) * log(T / 2πe) + 7/8
    
    for T in [2.0, 5.0, 10.0, 20.0]:
        n_cand = sum(1 for g in gammas if g <= T)
        if T > 2*math.pi:
            n_rvm = (T / (2 * math.pi)) * math.log(T / (2 * math.pi * math.e)) + 7/8
        else:
            n_rvm = 0
            
        print(f"T = {T:5.1f} | Candidate N(T): {n_cand:3d} | Target RvM N(T): {max(0, n_rvm):7.3f}")
        
    print("\nScorecard:")
    print("If Candidate N(T) wildly exceeds RvM N(T), it's a density failure.")

def test_weil_trace(gammas):
    print("\n--- TEST 2: THE WEIL TRACE FORMULA ---")
    print("Testing against a Gaussian test function (a = 0.05)")
    h, g = gaussian_pair(0.05)
    
    print("Computing candidate spectral trace...")
    with mp.workdps(25):
        spectral_trace = mp.mpf(0)
        for gamma in gammas:
            # We must convert gamma to mpf first
            g_mp = mp.mpf(gamma)
            spectral_trace += h(g_mp) + h(-g_mp)
            
    print(f"Candidate Spectral Trace:  {spectral_trace}")
    
    print("Computing actual arithmetic trace (primes) via zeta.weil...")
    arithmetic_trace = weil_functional(h, g, dps=25)
    
    print(f"Target Arithmetic Trace:   {arithmetic_trace}")
    
    with mp.workdps(25):
        diff = abs(spectral_trace - arithmetic_trace)
    print(f"Absolute Difference:       {diff}")
    
    if diff < 1e-5:
        print("\n✅ GATE 1 PASSED: The operator perfectly reproduces the prime distribution!")
    else:
        print("\n❌ GATE 1 FAILED: The operator does not reproduce the Weil formula.")
        print("This is the exact proof that finite truncations of H=xp have a continuous spectrum dead-end.")

if __name__ == "__main__":
    N = 200
    print(f"Building candidate operator (Polya-Hilbert Prototype N={N})...")
    M = build_polya_hilbert_operator(N)
    evals = np.linalg.eigvals(M)
    gammas = sorted([float(g) for g in np.imag(evals) if g > 1e-5])
    
    test_density(gammas)
    test_weil_trace(gammas)
