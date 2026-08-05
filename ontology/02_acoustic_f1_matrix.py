"""
Discovery Lab 2: The Acoustic Matrix of F1 (The Primordial Instrument)

If the primes are the geometry, and the Riemann zeros are the resonant frequencies,
we need to build the mathematical equivalent of a guitar.

We construct the "Arithmetic Graph":
- The "nodes" (the space) are the integers up to N.
- The "springs" (the edges) connect two integers if they differ by a prime factor (e.g. 2 and 6 are connected by a spring for prime 3).
- The stiffness of the spring (the weight) is dictated by the prime's period: 1 / ln(p).

We then compute the Graph Laplacian (the wave equation of this space) 
and listen to the eigenvalues (the resonant frequencies).
"""

import math
import numpy as np

# Music mapping function
NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']

def midi_to_note_name(midi_val):
    midi_rounded = int(round(midi_val))
    degree = midi_rounded % 12
    octave = midi_rounded // 12 - 1
    return f"{NOTE_NAMES[degree]}{octave}"

def map_spectrum_to_music(freqs, base_midi=40):
    # Filter out the zero mode (the trivial translation of the instrument)
    valid_freqs = [f for f in freqs if f > 1e-5]
    valid_freqs.sort()
    
    if not valid_freqs:
        return
        
    base_freq = valid_freqs[0]
    
    print(f"\n--- Acoustic Spectrum (The Notes) ---")
    for i, freq in enumerate(valid_freqs[:25]):
        ratio = freq / base_freq
        midi_val = base_midi + 12 * math.log2(ratio)
        note = midi_to_note_name(midi_val)
        cents = (midi_val - round(midi_val)) * 100
        print(f"Mode {i+1:2d} (freq={freq:7.3f}) -> {note:>4} {cents:+5.1f} cents")

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

def get_primes(limit):
    return [p for p in range(2, limit + 1) if is_prime(p)]

def build_arithmetic_laplacian(N):
    """
    Builds the Laplacian matrix for the integer multiplication graph up to N.
    Edge between u and v if v = u * p for a prime p.
    Weight = 1.0 / ln(p)
    """
    primes = get_primes(N)
    
    # Adjacency matrix
    A = np.zeros((N, N))
    
    for u in range(1, N + 1):
        for p in primes:
            v = u * p
            if v <= N:
                weight = 1.0 / math.log(p)
                # u and v are 1-indexed, so we use u-1 and v-1
                A[u-1, v-1] = weight
                A[v-1, u-1] = weight
                
    # Degree matrix
    D = np.diag(np.sum(A, axis=1))
    
    # Laplacian
    L = D - A
    return L

if __name__ == "__main__":
    N = 100
    print(f"Building F1 Acoustic Instrument using integers 1 to {N}...")
    
    L = build_arithmetic_laplacian(N)
    print(f"Laplacian Matrix Shape: {L.shape}")
    
    print("\nComputing the Wave Equation (Eigenvalues of the Laplacian)...")
    evals = np.linalg.eigvals(L)
    
    # The physical frequencies of a mass-spring network are sqrt(eigenvalues of Laplacian)
    # We take the absolute value to handle tiny negative numerical noise on the 0 eigenvalue
    freqs = np.sqrt(np.abs(evals))
    
    map_spectrum_to_music(freqs, base_midi=40)
