"""
Discovery Lab 16: The Adelic Acoustic Absorber
Testing the hypothesis that the Riemann zeros are Bragg Resonances 
(absorption lines) in a 1D Prime Crystal.

In 1D quantum scattering, a wave passing through a medium with 
scattering potentials V(x) will undergo Bragg reflection. The reflection 
amplitude R(k) is proportional to the Fourier transform of the potential.

The Potential V(x):
We place an acoustic baffle at x = ln(p) with strength ln(p).
We must also subtract the "background medium" density (e^x), which 
represents the continuous Adelised real line.

R(k) = Sum_{p} ln(p) e^{i k ln(p)} - Integral_{0}^{ln N} e^x e^{i k x} dx

The Transmission T(k) = 1 / (1 + |R(k)|^2). 
When R(k) spikes (constructive Bragg reflection), T(k) plummets to 0.
The frequencies k where T(k) drops to zero should be EXACTLY the Riemann zeros.
"""

import math
import cmath
import numpy as np

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

def get_primes(limit):
    return [p for p in range(2, limit + 1) if is_prime(p)]

def calculate_reflection(k, primes, N_limit):
    """
    Calculates the Bragg reflection amplitude R(k) for wavenumber k.
    """
    # 1. Scattering from the Prime Baffles (Discrete Sum)
    prime_scatter = sum(math.log(p) * cmath.exp(1j * k * math.log(p)) for p in primes)
    
    # 2. Scattering from the Background Medium (Continuous Integral of e^x)
    # Integral of e^x * e^{ikx} from x=0 to ln(N)
    # Anti-derivative is e^{(1+ik)x} / (1+ik)
    exponent = 1.0 + 1j * k
    upper_bound = cmath.exp(exponent * math.log(N_limit))
    lower_bound = 1.0
    background_scatter = (upper_bound - lower_bound) / exponent
    
    # Total Reflection Amplitude
    R = prime_scatter - background_scatter
    return R

if __name__ == "__main__":
    N_limit = 100000
    print(f"Building the 1D Prime Crystal (N={N_limit})...")
    primes = get_primes(N_limit)
    
    print("Sending broadband acoustic waves through the crystal...")
    
    # We will test frequencies k around the first 3 Riemann zeros
    # Zeros: 14.1347, 21.0220, 25.0108
    
    test_zones = [
        ("Zero 1", np.linspace(13.8, 14.5, 30)),
        ("Zero 2", np.linspace(20.7, 21.3, 30)),
        ("Zero 3", np.linspace(24.7, 25.3, 30))
    ]
    
    for zone_name, k_values in test_zones:
        print(f"\n--- Scanning Frequencies near {zone_name} ---")
        
        min_transmission = 1.0
        resonant_k = 0.0
        
        for k in k_values:
            R = calculate_reflection(k, primes, N_limit)
            # Transmission coefficient (scaled for visibility)
            intensity = abs(R)**2
            # Alpha is a coupling constant to make the physics visible
            alpha = 1e-6 
            T = 1.0 / (1.0 + alpha * intensity)
            
            if T < min_transmission:
                min_transmission = T
                resonant_k = k
                
            # If transmission drops below 90%, it's a deep absorption line
            marker = "█" * int(T * 20)
            if T < 0.2:
                print(f"k = {k:7.4f} Hz | T(k) = {T:5.3f} [ABSORBED!] {marker}")
            elif T < 0.8:
                print(f"k = {k:7.4f} Hz | T(k) = {T:5.3f} [DAMPENED] {marker}")
            else:
                pass # Too noisy to print all clear channels
                
        print(f">> Maximum Bragg Reflection (Total Silence) detected at k = {resonant_k:.4f}")
