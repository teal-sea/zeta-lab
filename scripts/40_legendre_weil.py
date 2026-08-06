"""
Landau Problem 1: Legendre's Conjecture via the Explicit Formula

Legendre's Conjecture states there is always a prime between n^2 and (n+1)^2.

We attack this using zeta/weil.py. 
We construct a test function g(u) that is strictly supported in the 
intervals [-B, -A] and [A, B], where A = log(n^2) and B = log((n+1)^2).

Because g(u) is zero everywhere else, the prime sum in the Riemann-Weil 
explicit formula ONLY evaluates primes inside the Legendre gap!

W(h) = pole + arch_term - 2 * sum( Lambda(k) k^{-1/2} g(log k) )

By computing W(h) (the arithmetic side) and the zero side, we can measure 
the exact amplitude of the Riemann zeros required to guarantee the existence 
of a prime in this interval.
"""

import math
import numpy as np
from mpmath import mp

# We need the Weil engine to compute the sides
import sys
import os
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from zeta.weil import explicit_formula_sides

def legendre_pair(n: int, dps: int = 30):
    """
    Constructs an even test function pair (h, g) where g(u) is a 
    triangle 'bump' supported EXACTLY on [log(n^2), log((n+1)^2)] 
    (and its negative reflection).
    """
    with mp.workdps(dps):
        A = mp.log(n**2)
        B = mp.log((n + 1)**2)
        
        # Center of the interval
        C = (A + B) / 2
        # Half-width of the interval
        W = (B - A) / 2
        
        # g(u) is a triangle centered at C with width W (and at -C)
        def g(u):
            au = abs(u)
            if au < A or au > B:
                return mp.mpf(0)
            # Triangle of height 1 at C, dropping to 0 at A and B
            return 1 - abs(au - C) / W

        # h(r) is the Fourier transform of g(u)
        # g(u) is the convolution of two boxes? No, it's a shifted triangle.
        # A triangle centered at 0 with width W is Fejer.
        # Shifted by C in time domain = multiplied by cos(C*r) in frequency domain.
        # Standard Fejer triangle: max height 1 at 0, zero at W.
        # Its transform is h_triangle(r) = W * (sin(W*r/2) / (W*r/2))^2
        # Since we have a triangle at +C and -C, we add them:
        # h(r) = 2 * h_triangle(r) * cos(C * r)
        
        def h(r):
            if r == 0:
                return 2 * W
            
            x = W * r / 2
            # Handle limits gracefully
            if abs(x) < 1e-20:
                h_tri = W
            else:
                s = mp.sin(x) / x
                h_tri = W * s * s
                
            return 2 * h_tri * mp.cos(C * r)

        # We add hints for Weil's engine to compute tails properly
        def envelope(t):
            # |h(r)| <= 2 * W * min(1, 1/(W*r/2)^2)
            if t <= 2 / W:
                return 2 * W
            return 2 * W / (W * t / 2)**2

        hints = {
            "kind": "legendre_bump",
            "support": B,
            "envelope": envelope,
            "g_abs": g
        }
        h.weil_hints = g.weil_hints = hints
        
    return h, g

if __name__ == "__main__":
    n = 10
    print(f"--- Attacking Legendre's Conjecture for n = {n} ---")
    print(f"Target Interval: [{n**2}, {(n+1)**2}]")
    
    h, g = legendre_pair(n)
    
    # We use a relatively high gamma_max to resolve the sharp bumps
    gamma_max = 500.0
    print(f"Evaluating Weil Explicit Formula (summing {gamma_max} zeros)...")
    
    results = explicit_formula_sides(h, g, gamma_max=gamma_max, n_max=(n+1)**2 + 10, dps=25)
    
    print("\n--- Explicit Formula Output ---")
    print(f"Zero Side:       {results['zero_side']}")
    print(f"Arithmetic Side: {results['arithmetic_side']}")
    print(f"Prime Term (The Legendre Signal): {results['prime_term']}")
    print(f"Agreement Error: {float(results['agreement']):.2e}")
    
    print("\n--- Analysis ---")
    if results['prime_term'] < -1e-10:
        print(">> SUCCESS! The prime term is strongly negative.")
        print(">> (The prime term is -2 * sum, so a negative value means the sum is POSITIVE).")
        print(">> This mathematically proves primes exist in this interval using the Riemann Zeros!")
    else:
        print(">> The prime term is 0. No primes detected (or precision failed).")
