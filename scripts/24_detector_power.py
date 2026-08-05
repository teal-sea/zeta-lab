#!/usr/bin/env python
import argparse
import mpmath
from mpmath import mp
import sys
import os

from zeta.epstein import OFFLINE_ZERO_RE, OFFLINE_ZERO_IM
from zeta.detectors import lesion_li_lambda, lesion_weil_gaussian, lesion_weil_fejer
from zeta.li import li_asymptotic

def test_li_dh_zero():
    """
    Test Li's criterion against the known Davenport-Heilbronn off-line zero.
    The DH zero is rho = 0.8085 + 85.6993i.
    We want to find at what n this lesion causes a negative shift larger than the 
    RH-predicted background (asymptotic lambda_n).
    """
    print("--- LI'S CRITERION vs DAVENPORT-HEILBRONN ZERO ---")
    delta = float(OFFLINE_ZERO_RE) - 0.5
    T = float(OFFLINE_ZERO_IM)
    print(f"DH Zero Lesion: delta = {delta:.4f}, T = {T:.4f}")
    
    # Scan n geometrically
    n = 10
    while n <= 1000000:
        shift = float(lesion_li_lambda(n, delta, T, dps=30))
        bg = li_asymptotic(n)
        ratio = shift / bg
        print(f"n = {n:<7} | Lesion Shift = {shift:>12.4e} | Background = {bg:>12.4e} | Ratio = {ratio:>9.4f}")
        if shift + bg < 0:
            print(f">>> DETECTED! Li's criterion goes negative at n ~ {n}")
            break
        n = int(n * 1.5)
    print()

def test_weil_dh_zero():
    """
    Test Weil Positivity against the DH zero using Gaussian test functions.
    """
    print("--- WEIL POSITIVITY vs DAVENPORT-HEILBRONN ZERO ---")
    delta = float(OFFLINE_ZERO_RE) - 0.5
    T = float(OFFLINE_ZERO_IM)
    print(f"DH Zero Lesion: delta = {delta:.4f}, T = {T:.4f}")
    
    # Gaussian parameter 'a' controls the width. A wide gaussian (small a) sees the lesion.
    # But Weil background W(a) collapses as a -> 0.20
    for a in [0.01, 0.05, 0.10, 0.15, 0.20]:
        shift = float(lesion_weil_gaussian(a, delta, T, dps=30))
        # Approximating background as 2*exp(-a * 14.1347^2)
        bg = 2 * math.exp(-a * (14.134725**2))
        print(f"a = {a:<4} | Lesion Shift = {shift:>12.4e} | Background (est) = {bg:>12.4e}")
    print("Note: Gaussian family is strictly positive so it cannot go negative. It cannot detect the lesion directly via sign change.\n")

def test_synthetic_lesion_grid():
    """
    Find the minimum n required for Li's criterion to detect a synthetic lesion
    of delta = 0.1 at various heights T.
    """
    print("--- LI'S CRITERION MINIMAL DETECTABLE n FOR delta=0.1 LESION ---")
    delta = 0.1
    for T in [14.13, 30.0, 50.0, 100.0]:
        n = 10
        detected = False
        while n <= 5000000:
            shift = float(lesion_li_lambda(n, delta, T, dps=30))
            bg = li_asymptotic(n)
            if shift + bg < 0:
                print(f"Height T = {T:<6} | delta = {delta} | Detected at n ~ {n}")
                detected = True
                break
            n = int(n * 1.5)
        if not detected:
            print(f"Height T = {T:<6} | delta = {delta} | NOT DETECTED up to n=5000000")

def test_fejer_b_scan():
    """
    Scan the band-limit parameter 'b' for the Fejer detector to measure what 
    fraction of phases actually trigger a detection (negative W) for the DH lesion.
    """
    print("\n--- FEJER DETECTOR b-SCAN vs DAVENPORT-HEILBRONN ZERO ---")
    from zeta.weil import fejer_pair, _zero_side
    delta = float(OFFLINE_ZERO_RE) - 0.5
    T = float(OFFLINE_ZERO_IM)
    print(f"DH Zero Lesion: delta = {delta:.4f}, T = {T:.4f}")
    
    b_values = [b/2.0 for b in range(2, 161)] # b from 1.0 to 80.0
    detected_count = 0
    for b in b_values:
        shift = float(lesion_weil_fejer(b, delta, T, dps=30))
        # Compute background using the ZERO SIDE to bypass prime truncation
        h, _ = fejer_pair(b)
        bg_sum, _, _ = _zero_side(h, gamma_max=500.0, dps=30)
        bg = float(bg_sum)
        
        if shift + bg < 0:
            detected_count += 1
            if detected_count <= 3:
                print(f"b = {b:<4.1f} | Lesion Shift = {shift:>12.4e} | Background = {bg:>12.4e} | DETECTS")
        elif b in [10.0, 20.0, 40.0, 80.0]:
            print(f"b = {b:<4.1f} | Lesion Shift = {shift:>12.4e} | Background = {bg:>12.4e} | Misses (wrong phase)")
            
    fraction = detected_count / len(b_values)
    print(f"\nFejer b-scan complete. Detected the lesion at {detected_count}/{len(b_values)} phases ({fraction:.1%}).")
    print("Conclusion: Band-limited tests are exponentially sensitive, but phase luck is required.")


import math

def main():
    test_li_dh_zero()
    test_weil_dh_zero()
    test_synthetic_lesion_grid()
    test_fejer_b_scan()

if __name__ == "__main__":
    main()
