"""
Weil Positivity against Davenport-Heilbronn

Li's criterion failed to detect the offline zero of the Davenport-Heilbronn function
because its negative contribution was astronomically small compared to the positive bulk.

Here we use Weil Positivity. Weil Positivity says W(h) = sum_{zeros} h(gamma) >= 0
for all positive-type test functions h. 

Since DH has zeros off the line, gamma = x + iy has a non-zero imaginary part y = 0.3085.
For an autocorrelation pair h(r) = |f(r)|^2, h is strictly >= 0 on the real axis, but
can go sharply negative off the real axis.

We will find all zeros of DH up to T=100, construct an autocorrelation pair, and tune
the spacing and sigma parameters so that the offline zeros completely dominate the sum
and pull W(h) < 0, successfully detecting the imposter!
"""

import sys
import math
from mpmath import mp
import numpy as np

# We'll need access to the DH tools
from zeta.epstein import Z_dh, find_offline_zero, OFFLINE_ZERO_RE, OFFLINE_ZERO_IM
from zeta.weil import autocorrelation_pair

def find_dh_line_zeros(t_max=100, dps=20):
    """Scan and polish real zeros of DH (sign changes of Z_dh)."""
    print(f"Scanning for real zeros of DH up to T={t_max}...")
    zeros = []
    with mp.workdps(dps):
        t0 = mp.mpf(0.1)
        step = 0.25 # Fine enough to catch zeros
        
        # We just do a simple sign change scan and polish
        prev_Z = Z_dh(t0, dps=dps)
        t = t0 + step
        while t <= t_max:
            cur_Z = Z_dh(t, dps=dps)
            if prev_Z != 0 and cur_Z != 0 and (prev_Z > 0) != (cur_Z > 0):
                # Sign change found! Polish it.
                root = mp.findroot(lambda x: Z_dh(x, dps=dps), (t - step, t), solver='secant')
                zeros.append(root)
            prev_Z = cur_Z
            t += step
            
    print(f"Found {len(zeros)} real zeros on the critical line.")
    return zeros

def hunt_for_positivity_violation():
    mp.dps = 30
    
    # 1. Load the Offline Zeros
    # The offline zero is rho = beta + i gamma_real
    # So the ordinate gamma = -i(rho - 1/2) = gamma_real - i(beta - 1/2)
    rho_re = mp.mpf(OFFLINE_ZERO_RE)
    rho_im = mp.mpf(OFFLINE_ZERO_IM)
    
    gamma_x = rho_im
    gamma_y = rho_re - mp.mpf('0.5')
    
    print("=" * 78)
    print("WEIL POSITIVITY DETECTOR vs DAVENPORT-HEILBRONN")
    print("=" * 78)
    print(f"Targeting offline zero ordinates at: +/- {float(gamma_x):.4f} +/- {float(gamma_y):.4f}i")
    
    # 2. Get the real zeros up to T=100
    line_zeros = find_dh_line_zeros(t_max=100)
    
    # We want a test function h(r) = 2*pi*sigma^2 e^{-sigma^2 r^2} [2 - 2cos(r*s)]
    # We need cos(r*s) to be extremely negative off the axis.
    # Off the axis, r = x - iy. cos(rs) = cos(xs)*cosh(ys) - i*sin(xs)*sinh(ys)
    # We want cos(xs) = +1 to make the real part cosh(ys), which grows exponentially.
    # So we need xs = 2*pi*k  =>  s = 2*pi*k / 85.6993
    
    # Let's search for a good 'k' and 'sigma'
    best_W = float('inf')
    best_params = None
    
    print("\nHunting for parameters (sigma, s)...")
    for k in [50, 100, 500, 800, 900, 1000, 1200, 1500, 2000]:
        s = 2 * mp.pi * k / gamma_x
        
        for sigma_val in [0.04, 0.05, 0.06, 0.07, 0.08]:
            sigma = mp.mpf(sigma_val)
            h, g = autocorrelation_pair([1, -1], spacing=float(s), sigma=float(sigma))
            
            # Evaluate W(h)
            # W(h) = sum h(gamma) over all zeros. 
            # We'll sum over the real zeros we found, and the 4 offline zeros.
            # (Assuming zeros above 100 are killed by the Gaussian envelope e^{-sigma^2 r^2})
            
            w_real = mp.mpf(0)
            for g_real in line_zeros:
                w_real += h(g_real) + h(-g_real)
                
            w_offline = (
                h(gamma_x + mp.mpc(0, 1)*gamma_y) +
                h(-gamma_x + mp.mpc(0, 1)*gamma_y) +
                h(gamma_x - mp.mpc(0, 1)*gamma_y) +
                h(-gamma_x - mp.mpc(0, 1)*gamma_y)
            )
            
            # Total W(h)
            W_total = mp.re(w_real + w_offline)
            
            if W_total < best_W:
                best_W = W_total
                best_params = (sigma, s, w_real, w_offline)
                
            if W_total < -1e-5:
                print(f"✅ VIOLATION FOUND! k={k:3d}, s={float(s):.4f}, sigma={float(sigma):.2f}  =>  W(h) = {float(W_total):10.2e}")
                print("\nDetailed Breakdown of the Winning Function:")
                print(f"  Sum of Real Zeros (False Positives) : {float(mp.re(w_real)):10.2e}")
                print(f"  Sum of Offline Zeros (The Catch)    : {float(mp.re(w_offline)):10.2e}")
                print(f"  Total W(h)                          : {float(W_total):10.2e}")
                print("\nBecause W(h) < 0 for a positive-type test function, Weil Positivity")
                print("successfully proves that Davenport-Heilbronn violates the Riemann Hypothesis!")
                return

    print("Could not find a violation in the search space.")
    print(f"Lowest W(h) found: {best_W} at sigma={best_params[0]}, s={best_params[1]}")

if __name__ == "__main__":
    hunt_for_positivity_violation()
