import json
import os
import numpy as np
from mpmath import mp
from scipy.optimize import brentq
from multiprocessing import Pool, cpu_count
from functools import partial

import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(__file__))))

from zeta.epstein import (
    epstein_reduced_forms, epstein_representation_count,
    Z_epstein
)
from zeta.factorization import factorization_defect, log_derivative_coefficients
from hunts.factorization_vs_position.detector import generalized_residue_scan
from zeta.detector import arithmetic_side, DEFAULT_WIDTH

def get_epstein_archimedean_bracket_fn(D):
    def bracket(r):
        A = mp.sqrt(abs(D)) / (2 * mp.pi)
        s = mp.mpc(mp.mpf(1)/2, r)
        return 2 * (mp.log(A) + mp.re(mp.digamma(s)))
    return bracket

def eval_Z(t, form, dps):
    try:
        return float(Z_epstein(t, form, dps))
    except ValueError:
        return float(Z_epstein(t, form, dps+5))

def find_online_zeros_epstein(form, t_max: float = 25.0, dps: int = 15, step: float = 0.05):
    zeros = []
    t_vals = np.arange(0.0, t_max + step, step)
    
    print(f"      Evaluating {len(t_vals)} points on the grid...")
    eval_fn = partial(eval_Z, form=form, dps=dps)
    
    with Pool(cpu_count()) as p:
        Z_vals = p.map(eval_fn, t_vals)
        
    Z_vals = np.array(Z_vals)
    
    for i in range(len(t_vals) - 1):
        if Z_vals[i] * Z_vals[i+1] < 0:
            def z_func(t_arg):
                return eval_fn(t_arg)
            root = brentq(z_func, t_vals[i], t_vals[i+1])
            zeros.append(float(root))
        elif Z_vals[i] == 0:
            zeros.append(float(t_vals[i]))
            
    return zeros

def main():
    # Only test a few discriminants to save time, plus we'll add zeta as a control manually
    discriminants = [-15, -20, -23, -24, -31]
    
    results = []
    t_max = 25.0
    c_values = np.linspace(10.0, 20.0, 11)
    
    print("Running Experiment 2 on Epstein Zeta forms (Multiprocessing)")
    
    # 0. Zeta control
    print("\n--- Zeta (Control) ---")
    # Zeros of zeta up to 25
    zeta_zeros = [14.134725141734694, 21.022039638771555, 25.010857580145689]
    zeta_zeros = [z for z in zeta_zeros if z <= t_max]
    
    def zeta_arch_bracket(r):
        return mp.re(mp.digamma(mp.mpf(1)/4 + mp.mpc(0, 1)*r/2)) - mp.log(mp.pi)

    # For zeta, b_n = Lambda(n) / sqrt(n) handled in detector? 
    # Let's just generate b_n for zeta using factorization defect logic
    zeta_a = [0.0] + [1.0]*2000
    zeta_df = factorization_defect(zeta_a, 2000)
    zeta_b = log_derivative_coefficients(zeta_a, 2000)
    
    scan_res_zeta = generalized_residue_scan(
        c_values=c_values,
        b=zeta_b,
        archimedean_bracket_fn=zeta_arch_bracket,
        online_zeros=zeta_zeros,
        has_pole=True,
        a=0.25,
        n_max=2000
    )
    results.append({
        "discriminant": 0,
        "form": "zeta",
        "factorization_defect": float(zeta_df),
        "max_position_residue": float(scan_res_zeta["max_abs_residue"]),
        "argmax_c": float(scan_res_zeta["argmax_c"]),
        "online_zero_count": len(zeta_zeros)
    })
    print(f"Max absolute position residue = {scan_res_zeta['max_abs_residue']:.4e} at c = {scan_res_zeta['argmax_c']:.1f}")

    for D in discriminants:
        forms = epstein_reduced_forms(D)
        for form in forms:
            if form[0] != 1:
                print(f"\n--- Skipping non-principal form D={D}, Form={form} ---")
                continue
                
            print(f"\n--- D={D}, Form={form} ---")
            
            a = [0.0]
            for n in range(1, 2001):
                a.append(float(epstein_representation_count(n, form)))
                
            df = factorization_defect(a, 2000)
            print(f"Factorization Defect D(F) = {df:.6f}")
            
            b = log_derivative_coefficients(a, 2000)
            
            print(f"Finding on-line zeros up to t={t_max}...")
            zeros = find_online_zeros_epstein(form, t_max=t_max, dps=15, step=0.05)
            print(f"Found {len(zeros)} on-line zeros.")
            
            print("Running Weil position residue scan...")
            arch_bracket = get_epstein_archimedean_bracket_fn(D)
            
            scan_res = generalized_residue_scan(
                c_values=c_values,
                b=b,
                archimedean_bracket_fn=arch_bracket,
                online_zeros=zeros,
                has_pole=True, 
                a=0.25,
                n_max=2000
            )
            
            max_res = scan_res["max_abs_residue"]
            argmax_c = scan_res["argmax_c"]
            print(f"Max absolute position residue = {max_res:.4e} at c = {argmax_c:.1f}")
            
            results.append({
                "discriminant": int(D),
                "form": list(form),
                "factorization_defect": float(df),
                "max_position_residue": float(max_res),
                "argmax_c": float(argmax_c),
                "online_zero_count": len(zeros)
            })
            
    out_path = os.path.join(os.path.dirname(__file__), "results2.json")
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved results to {out_path}")

if __name__ == "__main__":
    main()
