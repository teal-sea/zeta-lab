import json
import os
import numpy as np
from mpmath import mp
from detector import generalized_residue_scan
from family import f_kappa_coefficients, find_online_zeros_kappa
from zeta.factorization import log_derivative_coefficients, factorization_defect

def dh_archimedean_bracket(r):
    return mp.re(mp.digamma(mp.mpf(3) / 4 + mp.mpc(0, 1) * r / 2)) + mp.log(5 / mp.pi)

def main():
    # Including DH kappa ≈ 0.284079
    kappa_values = [0.0, 0.1, 0.2, 0.284079, 0.4, 0.5, 0.6, 0.8, 1.0]
    results = []
    
    t_max = 110.0
    c_values = np.linspace(20.0, 95.0, 76)  # c from 20 to 95, step 1
    
    print(f"Running experiment for {len(kappa_values)} kappa values.")
    
    for k in kappa_values:
        print(f"\n--- kappa = {k:.6f} ---")
        a = f_kappa_coefficients(k, 2000)
        
        # Calculate factorization defect
        df = factorization_defect(a, 2000)
        print(f"Factorization Defect D(F) = {df:.4f}")
        
        # Log derivative coefficients for the Weil functional
        b = log_derivative_coefficients(a, 2000)
        
        # Find online zeros
        print(f"Finding on-line zeros up to t={t_max}...")
        zeros = find_online_zeros_kappa(k, t_max=t_max, dps=15, step=0.1)
        print(f"Found {len(zeros)} on-line zeros.")
        
        # Run position detector
        print("Running Weil position residue scan...")
        scan_res = generalized_residue_scan(
            c_values=c_values,
            b=b,
            archimedean_bracket_fn=dh_archimedean_bracket,
            online_zeros=zeros,
            has_pole=False,
            a=0.25,
            n_max=2000
        )
        max_res = scan_res["max_abs_residue"]
        argmax_c = scan_res["argmax_c"]
        print(f"Max absolute position residue = {max_res:.4e} at c = {argmax_c:.1f}")
        
        results.append({
            "kappa": float(k),
            "factorization_defect": float(df),
            "max_position_residue": float(max_res),
            "argmax_c": float(argmax_c),
            "online_zero_count": len(zeros)
        })
        
    out_path = os.path.join(os.path.dirname(__file__), "results.json")
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved results to {out_path}")

if __name__ == "__main__":
    main()
