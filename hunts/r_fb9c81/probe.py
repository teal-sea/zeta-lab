import sys
import os
import json
import numpy as np

def run_probe():
    # We will simulate the exact off-diagonal bound vs diagonal bound for
    # x = 1000, U = x**(0.75 / 0.51)
    x = 1000.0
    alpha = 0.51
    delta = 0.75
    H = x ** (1/0.51)
    U = H ** delta
    W = int(H ** 1.05) # gamma = 1.05
    
    # We use a mock |a_2(n)|^2 = log n
    n = np.arange(1, min(W + 1, 10000000), dtype=float)
    a2_sq = np.log(np.maximum(n, 2.0))
    
    # Lower range
    n_lower = n[n <= x]
    c2_lower = (x**-2) * a2_sq[n <= x] * n_lower
    
    # Upper range
    n_upper = n[n > x]
    c2_upper = (x**2) * a2_sq[n > x] * n_upper**-3.0
    
    c2 = np.concatenate([c2_lower, c2_upper])
    
    diag = U * np.sum(c2)
    off_diag_bound = np.sum(n * c2)
    
    results = {
        "x": x,
        "H": H,
        "U": U,
        "W": W,
        "diagonal": diag,
        "off_diagonal_bound": off_diag_bound,
        "ratio_off_to_diag": off_diag_bound / diag,
        "x_log_x": x * np.log(x)
    }
    
    with open("hunts/r_fb9c81/results.json", "w") as f:
        json.dump(results, f, indent=2)
        
    print(json.dumps(results, indent=2))

if __name__ == "__main__":
    run_probe()
