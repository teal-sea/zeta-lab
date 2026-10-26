import sympy
import time
import sys
import psutil
import os
import json
import signal
from pathlib import Path

sys.path.insert(0, str(Path("hunts/r_044dd2").resolve()))
from polynomial_sieve import build_system

def timeout_handler(signum, frame):
    raise TimeoutError("Groebner basis computation timed out")

def run_groebner():
    support_path = Path("hunts/r_044dd2/artifacts/orbit18-support-07.json")
    print("Building system...", flush=True)
    support, targets, all_relations, histogram = build_system(support_path)
    
    print(f"Support size: {len(support)}", flush=True)
    print(f"Targets: {len(targets)}", flush=True)
    print(f"Relations: {len(all_relations)}", flush=True)
    
    vars_list = sympy.symbols(f"x0:{len(support)}")
    
    polys = []
    
    def to_poly(terms):
        expr = 0
        for term in terms:
            monom = 1
            for var_idx in term:
                monom *= vars_list[var_idx]
            expr += monom
        return expr

    for coloring, terms in targets:
        polys.append(to_poly(terms))
        
    for rel in all_relations:
        polys.append(to_poly(rel.terms))
        
    print(f"Total polynomials: {len(polys)}", flush=True)
    print("Computing Groebner basis (grevlex)...", flush=True)
    
    pricing = {
        'solver': 'sympy.groebner',
        'ordering': 'grevlex',
        'variables': len(support),
        'equations': len(polys)
    }
    
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.alarm(5 * 60) # 5 minutes timeout
    
    t0 = time.time()
    try:
        basis = sympy.groebner(polys, vars_list, order='grevlex')
        t1 = time.time()
        signal.alarm(0)
        
        basis_str = str(list(basis))
        mem_mb = psutil.Process(os.getpid()).memory_info().rss / 1024 / 1024
        
        pricing['wall_clock_seconds'] = t1 - t0
        pricing['peak_memory_mb'] = mem_mb
        pricing['stopped_at'] = 'Completed'
        pricing['result'] = basis_str
        
        print("Completed!", flush=True)
        
    except TimeoutError:
        t1 = time.time()
        mem_mb = psutil.Process(os.getpid()).memory_info().rss / 1024 / 1024
        pricing['wall_clock_seconds'] = t1 - t0
        pricing['peak_memory_mb'] = mem_mb
        pricing['stopped_at'] = 'Timeout (5 minutes)'
        print("Timeout reached.", flush=True)
        
    except Exception as e:
        t1 = time.time()
        mem_mb = psutil.Process(os.getpid()).memory_info().rss / 1024 / 1024
        pricing['wall_clock_seconds'] = t1 - t0
        pricing['peak_memory_mb'] = mem_mb
        pricing['stopped_at'] = f"Failed: {type(e).__name__} - {str(e)}"
        print(f"Failed: {e}", flush=True)
        
    with open("hunts/r_abf47b/results.json", "w") as f:
        json.dump(pricing, f, indent=2)

if __name__ == "__main__":
    run_groebner()
