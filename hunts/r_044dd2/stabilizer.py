import json
import itertools
from pathlib import Path

def apply_perm_to_matching(pi, matching):
    return tuple(sorted(tuple(sorted((pi[u], pi[v]))) for u, v in matching))

def get_stabilizer(orbit_id):
    results_path = Path("/Users/thomas/Zeta/hunts/r_322dae/results.json")
    payload = json.loads(results_path.read_text())
    orbit = next(o for o in payload["census_8x3"]["orbits"] if o["orbit_id"] == orbit_id)
    triple = tuple(tuple(tuple(edge) for edge in m) for m in orbit["canonical_triple_matchings"])
    
    stabilizer = []
    for pi in itertools.permutations(range(8)):
        for sigma in itertools.permutations(range(3)):
            sigma_inv = {sigma[i]: i for i in range(3)}
            
            # check if (pi, sigma) stabilizes the triple
            match = True
            for c in range(3):
                mapped_M = apply_perm_to_matching(pi, triple[sigma_inv[c]])
                if mapped_M != triple[c]:
                    match = False
                    break
            if match:
                stabilizer.append((pi, sigma))
    return stabilizer

if __name__ == "__main__":
    stab = get_stabilizer(18)
    print("Stabilizer size:", len(stab))
    for idx, (pi, sigma) in enumerate(stab):
        print(f"Element {idx}: pi={pi}, sigma={sigma}")
