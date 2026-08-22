import json
import argparse
from pathlib import Path

N = 8
D = 3

def all_keys():
    return tuple((u, v, a, b) for u in range(N) for v in range(u + 1, N) for a in range(D) for b in range(D))

KEYS = all_keys()
KEY_TO_IDX = {k: i for i, k in enumerate(KEYS)}

def apply_pi_sigma_to_coloring(coloring, pi, sigma):
    pi_inv = {pi[i]: i for i in range(N)}
    return [sigma[coloring[pi_inv[i]]] for i in range(N)]

def apply_pi_sigma_to_key(key_idx, pi, sigma):
    u, v, a, b = KEYS[key_idx]
    nu, nv = pi[u], pi[v]
    na, nb = sigma[a], sigma[b]
    if nu > nv:
        nu, nv = nv, nu
        na, nb = nb, na
    return KEY_TO_IDX[(nu, nv, na, nb)]

def apply_pi_sigma_to_monomial(monomial, pi, sigma):
    return sorted([apply_pi_sigma_to_key(idx, pi, sigma) for idx in monomial])

def expand_certificate(cert_path, pi, sigma, out_path):
    data = json.loads(cert_path.read_text())
    cert = data["certificate"]
    
    cert["trinomial_coloring"] = apply_pi_sigma_to_coloring(cert["trinomial_coloring"], pi, sigma)
    cert["trinomial_terms"] = [apply_pi_sigma_to_monomial(term, pi, sigma) for term in cert["trinomial_terms"]]
    
    # Update relations
    for rel in cert["relations"]:
        rel["binomial_coloring"] = apply_pi_sigma_to_coloring(rel["binomial_coloring"], pi, sigma)
        rel["left_monomial"] = apply_pi_sigma_to_monomial(rel["left_monomial"], pi, sigma)
        rel["right_monomial"] = apply_pi_sigma_to_monomial(rel["right_monomial"], pi, sigma)
        
    out_path.write_text(json.dumps(data, indent=2) + "\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("cert", type=Path)
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    
    # Orbit 18 non-trivial stabilizer element
    pi = (6, 7, 3, 2, 4, 5, 0, 1)
    sigma = (0, 2, 1)
    
    expand_certificate(args.cert, pi, sigma, args.out)
