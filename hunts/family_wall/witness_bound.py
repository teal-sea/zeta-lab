"""Witness bound:  Phi_n <= H (1 + W(g))  for any g >= 0 with sum(g) <= (n-1)/H.
Also the sharper form  Phi_n <= H + max_p [ H c/(1+(k-2)c) - k/p ],  c = W + S/p.
"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
import sys, math, json, itertools, time
sys.path.insert(0, HERE)
from famlib import *
import numpy as np
from scipy.optimize import minimize

Z1, Z2 = 1.0572782910088552, 2.030067530128161


def tile(pattern, k, Stot):
    reps = int(np.ceil(k / len(pattern))) + 1
    g = np.array(list(pattern) * reps)[:k].astype(float)
    return g * (Stot / g.sum())


def min_W_constrained(k, Stot, seeds):
    cons = [{'type': 'eq', 'fun': lambda g: g.sum() - Stot, 'jac': lambda g: np.ones(k)}]
    bnds = [(0.0, 80.0)] * k
    vals = np.array([Wsum(s) for s in seeds])
    best = (np.inf, None)
    for i in np.argsort(vals)[:min(60, len(seeds))]:
        r = minimize(Wsum_grad, seeds[i], jac=True, method='SLSQP', bounds=bnds,
                     constraints=cons, options={'maxiter': 600, 'ftol': 1e-16})
        if r.fun < best[0] and abs(r.x.sum() - Stot) < 1e-7 and r.x.min() > -1e-9:
            best = (float(r.fun), r.x.copy())
    return best


def sharper_bound(k, W, S):
    """max over p of  H c/(1+(k-2)c) - k/p  with c = W + S/p."""
    ts = np.geomspace(1e-8, 0.05, 200000)          # t = 1/p
    c = W + S * ts
    val = H * c / (1.0 + max(k - 2, 0) * c) - k * ts
    i = int(np.argmax(val))
    return float(val[i]), float(1.0 / ts[i])


if __name__ == '__main__':
    # candidate periodic patterns of 1s and 2s, tiled
    pats = []
    for L in range(1, 9):
        for wd in itertools.product([Z1, Z2], repeat=L):
            pats.append(wd)
    print(" n    k    S=k/H      W_witness      H(1+W)        sharper bound   p*      < ceiling?")
    out = []
    prev = None
    for k in list(range(2, 41)) + list(range(42, 81, 2)):
        n = k + 1
        Stot = k / H
        seeds = [tile(p_, k, Stot) for p_ in pats]
        seeds += [np.full(k, Stot / k)]
        if prev is not None and len(prev) == k - 1:
            seeds.append(np.concatenate([prev, [prev[-1]]]) * 1.0)
        seeds = [s * (Stot / s.sum()) for s in seeds]
        Wv, g = min_W_constrained(k, Stot, seeds)
        prev = g
        b1 = H * (1 + Wv)
        b2v, pstar = sharper_bound(k, Wv, Stot)
        b2 = H + b2v
        triv = H * (k) / (k - 1) if k > 1 else float('inf')
        best = min(b1, b2, triv)
        out.append({'n': n, 'k': k, 'W': Wv, 'b_witness': b1, 'b_sharp': b2,
                    'b_trivial': triv, 'best': best, 'gaps': list(g)})
        print(f"{n:3d}  {k:3d}  {Stot:8.4f}  {Wv:.9f}  {b1:.10f}  {b2:.10f}  {pstar:9.1f}  "
              f"triv={triv:.6f}  best={best:.8f}  {'YES' if best < CEIL else 'no '}")
        sys.stdout.flush()
    json.dump(out, open(os.path.join(HERE, 'artifacts', 'witness.json'), 'w'))
    print()
    print("max over the table of the best bound:", max(r['best'] for r in out))
    print("ceiling:", CEIL)
