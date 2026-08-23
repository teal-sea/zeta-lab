"""Rigorous multi-witness envelope bound.

For ANY finite set of gap vectors g_j,  c*(p) <= min_j (W_j + S_j/p), hence
    Phi_n <= H + max_{p>0} min_j [ H c_j(p)/(1+(k-2)c_j(p)) - k/p ],   c_j(p)=W_j+S_j/p
which is rigorous whatever the witnesses are (better witnesses -> tighter bound).
Witness ladder: j long letters among k, balanced (Sturmian) arrangement, then
W minimised at fixed total length.
"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
import sys, math, json, time
sys.path.insert(0, HERE)
from famlib import *
import numpy as np
from scipy.optimize import minimize

Z1, Z2 = 1.0572782910088552, 2.030067530128161


def sturmian(k, j):
    """balanced word with j long letters among k."""
    return np.array([Z2 if (math.floor((i + 1) * j / k) - math.floor(i * j / k)) == 1 else Z1
                     for i in range(k)])


def minW_fixedS(g0, Stot, tries=3):
    k = len(g0)
    cons = [{'type': 'eq', 'fun': lambda g: g.sum() - Stot, 'jac': lambda g: np.ones(k)}]
    g0 = g0 * (Stot / g0.sum())
    best = (Wsum(g0), g0)
    x = g0
    for _ in range(tries):
        r = minimize(Wsum_grad, x, jac=True, method='SLSQP', bounds=[(0.0, 80.0)] * k,
                     constraints=cons, options={'maxiter': 500, 'ftol': 1e-16})
        if r.fun < best[0] and abs(r.x.sum() - Stot) < 1e-7 and r.x.min() > -1e-9:
            best = (float(r.fun), r.x.copy())
        x = r.x
    return best


def ladder(k):
    out = []
    for j in range(0, k + 1):
        wd = sturmian(k, j)
        Stot = float(wd.sum())
        Wv, g = minW_fixedS(wd, Stot)
        out.append((Wv, Stot))
        # also a stretched variant (scan mean gap a bit above the natural one)
        for f in (0.90, 0.94, 0.97, 1.03, 1.06, 1.10):
            S2_ = Stot * f
            Wv2, _ = minW_fixedS(wd, S2_)
            out.append((Wv2, S2_))
    return out


def envelope_bound(k, wits, kd=None):
    kd = (k - 2) if kd is None else kd
    ts = np.geomspace(1e-7, 0.02, 30000)
    W = np.array([x[0] for x in wits])[:, None]
    S = np.array([x[1] for x in wits])[:, None]
    c = W + S * ts[None, :]
    val = H * c / (1.0 + max(kd, 0) * c) - k * ts[None, :]
    low = val.min(axis=0)
    i = int(np.argmax(low))
    return float(low[i]), float(1.0 / ts[i])


if __name__ == '__main__':
    ks = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else list(range(2, 41))
    res = []
    for k in ks:
        t0 = time.time()
        wits = ladder(k)
        gv, pstar = envelope_bound(k, wits)
        triv = H * k / (k - 1)
        bound = min(H + gv, triv)
        res.append({'n': k + 1, 'k': k, 'gain_bound': gv, 'bound': bound,
                    'p_star': pstar, 'trivial': triv,
                    'wits': [[float(a), float(b)] for a, b in wits]})
        print(f"n={k+1:3d} k={k:3d}  gain<= {gv:.6e}  Phi<= {bound:.10f}  p*={pstar:9.1f}  "
              f"triv={triv:.8f}  ceil-bound={CEIL-bound:+.6f}  [{time.time()-t0:.0f}s]")
        sys.stdout.flush()
    json.dump(res, open(os.path.join(HERE, 'artifacts', f'envelope_{ks[0]}_{ks[-1]}.json'), 'w'))
