"""Floor of the functional with a WIDE seeding box, after the verifier found a basin outside
the narrow one.

Every float floor in hunt #90, including the ones measured on 2026-09-06 with the "strong"
oracle, seeded gap vectors in [0.9, 2.3]^6 because every minimum anyone had seen had all six
gaps there. AMTOPA's branch-and-bound then refused the window candidates at cells with a gap
near 2.91, and descending from those cells drops the functional 6e-5 below the claimed floor.
The narrow box was the bias, one level out from the one that killed harvest.

This seeds uniformly on [0.9, 4.2]^6 as well, and on a mixture that draws each gap
independently from the observed clusters, which is far denser in the corners of the product
than a uniform sample of the same size.

    python wide_floor.py <label> <window_search.json> [ab.json] [seeds] [descents]
"""
import json, sys, time
import numpy as np
from scipy.optimize import minimize
import family as fam
from ceiling import W_matrix, family_bound
from epsstar import _fun_jac

Q = 6
AM = 0.6734164909714992949
label = sys.argv[1]
src = json.load(open(sys.argv[2]))
ab = json.load(open(sys.argv[3])) if len(sys.argv) > 3 and sys.argv[3] != '-' else src
SEEDS = int(sys.argv[4]) if len(sys.argv) > 4 else 600_000
DESC = int(sys.argv[5]) if len(sys.argv) > 5 else 500
c = np.array(src['c'], float)
B = float(src['B'])
a = np.array(ab['a'], float)
b = np.array(ab['b'], float)
w = fam.frequencies(len(c))
k0 = float(fam.kernel(0.0, c, w)[0])
u, _, _, M = fam.window_matrices(w)
H = fam.H_of(c, u, M)
hi = min(0.02 / float(np.min(b[b > 0])), 40.0)
bounds = [(0.0, hi)] * Q
rng = np.random.default_rng(2026)

# clusters seen in the minima and in the cells the verifier refused
CLUSTERS = np.array([1.035, 1.045, 1.955, 1.975, 2.905, 2.925, 3.86, 3.90])
pick = rng.integers(0, len(CLUSTERS), size=(SEEDS, Q))
jitter = rng.uniform(-0.06, 0.06, size=(SEEDS, Q))
S = np.vstack([
    CLUSTERS[pick] + jitter,
    rng.uniform(0.9, 4.2, size=(SEEDS, Q)),
    rng.uniform(0.9, 2.3, size=(SEEDS // 2, Q)),
    rng.uniform(0.0, min(hi, 6.0), size=(SEEDS // 4, Q)),
])
S = np.clip(S, 0.0, hi)
t0 = time.time()
vals = S @ b + W_matrix(S, c, w, k0) @ a
best = (np.inf, None)
for idx in np.argsort(vals)[:DESC]:
    r = minimize(lambda g: _fun_jac(g, a, b, c, w, k0), S[idx], jac=True, method='L-BFGS-B',
                 bounds=bounds, options={'maxiter': 5000, 'ftol': 1e-18, 'gtol': 1e-14})
    if r.fun < best[0]:
        best = (float(r.fun), r.x.copy())
floor = best[0]
claimed = float(ab.get('eps_floor', src.get('eps', float('nan'))))
lo, hii = 1e-6, 0.02
for _ in range(200):
    mid = (lo + hii) / 2
    if family_bound(H, mid, B)[0] < AM:
        lo = mid
    else:
        hii = mid
crit = (lo + hii) / 2
v, m = family_bound(H, floor, B)
print(f'{label}: wide floor {floor:.10f}  at {" ".join("%.5f" % x for x in best[1])}  [{time.time()-t0:.0f}s]')
print(f'  narrow-box floor was {claimed:.10f}; over-reported by {claimed - floor:+.3e}')
print(f'  needs {crit:.10f} to hold the record: {"ALIVE" if floor > crit else "DEAD"} by {floor - crit:+.3e}')
print(f'  assembled {v:.16f}  ({v - AM:+.3e} vs the record)  m={m}')
json.dump({'label': label, 'wide_floor': floor, 'argmin': best[1].tolist(), 'narrow': claimed,
           'crit': crit, 'bound': v, 'delta': v - AM, 'alive': bool(floor > crit)},
          open(f'wide_{label}.json', 'w'), indent=1)
