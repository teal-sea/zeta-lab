"""Re-solve the cutting-plane LP of this hunt with a stronger separation oracle.

Why. epsstar.harvest() seeds 60,000 points on [0, 6]^6 plus 30,000 on [0.6, 3.2]^6 and
descends from the best 48 with maxiter 300. Run at the LP's own final (a, b) it returns
0.0079168578, and the leader's verifier (RESULTS.md section 7.7, round 3) reached cells with
lower values. Descending from those cells finds the basin at (1.0387, 1.9635, 1.0389, 1.0354,
1.9617, 1.0397) where F is 0.0078960, 2.1e-5 under what the LP claimed. Every minimum ever
seen on this family has all six gaps in [0.9, 2.3], so this oracle seeds 400,000 points there
on top of 100,000 on [0, 6]^6, descends from the best 300 plus the 200 lowest points of the
current pool, with maxiter 5000 and gtol 1e-14. Everything else is epsstar.eps_star unchanged.

What it did (2026-09-06, RESULTS.md section 7.7, RUNS.md section 13): 45 rounds, about 13 s
each, LP value down from 0.0079186025 to 0.0079111939 with 14,060 cuts; then HiGHS failed on
the next solve (status 15) and eps_star raised, so nothing below was saved. The LP value is
monotone and an upper bound on eps* at every round, because every cut is a real gap vector.

Float throughout. This estimates eps*; it proves nothing.

SUPERSEDED, 2026-09-06, later the same day. This oracle's seeding box is [0.9, 2.3]^6, chosen
because every minimum anyone had seen had all six gaps there. AMTOPA's branch-and-bound then
refused the window candidates at cells with one gap near 2.91, and descending from those cells
drops the functional 6.4e-5 below what this oracle reports. The box was the bias, exactly as it
was for harvest, and it was inherited the same way: by looking at where the previous oracle's
minima were. Use wide_floor.py's seeding. What survives from this file is its LP arm: the LP
VALUE is an upper bound on eps* whatever the oracle does, so RESULTS.md section 7.7's
"headroom at most 8.9e-8" still stands; the achieved floors it reports do not.

    python resolve_strong_oracle.py [rounds]        # from this directory
"""
import json, sys, time
import numpy as np
from scipy.optimize import minimize

import family as fam
import epsstar
from ceiling import W_matrix

Q = 6
OUT = 'artifacts/resolve_strong_oracle'
cand = json.load(open('artifacts/candidate_round3.amtopa'))
c = np.array(cand['window']['numerators'], float) / cand['window']['denominator']
w = fam.frequencies(len(c))
k0 = float(fam.kernel(0.0, c, w)[0])
den = cand['pair_weights']['denominator']
lookup = {(i, j): n / den for i, j, n in cand['pair_weights']['entries']}
a0 = np.array([lookup[p] for p in fam.PAIR_LIST])
b0 = np.array(cand['position_pressure']['numerators'], float) / cand['position_pressure']['denominator']
B = 93.0 / 23000.0

POOL_SEEDS = 200


def strong_harvest(a, b, c, w, k0, rng, coarse=60000, keep=48, hi=None):
    if hi is None:
        hi = min(0.02 / float(np.min(b[b > 0])) if np.any(b > 0) else 40.0, 40.0)
    S = np.vstack([
        rng.uniform(0.0, min(hi, 6.0), size=(100000, Q)),
        rng.uniform(0.9, 2.3, size=(400000, Q)),
        np.array(np.meshgrid(*[(1.0, 2.0, 3.0)] * Q)).reshape(Q, -1).T,
    ])
    vals = S @ b + W_matrix(S, c, w, k0) @ a
    order = np.argsort(vals)[:300]
    starts = [S[i] for i in order]
    pool = strong_harvest.pool
    if pool is not None and pool.shape[0]:
        pv = pool @ b + W_matrix(pool, c, w, k0) @ a
        starts += [pool[i] for i in np.argsort(pv)[:POOL_SEEDS]]
    bounds = [(0.0, hi)] * Q
    mins, seen = [], []
    best = (np.inf, None)
    for s in starts:
        res = minimize(lambda g: epsstar._fun_jac(g, a, b, c, w, k0), s, jac=True,
                       method='L-BFGS-B', bounds=bounds,
                       options={'maxiter': 5000, 'ftol': 1e-18, 'gtol': 1e-14})
        g, v = res.x, float(res.fun)
        if v < best[0]:
            best = (v, g.copy())
        if not any(np.max(np.abs(g - t)) < 1e-5 for t in seen):
            seen.append(g.copy())
            mins.append(g.copy())
    return best[0], best[1], mins


strong_harvest.pool = None
epsstar.harvest = strong_harvest

pool = np.load('artifacts/cut_pool.npy')
# The five local minima found on 2026-09-06 at the round-3 (a, b); the lowest is the basin
# the original oracle missed.
extra = np.array([
    [1.038654, 1.963484, 1.038887, 1.035361, 1.961736, 1.039690],
    [1.035744, 1.042579, 1.962899, 1.041119, 1.968439, 1.042788],
    [1.974325, 1.047202, 1.971694, 1.042848, 1.977756, 1.043091],
    [1.958123, 1.047403, 1.965899, 1.033679, 1.028196, 1.029171],
    [1.963799, 1.047150, 1.969948, 1.034764, 1.035392, 1.980460],
])
pool = np.vstack([pool, extra])
strong_harvest.pool = pool
print(f'pool {pool.shape[0]} cuts (committed pool + 5 minima at the round-3 weights)', flush=True)


class _Stamped:
    """eps_star prints every fifth round; stamp those lines with elapsed seconds."""
    def __init__(self):
        self.t = time.time()

    def __call__(self, *args, **kw):
        print(f'[{time.time() - self.t:6.0f}s]', *args, flush=True)


epsstar.print = _Stamped()

rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 80
r = epsstar.eps_star(B, c, w, k0, rounds=rounds, seed=4, tol=1e-10, verbose=True,
                     a_init=a0, b_init=b0, cut_pool=pool, patience=4)
np.save(OUT + '_cuts.npy', r['cuts'])
np.save(OUT + '_a.npy', r['a'])
np.save(OUT + '_b.npy', r['b'])
lead = 0.0079111052
print(f"FINAL  upper (LP value) {r['upper']:.10f}   lower (achieved floor) {r['lower']:.10f}   "
      f"cuts {r['cuts'].shape[0]}   leader float floor {lead:.10f}   "
      f"upper - leader {r['upper'] - lead:+.3e}   lower - leader {r['lower'] - lead:+.3e}"
      + (f"   INCONSISTENT {r['inconsistent']}" if 'inconsistent' in r else ''), flush=True)
json.dump({'upper': r['upper'], 'lower': r['lower'], 'a': r['a'].tolist(), 'b': r['b'].tolist(),
           'cuts': int(r['cuts'].shape[0])}, open(OUT + '.json', 'w'), indent=1)
