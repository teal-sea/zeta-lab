"""The cutting-plane LP with the WIDE oracle, at AMTOPA's own window and total pressure.

Every previous run of this LP, theirs and ours, seeded its separation oracle in gap boxes that
excluded the region the verifier later pointed at: a vector with one gap near 2.91 and the rest
near 1.04 and 1.97. With that region in the seeding, the question the whole hunt asks becomes
answerable: is AMTOPA's point the maximiser of min_g F over their polytope?

The LP value is an upper bound on eps* whatever the oracle does. The achieved floor is a lower
bound at the (a, b) it reports. If the LP converges to AMTOPA's own floor 0.0079111052, their
configuration is optimal and the pair-weight and pressure axes are closed for good.

    python lp_wide.py [rounds]

Result, 2026-09-06 (RESULTS.md section 7.8): 40 rounds, 13,387 cuts, LP value 0.007912132524
and achieved floor 0.007909735797 against AMTOPA's own 0.0079111052. Their point is better
than anything the LP found, and the bracket on eps* closes at 8.9e-08.
"""
import json, sys, time
import numpy as np
from scipy.optimize import minimize, linprog as _linprog
import family as fam
import epsstar
from ceiling import W_matrix, family_bound
from exact_assembly import bound_at
from fractions import Fraction as F

Q = 6
AM = 0.6734164909714992949
OUT = 'lp_wide'
c = fam.amtopa_coeffs()
w = fam.frequencies(len(c))
k0 = float(fam.kernel(0.0, c, w)[0])
B = 93.0 / 23000.0
CLUSTERS = np.array([1.035, 1.045, 1.955, 1.975, 2.905, 2.925, 3.86, 3.90])
N = 250_000


def wide_harvest(a, b, c, w, k0, rng, coarse=60000, keep=48, hi=None):
    if hi is None:
        hi = min(0.02 / float(np.min(b[b > 0])) if np.any(b > 0) else 40.0, 40.0)
    pick = rng.integers(0, len(CLUSTERS), size=(N, Q))
    S = np.vstack([
        CLUSTERS[pick] + rng.uniform(-0.06, 0.06, size=(N, Q)),
        rng.uniform(0.9, 4.2, size=(N, Q)),
        rng.uniform(0.9, 2.3, size=(N // 2, Q)),
        rng.uniform(0.0, min(hi, 6.0), size=(N // 2, Q)),
        np.array(np.meshgrid(*[(1.0, 2.0, 3.0)] * Q)).reshape(Q, -1).T,
    ])
    S = np.clip(S, 0.0, hi)
    vals = S @ b + W_matrix(S, c, w, k0) @ a
    starts = [S[i] for i in np.argsort(vals)[:300]]
    pool = wide_harvest.pool
    if pool is not None and len(pool):
        pv = pool @ b + W_matrix(pool, c, w, k0) @ a
        starts += [pool[i] for i in np.argsort(pv)[:200]]
    bounds = [(0.0, hi)] * Q
    mins, seen = [], []
    best = (np.inf, None)
    for s in starts:
        r = minimize(lambda g: epsstar._fun_jac(g, a, b, c, w, k0), s, jac=True,
                     method='L-BFGS-B', bounds=bounds,
                     options={'maxiter': 5000, 'ftol': 1e-18, 'gtol': 1e-14})
        g, v = r.x, float(r.fun)
        if v < best[0]:
            best = (v, g.copy())
        if not any(np.max(np.abs(g - t)) < 1e-5 for t in seen):
            seen.append(g.copy())
            mins.append(g.copy())
    wide_harvest.pool = np.vstack([pool, np.array(mins)]) if pool is not None and mins else (np.array(mins) if mins else pool)
    return best[0], best[1], mins


wide_harvest.pool = None
epsstar.harvest = wide_harvest


def lp_fallback(*args, **kw):
    for m in ('highs', 'highs-ipm', 'highs-ds'):
        kw['method'] = m
        r = _linprog(*args, **kw)
        if r.success:
            return r
        print(f'    linprog {m}: {r.message}', flush=True)
    return r


epsstar.linprog = lp_fallback


class _S:
    def __init__(self):
        self.t = time.time()

    def __call__(self, *a, **k):
        print(f'[{time.time() - self.t:6.0f}s]', *a, flush=True)


epsstar.print = _S()

rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 40
print(f'LP at AMTOPA window, B = 93/23000, wide oracle, {rounds} rounds', flush=True)
r = epsstar.eps_star(B, c, w, k0, rounds=rounds, seed=5, tol=1e-10, verbose=True, patience=4)
lo, up = r['lower'], r['upper']
THEIRS = 0.0079111052
print(f"FINAL wide LP: achieved floor {lo:.12f}   LP upper {up:.12f}   cuts {r['cuts'].shape[0]}", flush=True)
print(f"  AMTOPA's own floor {THEIRS:.12f}", flush=True)
print(f"  achieved - theirs {lo - THEIRS:+.3e}     LP upper - theirs {up - THEIRS:+.3e}", flush=True)
H = F(336094079, 500000000)
for name, e in (('achieved', lo), ('LP upper', up)):
    tgt = F(int(e * 2500000), 2500000)
    best = None
    for m in range(7, 4001):
        try:
            v = bound_at(m, H, tgt, F(93, 23000), 6, 60)
        except AssertionError:
            continue
        if best is None or v > best[0]:
            best = (v, m)
    print(f'  bound at the {name} {float(best[0]):.16f}  ({float(best[0]) - AM:+.3e} vs the record)  m={best[1]}', flush=True)
np.save(OUT + '_cuts.npy', r['cuts'])
json.dump({'lower': lo, 'upper': up, 'a': r['a'].tolist(), 'b': r['b'].tolist(),
           'cuts': int(r['cuts'].shape[0]), 'theirs': THEIRS}, open(OUT + '.json', 'w'), indent=1)
