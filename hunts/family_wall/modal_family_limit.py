"""Modal check of the predicted n-point floors at larger n over a wide pressure range.

Predicted floor (this hunt):  c_pred(p) = min_j [ W_j + S_j / p ]  over the witness
ladder of balanced 1-2 words (j long letters among k = n-1, length-minimised at fixed
total length).  This job re-derives the floor INDEPENDENTLY, by multistart global
minimisation of

  F_{n-1}(g) = (1/p) sum g_i + sum_{s=1}^{n-1} (2/(n-s)) sum_{i=1}^{n-s} w(g_i+..+g_{i+s-1}),
  w(x) = k(x)^2,  k = K(x)/K(0),  K(x) = int_{-1/2}^{1/2} cos(sqrt2 t) cos(2 pi x t) dt,

and reports, per (n, p), the attained floor and Phi_n. Float only: each best F is the
value of F at a point, hence an UPPER bound on inf F, and the Phi built from it is an
OPTIMISTIC estimate of the bound the family can support at that pressure.

Control that must hold: n = 7, p = 3000 best F within 1e-9 of the published Arb value
0.0038262312115073.

Run:  ~/Zeta/.venv/bin/modal run hunts/family_wall/modal_family_limit.py
"""
from __future__ import annotations

import json
import math
import os
import time

import modal

image = modal.Image.debian_slim(python_version="3.12").pip_install("numpy==2.1.3", "scipy==1.14.1")
app = modal.App("zeta-hunt82-family-limit", image=image)

N_POINTS = (7, 10, 14, 20)
PRESSURES = (1200, 1800, 2600, 3000, 3400, 4400, 6000, 8500, 13000, 20000)
CONTAINERS = 8
RESTARTS = 200

CONTROL_F = 0.0038262312115073
CONTROL_N, CONTROL_P = 7, 3000

H_CONST = 0.6725007036794116
ZEROS = (1.0572782910088552, 2.030067530128161, 3.0202429921714815, 4.015235607036755)


def _kernel_src():
    return r"""
import math
import numpy as np
from scipy.optimize import minimize

S2 = math.sqrt(2.0)
INV = 1.0 / S2
K0 = S2 * math.sin(INV)

def Kraw(x):
    x = np.asarray(x, dtype=float)
    u = math.pi * x - INV
    v = math.pi * x + INV
    return 0.5 * (np.sin(u) / u + np.sin(v) / v)

def dKraw(x):
    x = np.asarray(x, dtype=float)
    u = math.pi * x - INV
    v = math.pi * x + INV
    return 0.5 * (math.pi * (u * np.cos(u) - np.sin(u)) / (u * u)
                  + math.pi * (v * np.cos(v) - np.sin(v)) / (v * v))

def w(x):
    return (Kraw(x) / K0) ** 2

def dw(x):
    return 2.0 * (Kraw(x) / K0) * (dKraw(x) / K0)

def F_grad(g, p):
    g = np.asarray(g, dtype=float)
    k = len(g); n = k + 1
    cs = np.concatenate(([0.0], np.cumsum(g)))
    tot = float(g.sum()) / p
    diff = np.zeros(k + 1)
    for s in range(1, n):
        wins = cs[s:k + 1] - cs[0:k + 1 - s]
        coef = 2.0 / (n - s)
        tot += coef * float(np.sum(w(wins)))
        d = coef * dw(wins)
        np.add.at(diff, np.arange(0, k - s + 1), d)
        np.add.at(diff, np.arange(s, k + 1), -d)
    return tot, np.cumsum(diff[:k]) + 1.0 / p

def polish(g0, p, maxiter):
    k = len(g0)
    return minimize(lambda x: F_grad(x, p), g0, jac=True, method='L-BFGS-B',
                    bounds=[(0.0, 60.0)] * k,
                    options={'maxiter': maxiter, 'ftol': 1e-18, 'gtol': 1e-13})
"""


@app.function(cpu=2.0, timeout=3600)
def cell(n: int, p: int, shard: int, nshard: int, restarts: int):
    ns = {}
    exec(_kernel_src(), ns)
    import numpy as np
    F_grad, polish = ns['F_grad'], ns['polish']
    k = n - 1
    rng = np.random.default_rng(1000 * n + 7 * p + shard)
    seeds = []
    # deterministic 1-2 words, sharded across containers
    total = 2 ** k
    for idx in range(shard, min(total, 16000), nshard):
        seeds.append(np.array([ZEROS[(idx >> i) & 1] for i in range(k)], dtype=float))
    # random zero-words, random uniform, uniform lattices
    for _ in range(restarts):
        seeds.append(np.array([ZEROS[rng.integers(0, 4)] for _ in range(k)], dtype=float))
    for _ in range(restarts):
        seeds.append(rng.uniform(0.4, 5.0, k))
    for v in np.linspace(0.4, 8.0, 60):
        seeds.append(np.full(k, float(v)))

    stage1 = [polish(s, p, 40) for s in seeds]
    vals = np.array([r.fun for r in stage1])
    best = (float('inf'), None)
    for i in np.argsort(vals)[:48]:
        r = polish(stage1[i].x, p, 1200)
        if r.fun < best[0]:
            best = (float(r.fun), [float(x) for x in r.x])
    return {'n': n, 'p': p, 'shard': shard, 'F': best[0], 'gaps': best[1]}


@app.local_entrypoint()
def main():
    t0 = time.time()
    jobs = [(n, p, s, CONTAINERS, RESTARTS)
            for n in N_POINTS for p in PRESSURES for s in range(CONTAINERS)]
    print(f"{len(jobs)} cells")
    results = list(cell.starmap(jobs))
    agg = {}
    for r in results:
        key = (r['n'], r['p'])
        if key not in agg or r['F'] < agg[key]['F']:
            agg[key] = r

    ctrl = agg.get((CONTROL_N, CONTROL_P))
    ok = ctrl is not None and abs(ctrl['F'] - CONTROL_F) < 1e-9
    print(f"control n={CONTROL_N} p={CONTROL_P}: F={ctrl['F'] if ctrl else None} "
          f"expected {CONTROL_F} ok={ok}")

    out = {'app': 'zeta-hunt82-family-limit', 'n_points': list(N_POINTS),
           'pressures': list(PRESSURES), 'containers': CONTAINERS,
           'restarts_per_container': RESTARTS,
           'control': {'n': CONTROL_N, 'p': CONTROL_P,
                       'expected_F': CONTROL_F,
                       'found_F': ctrl['F'] if ctrl else None, 'ok': bool(ok)},
           'note': 'float floors are UPPER bounds on inf F; Phi built from them is optimistic',
           'table': []}
    for n in N_POINTS:
        k = n - 1
        peak = None
        for p in PRESSURES:
            r = agg[(n, p)]
            c = r['F']
            m = k + int(math.floor(1.0 / c))
            phi = (H_CONST - k * (m - 1) / (p * m)) / (1.0 - c * (m - k) / m)
            row = {'n': n, 'p': p, 'F': c, 'm_cap': m, 'phi': phi,
                   'gap_sum': float(sum(r['gaps'])), 'gaps': r['gaps']}
            out['table'].append(row)
            if peak is None or phi > peak['phi']:
                peak = row
        print(f"n={n}: peak Phi={peak['phi']:.10f} at p={peak['p']} F={peak['F']:.10f} "
              f"S={peak['gap_sum']:.5f} gbar={peak['gap_sum']/k:.5f}")
        out.setdefault('peaks', {})[f'n{n}'] = peak

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        'artifacts', 'family-limit-modal.json')
    with open(path, 'w') as fh:
        json.dump(out, fh, indent=1)
    print(f"wrote {path}  [{time.time()-t0:.0f}s]")
