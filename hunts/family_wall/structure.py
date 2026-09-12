"""The structural formula:  Phi_n - H  =  H * (convex non-increasing envelope of the
finite-k minimal energy-per-point curve W_k(gbar), evaluated at gbar = 1/H),
damped by 1/(1+(k-1)c) and reduced by the floor(1/c) defect."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
import sys, math, json
sys.path.insert(0, HERE)
from famlib import *
import numpy as np

d = json.load(open(os.path.join(ROOT, 'hunts', 'ainta_seven_point', 'artifacts', 'npoint-sweep.json')))
fams = {}
for r in d['table']:
    fams.setdefault((r['n_points'], r['pattern']), []).append(r)

print(f"1/H = {1/H:.9f}   (the mean gap that the peak selects)")
print()
for n, pat1, pat2 in [(7, '1-2-2-1-2-1', '1-2-2-2-2-1'),
                      (8, '1-2-1-2-1-2-1', '1-2-2-1-2-2-1'),
                      (9, '1-2-1-2-2-1-2-1', '1-2-2-2-1-2-2-1')]:
    k = n - 1
    def WS(pat):
        gs = [np.array(x['argmin']) for x in fams[(n, pat)]]
        return float(np.mean([Wsum(x) for x in gs])), float(np.mean([x.sum() for x in gs]))
    W1, S1 = WS(pat1); W2, S2 = WS(pat2)
    gb1, gb2 = S1/k, S2/k
    px = (S2 - S1)/(W1 - W2)
    tx = 1.0/px
    chord = W1 + (1/H - gb1)*(W2 - W1)/(gb2 - gb1)
    cx = W1 + S1*tx
    q = int(math.floor(1.0/cx)); m = k + q
    phi = (H - k*(m-1)/(px*m))/(1.0 - cx*(m-k)/m)
    print(f"n={n}: rungs gbar={gb1:.5f} (W={W1:.3e}) and gbar={gb2:.5f} (W={W2:.3e})")
    print(f"      chord at 1/H            W_conv = {chord:.6e}")
    print(f"      H * W_conv                     = {H*chord:.6e}")
    print(f"      damped  H c/(1+(k-1)c) - k/p   = {H*cx/(1+(k-1)*cx) - k/px:.6e}")
    print(f"      exact   Phi(p_x) - H           = {phi - H:.6e}   (Phi = {phi:.10f}, p_x={px:.1f})")
    print()
