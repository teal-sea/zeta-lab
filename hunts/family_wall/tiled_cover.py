"""Uniform coverage of the large-n range.

For every k in a range, tile one fixed periodic pattern, rescale the tiling to total
length exactly k/H, and evaluate W. Then

    Phi_n <= H (1 + W(g))          (witness leg, since sum(g) = k/H)
    Phi_n <= H k/(k-1)             (trivial leg, since m >= k)

and the reported bound is the smaller. No optimisation runs inside the loop: the witness
is explicit, and a worse witness only weakens the bound, never invalidates it.
"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json
sys.path.insert(0, HERE)
from famlib import *
import numpy as np

KLO, KHI = 35, 400

wit = json.load(open(os.path.join(HERE, 'artifacts', 'witness.json')))
src = min([r for r in wit if r['k'] >= 20], key=lambda r: r['W'])
pat = np.array(src['gaps'])
print(f"tiling pattern: the k={src['k']} constrained minimiser (W={src['W']:.9f})")

worst = (0.0, None)
rows = []
for k in range(KLO, KHI + 1):
    reps = int(np.ceil(k / len(pat))) + 1
    g = np.tile(pat, reps)[:k].astype(float)
    g = g * ((k / H) / g.sum())
    Wv = Wsum(g)
    b = min(H * (1 + Wv), H * k / (k - 1))
    rows.append({'k': k, 'n': k + 1, 'W': Wv, 'bound': b})
    if b > worst[0]:
        worst = (b, k)
tail = H * KHI / (KHI - 1)
print(f"k = {KLO}..{KHI}   worst bound {worst[0]:.10f} at k={worst[1]}")
print(f"k >= {KHI+1}     trivial bound <= H*{KHI}/{KHI-1} = {tail:.10f}")
print(f"ceiling {CEIL};  both strictly below: {worst[0] < CEIL and tail < CEIL}")
json.dump({'k_lo': KLO, 'k_hi': KHI, 'rows': rows, 'worst': worst[0],
           'worst_k': worst[1], 'tail_bound': tail},
          open(os.path.join(HERE, 'artifacts', 'tiled-cover.json'), 'w'))
