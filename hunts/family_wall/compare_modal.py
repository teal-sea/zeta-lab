import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
import sys, math, json
sys.path.insert(0, HERE)
from famlib import *
from step11_envelope import ladder
import numpy as np

mod = json.load(open('os.path.join(ROOT, 'hunts', family_wall/artifacts/family-limit-modal.json'))
print("control:", mod['control'])
print()
print(" n     p     Modal floor      predicted floor   pred-Modal    Phi(Modal)     Phi(pred)")
lad = {}
out = []
for row in mod['table']:
    n, p = row['n'], row['p']
    k = n - 1
    if k not in lad:
        lad[k] = ladder(k)
    cp = min(W + S / p for W, S in lad[k])
    cm = row['F']
    def phi(c):
        m = k + int(math.floor(1.0 / c))
        return (H - k * (m - 1) / (p * m)) / (1.0 - c * (m - k) / m)
    out.append({'n': n, 'p': p, 'modal': cm, 'pred': cp, 'phi_modal': phi(cm), 'phi_pred': phi(cp)})
    print(f"{n:3d} {p:6d}  {cm:.10f}   {cp:.10f}   {cp-cm:+.3e}   {phi(cm):.10f}  {phi(cp):.10f}"
          + ("   <-- prediction BEATS modal" if cp < cm - 1e-12 else ""))
print()
for n in sorted({r['n'] for r in out}):
    rs = [r for r in out if r['n'] == n]
    bm = max(rs, key=lambda r: r['phi_modal'])
    bp = max(rs, key=lambda r: r['phi_pred'])
    print(f"n={n:3d}  peak Phi from Modal floor = {bm['phi_modal']:.10f} at p={bm['p']};  "
          f"from predicted floor = {bp['phi_pred']:.10f} at p={bp['p']}")
json.dump(out, open(os.path.join(HERE, 'artifacts', 'compare.json'), 'w'))
