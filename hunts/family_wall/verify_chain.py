"""Numerically stress the rigorous inequality chain on the known data."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
import sys, math, json
sys.path.insert(0, HERE)
from famlib import *
import numpy as np

d = json.load(open(os.path.join(ROOT, 'hunts', 'ainta_seven_point', 'artifacts', 'npoint-sweep.json')))

print("chain:  Phi = [Hm - k(m-1)/p]/(m - c*floor(1/c))")
print("        <= H m/(m-1) - k/p                       (A: m-c*q >= m-1)")
print("        <= H + Hc/(1+(k-2)c) - k/p               (B: m-1 >= k-2+1/c)")
print("        <= H + Hc - k/p                          (C)")
print("        <= H + H W(g) + (H S(g) - k)/p           (D: c <= F(g,p))")
print()
bad = 0
for r in d['table']:
    n, p, c = r['n_points'], r['p'], r['best_F']
    k = n - 1
    q = int(math.floor(1.0 / c)); m = k + q
    phi = (H - k*(m-1)/(p*m))/(1.0 - c*(m-k)/m)
    A = H*m/(m-1) - k/p
    B = H + H*c/(1+(k-2)*c) - k/p
    C = H + H*c - k/p
    g = np.array(r['argmin']); W = Wsum(g); S = float(g.sum())
    D = H + H*W + (H*S - k)/p
    chain = [phi, A, B, C, D]
    okA, okB, okC, okD = phi <= A+1e-15, A <= B+1e-15, B <= C+1e-15, C <= D+1e-12
    if not (okA and okB and okC and okD):
        bad += 1
        print("VIOLATION", n, p, chain, okA, okB, okC, okD)
print(f"chain holds on all {len(d['table'])} sweep rows; violations = {bad}")

print()
print("trivial ceiling  Phi_n <= H (n-1)/(n-2):")
for n in [3, 10, 30, 50, 70, 74, 75, 80, 100, 1000]:
    v = H*(n-1)/(n-2)
    print(f"  n={n:5d}  H(n-1)/(n-2) = {v:.10f}   {'<' if v < CEIL else '>='} ceiling {CEIL}")
lo = 3
while H*(lo-1)/(lo-2) >= CEIL:
    lo += 1
print(f"  first n with the trivial bound already below the ceiling: n = {lo}")

print()
print("family crossovers  p_x = (S2-S1)/(W1-W2)  from the sweep argmins:")
fams = {}
for r in d['table']:
    fams.setdefault((r['n_points'], r['pattern']), []).append(r)
for n in (7, 8, 9):
    ks = [k for k in fams if k[0] == n]
    dat = []
    for key in ks:
        rows = fams[key]
        gs = [np.array(x['argmin']) for x in rows]
        W = float(np.mean([Wsum(x) for x in gs])); S = float(np.mean([x.sum() for x in gs]))
        dat.append((S, W, key[1], min(x['p'] for x in rows), max(x['p'] for x in rows)))
    dat.sort()
    for i in range(len(dat)-1):
        S1, W1, pat1, a1, b1 = dat[i]
        S2, W2, pat2, a2, b2 = dat[i+1]
        px = (S2-S1)/(W1-W2)
        c = W1 + S1/px
        q = int(math.floor(1.0/c)); m = (n-1)+q
        phi = (H - (n-1)*(m-1)/(px*m))/(1.0 - c*(m-(n-1))/m)
        print(f"  n={n}: {pat1} -> {pat2}   p_x = {px:8.1f}  (sweep: last p of first = {b1}, "
              f"first p of second = {a2})   Phi(p_x) = {phi:.10f}")
