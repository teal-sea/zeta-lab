"""What is the functional at the cells AMTOPA's verifier refused?

Takes a candidate in their schema and box coordinates in grid units (first == second, a
width-zero terminal cell), and reports, at each cell: the midpoint value of F, the tangent
bound the verifier prunes with (value minus sum|grad|/(2*GRID)), whether that clears the
candidate's target, and the smallest eigenvalue of the interval Hessian lower bound their
convexity gate needs positive definite. Then descends from the cell to see whether it sits in
a basin below the target, which is the difference between a margin failure and a false claim.

    python cell_check.py <candidate.amtopa> <boxes.json>
"""
import json, sys
import numpy as np
from scipy.optimize import minimize
import family as fam
from epsstar import _fun_jac

GRID = 4000
Q = 6
cand = json.load(open(sys.argv[1]))
boxes = json.load(open(sys.argv[2]))
t = cand['local_search']['candidate_target_for_certification']
target = t['numerator'] / t['denominator']
c = np.array(cand['window']['numerators'], float) / cand['window']['denominator']
w = fam.frequencies(len(c))
k0 = float(fam.kernel(0.0, c, w)[0])
den = cand['pair_weights']['denominator']
lookup = {(i, j): n / den for i, j, n in cand['pair_weights']['entries']}
a = np.array([lookup[p] for p in fam.PAIR_LIST])
b = np.array(cand['position_pressure']['numerators'], float) / cand['position_pressure']['denominator']
W = lambda x: fam.Wfun(np.atleast_1d(x), c, w, k0)
h = 1e-5
W1 = lambda x: (W(x + h) - W(x - h)) / (2 * h)
W2 = lambda x: (W(x + h) - 2 * W(x) + W(x - h)) / (h * h)
hi = min(0.02 / float(np.min(b[b > 0])), 40.0)
bounds = [(0.0, hi)] * Q

print(f'candidate {sys.argv[1].split("/")[-1]}  target {t["numerator"]}/{t["denominator"]} = {target:.10f}')
print(f'claimed floor {cand["local_search"]["float_minimum_observed"]}')
for box in boxes:
    first = np.array(box['box'], dtype=int)
    mid = (2 * first + 1) / (2 * GRID)
    prefix = np.concatenate(([0], np.cumsum(first)))
    ymid = np.concatenate(([0.0], np.cumsum(mid)))
    value = float(b @ mid)
    grad = b.copy()
    M = np.zeros((Q, Q))
    for k, (i, j) in enumerate(fam.PAIR_LIST):
        d = ymid[j] - ymid[i]
        value += a[k] * float(W(d)[0])
        grad[i:j] += a[k] * float(W1(d)[0])
        span = j - i
        lo = prefix[j] - prefix[i]
        xs = np.linspace(lo / GRID, (lo + span) / GRID, 400)
        M[i:j, i:j] += a[k] * float(np.min(W2(xs)))
    slack = float(np.sum(np.abs(grad))) / (2 * GRID)
    tang = value - slack
    eig = float(np.linalg.eigvalsh(M)[0])
    r = minimize(lambda g: _fun_jac(g, a, b, c, w, k0), mid, jac=True, method='L-BFGS-B',
                 bounds=bounds, options={'maxiter': 5000, 'ftol': 1e-18, 'gtol': 1e-14})
    print(f"\nshard {box.get('shard','?')}  gaps {' '.join('%.5f' % x for x in mid)}")
    print(f"  F(midpoint) {value:.10f}   {'ABOVE' if value > target else 'BELOW'} the target by {value - target:+.3e}")
    print(f"  tangent bound {tang:.10f} (slack {slack:.2e})   {'clears' if tang >= target else 'FAILS'} by {tang - target:+.3e}")
    print(f"  interval Hessian min eigenvalue {eig:+.5f}   {'gate can fire' if eig > 0 else 'GATE CANNOT FIRE'}")
    print(f"  descends to {r.fun:.10f} at {' '.join('%.5f' % x for x in r.x)}   "
          f"{'BELOW the target by %+.3e -- the floor is wrong' % (r.fun - target) if r.fun < target else 'still above the target'}")
    print(f"  reported plain lower bound {box.get('lower', float('nan')):.10f} "
          f"(loose by {value - box.get('lower', float('nan')):.2e} against the midpoint value)")
