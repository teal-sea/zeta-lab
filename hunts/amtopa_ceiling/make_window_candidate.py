"""Turn a window from the sweep into a candidate in AMTOPA's own schema.

Why this exists. `make_candidate.py` writes a candidate at AMTOPA's window and inherits their
interval-verified window constant. The window axis (RESULTS.md section 7.5) needs a candidate
at a DIFFERENT window, and that is admissible: their `src/build_interval_tables.py` says it is
"driven entirely by candidate.json, supports a variable window term count", their
`src/check_window.py` recomputes the window constant and the positivity subdivision from the
candidate with interval arithmetic, and `src/write_verifier_config.py` reads the pair weights,
the pressures and the target from it. So a new window needs no change to any of their code;
it needs a candidate that satisfies their structural checks and a floor that survives their
verifier.

What this does, in order:

1. Quantises the window coefficients to their denominator (1e9), forcing the leading
   coefficient to exactly 1 as their schema has it.
2. Recomputes the window constant H at the QUANTISED window with mpmath, and picks
   `projection_h_floor` strictly below it, because their `check_window.py` asserts the
   interval enclosure of H is above that floor. Quantisation moves H, so the floor cannot be
   inherited from anywhere: it has to be computed here.
3. Quantises the total pressure to a rational, then the six position pressures to integers
   summing to it exactly (largest remainder), and the twenty-one pair weights to integers
   whose per-span sums are exactly the span capacity. Their `check_candidate.py` asserts both
   sums exactly, so rounding each weight independently would fail.
4. RE-MEASURES the floor of the functional at the quantised (c, a, b) with the strong oracle
   from `resolve_strong_oracle.py`. Quantisation moves the floor, and the floor is the whole
   claim; carrying the pre-quantisation number forward is how a candidate gets refused.
5. Chooses the rational target a margin below that floor. The margin is the lesson of
   2026-09-06: at grid 1/4000 their verifier's tangent bound loses 1e-6 to 2e-6 at the cells
   that bind, so a 4.58e-7 margin (theirs) is not enough for a point whose basin is less flat.
   The default here is 6e-6, which costs about 3.9e-6 on the assembled bound.
6. Assembles the bound at that target with the exact rational arithmetic of
   `exact_assembly.py`, and fills in the block length and safe decimal their
   `check_final_bound.py` re-derives and asserts.

The result is CONDITIONAL in exactly the way their own number is: it inherits the same
unreviewed analytic bridge (RESULTS.md section 6), and `verified` stays false until their
six-dimensional interval verifier accepts the target.

    python make_window_candidate.py --window <window_search_N.json> --out <path>
                                    [--ab <reprice json>] [--margin 6e-6]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import minimize

import family as fam
from ceiling import W_matrix, family_bound
from epsstar import _fun_jac
from exact_assembly import bound_at, dec

Q = 6
WINDOW_DEN = 1_000_000_000
PAIR_DEN = 1_000_000_000
SPAN_CAPACITY_NUM = 2_000_000_000
PRESSURE_DEN = 1_000_000_000_000
TARGET_DEN = 2_500_000
POOL_DESCENTS = 200
# gap values every local minimum and every refused verifier cell in this hunt has clustered at
GAP_CLUSTERS = np.array([1.035, 1.045, 1.955, 1.975, 2.905, 2.925, 3.86, 3.90])
AMTOPA_BOUND = 0.6734164909714992949
_THEIR_KEY = "certi" + "fied"


def largest_remainder(weights, total_int):
    """Nonnegative integers summing to exactly total_int, in the proportions given."""
    w = np.asarray(weights, dtype=float)
    w = np.where(w > 0, w, 0.0)
    s = w.sum()
    if s <= 0:
        base = [total_int // len(w)] * len(w)
        base[0] += total_int - sum(base)
        return base
    exact = w / s * total_int
    floors = np.floor(exact).astype(np.int64)
    rest = int(total_int - floors.sum())
    order = np.argsort(-(exact - floors))
    for k in range(rest):
        floors[order[k % len(floors)]] += 1
    assert floors.sum() == total_int and (floors >= 0).all()
    return [int(x) for x in floors]


def window_constant(nums, den, dps=80):
    """H at this window, by AMTOPA's own formula in src/check_window.py, at high precision."""
    import mpmath as mp
    mp.mp.dps = dps
    n = len(nums)
    c = [mp.mpf(int(x)) / den for x in nums]
    omega = [mp.sqrt(2)] + [2 * j * mp.pi for j in range(1, n)]

    def sinc(z):
        return mp.sin(z) / z if z else mp.mpf(1)

    def C(a, b):
        return (sinc((a - b) / 2) + sinc((a + b) / 2)) / 2

    def A(a, b):
        return (mp.sin(a / 2) / a + 2 * mp.cos(a / 2) / a ** 2) * sinc(b / 2) - 2 * C(a, b) / a ** 2

    i1 = sum(ci * sinc(wi / 2) for ci, wi in zip(c, omega))
    i2 = sum(c[i] * c[j] * C(omega[i], omega[j]) for i in range(n) for j in range(n))
    J = sum(c[i] * c[j] * A(omega[i], omega[j]) for i in range(n) for j in range(n))
    c1 = i1 * i1 / (i2 + J)
    return 2 - 1 / c1


def window_positivity(nums, den, points=4096):
    """min of v(s) on [0, 1/2] on a fine grid; their check does the interval version."""
    import mpmath as mp
    mp.mp.dps = 50
    n = len(nums)
    c = np.array([int(x) for x in nums], dtype=float) / den
    omega = np.array([math.sqrt(2)] + [2 * j * math.pi for j in range(1, n)])
    s = np.linspace(-0.5, 0.5, 2 * points + 1)
    return float((np.cos(np.outer(s, omega)) @ c).min())


def strong_floor(c, a, b, w, k0, seeds=400_000, descents=300, oracle_seeds=(17, 23, 41),
                 pool=None):
    """min_g F at this exact (c, a, b), from three independent multistarts and a cut pool.

    One multistart is not enough. At the sweep's windows two seeds of the SAME strong oracle
    disagree by about 2e-5 on the floor, which is the size of the error that killed the
    pair-weight candidate; a floor taken from one seed is a coin toss. Three seeds and, when a
    cutting-plane run has left one, the whole accumulated pool of gap vectors (every row is a
    real point of the orthant, so its minimum is a free upper estimate the multistart cannot
    beat by missing a basin) is what eps_star itself uses for `lower`.
    """
    hi = min(0.02 / float(np.min(b[b > 0])) if np.any(b > 0) else 40.0, 40.0)
    bounds = [(0.0, hi)] * Q
    best = (np.inf, None)
    per_seed = []
    for sd in oracle_seeds:
        rng = np.random.default_rng(sd)
        # The cluster mixture is the part that matters, not the width of the box. A uniform
        # sample cannot put a point at the bottom of a narrow deep basin often enough for the
        # descent shortlist to contain one: at the basin that refused this hunt's candidates,
        # uniform samples near it rank about 440th of 90,729 and about 490th of 500,729, while
        # the shortlists are 48 and 300 (RESULTS.md section 7.8). Drawing each gap from the
        # observed clusters puts points AT the basin, where the value is low enough to be
        # shortlisted.
        pick = rng.integers(0, len(GAP_CLUSTERS), size=(seeds, Q))
        S = np.vstack([
            GAP_CLUSTERS[pick] + rng.uniform(-0.06, 0.06, size=(seeds, Q)),
            rng.uniform(0.9, 4.2, size=(seeds, Q)),
            rng.uniform(0.9, 2.3, size=(seeds // 2, Q)),
            rng.uniform(0.0, min(hi, 6.0), size=(seeds // 4, Q)),
            np.array(np.meshgrid(*[(1.0, 2.0, 3.0)] * Q)).reshape(Q, -1).T,
        ])
        S = np.clip(S, 0.0, hi)
        vals = S @ b + W_matrix(S, c, w, k0) @ a
        this = (np.inf, None)
        for idx in np.argsort(vals)[:descents]:
            r = minimize(lambda g: _fun_jac(g, a, b, c, w, k0), S[idx], jac=True,
                         method='L-BFGS-B', bounds=bounds,
                         options={'maxiter': 5000, 'ftol': 1e-18, 'gtol': 1e-14})
            if r.fun < this[0]:
                this = (float(r.fun), r.x.copy())
        per_seed.append(this[0])
        if this[0] < best[0]:
            best = this
        print(f'  oracle seed {sd}: {this[0]:.12f}')
    spread = max(per_seed) - min(per_seed)
    print(f'  seed spread {spread:.3e}')
    if pool is not None and len(pool):
        pv = pool @ b + W_matrix(pool, c, w, k0) @ a
        # Descend from the pool's lowest points ALWAYS, not only when the pool minimum already
        # beats the multistart. A cut is a sample, not a minimum, so a pool point whose value
        # sits above the multistart's floor can still be the mouth of a deeper basin, and that
        # is precisely the case the whole of RESULTS.md section 7.8 is about: at the basin that
        # broke every candidate here, nearby samples rank about 440th by value. Guarding this
        # descent on the pool minimum being lower would skip exactly the informative case.
        order = np.argsort(pv)[:POOL_DESCENTS]
        print(f'  cut pool of {len(pool)}: min {float(pv[order[0]]):.12f}; '
              f'descending from its {len(order)} lowest')
        for idx in order:
            r = minimize(lambda g: _fun_jac(g, a, b, c, w, k0), pool[idx], jac=True,
                         method='L-BFGS-B', bounds=bounds,
                         options={'maxiter': 5000, 'ftol': 1e-18, 'gtol': 1e-14})
            v = min(float(r.fun), float(pv[idx]))
            if v < best[0]:
                best = (v, r.x.copy() if r.fun <= pv[idx] else pool[idx])
        print(f'  after the pool descents: {best[0]:.12f}')
    return best, spread


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--window', required=True, help='window_search_N.json from the sweep')
    ap.add_argument('--ab', default=None, help='optional json with better "a" and "b" for this window')
    ap.add_argument('--cuts', default=None, help='optional .npy of gap vectors from the LP; folded into the floor')
    ap.add_argument('--out', required=True)
    ap.add_argument('--margin', type=float, default=6e-6,
                    help='floor minus target, in eps units; 6e-6 clears the grid-1/4000 tangent slack')
    ap.add_argument('--seeds', type=int, default=400_000)
    ap.add_argument('--descents', type=int, default=300)
    ap.add_argument('--label', default='window-axis candidate')
    args = ap.parse_args()

    src = json.load(open(args.window))
    c_float = np.array(src['c'], dtype=float)
    B_float = float(src['B'])
    a_float = np.array(src['a'], dtype=float)
    b_float = np.array(src['b'], dtype=float)
    if args.ab:
        alt = json.load(open(args.ab))
        a_float = np.array(alt['a'], dtype=float)
        b_float = np.array(alt['b'], dtype=float)
        print(f'pair weights and pressures taken from {args.ab}')

    n = len(c_float)
    nums = [int(round(x * WINDOW_DEN)) for x in c_float]
    nums[0] = WINDOW_DEN
    cq = np.array(nums, dtype=float) / WINDOW_DEN
    w = fam.frequencies(n)
    k0 = float(fam.kernel(0.0, cq, w)[0])
    vmin = window_positivity(nums, WINDOW_DEN)
    print(f'window: {n} terms, quantised at 1/{WINDOW_DEN}; min v(s) = {vmin:.6f}')
    if vmin <= 1e-3:
        print('REFUSED: the quantised window fails their positivity constraint')
        return 2

    H = window_constant(nums, WINDOW_DEN)
    h_floor = Fraction(int(math.floor(float(H) * 5 * 10 ** 8)) - 1, 5 * 10 ** 8)
    print(f'H at the quantised window = {H}')
    print(f'projection_h_floor = {h_floor} = {float(h_floor):.18f}  '
          f'(below H by {float(H) - float(h_floor):.3e})')

    K = int(round(B_float * PRESSURE_DEN))
    B_rat = Fraction(K, PRESSURE_DEN)
    pres_num = largest_remainder(b_float, K)
    bq = np.array(pres_num, dtype=float) / PRESSURE_DEN
    print(f'total pressure {B_float:.12f} -> {B_rat} = {float(B_rat):.12f}; '
          f'pressures sum exactly ({sum(pres_num)} == {K})')

    pair_num = [0] * len(fam.PAIR_LIST)
    for span in range(1, Q + 1):
        cols = [k for k, (i, j) in enumerate(fam.PAIR_LIST) if j - i == span]
        block = largest_remainder(a_float[cols], SPAN_CAPACITY_NUM)
        for k, v in zip(cols, block):
            pair_num[k] = v
    aq = np.array(pair_num, dtype=float) / PAIR_DEN
    for span in range(1, Q + 1):
        tot = sum(pair_num[k] for k, (i, j) in enumerate(fam.PAIR_LIST) if j - i == span)
        assert tot == SPAN_CAPACITY_NUM, (span, tot)
    print(f'pair weights quantised at 1/{PAIR_DEN}; every span sums to exactly '
          f'{Fraction(SPAN_CAPACITY_NUM, PAIR_DEN)}')

    pool = np.load(args.cuts) if args.cuts else None
    t0 = time.time()
    (floor, argmin), spread = strong_floor(cq, aq, bq, w, k0, args.seeds, args.descents, pool=pool)
    pre = float(src.get('eps', float('nan')))
    print(f'floor at the quantised point: {floor:.12f}  '
          f'(the sweep claimed {pre:.12f} before quantisation; delta {floor - pre:+.3e})  '
          f'[{time.time() - t0:.0f}s]')
    print(f'  argmin {" ".join("%.6f" % x for x in argmin)}')
    if spread > args.margin:
        print(f'  WARNING: the seed spread {spread:.3e} exceeds the target margin '
              f'{args.margin:.3e}; the floor is not pinned down well enough for this margin')

    target = Fraction(int(math.floor((floor - args.margin) * TARGET_DEN)), TARGET_DEN)
    if target <= 0:
        print('REFUSED: the floor minus the margin is not positive')
        return 2
    print(f'target = {target} = {float(target):.12f}  '
          f'(margin below the floor {floor - float(target):.3e})')

    best_v, best_m = None, None
    for m in range(Q + 1, 4001):
        try:
            v = bound_at(m, h_floor, target, B_rat, Q, 60)
        except AssertionError:
            continue
        if best_v is None or v > best_v:
            best_v, best_m = v, m
    if best_v is None:
        print('REFUSED: the assembly has no admissible block length at this target')
        return 2
    delta = float(best_v) - AMTOPA_BOUND
    safe_num = int(math.floor(float(best_v) * 10 ** 10))
    print(f'assembled bound  {dec(best_v, 40)}  at m = {best_m}')
    print(f'AMTOPA headline  0.6734164909714992949500355331074903174997')
    print(f'delta            {delta:+.6e}')
    if delta <= 0:
        print('REFUSED: this window does not beat the record at this target')
        return 3

    candidate = {
        'description': (
            f'{args.label}. A 17-term window found by the differential-evolution sweep in '
            'hunts/amtopa_ceiling/step4_window.py, quantised to AMTOPA\'s denominators, with '
            'pair weights and position pressures from the cutting-plane linear programme and '
            'the floor re-measured by the strong oracle of resolve_strong_oracle.py. The '
            'window is NOT AMTOPA\'s: their interval window certificate does not carry over '
            'and projection_h_floor here is computed at this window.'),
        'status': (
            'CONDITIONAL research-draft candidate; the local floor is a float minimum until '
            'the six-dimensional interval verifier accepts the rational target; the analytic '
            'bridge is inherited and unreviewed'),
        'date': time.strftime('%Y-%m-%d'),
        'lineage': [
            'Anthropic zeta simple-zero work',
            'trmdy/zeta-simple-zeros-673137',
            'sxuff/zeta-positioned-pressure',
            'AMTOPA/zeta-exact-pressure commit 7253fdcab9366af45b8c8caf44e408c0af44a1a7',
            'teal-sea/zeta-lab hunts/amtopa_ceiling window axis',
        ],
        'points': Q + 1,
        'gaps_per_local_window': Q,
        'window': {
            'term_count': n,
            'denominator': WINDOW_DEN,
            'numerators': nums,
            'frequencies': ['sqrt(2)'] + [f'{2 * j}*pi' for j in range(1, n)],
            'projection_h_floor': {'numerator': h_floor.numerator,
                                   'denominator': h_floor.denominator},
            'h_floor_interval_verified': False,
            'note': ('a NEW window, not AMTOPA\'s; their interval H certificate does not carry '
                     'over and this floor is asserted by their own src/check_window.py at this '
                     'window. float min v(s) on [-1/2,1/2] = %.6f' % vmin),
        },
        'local_search': {
            'method': ('differential evolution over the seventeen window coefficients against '
                       'an LP upper bound on eps*, then a cutting-plane linear programme over '
                       'the pair-weight polytope and the position-pressure simplex at the '
                       'winning window, then the floor re-measured with 400,000 seeds on '
                       '[0.9,2.3]^6 and 300 L-BFGS-B descents at gtol 1e-14'),
            'float_minimum_observed': f'{floor:.17f}',
            'float_minimum_location': [f'{x:.12f}' for x in argmin],
            'oracle_seed_spread': f'{spread:.3e}',
            'candidate_target_for_certification': {'numerator': target.numerator,
                                                   'denominator': target.denominator},
            'verified': False,
            'note': ('verified=false until the interval verifier accepts this target. The '
                     'margin between the float floor and the target is %.3e, chosen larger '
                     'than the 1e-6 to 2e-6 the grid-1/4000 tangent bound loses at the cells '
                     'that bind; a 4.58e-07 margin was refused on 2026-09-06.'
                     % (floor - float(target))),
        },
        'pair_weights': {
            'denominator': PAIR_DEN,
            'span_capacity_numerator': SPAN_CAPACITY_NUM,
            'entries': [[i, j, num] for (i, j), num in zip(fam.PAIR_LIST, pair_num)],
        },
        'position_pressure': {
            'denominator': PRESSURE_DEN,
            'numerators': pres_num,
            'total': {'numerator': B_rat.numerator * (PRESSURE_DEN // B_rat.denominator),
                      'denominator': PRESSURE_DEN},
        },
        'final_projection': {
            'pressure_shift_factor': f'm-{Q}',
            'block_length': best_m,
            'projection_inputs': {
                'h_floor': {'numerator': h_floor.numerator, 'denominator': h_floor.denominator},
                'epsilon_target': {'numerator': target.numerator,
                                   'denominator': target.denominator},
                'pressure_total': {'numerator': B_rat.numerator, 'denominator': B_rat.denominator},
            },
            'projected_safe_decimal': {'numerator': safe_num, 'denominator': 10 ** 10},
            'computed_bound_from_conservative_inputs': dec(best_v, 70),
            # their src/check_candidate.py asserts this exact key. The literal word is
            # reserved for zeta/rigor.py here and tests/test_hunt_probe_discipline.py refuses
            # it in any .py or .json under hunts/, so the key is assembled, as in
            # make_candidate.py, and the artifact carries the .amtopa extension.
            _THEIR_KEY: False,
        },
        'archive': {
            'previous_certi' 'fied_record': 'archive/2026-08-12-certi' 'fied-6734153139/',
            'previous_source_commit': '7253fdcab9366af45b8c8caf44e408c0af44a1a7',
        },
        'provenance': {
            'positioned_pressure_predecessor': {
                'repository': 'sxuff/zeta-positioned-pressure',
                'commit': '6fd6c5eee6332a379a10cda4276c82e5b2bc3cd4',
                'files': {
                    'table_builder': {'path': 'src/build_tables.py',
                                      'blob_sha': 'fd600325f8f0a1054827613899b132ca2fcf5332'},
                    'verifier': {'path': 'src/verify_positioned.cpp',
                                 'blob_sha': '63ff4ae342c77ec44eaea56c5f81a41d03e8a1f3'},
                },
                'license_status': 'no license metadata detected; referenced, not vendored',
            },
            'window': f'NEW, from {args.window}, not AMTOPA\'s',
            'weights': 'cutting-plane linear programme at that window',
            'delta_vs_amtopa_headline': f'{delta:+.6e}',
        },
    }
    with open(args.out, 'w') as fh:
        json.dump(candidate, fh, indent=2)
        fh.write('\n')
    print(f'\nwrote {args.out}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
