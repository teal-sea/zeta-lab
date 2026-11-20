"""The GRH specialisation (sigma0 = 1/2) of the two-cutoff bound, Arb-enclosed.

    .venv/bin/python -m hunts.grh_class_number.bounds dtable
    .venv/bin/python -m hunts.grh_class_number.bounds theorem_a
    .venv/bin/python -m hunts.grh_class_number.bounds ladder

dtable     fine cover [10^2, 10^11] (ratio 1.01), a log-scale bridge
           [10^11, 10^50] and the tail constant at 10^50, all with
           sigma0 = 1/2; D_GRH(h) for every h <= H_TAB.  Adjacency of the
           cover cells is asserted, not assumed.
theorem_a  the clean form L(1, chi_D) >= C_A / log log |D|: tail constant at
           Q1 and a log-scale cover [10^2, Q1].
ladder     monotonicity in sigma0: 1/2 against the sibling hunt's 7/8 rows on
           every cell of the cover, and at identical parameters.
door       the bound from 2^40 on (a door, RESULTS.md): what the unconditional
           Jacobson-Mosunov table would complete.

Every bound is computed by the sibling hunt's modules, imported and not
edited (`hunts.qrh_class_number.lbound`, `.explicit`), with sigma0 = '1/2'.
The proof audit at sigma0 = 1/2 is RESULTS.md section 2.
"""

from __future__ import annotations

import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

from hunts.qrh_class_number import explicit as ex
from hunts.qrh_class_number import lbound as lb

HERE = Path(__file__).resolve().parent
SIBLING = HERE.parent / 'qrh_class_number'

SIGMA0 = '1/2'
FINE_FROM, FINE_TO, FINE_RATIO = 10**2, 10**11, 1.01
Q1 = 10**50
BRIDGE_RATIO = 1.02
#: the tail family at sigma0 = 1/2: a(q) = 2 log log q, b = (1 + eta) a
TAIL = dict(lam=Fraction(1), eta=Fraction(1, 4), dx=Fraction(1, 10), dy=Fraction(1, 10))
H_TAB = 10000
C_A = Fraction(1, 3)


def assert_adjacent(rows, q_from=None, q_to=None) -> None:
    """The cells [q_lo, q_hi] leave no gap: each starts where the last ended."""
    if q_from is not None:
        assert rows[0]['q_lo'] == q_from, (rows[0]['q_lo'], q_from)
    if q_to is not None:
        assert rows[-1]['q_hi'] == q_to, (rows[-1]['q_hi'], q_to)
    for r0, r1 in zip(rows, rows[1:]):
        assert r0['q_lo'] < r0['q_hi'], r0
        assert r0['q_hi'] == r1['q_lo'], (r0['q_hi'], r1['q_lo'])
    assert rows[-1]['q_lo'] < rows[-1]['q_hi']


def tail_h_lower(tail: dict) -> float:
    """Lower bound for h(D) at |D| = Q1 from the tail constant (Arb), and the
    check that sqrt(q) / log log q is increasing from Q1 on."""
    with ctx.workprec(lb.PREC):
        q = arb(tail['Q1'])
        c = arb(tail['c_lower'])
        lq = q.log()
        # d/dq [sqrt(q)/loglog q] > 0 iff (1/2) log q * log log q > 1
        assert lq * lq.log() / 2 > 1
        return ex._lower(q.sqrt() * c / (arb.pi() * lq.log()))


def d_bounds(rows, h_max: int):
    """D(h) for h = 1..h_max: the right end of the last cell with h_lower <= h."""
    out = []
    best_by_cell = [(r['h_lower'], r['q_hi']) for r in rows]
    for h in range(1, h_max + 1):
        last = rows[0]['q_lo']
        for hl, qhi in best_by_cell:
            if hl <= h:
                last = qhi
        out.append(last)
    return out


def dtable():
    t0 = time.time()
    fine = ex.cover(FINE_FROM, FINE_TO, FINE_RATIO, sigma0=SIGMA0)
    assert_adjacent(fine, FINE_FROM, FINE_TO)
    t1 = time.time()
    bridge = ex.cover(FINE_TO, Q1, BRIDGE_RATIO, sigma0=SIGMA0, log_scale=True)
    assert_adjacent(bridge, FINE_TO, Q1)
    tail = ex.tail_constant(Q1, sigma0=SIGMA0, **TAIL)
    th = tail_h_lower(tail)
    # beyond the fine cover every cell, and the tail, must exclude h <= H_TAB
    assert fine[-1]['h_lower'] > H_TAB, fine[-1]
    assert min(r['h_lower'] for r in bridge) > H_TAB
    assert th > H_TAB
    table = d_bounds(fine, H_TAB)
    assert table == sorted(table)
    out = {
        'statement': 'h(D) <= h implies |D| <= D_bound[h-1], for fundamental D < 0, '
                     'given that L(s, chi_D) has no zero with Re s > 1/2',
        'sigma0': SIGMA0, 'prec_bits': lb.PREC,
        'cover': [FINE_FROM, FINE_TO], 'ratio': FINE_RATIO, 'h_tab': H_TAB,
        'beyond_cover': {
            'bridge': [FINE_TO, Q1], 'bridge_log_ratio': BRIDGE_RATIO,
            'bridge_cells': len(bridge),
            'bridge_min_h_lower': min(r['h_lower'] for r in bridge),
            'tail': tail, 'tail_h_lower_at_Q1': th,
        },
        'seconds': {'fine': round(t1 - t0, 1), 'bridge_and_tail': round(time.time() - t1, 1)},
        'D_bound': table,
        'intervals': fine,
        'bridge_intervals': bridge,
    }
    (HERE / 'dtable_grh.json').write_text(json.dumps(out, indent=1) + '\n')
    print('dtable_grh', len(fine), 'cells', len(bridge), 'bridge cells',
          round(time.time() - t0, 1), 's')
    for h in (1, 2, 3, 10, 100, 500, 1000, 1500, 2000, 3000, 4000, 5000, 10000):
        print(h, table[h - 1])


def theorem_a():
    t0 = time.time()
    tail = ex.tail_constant(Q1, sigma0=SIGMA0, **TAIL)
    assert tail['c_lower'] >= float(C_A), tail
    rows = ex.cover(10**2, Q1, BRIDGE_RATIO, sigma0=SIGMA0, log_scale=True)
    assert_adjacent(rows, 10**2, Q1)
    fails = [r for r in rows if not (r['L_loglogq_lower'] is not None
                                     and r['L_loglogq_lower'] >= float(C_A))]
    start = max((r['q_hi'] for r in fails), default=rows[0]['q_lo'])
    out = {
        'statement': 'L(1, chi_D) >= 1/(3 log log |D|) for |D| >= q_start_cover (cover) '
                     'and |D| >= Q1 (tail), given no zero of L(s, chi_D) with Re s > 1/2',
        'sigma0': SIGMA0, 'c': str(C_A), 'q_start_cover': start, 'Q1': Q1, 'tail': tail,
        'min_L_loglogq_on_cover_after_start': min(
            r['L_loglogq_lower'] for r in rows if r['q_lo'] >= start),
        'littlewood_limit': math.pi**2 / (12 * math.exp(0.5772156649015329)),
        'seconds': round(time.time() - t0, 1),
        'intervals': rows,
    }
    (HERE / 'theorem_a_grh.json').write_text(json.dumps(out, indent=1) + '\n')
    print('theorem_a_grh: tail c =', tail['c_lower'], 'cover start', start,
          'min after start', out['min_L_loglogq_on_cover_after_start'],
          len(rows), 'cells', round(time.time() - t0, 1), 's')


def ladder():
    """Control (c): sigma0 = 1/2 is stronger than 7/8 on every cell."""
    t0 = time.time()
    g = json.loads((HERE / 'dtable_grh.json').read_text())['intervals']
    s = json.loads((SIBLING / 'dtable.json').read_text())['intervals']
    assert len(g) == len(s)
    worst = None
    for rg, rs in zip(g, s):
        assert (rg['q_lo'], rg['q_hi']) == (rs['q_lo'], rs['q_hi'])
        ratio = rg['L_lower'] / rs['L_lower']
        assert ratio > 1, (rg, rs)
        if worst is None or ratio < worst[0]:
            worst = (ratio, rg['q_lo'], rg['q_hi'])
    best = max(rg['L_lower'] / rs['L_lower'] for rg, rs in zip(g, s))
    # at identical parameters (the 7/8-optimal ones and the 1/2-optimal ones)
    tab = lb.tables()
    B = lb.meissel_mertens()
    same = []
    step = max(1, len(g) // 40)
    for rg, rs in list(zip(g, s))[::step]:
        for src in (rg, rs):
            p = (Fraction(src['a']), Fraction(src['b']), Fraction(src['dx']), Fraction(src['dy']))
            with ctx.workprec(lb.PREC):
                lo = lb.log_L1_lower(rg['q_hi'], *p, sigma0='1/2', B=B, tab=tab)
                mid = lb.log_L1_lower(rg['q_hi'], *p, sigma0='3/4', B=B, tab=tab)
                hi = lb.log_L1_lower(rg['q_hi'], *p, sigma0='7/8', B=B, tab=tab)
                assert lo > mid > hi, (rg['q_hi'], p)
                same.append({'q': rg['q_hi'], 'params_from': '1/2' if src is rg else '7/8',
                             'logL_half': ex._lower(lo), 'logL_three_quarters': ex._lower(mid),
                             'logL_seven_eighths': ex._lower(hi)})
    out = {
        'cells_compared': len(g),
        'min_ratio_L_half_over_L_seven_eighths': worst[0], 'at_cell': [worst[1], worst[2]],
        'max_ratio_L_half_over_L_seven_eighths': best,
        'same_parameter_points': same,
        'seconds': round(time.time() - t0, 1),
    }
    (HERE / 'controls_ladder.json').write_text(json.dumps(out, indent=1) + '\n')
    print({k: v for k, v in out.items() if k != 'same_parameter_points'})


def door():
    """h(D) > N for every |D| >= 2^40, from a log-scale cover and the tail."""
    t0 = time.time()
    rows = ex.cover(2**40, Q1, BRIDGE_RATIO, sigma0=SIGMA0, log_scale=True)
    assert_adjacent(rows, 2**40, Q1)
    tail = ex.tail_constant(Q1, sigma0=SIGMA0, **TAIL)
    th = tail_h_lower(tail)
    hmin = min(r['h_lower'] for r in rows)
    assert th > hmin
    out = {
        'statement': 'h(D) >= h_lower for every fundamental D with |D| >= 2^40, given that '
                     'L(s, chi_D) has no zero with Re s > 1/2',
        'from': 2**40, 'cells': len(rows), 'h_lower': hmin, 'first_cell': rows[0],
        'tail_h_lower_at_Q1': th, 'seconds': round(time.time() - t0, 1),
    }
    (HERE / 'door_2_40.json').write_text(json.dumps(out, indent=1) + '\n')
    print('for |D| >= 2^40: h >=', hmin)


if __name__ == '__main__':
    {'dtable': dtable, 'theorem_a': theorem_a, 'ladder': ladder, 'door': door}[sys.argv[1]]()
