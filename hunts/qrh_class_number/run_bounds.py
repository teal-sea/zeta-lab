"""Produce the verified bound files (Arb throughout).

    .venv/bin/python -m hunts.qrh_class_number.run_bounds dtable
    .venv/bin/python -m hunts.qrh_class_number.run_bounds theorem_a
    .venv/bin/python -m hunts.qrh_class_number.run_bounds abscissae

dtable     interval cover [10^2, 10^11] (ratio 1.01) and D(h), h <= 2000
theorem_a  tail constant at Q1 = 10^50 and a log-scale cover [10^2, 10^50]
           checking L(1, chi) * log log q >= 1/10 on every interval
abscissae  the same bound with sigma0 in {1/2, 7/8, 11/12, 15/16} at fixed q
eleven     Theorems A and C again with sigma0 = 11/12 (the October 5 paper's
           own theorem): tail constant, cover to 10^50, D(h) for h <= 1000
"""

from __future__ import annotations

import math
import sys
import time
from fractions import Fraction

from hunts.qrh_class_number import explicit as ex
from hunts.qrh_class_number import lbound as lb

HERE = ex.HERE
C_A = Fraction(1, 10)
Q1 = 10**50
TAIL = dict(lam=Fraction(1), eta=Fraction(3, 20), dx=Fraction(1, 25), dy=Fraction(1, 25))
H_TAB = 2000


def dtable():
    t0 = time.time()
    rows = ex.cover(10**2, 10**11, 1.01)
    # beyond 10^11 Theorem A gives h >= sqrt(q)/(10 pi loglog q), increasing
    q = 10**11
    tail_h = math.sqrt(q) / (10 * math.pi * math.log(math.log(q)))
    table = ex.d_table(rows, H_TAB, tail_h)
    ex.save(HERE / 'dtable.json', {
        'statement': 'h(D) <= h implies |D| <= D_bound(h), for fundamental D < 0, '
                     'given no zeros of L(s, chi_D) with Re s > 7/8',
        'sigma0': '7/8', 'cover': [10**2, 10**11], 'ratio': 1.01,
        'tail_beyond_cover': 'Theorem A: h(D) >= sqrt|D|/(10 pi loglog|D|), '
                             f'= {tail_h:.1f} at 10^11 and increasing',
        'seconds': round(time.time() - t0, 1),
        'D_bound': table, 'intervals': rows,
    })
    print('dtable', len(rows), 'intervals', round(time.time() - t0, 1), 's')
    for h in (1, 2, 3, 10, 100, 101, 200, 500, 1000, 2000):
        print(h, table[h - 1]['D_bound'])


def theorem_a():
    t0 = time.time()
    tail = ex.tail_constant(Q1, **TAIL)
    assert tail['c_lower'] >= float(C_A), tail
    rows = ex.cover(10**2, Q1, 1.02, log_scale=True)
    ok = [r for r in rows if r['L_loglogq_lower'] is not None
          and r['L_loglogq_lower'] >= float(C_A)]
    # the theorem's range starts after the last failing interval
    fails = [r for r in rows if not (r['L_loglogq_lower'] is not None
                                     and r['L_loglogq_lower'] >= float(C_A))]
    start = max((r['q_hi'] for r in fails), default=rows[0]['q_lo'])
    ex.save(HERE / 'theorem_a.json', {
        'statement': 'L(1, chi_D) >= 1/(10 log log |D|) for |D| >= q_start '
                     '(cover) and |D| >= Q1 (tail), given Re s > 7/8 zero-free',
        'c': str(C_A), 'q_start_cover': start, 'Q1': Q1, 'tail': tail,
        'min_L_loglogq_on_cover_after_start': min(
            r['L_loglogq_lower'] for r in rows if r['q_lo'] >= start),
        'seconds': round(time.time() - t0, 1),
        'intervals': rows,
    })
    print('theorem_a: tail c =', tail['c_lower'], 'cover start', start,
          len(rows), 'intervals', round(time.time() - t0, 1), 's')


def abscissae():
    out = []
    tab = lb.tables()
    B = lb.meissel_mertens()
    for s0 in ('1/2', '7/8', '11/12', '15/16'):
        fm = lb.FloatModel(sigma0=float(Fraction(s0)), tab=tab)
        for e in (6, 9, 12, 20, 50, 100):
            q = 10**e
            best, x = fm.optimise(math.log(q))
            params = lb.params_from_float(*x)
            r = ex.interval_bound(q, q, params, sigma0=s0, B=B, tab=tab)
            r['sigma0'] = s0
            r['loglogq'] = math.log(math.log(q))
            out.append(r)
            print(s0, e, round(r['L_lower'], 6), round(r['L_loglogq_lower'], 5), flush=True)
    ex.save(HERE / 'abscissae.json', out)


def eleven():
    t0 = time.time()
    s0 = '11/12'
    c = Fraction(1, 16)
    tail = ex.tail_constant(Q1, Fraction(1), Fraction(3, 20), Fraction(1, 25),
                            Fraction(1, 25), sigma0=s0)
    assert tail['c_lower'] >= float(c), tail
    rows_a = ex.cover(10**2, Q1, 1.02, sigma0=s0, log_scale=True)
    fails = [r for r in rows_a if not (r['L_loglogq_lower'] is not None
                                       and r['L_loglogq_lower'] >= float(c))]
    start = max((r['q_hi'] for r in fails), default=rows_a[0]['q_lo'])
    rows = ex.cover(10**2, 10**11, 1.02, sigma0=s0)
    q = 10**11
    tail_h = math.sqrt(q) * float(c) / (math.pi * math.log(math.log(q)))
    table = ex.d_table(rows, 1000, tail_h)
    ex.save(HERE / 'eleven_twelfths.json', {
        'sigma0': s0, 'c': str(c), 'tail': tail, 'theorem_a_cover_start': start,
        'theorem_a_cover_min': min(r['L_loglogq_lower'] for r in rows_a if r['q_lo'] >= start),
        'D_bound': {str(h): table[h - 1]['D_bound'] for h in (1, 2, 3, 10, 100, 200, 500, 1000)},
        'tail_h_at_1e11': tail_h, 'seconds': round(time.time() - t0, 1),
    })
    print('11/12: tail c', tail['c_lower'], 'cover start', start,
          {h: table[h - 1]['D_bound'] for h in (1, 100, 1000)}, round(time.time() - t0, 1), 's')


if __name__ == '__main__':
    {'dtable': dtable, 'theorem_a': theorem_a, 'abscissae': abscissae,
     'eleven': eleven}[sys.argv[1]]()
