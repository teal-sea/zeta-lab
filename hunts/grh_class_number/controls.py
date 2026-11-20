"""Controls for the GRH bound and the H = 5000 search.

    .venv/bin/python -m hunts.grh_class_number.controls lls
    .venv/bin/python -m hunts.grh_class_number.controls zero_term
    .venv/bin/python -m hunts.grh_class_number.controls independent
    .venv/bin/python -m hunts.grh_class_number.controls fault
    .venv/bin/python -m hunts.grh_class_number.controls crosschecks
    .venv/bin/python -m hunts.grh_class_number.controls pari OUTDIR
    .venv/bin/python -m hunts.grh_class_number.controls small_range OUTDIR

lls          the bound against the published GRH bound of Lamzouri, Li and
             Soundararajan (Theorem 1.5; valid for all q >= 3 by Languasco
             and Trudgian), cell by cell, and the class-number cutoffs
             against Cremona-Sutherland and Garcia-Grenie-Lee-Molteni
zero_term    the two halves of the inequality separately, at real characters
             with zeros from PARI: the explicit-formula identity as a measured
             defect, the prime sum against M, and the true zero sum Z(t)
             against the bound R(t)
independent  the Arb evaluation against a second route (mpmath quadrature)
fault        a planted sign error in the zero term, against the exact
             L(1, chi_D) of the listed fields: the control must go red
crosschecks  the H = 5000 lists against the sibling hunt's H = 1500 run,
             Watkins, Holmin-Kurlberg (odd h), Cremona-Sutherland and
             Garcia-Grenie-Lee-Molteni
small_range  exact L(1, chi_D) for every |D| <= 3 * 10^6 (Theorem A below
             the cover), and the list there against the sibling's full list
pari         PARI qfbclassno (an unrelated implementation, a cross-check and
             not an oracle of record) on the largest |D| of every h, random
             entries, windows inside the range and windows above D_GRH(h)
"""

from __future__ import annotations

import bisect
import hashlib
import json
import math
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from flint import arb, ctx

from hunts.qrh_class_number import explicit as ex
from hunts.qrh_class_number import lbound as lb

HERE = Path(__file__).resolve().parent
SIBLING = HERE.parent / 'qrh_class_number'
H = 5000
EULER = 0.5772156649015329


def _load(name, where=HERE):
    return json.loads((where / name).read_text())


def cell_of(cells, q: int):
    his = [c['q_hi'] for c in cells]
    k = bisect.bisect_left(his, q)
    assert cells[k]['q_lo'] <= q <= cells[k]['q_hi']
    return cells[k]


def cell_params(c):
    return Fraction(c['a']), Fraction(c['b']), Fraction(c['dx']), Fraction(c['dy'])


# ---------------------------------------------------------------- (b) LLS


def lls_lower(q) -> arb:
    """Lamzouri-Li-Soundararajan, Theorem 1.5 (GRH): the lower bound for
    |L(1, chi)|, chi primitive mod q.  Stated for q >= 10^10; Languasco and
    Trudgian (Theorem 1) prove the same inequality for every q >= 3."""
    with ctx.workprec(lb.PREC):
        lq = arb(q).log()
        llq = lq.log()
        inner = llq - arb(2).log() + arb(1) / 2 + 1 / llq + 14 * llq / lq
        return arb.pi() ** 2 / (12 * arb.const_euler().exp() * inner)


def lls_h(q: float) -> float:
    lq = math.log(q)
    llq = math.log(lq)
    return math.pi / (12 * math.exp(EULER)) * math.sqrt(q) / (
        llq - math.log(2) + 0.5 + 1 / llq + 14 * llq / lq)


def lls_cutoff(h: int) -> int:
    """Largest q with lls_h(q) <= h (lls_h is increasing on the range used;
    checked on a grid below)."""
    lo, hi = 10**3, 10**14
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if lls_h(mid) <= h:
            lo = mid
        else:
            hi = mid
    return lo


def lls():
    dt = _load('dtable_grh.json')
    rows = []
    for c in dt['intervals'] + dt['bridge_intervals']:
        theirs = float(lls_lower(c['q_hi']).mid())
        rows.append((c['q_hi'], c['L_lower'], theirs, c['L_lower'] / theirs))
    ratios = [r[3] for r in rows]
    grid = [10 ** (e / 4) for e in range(12, 53)]
    assert all(lls_h(x) < lls_h(y) for x, y in zip(grid, grid[1:]))
    D = dt['D_bound']
    sample_q = [10**2, 10**3, 10**4, 10**6, 10**8, 10**9, 10**10, 10**11, 10**12, 10**20, 10**50]
    samples = []
    for q in sample_q:
        r = min(rows, key=lambda r: abs(math.log(r[0]) - math.log(q)))
        samples.append({'q_hi': r[0], 'L_lower_this_hunt': r[1], 'L_lower_LLS': r[2], 'ratio': r[3]})
    a100 = [r for r in _load('abscissae.json', SIBLING) if r['sigma0'] == '1/2' and r['q_hi'] == 10**100][0]
    lls100 = float(lls_lower(10**100).mid())
    samples.append({'q_hi': 10**100, 'L_lower_this_hunt': a100['L_lower'], 'L_lower_LLS': lls100,
                    'ratio': a100['L_lower'] / lls100, 'source': 'sibling abscissae.json, sigma0 = 1/2'})
    cs = lambda h: (12 * math.exp(EULER) / math.pi) ** 2 * h * h * (math.log(math.log(h + 1)) + 4) ** 2
    out = {
        'statement': 'ratio of this hunt\'s Arb-enclosed lower bound for L(1, chi_D) to the LLS / '
                     'Languasco-Trudgian bound, both under GRH, at the right end of every cell',
        'cells': len(rows), 'range': [rows[0][0], rows[-1][0]],
        'min_ratio': min(ratios), 'min_ratio_at_q': rows[ratios.index(min(ratios))][0],
        'max_ratio': max(ratios), 'max_ratio_at_q': rows[ratios.index(max(ratios))][0],
        'this_hunt_stronger_on_every_cell': min(ratios) > 1,
        'samples': samples,
        'cutoffs': {str(h): {
            'D_GRH_this_hunt': D[h - 1],
            'LLS_LT_bound_inverted': lls_cutoff(h),
            'cremona_sutherland_prop19': int(cs(h)),
        } for h in (1, 100, 1000, 2000, 5000, 10000)},
        'gglm_pairs_as_transcribed': {'1': 1592, '100': 19124734, '2000': 8213527466},
        'lls_h_at_1e11': lls_h(1e11),
    }
    (HERE / 'controls_lls.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out, indent=1))


# ------------------------------------------- the two halves, with real zeros


def chi_D(D: int, p: int) -> int:
    """Kronecker symbol (D / p), p prime, D a fundamental discriminant."""
    if p == 2:
        if D % 2 == 0:
            return 0
        return 1 if D % 8 == 1 else -1
    r = D % p
    if r == 0:
        return 0
    return 1 if pow(r, (p - 1) // 2, p) == 1 else -1


def prime_sum(D: int, a: Fraction, b: Fraction):
    """sum_n Lambda(n) chi_D(n) w(n) / (n log n) with the trapezoid weight."""
    from mpmath import mp, mpf, log
    with mp.workdps(30):
        A, Bq = mpf(a.numerator) / a.denominator, mpf(b.numerator) / b.denominator
        total = mpf(0)
        for p in lb.primes_upto(int(math.exp(float(b))) + 2).tolist():
            c = chi_D(D, p)
            if c == 0:
                continue
            lp = log(p)
            k = 1
            while k * lp <= Bq:
                u = k * lp
                w = mpf(1) if u <= A else (Bq - u) / (Bq - A)
                total += mpf(c) ** k * w / (k * mpf(p) ** k)
                k += 1
        return total


def zero_side(zeros, t_log, T: float, q: int):
    """For t = e^{t_log}: the signed zero integral, the trivial-zero integral,
    Z_T(t) over the zeros 1/2 + i gamma with |gamma| <= T, and an estimate of
    the part of Z(t) above T."""
    from mpmath import mp, mpf, mpc, gammainc, e1, exp, im, re, pi, log
    with mp.workdps(30):
        L = mpf(t_log)
        signed = mpf(0)
        Z = mpf(0)
        for g in zeros:
            g = mpf(g)
            z0 = L * mpc(mpf(1) / 2, -g)
            # int_{1/2}^inf t^{-v} e^{i g L} / (v - i g)^2 dv = L * Gamma(-1, L (1/2 - i g))
            signed += 2 * re(L * gammainc(-1, z0))
            # int_{1/2}^inf t^{-v} / (v^2 + g^2) dv = Im[ e^{-i g L} E_1(L (1/2 - i g)) ] / g
            Z += 2 * im(exp(mpc(0, -g * L)) * e1(z0)) / g
        triv = sum(L * gammainc(-1, L * (2 * k + 2)) for k in range(0, 12))
        tail = exp(-L / 2) / L * (log(q * T / (2 * pi)) + 1) / (pi * T)
        return signed, triv, Z, tail


ZERO_SAMPLE = [(-163, 400.0), (-427, 300.0), (-5923, 300.0), (-99991, 200.0),
               (-999983, 200.0), (-2383747, 150.0), (-562394347, 100.0)]


def zero_term_one(D: int, T: float, pari=None):
    import cypari2
    from mpmath import mp, mpf, log, pi, sqrt
    pari = pari or cypari2.Pari()
    q = -D
    assert int(pari(f'isfundamental({D})')) == 1
    h = int(pari.qfbclassno(D))
    cells = _load('dtable_grh.json')['intervals']
    a, b, dx, dy = cell_params(cell_of(cells, q))
    with ctx.workprec(lb.PREC):
        d = lb.log_L1_lower(q, a, b, dx, dy, sigma0='1/2', detail=True)
        M, E_bound, Rx, Ry = (float(d[k].mid()) for k in ('M', 'E', 'Rx', 'Ry'))
        logL_bound = ex._lower(d['logL'])
    z = pari(f'lfunzeros(lfuncreate({D}), {T})')
    zeros = [float(z[i]) for i in range(len(z))]
    with mp.workdps(30):
        S = prime_sum(D, a, b)
        logL = log(pi * h / sqrt(q))
        E_actual = logL - S
        sx, tx, Zx, tailx = zero_side(zeros, mpf(b.numerator) / b.denominator, T, q)
        sy, ty, Zy, taily = zero_side(zeros, mpf(a.numerator) / a.denominator, T, q)
        ba = mpf(b.numerator) / b.denominator - mpf(a.numerator) / a.denominator
        E_zeros = (sx - sy + tx - ty) / ba
        tail_E = (tailx + taily) / ba
        return {
            'D': D, 'h': h, 'zeros_used': len(zeros), 'T': T, 'lowest_zero': zeros[0],
            'a': str(a), 'b': str(b), 'dx': str(dx), 'dy': str(dy),
            'log_L_exact': float(logL), 'prime_sum': float(S), 'M_lower_bound_for_prime_sum': M,
            'prime_sum_minus_M': float(S) - M,
            'E_actual': float(E_actual), 'E_from_zeros': float(E_zeros),
            'identity_defect': float(E_actual - E_zeros), 'identity_tail_estimate': float(tail_E),
            'trivial_zero_part_of_E': float((tx - ty) / ba),
            'E_bound': E_bound, 'abs_E_actual_over_bound': abs(float(E_actual)) / E_bound,
            'Z_x_zeros': float(Zx), 'Z_x_tail_estimate': float(tailx), 'R_x_bound': Rx,
            'Z_x_over_R_x': float(Zx + tailx) / Rx,
            'Z_y_zeros': float(Zy), 'Z_y_tail_estimate': float(taily), 'R_y_bound': Ry,
            'Z_y_over_R_y': float(Zy + taily) / Ry,
            'log_L_lower_bound': logL_bound, 'L_exact_over_bound': math.exp(float(logL) - logL_bound),
        }


def zero_term():
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(2 * 10**9)
    t0 = time.time()
    rows = []
    for D, T in ZERO_SAMPLE:
        r = zero_term_one(D, T, pari)
        rows.append(r)
        print({k: (round(v, 6) if isinstance(v, float) else v) for k, v in r.items()}, flush=True)
    out = {
        'statement': 'log L(1, chi_D) = prime_sum + E, E = (zero integrals at x minus at y, plus trivial '
                     'zeros) / (b - a); zeros of L(s, chi_D) from PARI lfunzeros (on the critical line, '
                     'up to height T; a measured control, not an enclosure)',
        'rows': rows,
        'max_abs_identity_defect': max(abs(r['identity_defect']) for r in rows),
        'max_Z_over_R': max(max(r['Z_x_over_R_x'], r['Z_y_over_R_y']) for r in rows),
        'min_prime_sum_minus_M': min(r['prime_sum_minus_M'] for r in rows),
        'seconds': round(time.time() - t0, 1),
    }
    (HERE / 'controls_zero_term.json').write_text(json.dumps(out, indent=1) + '\n')


# ------------------------------------- an independent route to the bound


def independent_bound(q: int, a: Fraction, b: Fraction, dx: Fraction, dy: Fraction):
    """Theorem B's right side at sigma0 = 1/2 by a second route: mpmath, a
    direct prime sum and adaptive quadrature in place of the sibling's Arb
    tables and upper Riemann sums.  Not an enclosure.  Returns (M, Rx, Ry, T)."""
    from mpmath import mp, mpf, log, pi, psi, zeta, quad, exp, inf
    with mp.workdps(25):
        A, Bq = mpf(a.numerator) / a.denominator, mpf(b.numerator) / b.denominator
        primes = lb.primes_upto(int(math.exp(float(b))) + 2).tolist()
        S_a = sum(mpf(1) / p for p in primes if log(p) <= A)
        S_b = sum(mpf(1) / p for p in primes if log(p) <= Bq)
        mid = sum(log(p) / p for p in primes if A < log(p) <= Bq)
        integral = Bq * S_b - A * S_a - mid
        P2 = sum(mpf(1) / (2 * p**2) - mpf(1) / (3 * p**3) for p in primes if 2 * log(p) <= A)
        P2 += sum(mpf(1) / (4 * p**4) - mpf(1) / (5 * p**5) for p in primes if 4 * log(p) <= A)
        M = -integral / (Bq - A) + P2

        def G(sig):
            return (log(mpf(q) / pi) / 2 + psi(0, (sig + 1) / 2) / 2
                    - zeta(sig, derivative=1) / zeta(sig)
                    + 2 * zeta(2 * sig, derivative=1) / zeta(2 * sig))

        def R(L, d):
            d = mpf(d.numerator) / d.denominator
            i1 = quad(lambda u: exp(-u * L) / (u + mpf(1) / 2) ** 2, [0, d])
            i2 = quad(lambda u: exp(-u * L) * G(1 + u) / (u + mpf(1) / 2), [d, 1, 2, 4, 8, inf])
            return exp(-L / 2) * ((d + mpf(1) / 2) * G(1 + d) * i1 + i2)

        T = pi**2 / 24 * (exp(-2 * A) / A + exp(-2 * Bq) / Bq)
        return float(M), float(R(Bq, dx)), float(R(A, dy)), float(T)


def independent():
    cells = _load('dtable_grh.json')['intervals']
    rows = []
    for q in (163, 10**4, 10**6, 10**8, 16396235837, 10**11):
        c = cell_of(cells, q)
        prm = cell_params(c)
        with ctx.workprec(lb.PREC):
            d = lb.log_L1_lower(c['q_hi'], *prm, sigma0='1/2', detail=True)
            arbv = {k: float(d[k].mid()) for k in ('M', 'Rx', 'Ry', 'T', 'logL')}
        M, Rx, Ry, T = independent_bound(c['q_hi'], *prm)
        logL = M - (Rx + Ry + T) / float(prm[1] - prm[0])
        rows.append({'q_hi': c['q_hi'], 'M_arb': arbv['M'], 'M_second_route': M,
                     'Rx_arb_over_second_route': arbv['Rx'] / Rx,
                     'Ry_arb_over_second_route': arbv['Ry'] / Ry,
                     'T_arb_over_second_route': arbv['T'] / T,
                     'logL_arb': arbv['logL'], 'logL_second_route': logL,
                     'second_route_minus_arb': logL - arbv['logL']})
        print(rows[-1], flush=True)
    out = {
        'statement': 'the Arb evaluation (upper Riemann sums on a grid) against mpmath adaptive '
                     'quadrature of the same expressions; the Arb value must be the smaller bound, '
                     'by the grid loss only',
        'rows': rows,
        'max_abs_M_difference': max(abs(r['M_arb'] - r['M_second_route']) for r in rows),
        'max_R_ratio': max(max(r['Rx_arb_over_second_route'], r['Ry_arb_over_second_route']) for r in rows),
        'min_R_ratio': min(min(r['Rx_arb_over_second_route'], r['Ry_arb_over_second_route']) for r in rows),
        'max_logL_gap': max(r['second_route_minus_arb'] for r in rows),
        'min_logL_gap': min(r['second_route_minus_arb'] for r in rows),
    }
    (HERE / 'controls_independent.json').write_text(json.dumps(out, indent=1) + '\n')


# ----------------------------------------------------- (d) the planted fault


def faulty_log_L(q_hi: int, params, fault: str) -> float:
    """The bound with a planted error.  'zero_sign': the zero term enters
    with the wrong sign (M + E in place of M - E)."""
    a, b, dx, dy = params
    with ctx.workprec(lb.PREC):
        d = lb.log_L1_lower(q_hi, a, b, dx, dy, sigma0='1/2', detail=True)
        if fault == 'zero_sign':
            return ex._lower(d['M'] + d['E'])
        if fault == 'none':
            return ex._lower(d['logL'])
        raise ValueError(fault)


def fault():
    s = _load(f'search_H{H}.json')
    cells = _load('dtable_grh.json')['intervals']
    red, green, worst = 0, 0, None
    for h in range(1, H + 1):
        n = s['max_absD_by_h'][str(h)]
        if n < cells[0]['q_lo']:
            continue
        c = cell_of(cells, n)
        L = math.pi * h / math.sqrt(n)
        M = float(arb(c['M']).mid())
        E = float(arb(c['E']).mid())
        if L < math.exp(M + E):
            red += 1
            if worst is None or L / math.exp(M + E) < worst['ratio']:
                worst = {'absD': n, 'h': h, 'L_exact': L, 'faulty_bound': math.exp(M + E),
                         'ratio': L / math.exp(M + E)}
        if L < c['L_lower']:
            green += 1
    # recompute the worst case in Arb
    c = cell_of(cells, worst['absD'])
    again = math.exp(faulty_log_L(c['q_hi'], cell_params(c), 'zero_sign'))
    out = {
        'fault': 'zero term with the wrong sign: exp(M + E) in place of exp(M - E)',
        'pairs_checked': 'the largest |D| of every h <= 5000',
        'violations_with_fault': red, 'violations_without_fault': green,
        'clearest_violation': worst, 'faulty_bound_recomputed_in_arb': again,
        'control_goes_red': red > 0 and green == 0 and again > worst['L_exact'],
    }
    (HERE / 'controls_fault.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out, indent=1))


# ------------------------------------------------------- (5) cross-checks

#: Garcia, Grenie, Lee, Molteni, arXiv:2610.14257v1, Table 1 (GRH): h0, number
#: of fields with h <= h0, largest |disc|.  Transcribed from this workflow's
#: literature notes of 2026-11-20, which read the PDF; not re-read here.
GGLM_TABLE1 = {
    100: (42272, 2383747), 200: (167157, 8377363), 300: (372393, 19225243),
    400: (665008, 35723227), 500: (1028749, 55171603), 600: (1488496, 81792547),
    700: (2014583, 114148483), 800: (2645480, 138731107), 900: (3342720, 199362403),
    1000: (4115897, 227932027), 1100: (4972445, 283506787), 1200: (5941733, 351036667),
    1300: (6960178, 398158363), 1400: (8061896, 480668203), 1500: (9245562, 562394347),
    1600: (10553429, 643541347), 1700: (11881764, 707327707), 1800: (13348410, 805169467),
    1900: (14824012, 898772323), 2000: (16453493, 1062350083),
}
#: Cremona and Sutherland, arXiv:2301.11169v4, section 5 (GRH): fundamental
#: discriminants with h <= 1000, and the largest (h = 996).  Same provenance.
CREMONA_SUTHERLAND = {'count_h_le_1000': 4115897, 'largest_absD': 227932027, 'its_h': 996}


def crosschecks():
    s = _load(f'search_H{H}.json')
    out = {}
    # the sibling hunt's 7/8 run, which covered |D| <= 12 409 254 457
    sib = _load('search_H1500.json', SIBLING)
    bad = [h for h in range(1, 1501)
           if s['count_by_h'][str(h)] != sib['count_by_h'][str(h)]
           or s['max_absD_by_h'][str(h)] != sib['max_absD_by_h'][str(h)]]
    out['sibling_H1500'] = {
        'h_compared': 1500, 'mismatches': bad,
        'sha256_h_le_1500_equal': s['sha256_sublist_h_le']['1500'] == sib['sha256_sorted_list'],
        'sha256_h_le_1000_equal': s['sha256_sublist_h_le']['1000']
        == _load('search_H1000.json', SIBLING)['sha256_sorted_list'],
        'sha256_h_le_100_equal': s['sha256_sublist_h_le']['100']
        == _load('search_H100.json', SIBLING)['sha256_sorted_list'],
    }
    w = _load('watkins.json', SIBLING)
    bad = [h for h in range(1, 101)
           if s['count_by_h'][str(h)] != w['count_by_h'][str(h)]
           or s['max_squarefree_k_by_h'][str(h)] != w['max_squarefree_k_by_h'][str(h)]]
    out['watkins_h_le_100'] = {'mismatches': bad,
                               'total': sum(s['count_by_h'][str(h)] for h in range(1, 101)),
                               'watkins_total': w['total']}
    hk = _load('holmin_kurlberg_odd_5000.json')['count_by_odd_h']
    bad = [h for h in range(1, H + 1, 2) if s['count_by_h'][str(h)] != hk[str(h)]]
    out['holmin_kurlberg_odd'] = {
        'odd_h_compared': len(range(1, H + 1, 2)), 'mismatches': bad,
        'fields_with_odd_h': sum(s['count_by_h'][str(h)] for h in range(1, H + 1, 2)),
        'of_which_h_above_1500': sum(s['count_by_h'][str(h)] for h in range(1501, H + 1, 2)),
    }
    bad = [k for k, (c, m) in GGLM_TABLE1.items() if s['cumulative_by_hundreds'][str(k)] != [c, m]]
    out['gglm_table1_h_le_2000'] = {'rows_compared': len(GGLM_TABLE1), 'mismatches': bad,
                                    'provenance': 'transcribed from the literature notes, not re-read'}
    c1000 = s['cumulative_by_hundreds']['1000']
    out['cremona_sutherland_h_le_1000'] = {
        'count_equal': c1000[0] == CREMONA_SUTHERLAND['count_h_le_1000'],
        'largest_equal': c1000[1] == CREMONA_SUTHERLAND['largest_absD']
        and s['max_absD_by_h']['996'] == CREMONA_SUTHERLAND['largest_absD'],
    }
    out['every_h_occurs'] = all(s['count_by_h'][str(h)] > 0 for h in range(1, H + 1))
    out['all_agree'] = (not out['sibling_H1500']['mismatches']
                        and out['sibling_H1500']['sha256_h_le_1500_equal']
                        and out['sibling_H1500']['sha256_h_le_1000_equal']
                        and out['sibling_H1500']['sha256_h_le_100_equal']
                        and not out['watkins_h_le_100']['mismatches']
                        and not out['holmin_kurlberg_odd']['mismatches']
                        and not out['gglm_table1_h_le_2000']['mismatches']
                        and out['cremona_sutherland_h_le_1000']['count_equal']
                        and out['cremona_sutherland_h_le_1000']['largest_equal'])
    (HERE / 'crosschecks.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out, indent=1))


def make_hk(src: Path):
    """Holmin-Kurlberg F(h) for odd h < 5000 from the authors' file."""
    raw = src.read_bytes()
    counts = {}
    for line in raw.decode().splitlines():
        if line.startswith('#') or not line.strip():
            continue
        h, f = line.split()
        if int(h) < H:
            counts[h] = int(f)
    assert len(counts) == H // 2
    old = _load('holmin_kurlberg_odd.json', SIBLING)
    assert all(counts[k] == v for k, v in old['count_by_odd_h'].items())
    out = {
        'source': 'S. Holmin, P. Kurlberg, list of F(h) for odd h < 10^6, conditional on GRH (Holmin, '
                  'Jones, Kurlberg, McLeman, Petersen, arXiv:1510.04387); fetched 2026-11-20',
        'url': old['url'], 'sha256_of_fetched_file': hashlib.sha256(raw).hexdigest(),
        'agrees_with_sibling_copy_for_h_below_1500': True,
        'count_by_odd_h': counts,
    }
    (HERE / 'holmin_kurlberg_odd_5000.json').write_text(json.dumps(out, indent=1) + '\n')
    print('odd h below', H, ':', len(counts), 'total', sum(counts.values()))


def small_range(outdir: Path):
    """Theorem A below the cover: exact L(1, chi_D) for every |D| <= 3 * 10^6."""
    from hunts.grh_class_number import search
    X0 = 3 * 10**6
    s = _load(f'search_H{H}.json')
    lo, hi = search.chunks(s['X'])[0][:2]
    assert lo == 3 and hi >= X0
    arr = np.fromfile(search.chunk_path(outdir, lo, hi), dtype=np.int64, sep=' ').reshape(-1, 2)
    arr = arr[arr[:, 0] <= X0]
    # every fundamental discriminant up to X0 is listed (none has h > H there)
    sq = np.ones(X0 + 1, dtype=bool)
    for p in range(2, int(X0**0.5) + 1):
        sq[p * p::p * p] = False
    n = np.arange(X0 + 1)
    fund = ((n % 4 == 3) & sq) | (((n % 16 == 4) | (n % 16 == 8)) & sq[n // 4] & (n % 4 == 0))
    fund[:3] = False
    assert np.array_equal(np.nonzero(fund)[0], arr[:, 0]), 'the list misses a discriminant below 3*10^6'
    nn, hh = arr[:, 0].astype(np.float64), arr[:, 1]
    w = np.where(arr[:, 0] == 3, 6, np.where(arr[:, 0] == 4, 4, 2))
    L = 2 * math.pi * hh / (w * np.sqrt(nn))
    prod = L * np.log(np.log(nn))
    bad = arr[:, 0][prod < 1 / 3]
    sel = arr[:, 0] >= 7
    j = int(np.argmin(prod[sel]))
    out = {
        'range': [3, X0], 'fundamental_discriminants': int(len(arr)),
        'largest_class_number': int(hh.max()),
        'discriminants_with_L_loglog_below_one_third': [int(x) for x in bad],
        'min_L_loglog_from_7': float(prod[sel][j]), 'attained_at_absD': int(arr[:, 0][sel][j]),
        'sha256_list': hashlib.sha256(''.join(f'{a} {b}\n' for a, b in arr.tolist()).encode()).hexdigest(),
        'sibling_sha256_full_list': _load('controls_exact_l.json', SIBLING)['sha256_full_list'],
    }
    out['equal_to_sibling_full_list'] = out['sha256_list'] == out['sibling_sha256_full_list']
    (HERE / 'theorem_a_small.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out, indent=1))


# -------------------------------------------------------------- PARI


def pari(outdir: Path):
    import cypari2
    from hunts.grh_class_number import search
    P = cypari2.Pari()
    P.allocatemem(10**9)
    t0 = time.time()
    s = _load(f'search_H{H}.json')
    X = s['X']
    D = _load('dtable_grh.json')['D_bound']
    rng = random.Random(20261120)
    cs = search.chunks(X)

    def pari_h(n):
        return int(P.qfbclassno(-n))

    def is_fund(n):
        return int(P(f'isfundamental({-n})')) == 1

    # (i) the largest |D| of every h
    bad_max = [(h, s['max_absD_by_h'][str(h)]) for h in range(1, H + 1)
               if pari_h(s['max_absD_by_h'][str(h)]) != h]
    # (ii) random entries and (iv) windows inside the range, from the list files
    windows = [2 * 10**6, 5 * 10**7, 3 * 10**8, 10**9, 25 * 10**8, 2999998000, 33 * 10**8,
               45 * 10**8, 7 * 10**9, 9 * 10**9, 11 * 10**9, 13 * 10**9, X - 3000]
    W = 3000
    n_random, bad_random, n_win, bad_win, win_listed = 0, [], 0, [], 0
    listed = {w: {} for w in windows}                 # a window may cross a chunk boundary
    for lo, hi, mode, a0, _ in cs:
        path = search.chunk_path(outdir, lo, hi)
        if path.stat().st_size == 0:
            continue
        arr = np.fromfile(path, dtype=np.int64, sep=' ').reshape(-1, 2)
        for i in rng.sample(range(len(arr)), min(6, len(arr))):
            n, h = int(arr[i, 0]), int(arr[i, 1])
            n_random += 1
            if pari_h(n) != h:
                bad_random.append((n, h))
        for w in windows:
            if w <= hi and w + W >= lo:
                sel = arr[(arr[:, 0] >= w) & (arr[:, 0] <= w + W)]
                listed[w].update({int(n): int(h) for n, h in sel})
    for w in windows:
        assert w >= 3 and w + W <= X
        win_listed += len(listed[w])
        for n in range(w, w + W + 1):
            if not is_fund(n):
                assert n not in listed[w]
                continue
            n_win += 1
            hp = pari_h(n)
            if (listed[w].get(n) != hp) if hp <= H else (n in listed[w]):
                bad_win.append((n, hp, listed[w].get(n)))
    # (iii) just above D_GRH(h): no class number <= h
    above = {}
    for h in (1, 2, 3, 10, 100, 500, 1000, 2000, 3000, 4000, 5000, 10000):
        d = D[h - 1]
        hs = [pari_h(n) for n in range(d + 1, d + 2001) if is_fund(n)]
        above[str(h)] = {'D_GRH': d, 'fundamental_in_window': len(hs), 'smallest_class_number': min(hs),
                         'violations': sum(1 for x in hs if x <= h)}
    out = {
        'H': H, 'pari_version': str(P.version()),
        'largest_absD_of_every_h': {'checked': H, 'mismatches': bad_max},
        'random_entries': {'checked': n_random, 'mismatches': bad_random},
        'windows_inside_range': {'starts': windows, 'width': W, 'fundamental_checked': n_win,
                                 'listed_in_windows': win_listed, 'mismatches': bad_win},
        'windows_above_D_GRH': above,
        'seconds': round(time.time() - t0, 1),
    }
    (HERE / 'controls_pari.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'pari':
        pari(Path(sys.argv[2]))
    elif cmd == 'small_range':
        small_range(Path(sys.argv[2]))
    elif cmd == 'make_hk':
        make_hk(Path(sys.argv[2]))
    else:
        {'lls': lls, 'zero_term': zero_term, 'fault': fault, 'crosschecks': crosschecks,
         'independent': independent}[cmd]()
