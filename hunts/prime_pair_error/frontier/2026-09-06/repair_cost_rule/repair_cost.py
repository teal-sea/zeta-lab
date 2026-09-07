#!/usr/bin/env python3
"""Direct final-weight updates with an a priori repair-potential bound.

No LP, large prime table, RH assumption, or asymptotic rate inference.
Original input files are never overwritten. Run from any directory.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import time
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
M, R, DEN = 15, 100000, 108
Q_STEPS = (20, 21, 20)
A = F(M - 1, M)


def load_coeff(data):
    return {int(k): F(v) for k, v in data.items() if F(v)}


def add(c, d, factor=F(1)):
    out = defaultdict(F, c)
    for j, v in d.items():
        out[j] += factor * v
    return {j: v for j, v in out.items() if v}


def bump_coeff(n):
    if n < 1:
        raise ValueError('carry start must be positive')
    out = defaultdict(F)
    out[n] += 1
    out[n + 1] -= 1
    out[n * (n + 1)] -= 1
    return {j: v for j, v in out.items() if v}


def masked_coeff(q):
    ds = {1: 1}
    for p in (2, 3, 5, 7):
        ds.update({p * d: -v for d, v in list(ds.items())})
    out = defaultdict(F)
    for d, v in ds.items():
        for j, a in bump_coeff(q).items():
            out[d * j] += v * a
    return {j: v for j, v in out.items() if v}


def floor_array(c, size, den=DEN):
    n = np.arange(size, dtype=np.int64)
    out = np.zeros(size, dtype=np.int64)
    for j, v in c.items():
        scaled = v * den
        if scaled.denominator != 1:
            raise ValueError('denominator not supported by exact integer arrays')
        out += int(scaled) * (n // j)
    return out


def lift_array(seed):
    n = np.arange(len(seed), dtype=np.int64)
    out = np.zeros_like(seed)
    scale = 1
    while scale < len(seed):
        out += seed[n // scale]
        scale *= M
    return out


def mass(c):
    return sum(map(abs, c.values()), F())


def balance(c):
    return sum((v / j for j, v in c.items()), F())


@lru_cache(None)
def logarithm_bounds(n):
    """Exact rational enclosure. atanh tail, then outward binary rounding."""
    if n < 1:
        raise ValueError('positive log argument required')
    bits, terms = 112, 40
    e = n.bit_length() - 1

    def series(x):
        u = (x - 1) / (x + 1)
        acc, power = F(), u
        for k in range(terms):
            acc += 2 * power / (2 * k + 1)
            power *= u * u
        tail = 2 * power / ((2 * terms + 1) * (1 - u * u))
        return acc, acc + tail

    low, high = series(F(n, 1 << e))
    l2, h2 = series(F(2))
    low += e * l2
    high += e * h2
    unit = 1 << bits
    return (F((low.numerator * unit) // low.denominator, unit),
            F(-((-high.numerator * unit) // high.denominator), unit))


def linear_log_bounds(weights):
    lo, hi = F(), F()
    for n, w in weights.items():
        ll, hh = logarithm_bounds(int(n))
        lo += w * (ll if w >= 0 else hh)
        hi += w * (hh if w >= 0 else ll)
    return lo, hi


def kappa_bounds(c):
    return linear_log_bounds({j: -v / j for j, v in c.items()})


def add_interval(a, b):
    return a[0] + b[0], a[1] + b[1]


def scale_interval(x, a):
    vals = (a * x[0], a * x[1])
    return min(vals), max(vals)


def subtract_interval(a, b):
    return a[0] - b[1], a[1] - b[0]


def fmt(x):
    if isinstance(x, F):
        return mp.mpf(x.numerator) / x.denominator
    return mp.mpf(x)


def interval_record(x):
    return {'lower': str(x[0]), 'upper': str(x[1]),
            'lower_decimal': mp.nstr(fmt(x[0]), 40),
            'upper_decimal': mp.nstr(fmt(x[1]), 40)}


def kappa(c):
    return -mp.fsum(fmt(v) * mp.log(j) / j for j, v in c.items())


def period_sup(c, period):
    assert balance(c) == 0
    assert all(period % j == 0 for j in c)
    den = math.lcm(*(v.denominator for v in c.values()))
    vals = floor_array(c, period, den)
    return F(int(vals.min()), den), F(int(vals.max()), den)


def repair(raw):
    """Repairs operate directly on the final weight, without M-dilation."""
    raw = raw.copy()
    repairs = []
    t = np.arange(len(raw), dtype=np.int64)
    for n in range(1, len(raw)):
        missing = DEN - int(raw[n])
        if missing > 0:
            lam = F(missing, DEN)
            repairs.append((n, lam))
            x = t[n:]
            raw[n:] += missing * (x // n - x // (n + 1) - x // (n * (n + 1)))
    assert raw[1:].min() >= DEN
    return raw, repairs


def coeff_record(c):
    return {str(j): str(v) for j, v in sorted(c.items())}


def budget_sums(N):
    if N < 1:
        return mp.mpf(0), mp.mpf(0), mp.mpf(0)
    xs = []
    scale = 1
    while scale <= N:
        xs.append(1 + mp.log(fmt(N) / scale))
        scale *= M
    tail_s1, tail_s2, scale, k = mp.mpf(0), mp.mpf(0), R, 0
    while scale <= N:
        term = 1 + mp.log(fmt(N) / scale)
        tail_s1 += term
        tail_s2 += (k + 1) * term
        scale *= M
        k += 1
    return mp.fsum(xs), tail_s1, tail_s2


def factorial_sum(c, N):
    return mp.fsum(fmt(v) * mp.loggamma(N // j + 1) for j, v in c.items() if N // j >= 2)


def base_certificate(d, H, star, N):
    ans, scale = mp.mpf(0), 1
    while scale <= N:
        ans += factorial_sum(d, N // scale)
        scale *= M
    scale, k = R, 0
    while scale <= N:
        ans += fmt(H) * (k + 1) * factorial_sum(star, N // scale)
        scale *= M
        k += 1
    return ans


def extra_certificate(f, T, star, N):
    ans, scale = factorial_sum(f, N), R
    while scale <= N:
        ans += fmt(T) * factorial_sum(star, N // scale)
        scale *= M
    return ans


def main(output_path: Path):
    t0 = time.monotonic()
    original = json.loads((ROOT / 'inputs/joint_results.json').read_text())
    seeds = json.loads((ROOT / 'inputs/seeds.json').read_text())
    d = load_coeff(original['new_coefficients'])
    star = load_coeff(seeds['repair_coefficients'])
    initial = load_coeff(seeds['starting_coefficients'])
    H0 = F(original['new_tail_H'])
    assert H0 == F(701, 36) and mass(d) == F(56345, 108)
    assert balance(d) == balance(star) == 0
    assert period_sup(star, 2310)[0] >= 0
    assert period_sup(initial, 30030)[0] >= 0
    assert min(floor_array(star, M, 1)[1:]) >= 1
    cs = scale_interval(kappa_bounds(star), 1 / A)
    cb = scale_interval(add_interval(kappa_bounds(d), scale_interval(cs, H0 / R)), 1 / A)
    assert kappa_bounds(d)[0] > 0 and kappa_bounds(star)[0] > 0
    basew = lift_array(floor_array(d, R))
    assert basew[1:].min() >= DEN
    w, correction, T = basew.copy(), {}, F()
    stages = []
    currentC = cb

    for step, q in enumerate(Q_STEPS, 1):
        hc = masked_coeff(q)
        period = 210 * q * (q + 1)
        lower_h, H = period_sup(hc, period)
        assert H.denominator == lower_h.denominator == 1
        lower_h, H = int(lower_h), int(H)
        assert H == 3 and lower_h == -3
        raw = w - floor_array(hc, R)
        raw_deficit = np.maximum(DEN - raw, 0)
        raw_deficit[0] = 0
        deficit_rows = [(int(n), F(int(raw_deficit[n]), DEN))
                        for n in np.flatnonzero(raw_deficit)]
        ds = dict(deficit_rows)
        # This potential is fixed before constructing any repairs.
        potential_coeff = {}
        for n, val in deficit_rows:
            potential_coeff = add(potential_coeff, bump_coeff(n), val)
        potential = kappa_bounds(potential_coeff)
        gross = kappa_bounds(hc)
        tail = scale_interval(cs, F(H, R))
        guarantee = subtract_interval(subtract_interval(gross, potential), tail)
        accepted = guarantee[0] > 0
        # Rejected stage is computed as an explicit negative-control diagnostic only.
        new_w, patches = repair(raw)
        assert all(lam <= ds.get(n, F()) for n, lam in patches)
        pc = {}
        for n, lam in patches:
            pc = add(pc, bump_coeff(n), lam)
        cost = kappa_bounds(pc)
        assert cost[1] <= potential[0]
        stepf = add(pc, hc, F(-1))
        assert balance(stepf) == 0
        trial_correction = add(correction, stepf)
        rebuilt = basew + floor_array(trial_correction, R)
        assert np.array_equal(rebuilt, new_w)
        newC = add_interval(currentC, add_interval(kappa_bounds(stepf), tail))
        actual_gain = subtract_interval(currentC, newC)
        if accepted:
            assert actual_gain[0] >= guarantee[0]
        else:
            assert actual_gain[1] < 0  # property of this negative control, not of all failures
        L = sum(ds.values(), F())
        assert mass(stepf) <= mass(hc) + 3 * L
        rows = {
            'step': step, 'q': q, 'accepted': accepted,
            'policy': 'accept only a strictly positive exact lower bound on pre-repair gain',
            'period': period, 'h_min': lower_h, 'h_sup': H,
            'raw_deficit_cells': len(ds), 'raw_deficit_sum': str(L),
            'raw_deficit_weighted_area': str(sum((val/F(n*(n+1)) for n,val in ds.items()),F())),
            'gross_gain': interval_record(gross), 'raw_repair_potential': interval_record(potential),
            'tail_cost': interval_record(tail), 'guaranteed_gain': interval_record(guarantee),
            'actual_repair_cost': interval_record(cost), 'actual_gain': interval_record(actual_gain),
            'trial_C': interval_record(newC), 'patch_count': len(patches),
            'patch_sum': str(sum((lam for n,lam in patches),F())),
            'patches': [[n,str(lam)] for n,lam in patches],
            'raw_deficits': [[n,str(val)] for n,val in deficit_rows],
            'step_coefficients': coeff_record(stepf),
            'trial_first_level_mass': str(mass(add(d,trial_correction))),
            'trial_extra_tail': str(T+H),
            'weights': {str(n):str(F(int(new_w[n]),DEN)) for n in (18,19,20,21,24,25,32)},
            'minimum_prefix': str(F(int(new_w[1:].min()),DEN))}
        if accepted:
            w, correction, T, currentC = new_w, trial_correction, T+H, newC
        stages.append(rows)
        print(f'step={step} q={q} accepted={accepted} C={rows["trial_C"]["lower_decimal"]} patches={len(patches)}',flush=True)

    Cstar = kappa(star) / fmt(A)
    Cbase = (kappa(d) + fmt(H0)*Cstar/R) / fmt(A)
    Cfinal = Cbase+kappa(correction)+fmt(T)*Cstar/R
    assert cb[0] <= F(str(Cbase)) <= cb[1]
    assert currentC[0] <= F(str(Cfinal)) <= currentC[1]
    a0, ab = mass(add(d, correction)), mass(d)
    comparisons=[]
    for N in (10**4,10**6,10**8,10**12):
        s1,s1tail,s2=budget_sums(N)
        uold=Cbase*N+fmt(ab)*s1+fmt(H0*mass(star))*s2
        u=Cfinal*N+fmt(a0)*(1+mp.log(N))+fmt(ab)*(s1-1-mp.log(N))+fmt(mass(star))*(fmt(H0)*s2+fmt(T)*s1tail)
        bold=base_certificate(d,H0,star,N)
        b=bold+extra_certificate(correction,T,star,N)
        assert b<=u and bold<=uold
        comparisons.append({k:mp.nstr(v,65) for k,v in {'N':N,'old_B':bold,'new_B':b,'B_saving':bold-b,'old_U':uold,'new_U':u,'U_saving':uold-u}.items()})
    # Uniform dominance of the displayed envelope beyond N0, not a sampled claim.
    total_gain = subtract_interval(cb, currentC)
    delta_mass = a0-ab
    assert delta_mass == F(5797,18) and T*mass(star) == 90
    assert total_gain[0] > F(1,600)
    assert logarithm_bounds(10)[1] < F(7,3)
    assert logarithm_bounds(15)[0] > 2 and logarithm_bounds(100)[0] > 2
    N0=10**7
    q_upper = delta_mass*F(52,3) + 90*F(10,3)*F(17,3)
    assert F(N0,600)>q_upper
    eventual={'N0':N0,'gain_lower_bound':'1/600','delta_first_level_mass':str(delta_mass),
              'additional_tail_mass':'90','q_N0_upper':str(q_upper),
              'positive_margin':str(F(N0,600)-q_upper),
              'argument':'For ell=log(N/R)>=2, Q(N)/N is decreasing; see REPAIR_COST.md.'}
    out={'status':'finite construction and elementary repair bound; no uniform RH rate or novelty claim',
         'parameters':{'M':M,'R':R,'denominator':DEN,'sequence':[20,21,20]},
         'baseline_C':interval_record(cb),'final_C':interval_record(currentC),
         'final_first_level_mass':str(a0),'old_first_level_mass':str(ab),
         'final_extra_tail':str(T),'baseline_tail':str(H0),
         'final_direct_coefficients':coeff_record(correction),
         'final_direct_mass':str(mass(correction)),
         'stages':stages,'comparisons':comparisons,'eventual_envelope_dominance':eventual,
         'source_checksums':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (ROOT/'inputs').iterdir() if p.is_file()},
         'seconds':time.monotonic()-t0}
    output_path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['stages','final_direct_coefficients','source_checksums']},indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'rerun_results.json')
    args=ap.parse_args()
    with mp.workdps(75):
        main(args.output)
