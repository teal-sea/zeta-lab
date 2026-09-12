#!/usr/bin/env python3
"""Small factorial-upper-certificate search; exact feasibility, numerical search.

Run: python pilot.py --output results.json
Only the optimizer needs NumPy/SciPy. Exact checks use Python integer/Fraction
arithmetic. Numerical optimality and analytic novelty are NOT established.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import platform
import time
from typing import Any


def divisors(period: int) -> list[int]:
    return [j for j in range(1, period + 1) if period % j == 0]


def exact_verify(period: int, radix: int, coeffs: dict[int, Fraction]) -> dict[str, Any]:
    """Verify a full period plus balance; not a sampled or floating check."""
    if period < 2 or not 2 <= radix <= period:
        raise ValueError('Require period >= radix >= 2')
    if not coeffs or any(j < 1 or period % j for j in coeffs):
        raise ValueError('Every denominator must divide the period')
    balance = sum((a / j for j, a in coeffs.items()), Fraction(0))
    if balance != 0:
        raise ValueError(f'Nonzero slope: {balance}')
    scale = math.lcm(*(a.denominator for a in coeffs.values()))
    numerators = {j: int(a * scale) for j, a in coeffs.items()}
    margins = []
    for r in range(period):
        value = sum(a * (r // j) for j, a in numerators.items())
        required = scale if 1 <= r < radix else 0
        if value < required:
            raise ValueError(f'Failed exact constraint at r={r}: {value}/{scale}')
        margins.append(value - required)
    return {'exact_feasible': True, 'balance': '0', 'period_residues_checked': period,
            'integer_scale': scale, 'minimum_scaled_margin': min(margins)}


def search(period: int, radix: int) -> dict[str, Any]:
    import numpy as np
    from scipy.optimize import linprog
    div = divisors(period)
    matrix = np.arange(period, dtype=np.int64)[:, None] // np.array(div)[None, :]
    required = np.zeros(period)
    required[1:radix] = 1
    objective = -np.log(div) / np.array(div) / (1 - 1 / radix)
    result = linprog(objective, A_ub=-matrix.astype(float), b_ub=-required,
                     A_eq=[1 / np.array(div)], b_eq=[0],
                     bounds=[(None, None)] * len(div), method='highs')
    if not result.success:
        raise RuntimeError(f'LP failed for {(period, radix)}: {result.message}')
    coeffs = {j: Fraction(float(a)).limit_denominator(1_000_000)
              for j, a in zip(div, result.x)}
    coeffs = {j: a for j, a in coeffs.items() if a}
    checked = exact_verify(period, radix, coeffs)
    constant = -sum(float(a) * math.log(j) / j for j, a in coeffs.items()) / (1 - 1 / radix)
    return {'period': period, 'radix': radix,
            'coefficients': {str(j): str(a) for j, a in coeffs.items()},
            'leading_constant_float': constant,
            'coefficient_l1': str(sum(map(abs, coeffs.values()), Fraction(0))),
            'optimizer_status': result.message, **checked}


def lifted_coefficients(N: int, radix: int, seed: dict[int, Fraction]) -> dict[int, Fraction]:
    if N < 1:
        raise ValueError('N must be positive')
    result: dict[int, Fraction] = {}
    power = 1
    while power <= N:
        for j, a in seed.items():
            result[j * power] = result.get(j * power, Fraction(0)) + a
        power *= radix
    return {j: a for j, a in result.items() if a}


def exact_finite_checks(record: dict[str, Any]) -> dict[str, Any]:
    """Supplement the general proof with complete finite staircase checks."""
    seed = {int(j): Fraction(a) for j, a in record['coefficients'].items()}
    rows = []
    for N in (30, 100, 1000, 10000):
        coeffs = lifted_coefficients(N, record['radix'], seed)
        scale = math.lcm(*(a.denominator for a in coeffs.values()))
        nums = {j: int(a * scale) for j, a in coeffs.items() if j <= N}
        minimum = min(sum(a * (t // j) for j, a in nums.items())
                      for t in range(1, N + 1))
        if minimum < scale:
            raise AssertionError('Lifted certificate failed')
        rows.append({'N': N, 'all_staircase_constraints_exact': True,
                     'minimum_staircase': str(Fraction(minimum, scale)),
                     'log_factorial_upper_bound_float': sum(float(a) * math.lgamma(N // j + 1)
                                                           for j, a in coeffs.items())})
    # Independent prime-exponent check of the factorial identity, without logs.
    N = 100
    coeffs = lifted_coefficients(N, record['radix'], seed)
    primes = [p for p in range(2, N + 1)
              if all(p % d for d in range(2, math.isqrt(p) + 1))]
    for p in primes:
        left = Fraction(0)
        for j, a in coeffs.items():
            m, val = N // j, 0
            while m:
                m //= p
                val += m
            left += a * val
        right, power = Fraction(0), p
        while power <= N:
            right += sum((a * (N // (j * power)) for j, a in coeffs.items()), Fraction(0))
            power *= p
        if left != right:
            raise AssertionError('Prime-exponent identity failed')
    return {'finite_staircase_checks': rows, 'prime_exponent_identity_checks': len(primes)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('results.json'))
    args = parser.parse_args()
    start = time.perf_counter()
    results, best = [], []
    for period in (30, 210, 2310):
        batch = [search(period, radix) for radix in range(2, 31)]
        results.extend(batch)
        selected = min(batch, key=lambda r: r['leading_constant_float'])
        selected = {**selected, **exact_finite_checks(selected)}
        best.append(selected)
    data = {'status': 'classical certificate-method pilot; no RH or novelty claim',
            'python': platform.python_version(), 'cases': results, 'best_in_numerical_search': best,
            'elapsed_seconds': time.perf_counter() - start,
            'limitations': ['No established LP optimality.',
                            'Exact checks establish feasibility, not novelty.',
                            'All resulting fixed-template bounds remain C*N + O(log^2 N), with C>1.',
                            'No improvement over modern prime-counting bounds or total CHHL error.']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    print(f'{len(results)} LP candidates independently checked with exact arithmetic.')
    for r in best:
        print(f"period={r['period']}, radix={r['radix']}, C={r['leading_constant_float']:.12f}, coefficients={r['coefficients']}")
    print(f'Wrote {args.output}; elapsed={data["elapsed_seconds"]:.3f}s')


if __name__ == '__main__':
    main()
