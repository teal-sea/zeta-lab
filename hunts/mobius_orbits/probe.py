"""Exact finite checks of Mobius orbit and level-set identities, not RH."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd, isqrt, log
from pathlib import Path
from time import perf_counter


def mobius_sieve(limit: int) -> list[int]:
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if prime[p]:
            for j in range(p, limit + 1, p):
                prime[j] = False
                mu[j] *= -1
            for j in range(p * p, limit + 1, p * p):
                mu[j] = 0
    return mu


def trial_mu(n: int) -> int:
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        while n % p == 0:
            n //= p
        p += 1
    return -sign if n > 1 else sign


def signed_divisors(P: int) -> list[tuple[int, int]]:
    if P <= 1 or trial_mu(P) == 0:
        raise ValueError('P must be squarefree and greater than one')
    return [(d, trial_mu(d)) for d in range(1, P + 1) if P % d == 0]


def rough_count(x: int, divisors: list[tuple[int, int]]) -> int:
    return sum(sign * (x // d) for d, sign in divisors)


def check_case(N: int, P: int, mu: list[int], mertens: list[int]) -> dict:
    half = N // 2
    U = isqrt(half)
    divisors = signed_divisors(P)
    upper = half // 2
    E = max((Fraction(abs(mertens[t]), t) for t in range(U, upper + 1)), default=Fraction(0))
    signed_total = complete_total = boundary_total = majorant = baseline = level_bound = 0.0
    counts = {'b_rows': 0, 'complete_orbits': 0, 'incomplete_orbits': 0}
    missing_boundary = wrong_sign = None
    for b in range(2, U + 1):
        V = half // b
        direct = sum(mu[a] * (1 - N // (a * b)) for a in range(U + 1, V + 1))
        full = boundary = 0
        bound = Fraction(0)
        for m in range(1, V + 1):
            if gcd(m, P) != 1:
                continue
            active = [(d, sign) for d, sign in divisors if U < d * m <= V]
            if not active:
                continue
            kernel = sum(sign * (1 - N // (d * m * b)) for d, sign in active)
            if U < m and P * m <= V:
                phi = rough_count(N // (m * b), divisors)
                assert kernel == -phi
                full += mu[m] * kernel
                bound += phi  # explicitly discards abs(mu(m)) <= 1
                counts['complete_orbits'] += 1
            else:
                boundary += mu[m] * kernel
                bound += sum((Fraction(N, d * m * b) for d, _ in active), Fraction(0))
                counts['incomplete_orbits'] += 1
        assert direct == full + boundary, (N, P, b, direct, full, boundary)
        assert abs(direct) <= bound
        Q = N // (b * (U + 1))
        levels = -sum(mertens[N // (b * k)] - mertens[U] for k in range(2, Q + 1))
        assert levels == direct, (N, b, direct, levels)
        envelope = Fraction(2 * N, b) * E * sum((Fraction(1, k) for k in range(2, Q + 1)), Fraction(0))
        assert abs(direct) <= envelope
        if boundary and missing_boundary is None:
            missing_boundary = {'N': N, 'P': P, 'b': b, 'defect': boundary}
        if full and wrong_sign is None:
            wrong_sign = {'N': N, 'P': P, 'b': b, 'defect': 2 * full}
        counts['b_rows'] += 1
        lb = log(b)
        signed_total += direct * lb
        complete_total += full * lb
        boundary_total += boundary * lb
        majorant += float(bound) * lb
        baseline += float(sum((Fraction(N, a * b) for a in range(U + 1, V + 1)), Fraction(0))) * lb
        level_bound += float(envelope) * lb
    c = Fraction(sum(gcd(j, P) == 1 for j in range(1, P + 1)), P)
    return {'N': N, 'P': P, **counts, 'exact_defect': 0,
            'finite_mertens_envelope': str(E),
            'float_diagnostics': {'sigma2': signed_total, 'complete': complete_total,
                'boundary': boundary_total, 'orbit_majorant': majorant,
                'unpaired_majorant': baseline, 'orbit_to_unpaired': majorant / baseline if baseline else None,
                'finite_level_bound': level_bound},
            'proposed_fixed_P_leading_coefficient': str(c * c / 48),
            'missing_boundary_lesion': missing_boundary, 'wrong_complete_sign_lesion': wrong_sign}


def run(max_n: int, large: list[int]) -> dict:
    start = perf_counter()
    Ns = sorted(set(range(4, max_n + 1)) | set(large))
    limit = max(Ns) // 2
    mu = mobius_sieve(limit)
    assert all(mu[n] == trial_mu(n) for n in range(1, limit + 1))
    mertens = [0]
    for val in mu[1:]:
        mertens.append(mertens[-1] + val)
    Ps = [2, 6, 30, 210]
    for P in Ps:
        ds = signed_divisors(P)
        assert sum(sign for _, sign in ds) == 0
        for x in range(1001):
            assert rough_count(x, ds) == sum(gcd(j, P) == 1 for j in range(1, x + 1))
    rows = [check_case(N, P, mu, mertens) for N in Ns for P in Ps]
    boundary_lesion = next((r['missing_boundary_lesion'] for r in rows if r['missing_boundary_lesion']), None)
    sign_lesion = next((r['wrong_complete_sign_lesion'] for r in rows if r['wrong_complete_sign_lesion']), None)
    assert boundary_lesion is not None
    assert sign_lesion is not None
    return {'status': 'finite exact checks passed; RH not established',
            'range': {'consecutive_N': [4, max_n], 'extra_N': large, 'P': Ps},
            'case_count': len(rows), 'exact_b_row_count': sum(r['b_rows'] for r in rows),
            'mobius_independent_checks': limit, 'coprime_count_checks': len(Ps) * 1001,
            'lesions_detected': {'missing_boundary': boundary_lesion, 'wrong_complete_sign': sign_lesion},
            'exact_max_defect': max(r['exact_defect'] for r in rows),
            'rows': rows, 'elapsed_seconds': perf_counter() - start,
            'limits': ['integer identities only on the listed finite range',
                       'log-weighted totals use ordinary binary floating point',
                       'asymptotic coefficient is a prediction of the handwritten argument, not inferred from the scan',
                       'finite Mertens envelope is not an all-scale decay bound',
                       'no proof or disproof of RH, and no novelty claim']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=300)
    parser.add_argument('--large', type=int, nargs='*', default=[1000, 10000])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.max_n < 100 or any(n < 4 or n > 100000 for n in args.large):
        parser.error('use max-n >= 100 and extra N in [4, 100000]')
    if args.max_n > 1000:
        parser.error('consecutive range capped at 1000 for local compute')
    result = run(args.max_n, args.large)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))
    print('Last case:', json.dumps(result['rows'][-1]))
