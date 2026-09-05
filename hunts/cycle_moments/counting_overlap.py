"""Exact same-kernel spectra with different simple-point counts.

Matrix checks use integer Fourier coefficients and Fraction arithmetic. The
complete moment sequence follows from the checked recurrence K^3=4K^2-3K.
Independent quadrature checks the Fourier coefficients at 60 decimal digits.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
import json
from pathlib import Path

from mpmath import mp


def matrix_mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def matrix_trace(a):
    return sum((a[i][i] for i in range(len(a))), F(0))


def kernel_integer(n):
    return {0: F(1), 1: F(1, 2), 2: F(1, 8)}.get(abs(n), F(0))


def gram(points):
    return [[kernel_integer(x-y) for y in points] for x in points]


def cycle_sum(k, degree, distinct):
    tuples = (permutations(range(len(k)), degree) if distinct
              else product(range(len(k)), repeat=degree))
    answer = F(0)
    for indices in tuples:
        term = F(1)
        for j in range(degree):
            term *= k[indices[j]][indices[(j+1) % degree]]
        answer += term
    return answer


def check_example(points, expected_simple, expected_s, expected_q, expected_d4):
    k = gram(points)
    k2 = matrix_mul(k, k)
    k3 = matrix_mul(k2, k)
    # Matrix identity, not a finite sample of scalar moment equalities.
    assert k3 == [[4*k2[i][j]-3*k[i][j] for j in range(5)] for i in range(5)]
    assert matrix_trace(k) == 5
    assert matrix_trace(k2) == 11
    power = k
    moments = []
    for degree in range(1, 9):
        value = matrix_trace(power)
        assert value == 3**degree+2
        if degree <= 4:
            assert cycle_sum(k, degree, distinct=False) == value
        moments.append(value)
        power = matrix_mul(power, k)
    overlap_s = sum((sum((x*x for x in row), F(0))**2 for row in k), F(0))
    overlap_q = sum((x**4 for row in k for x in row), F(0))
    d3 = cycle_sum(k, 3, distinct=True)
    d4 = cycle_sum(k, 4, distinct=True)
    assert d3 == 6
    assert overlap_s == expected_s
    assert overlap_q == expected_q
    assert d4 == expected_d4
    assert d4 == moments[3]-4*moments[2]-2*overlap_s+10*moments[1]+overlap_q-30
    counts = Counter(points)
    simple = sum(mult == 1 for mult in counts.values())
    assert simple == expected_simple
    assert (overlap_q == moments[1]) == (simple == 2)
    return {
        'points_with_multiplicity': list(points),
        'multiplicities': list(counts.values()),
        'simple_real_count': simple,
        'nonzero_spectrum': [3, 1, 1],
        'zero_eigenvalues_in_occurrence_gram': 2,
        'all_moments_formula': 'M_j = 3^j + 2 for every integer j >= 1',
        'matrix_recurrence_checked': 'K^3 = 4 K^2 - 3 K',
        'moments_1_through_8': list(map(str, moments)),
        'S': str(overlap_s), 'Q': str(overlap_q),
        'D3': str(d3), 'D4': str(d4),
        'gram': [[str(x) for x in row] for row in k],
    }


def check_amplification(blocks, type_a):
    points = tuple(10*j+x for j in range(blocks)
                   for x in ((0, 0, 0, 3, 6) if j < type_a else (0, 0, 1, 1, 4)))
    k = gram(points)
    for i, row in enumerate(k):
        for j, value in enumerate(row):
            if i//5 != j//5:
                assert value == 0
    overlap_s = sum((sum((x*x for x in row), F(0))**2 for row in k), F(0))
    overlap_q = sum((x**4 for row in k for x in row), F(0))
    simple = sum(mult == 1 for mult in Counter(points).values())
    assert simple == blocks+type_a
    assert overlap_s == 26*blocks+3*type_a
    assert overlap_q == F(19*blocks+3*type_a, 2)
    assert simple == (overlap_s-23*blocks)/3
    power = k
    for degree in range(1, 5):
        assert matrix_trace(power) == blocks*(3**degree+2)
        power = matrix_mul(power, k)
    expected_d4 = F(9, 2)*(blocks-type_a)
    if blocks <= 2:
        assert cycle_sum(k, 4, distinct=True) == expected_d4
    return {'blocks': blocks, 'type_a': type_a, 'simple_real_count': simple,
            'S': str(overlap_s), 'Q': str(overlap_q), 'D4': str(expected_d4)}


def check_fourier_coefficients():
    with mp.workdps(60):
        def density(u):
            return 1+mp.cos(2*mp.pi*u)+mp.cos(4*mp.pi*u)/4

        defects = {}
        for difference in range(27):
            observed = mp.quad(
                lambda u: density(u)*mp.cos(2*mp.pi*difference*u),
                [mp.mpf(-1)/2, 0, mp.mpf(1)/2],
            )
            rational = kernel_integer(difference)
            expected = mp.mpf(rational.numerator)/rational.denominator
            defect = abs(observed-expected)
            assert defect < mp.mpf('1e-50')
            defects[str(difference)] = mp.nstr(defect, 12)
    return {'decimal_precision': 60, 'fourier_coefficient_defects': defects}


def main():
    # p(u)=1+x+(1/4)(2x^2-1)=1/4+(1/2)(1+x)^2, x=cos(2pi u).
    lhs_coefficients = [F(1)-F(1, 4), F(1), F(1, 2)]
    rhs_coefficients = [F(1, 4)+F(1, 2), F(1), F(1, 2)]
    assert lhs_coefficients == rhs_coefficients
    first = check_example((0, 0, 0, 3, 6), 2, F(29), F(11), F(0))
    second = check_example((0, 0, 1, 1, 4), 1, F(26), F(19, 2), F(9, 2))
    assert first['moments_1_through_8'] == second['moments_1_through_8']
    assert first['simple_real_count'] != second['simple_real_count']
    amplifications = [check_amplification(h, t) for h in range(1, 4)
                      for t in range(h+1)]
    result = {
        'status': 'exact finite counting distinction; no zeta asymptotic claim',
        'arithmetic': 'exact rational matrix checks; separate numerical Fourier quadrature',
        'density': '1+cos(2pi u)+(1/4)cos(4pi u) on [-1/2,1/2], zero outside',
        'density_lower_bound_on_support': '1/4',
        'examples': [first, second],
        'amplification_checks': amplifications,
        'independent_quadrature': check_fourier_coefficients(),
    }
    Path(__file__).with_name('counting_overlap_results.json').write_text(
        json.dumps(result, indent=2)+'\n')
    print(json.dumps({'simple_counts': [first['simple_real_count'], second['simple_real_count']],
                      'common_positive_power_traces': '3^j+2',
                      'amplification_checks': len(amplifications),
                      'independent_fourier_checks': 27}, indent=2))


if __name__ == '__main__':
    main()
