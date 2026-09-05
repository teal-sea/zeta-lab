"""Two isospectral point configurations for one positive Fourier density.

Exact rational matrices and independent Fourier quadrature check the example
in SAME-KERNEL-EXAMPLE.md. These are constructed points, not zeta zeros.
"""

from fractions import Fraction as F
import json
from pathlib import Path

from mpmath import mp

from distinct_cycles import check


def main():
    epsilon = F(1, 16)
    coefficients = {3: F(4,5), 4: F(3,5), 5: F(3,5), 6: F(-4,5),
                    21: F(12,13), 28: F(5,13), 35: F(5,13), 42: F(-12,13)}
    lower = 1-2*epsilon*sum(abs(value) for value in coefficients.values())
    assert lower == F(21,65) > 0
    configurations = []
    for c, s, marks in [(F(3,5), F(4,5), [0,1,4,6]),
                        (F(5,13), F(12,13), [0,7,28,42])]:
        matrix = [[F(1) if x == y else epsilon*coefficients.get(abs(x-y), F(0))
                   for y in marks] for x in marks]
        frame = [(F(1), F(0)), (F(0), F(1)), (c, s), (-s, c)]
        gram = [[sum(x*y for x, y in zip(v, w)) for w in frame] for v in frame]
        assert matrix == [[(1-epsilon)*int(i == j)+epsilon*gram[i][j]
                           for j in range(4)] for i in range(4)]
        result = check(matrix)
        distinct = F(result['identities']['4']['direct_distinct_sum'])
        assert distinct == -8*epsilon**4*c*c*s*s
        configurations.append({'points_for_rescaled_density': [2*x for x in marks],
                               'matrix_checks': result})
    first, second = [row['matrix_checks'] for row in configurations]
    assert first['moments'] == second['moments']
    assert first['identities']['4']['direct_distinct_sum'] == '-9/320000'
    assert second['identities']['4']['direct_distinct_sum'] == '-225/14623232'
    with mp.workdps(45):
        def real(value):
            return mp.mpf(value.numerator)/value.denominator
        def density(u):
            # q(u)=2p(2u) on [-1/4,1/4].
            return 2*(1+2*real(epsilon)*sum(real(value)*mp.cos(4*mp.pi*k*u)
                                           for k, value in coefficients.items()))
        defects = {}
        breaks = [mp.mpf(-1)/4+mp.mpf(j)/32 for j in range(17)]
        # Selected zero and nonzero coefficients, in both disjoint frequency sets.
        for d in [0, 1, 3, 6, 21, 28, 42]:
            observed = mp.quad(lambda u: density(u)*mp.cos(4*mp.pi*d*u), breaks)
            expected = F(1) if d == 0 else epsilon*coefficients.get(d, F(0))
            defect = abs(observed-real(expected))
            assert defect < mp.mpf('1e-35')
            defects[str(2*d)] = mp.nstr(defect, 12)
    result = {'status': 'exact constructed point configurations, not zeta zeros',
              'epsilon': str(epsilon), 'p_lower_bound_on_support': str(lower),
              'q_support': ['-1/4', '1/4'], 'q_lower_bound_on_support': str(2*lower),
              'common_eigenvalues': ['15/16', '15/16', '17/16', '17/16'],
              'configurations': configurations,
              'quadrature_decimal_precision': 45, 'fourier_quadrature_defects': defects}
    Path(__file__).with_name('same_kernel_results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'common_eigenvalues': result['common_eigenvalues'],
                      'distinct_fourth_cycles': [first['identities']['4']['direct_distinct_sum'],
                                                second['identities']['4']['direct_distinct_sum']],
                      'fourier_quadrature_defects': defects}, indent=2))


if __name__ == '__main__':
    main()
