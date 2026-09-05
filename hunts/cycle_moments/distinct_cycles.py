"""Exact repeated-index bookkeeping for weighted triangles and four-cycles.

Compare direct enumeration, partition-lattice inversion, and reduced trace
formulas. Indices label occurrences, even when their feature vectors coincide.
"""

from fractions import Fraction as F
from itertools import product
from math import factorial, prod
import json
from pathlib import Path


def partitions(size):
    """Canonical set partitions, generated independently of the trace formulas."""
    if size == 0:
        yield ()
        return
    for previous in partitions(size - 1):
        for index in range(len(previous)):
            yield previous[:index] + (previous[index] + (size-1,),) + previous[index+1:]
        yield previous + ((size-1,),)


def mobius(partition):
    return prod((-1)**(len(block)-1)*factorial(len(block)-1)
                for block in partition)


def cycle(kernel, indices):
    return prod(kernel[indices[j]][indices[(j+1) % len(indices)]]
                for j in range(len(indices)))


def unrestricted_on_partition(kernel, partition):
    degree = sum(map(len, partition))
    answer = F(0)
    for labels in product(range(len(kernel)), repeat=len(partition)):
        indices = [0]*degree
        for label, block in zip(labels, partition):
            for position in block:
                indices[position] = label
        answer += cycle(kernel, indices)
    return answer


def matrix_multiply(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(a)))
             for j in range(len(a))] for i in range(len(a))]


def check(kernel):
    n = len(kernel)
    assert all(kernel[i][i] == 1 for i in range(n))
    assert all(kernel[i][j] == kernel[j][i] for i in range(n) for j in range(n))
    power = kernel
    moments = {1: F(n)}
    for degree in [2, 3, 4]:
        power = matrix_multiply(power, kernel)
        moments[degree] = sum(power[i][i] for i in range(n))
    star = sum(sum(value**2 for value in row)**2 for row in kernel)
    entry_fourth = sum(value**4 for row in kernel for value in row)
    reduced = {
        3: moments[3]-3*moments[2]+2*n,
        4: moments[4]-4*moments[3]+10*moments[2]-2*star+entry_fourth-6*n,
    }
    results = {}
    for degree in [3, 4]:
        direct = sum(cycle(kernel, indices)
                     for indices in product(range(n), repeat=degree)
                     if len(set(indices)) == degree)
        inverted = sum(mobius(p)*unrestricted_on_partition(kernel, p)
                       for p in partitions(degree))
        assert direct == inverted == reduced[degree]
        wrong = (moments[3]-3*moments[2]+n if degree == 3 else
                 moments[4]-6*moments[3]+11*moments[2]-6*n)
        results[str(degree)] = {
            'direct_distinct_sum': str(direct),
            'partition_inversion': str(inverted),
            'reduced_formula': str(reduced[degree]),
            'deliberately_wrong_simplification': str(wrong),
            'wrong_minus_exact': str(wrong-direct),
        }
    return {'size': n, 'moments': {str(k): str(v) for k, v in moments.items()},
            'star_sum': str(star), 'entry_fourth_sum': str(entry_fourth),
            'identities': results}


def main():
    vectors = [(F(1), F(0)), (F(3,5), F(4,5)), (F(0), F(1)),
               (F(-3,5), F(4,5)), (F(1), F(0))]
    gram = [[sum(x*y for x, y in zip(v, w)) for w in vectors] for v in vectors]
    generic = check(gram)
    # The tempting scalar falling-factorial formula passes this control,
    # but fails for the nonconstant weighted cycles above.
    constant = check([[F(1)]*5 for _ in range(5)])
    assert generic['identities']['4']['wrong_minus_exact'] != '0'
    assert constant['identities']['4']['wrong_minus_exact'] == '0'
    assert generic['identities']['3']['wrong_minus_exact'] == '-5'
    frames = []
    for c, s in [(F(3,5), F(4,5)), (F(5,13), F(12,13))]:
        assert c*c+s*s == 1
        frame = [(F(1), F(0)), (F(0), F(1)), (c, s), (-s, c)]
        kernel = [[sum(x*y for x, y in zip(v, w)) for w in frame] for v in frame]
        # This identity pins every power trace, not only the first four:
        # K^j=2^(j-1)K for j>=1, by induction.
        assert matrix_multiply(kernel, kernel) == [[2*x for x in row] for row in kernel]
        checked = check(kernel)
        fourth = F(checked['identities']['4']['direct_distinct_sum'])
        assert fourth == -8*c*c*s*s
        frames.append({'cosine': str(c), 'sine': str(s), 'checks': checked})
    assert frames[0]['checks']['moments'] == frames[1]['checks']['moments']
    assert (frames[0]['checks']['identities']['4']['direct_distinct_sum'] !=
            frames[1]['checks']['identities']['4']['direct_distinct_sum'])
    output = {'status': 'exact finite identities, no new zeta bound',
              'weighted_gram_with_repeated_vector': generic,
              'constant_kernel_control': constant,
              'isospectral_frames_with_different_distinct_fourth_cycles': frames,
              'mobius_coefficients': {
                  str(n): [{'blocks': p, 'coefficient': mobius(p)} for p in partitions(n)]
                  for n in [3, 4]}}
    Path(__file__).with_name('distinct_cycle_results.json').write_text(
        json.dumps(output, indent=2)+'\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'mobius_coefficients'}, indent=2))


if __name__ == '__main__':
    main()
