"""Exact finite checks for the overlap bounds in OVERLAP-BOUND.md.

Uses fractions only. The examples come from explicitly positive, even
Fourier profiles on [-1/2, 1/2]. This script proves no zeta asymptotic.
Run with the repository virtual environment; no third-party dependency.
"""

from collections import Counter
from fractions import Fraction as F
import json
from math import ceil
from pathlib import Path


def multiply(a, b):
    return [[sum((x*y for x, y in zip(row, column)), F(0))
             for column in zip(*b)] for row in a]


def is_psd(matrix):
    """Exact symmetric Schur-complement criterion, including singular cases."""
    if not matrix:
        return True
    n = len(matrix)
    assert all(matrix[i][j] == matrix[j][i]
               for i in range(n) for j in range(n))
    if any(matrix[i][i] < 0 for i in range(n)):
        return False
    pivot = next((i for i in range(n) if matrix[i][i] > 0), None)
    if pivot is None:
        return all(x == 0 for row in matrix for x in row)
    rest = [i for i in range(n) if i != pivot]
    return is_psd([
        [matrix[i][j]-matrix[i][pivot]*matrix[pivot][j]/matrix[pivot][pivot]
         for j in rest] for i in rest
    ])


def integer_kernel(difference, first=F(1, 2), third=F(0)):
    return {0: F(1), 1: first, 2: F(1, 8), 3: third}.get(
        abs(difference), F(0))


def check(name, points, first=F(1, 2), third=F(0),
          alpha=F(1), beta=F(3), expected_simple=None):
    # p=3/4+2 first*c+c^2/2+2 third*cos(6 pi u).
    # Complete the square for a valid global lower bound.
    profile_lower = F(3, 4)-2*first**2-2*abs(third)
    assert abs(first) <= F(1, 2) and profile_lower > 0
    mult = Counter(points)
    locations = sorted(mult)
    counts = [mult[x] for x in locations]
    rank = len(locations)
    n = len(points)
    simple = sum(m == 1 for m in counts)
    if expected_simple is not None:
        assert simple == expected_simple
    gram = [[integer_kernel(x-y, first, third) for y in points] for x in points]
    distinct = [[integer_kernel(x-y, first, third) for y in locations]
                for x in locations]
    # Congruence by diag(1/sqrt(m)) turns H-alpha I and beta I-H
    # into these rational matrices, avoiding square roots entirely.
    lower = [[distinct[i][j]-(alpha/counts[i] if i == j else 0)
              for j in range(rank)] for i in range(rank)]
    upper = [[(beta/counts[i] if i == j else 0)-distinct[i][j]
              for j in range(rank)] for i in range(rank)]
    assert alpha > 0 and beta < 4 and is_psd(lower) and is_psd(upper)
    gram2 = multiply(gram, gram)
    m2 = sum(gram2[i][i] for i in range(n))
    row_energy = [sum(x*x for x in row) for row in gram]
    assert m2 == sum(row_energy)
    star = sum(x*x for x in row_energy)
    fourth = sum(x**4 for row in gram for x in row)
    harmonic = sum((F(1, m) for m in counts), F(0))
    assert harmonic == F(simple, 3)+F(5*rank-n, 6)
    a, b = alpha+beta, alpha*beta
    bound = 3*star/b**2-(3*a*a/b**2-F(1, 2))*n+(6*a/b-F(5, 2))*rank
    assert star <= a*a*n-2*a*b*rank+b*b*harmonic
    assert ceil(bound) <= simple
    result = {
        "name": name, "N": n, "R": rank, "simple": simple,
        "profile_lower": str(profile_lower), "band": [str(alpha), str(beta)],
        "M2": str(m2), "S": str(star), "Q": str(fourth),
        "pair_bound": str(2*n-m2), "perturbed_band_bound": str(bound),
        "perturbed_band_ceiling": ceil(bound),
    }
    if alpha == 1 and beta == 3:
        star_joint = star/3-F(3, 2)*m2+F(7, 6)*n+rank
        fourth_joint = (4*fourth-m2-15*n+18*rank)/6
        assert star_joint >= bound
        assert star_joint-bound == F(3, 2)*(4*n-3*rank-m2)
        assert ceil(star_joint) <= simple and ceil(fourth_joint) <= simple
        result.update({"S_M2_bound": str(star_joint),
                       "Q_M2_bound": str(fourth_joint)})
        if multiply(gram2, gram) == [
                [4*gram2[i][j]-3*gram[i][j] for j in range(n)]
                for i in range(n)]:
            assert simple == star/3-F(29, 6)*n+F(11, 2)*rank
            result["endpoint_spectrum_identity"] = True
    return result


def main():
    triple = [0, 0, 0, 3, 6]
    pairs = [0, 0, 1, 1, 4]
    results = [
        check("triple and two singles", triple, expected_simple=2),
        check("two doubletons and one single", pairs, expected_simple=1),
        check("interior spectrum", pairs, first=F(2, 5), expected_simple=1),
        check("isolated doubleton", [0, 0, 3], expected_simple=1),
        check("three singles", [0, 3, 6], expected_simple=3),
        check("two triples", [0, 0, 0, 3, 3, 3], expected_simple=0),
        check("perturbed triple", triple, third=F(1, 200),
              alpha=F(49, 50), beta=F(151, 50), expected_simple=2),
    ]
    assert results[0]["M2"] == results[1]["M2"] == "11"
    assert results[0]["S"] == "29" and results[0]["Q"] == "11"
    assert results[1]["S"] == "26" and results[1]["Q"] == "19/2"
    assert results[-1]["perturbed_band_ceiling"] == 2
    # Exact block family: the separation makes every cross-block kernel zero.
    for k in range(1, 5):
        for number_triples in range(k+1):
            points = [x+10*j for j in range(k)
                      for x in (triple if j < number_triples else pairs)]
            checked = check(f"{k} blocks, {number_triples} triple blocks", points,
                            expected_simple=k+number_triples)
            assert F(checked["S"]) == 26*k+3*number_triples
            assert F(checked["Q"]) == F(19*k+3*number_triples, 2)
            assert F(checked["S_M2_bound"]) == k+number_triples
            assert F(checked["Q_M2_bound"]) == k+number_triples
            results.append(checked)
    result = {"arithmetic": "exact rational",
              "scope": "finite Fourier examples; no zeta asymptotic",
              "checks": results}
    Path(__file__).with_name('overlap_bound_results.json').write_text(
        json.dumps(result, indent=2)+'\n')
    print(json.dumps({'exact_checks': len(results),
                      'example_S_bounds': [results[0]['S_M2_bound'], results[1]['S_M2_bound']],
                      'perturbed_bound_ceiling': results[6]['perturbed_band_ceiling']}, indent=2))


if __name__ == "__main__":
    main()
