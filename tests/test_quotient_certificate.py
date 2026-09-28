"""Independent arithmetic checks for the quotient-certificate investigation."""
from fractions import Fraction
import importlib.util
import json
import math
from pathlib import Path

from mpmath import mp
import pytest
from sympy import Matrix, factorint


HUNT = Path(__file__).resolve().parents[1] / "hunts/quotient_certificate"
SPEC = importlib.util.spec_from_file_location("quotient_certificate_probe", HUNT / "probe.py")
probe = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(probe)


def test_quotient_enumeration_matches_every_integer_argument():
    for N in range(2, 501):
        assert probe.quotient_cells(N) == sorted({N // d for d in range(2, N + 1)})


def test_rounding_repair_recovers_a_planted_violation():
    nums, delta = probe.repair([0.999, -0.501], [1, 2, 3], 1000)
    assert delta > 0
    assert all(sum(a * (n // j) for j, a in enumerate(nums, 1)) >= 1000
               for n in (1, 2, 3))
    with pytest.raises(ValueError):
        probe.repair([1], [], 1000)


def test_stored_bounds_are_feasible_and_have_independent_prime_excess():
    data = json.loads((HUNT / "results.json").read_text())
    assert data["status"] == "complete"
    assert data["completed"] == data["requested"] == len(data["results"]) == 3
    assert [row["N"] for row in data["results"]] == [1000, 10000, 100000]
    expected = [41.28216944, 226.83268961, 1035.23393430]
    for row, target in zip(data["results"], expected):
        N, D, nums = row["N"], row["denominator"], row["coefficient_numerators"]
        # Python integers avoid overflow and do not reuse the probe's cell generator.
        cells = {N // d for d in range(2, N + 1)}
        heights = {n: sum(a * (n // j) for j, a in enumerate(nums, 1)) for n in cells}
        assert len(cells) == row["cells_checked"]
        assert min(heights.values()) >= D
        value = row["evaluations"][-1]
        assert abs(float(value["excess"]) - target) < 1e-4
        assert row["lp_dual_equation_residual_measured"] < 1e-6
        assert row["lp_dual_min_measured"] >= -1e-9
        # Factor each d independently in the small case, rather than using a sieve.
        if N == 1000:
            with mp.workdps(70):
                direct = mp.mpf(0)
                for d in range(2, N + 1):
                    factors = factorint(d)
                    if len(factors) == 1:
                        p = int(next(iter(factors)))
                        direct += mp.log(p) * (heights[N // d] - D) / D
                assert abs(direct - mp.mpf(value["excess"])) < mp.mpf("1e-60")


def test_prime_cell_dimension_count_has_exact_log2_counterexample():
    N, y = 27, 9
    cells = set(range(1, math.isqrt(N) + 1))
    weights = {}
    for d in range(2, N + 1):
        factors = factorint(d)
        if len(factors) == 1:
            p = int(next(iter(factors)))
            n = N // d
            cells.add(n)
            weights[n] = weights.get(n, 1) * p
    assert sorted(cells) == [1, 2, 3, 4, 5, 6, 9, 13]
    rows = {n: [n // j for j in range(1, y + 1)] for n in cells}
    assert y > len(cells)
    assert Matrix([rows[n] for n in sorted(cells)]).rank() == 7
    relation = {1: -1, 3: 1, 6: -1, 9: -1, 13: 1}
    assert all(sum(sign * rows[n][j] for n, sign in relation.items()) == 0
               for j in range(y))
    assert sum(relation.values()) == -1
    # The relation forces e_3 + e_13 >= 1; both weights are at least log(2).
    assert weights[3] == 42 and weights[13] == 2
    c = [1, -1, -1, 0, -1, 1, 0, 0, -1]
    slack = {n: sum(a * b for a, b in zip(c, rows[n])) - 1 for n in cells}
    assert slack == {n: int(n == 13) for n in cells}
    # This feasible witness attains the lower bound, so the gap is exactly log(2).
    assert math.prod(weight ** slack[n] for n, weight in weights.items()) == 2


def test_small_lp_reproduces_improvement_outside_the_all_cell_family():
    row = probe.solve(1000, 31)
    assert abs(float(row["evaluations"][-1]["excess"]) - 41.28216944) < 1e-6
    nums, D = row["coefficient_numerators"], row["denominator"]
    assert sum(a * (1000 // j) for j, a in enumerate(nums, 1)) < D


def test_integer_sawtooth_covariance_by_full_period_enumeration():
    for i in range(1, 21):
        for j in range(1, 21):
            period = math.lcm(i, j)
            actual = sum(
                (Fraction(n % i, i) - Fraction(i - 1, 2 * i)) *
                (Fraction(n % j, j) - Fraction(j - 1, 2 * j))
                for n in range(period)
            ) / period
            assert actual == Fraction(math.gcd(i, j)**2 - 1, 12 * i * j)


@pytest.mark.parametrize("primes", [(2, 3), (2, 3, 5), (2, 3, 5, 7), (2, 3, 5, 7, 11)])
def test_balanced_correlated_family_has_stated_variance(primes):
    c = {1: Fraction(1)}
    for p in primes:
        c.update({p * d: -v for d, v in list(c.items())})
    delta = math.prod(Fraction(p - 1, p) for p in primes)
    tau = len(c)
    c[1] -= delta
    assert sum(v / d for d, v in c.items()) == 0
    variance = sum(a * b * Fraction(math.gcd(i, j)**2 - 1, 12 * i * j)
                   for i, a in c.items() for j, b in c.items())
    assert 12 * variance == tau * delta - delta**2
    assert sum(v**2 for v in c.values()) == tau - 2 * delta + delta**2
