"""Exact controls for scale-dependent paid costs, not a growth-rate proof."""

from fractions import Fraction as F
import importlib.util
from math import isqrt
from pathlib import Path

import pytest


PATH = Path(__file__).resolve().parents[1] / "hunts/paid_shortfall_scaling/scaling.py"
SPEC = importlib.util.spec_from_file_location("paid_scaling", PATH)
S = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(S)


def test_sieve_matches_independent_factorization():
    _, mu, primes = S.sieve(512)
    assert mu[1] == 1
    for n in range(2, 513):
        factors = S.BASE.trial_factors(n)
        expected = 0 if any(e > 1 for _, e in factors) else (-1) ** len(factors)
        assert mu[n] == expected
        assert (n in primes) == (factors == ((n, 1),))


def test_prefix_balance_coverage_and_mass():
    for y in range(2, 65):
        c = S.balanced_prefix(y)
        assert sum((a / j for j, a in c.items()), F(0)) == 0
        assert sum(map(abs, c.values()), F(0)) <= 2 * y - 1
        assert all(S.BASE.floor_sum(c, q) == 1 for q in range(1, y))
        for q in (y, y + 1, y * y, y * y + 1):
            assert abs(S.BASE.floor_sum(c, q)) <= sum(map(abs, c.values()), F(0))


def test_average_formula_including_smallest_support():
    for y in range(2, 25):
        a = max(2, (y + 1) // 2)
        actual = S.averaged_prefix(y)
        expected = S.BASE.combine(*((F(1, y - a + 1), S.balanced_prefix(h)) for h in range(a, y + 1)))
        assert actual == expected
        assert sum(map(abs, actual.values()), F(0)) <= a + y - 1
        assert sum((v / j for j, v in actual.items()), F(0)) == 0
        assert all(S.BASE.floor_sum(actual, q) == 1 for q in range(1, a))


def test_exact_cap_mass_and_square_extraction():
    assert S.exact_cap_checks(512) == 513
    assert [S.exponent_coefficient(k) for k in range(2, 13)] == [1, 2, 1, 4, -2, 6, 1, 2, -4, 10, -2]
    for N in range(4):
        assert S.cap_mass_vector(N) == {}
    for r in range(2, 40):
        assert sum((F(S.exponent_coefficient(k), k) for k in range(2, r + 1) if r % k == 0), F(0)) == 1 - F(1, r)


@pytest.mark.parametrize("backend", ["python-flint", "mpmath.iv"])
def test_explicit_cap_constant_eight(backend):
    pytest.importorskip("flint" if backend == "python-flint" else "mpmath")
    with S.BASE.log_intervals(backend, 70) as log:
        for root in (2, 3, 4, 5, 8, 10, 16):
            N = root**3
            square = dict(S.BASE.factorial_vector_items(isqrt(N)))
            error = S.BASE.combine((8 * root, S.BASE.log_vector(N)), (1, square), (-1, S.cap_mass_vector(N)))
            assert S.BASE.enclose_expression(0, error, log)[0] >= 0


@pytest.mark.parametrize("cap", ["raw", "perfect_power"])
def test_exact_averaging_discount(cap):
    for y in (2, 4, 6, 8, 12):
        a = max(2, (y + 1) // 2)
        S.averaging_identity(y * y, [S.balanced_prefix(h) for h in range(a, y + 1)], cap)
    assert S.averaging_identity(14, [{1: F(0)}, {1: F(2)}], cap)
    assert not S.averaging_identity(14, [{1: F(2)}, {1: F(3)}], cap)


def test_complete_excess_localizes_without_large_integer_weights():
    for N in (4, 14, 36, 64, 144, 576):
        _, _, primes = S.sieve(N)
        for h in (2, max(2, isqrt(N))):
            case = S.cost_case(N, S.balanced_prefix(h), primes)
            assert S.prefix_excess(N, h) == case["excess_over_psi"]["perfect_power"]
            bound = S.BASE.combine((case["max_deficit"], S.cap_mass_vector(N // h)), (-1, case["cap_saving"]))
            assert S.BASE.nonnegative_coefficients(bound)
            penalty_bound = S.BASE.combine((case["max_deficit"], dict(S.BASE.factorial_vector_items(N // h))),
                                          (-1, case["penalties"]["perfect_power"]))
            assert S.BASE.nonnegative_coefficients(penalty_bound)


@pytest.mark.parametrize("N,y,winner", [(4, 2, 2), (144, 12, 12), (576, 24, 18)])
def test_bounded_cutoff_selection(N, y, winner):
    pytest.importorskip("flint")
    actual, excess, count, comparisons = S.select_prefix(N, y)
    assert actual == winner
    assert excess == S.prefix_excess(N, winner)
    assert count == y - max(2, (y + 1) // 2) + 1
    assert comparisons == 4 * count


@pytest.mark.parametrize("y", [0, 1, -1, 2.5])
def test_undefined_prefix_rejected(y):
    with pytest.raises(ValueError):
        S.balanced_prefix(y)
    with pytest.raises(ValueError):
        S.averaged_prefix(y)
    with pytest.raises(ValueError):
        S.select_prefix(144, y)
