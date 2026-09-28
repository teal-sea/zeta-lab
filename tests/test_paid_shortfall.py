"""Finite exact controls for the paid-shortfall construction, not an asymptotic proof."""

from fractions import Fraction as F
import importlib.util
from pathlib import Path

import pytest


SOURCE = Path(__file__).resolve().parents[1] / "hunts/paid_shortfall/construction.py"
SPEC = importlib.util.spec_from_file_location("paid_shortfall_construction", SOURCE)
construction = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(construction)


@pytest.mark.parametrize("seed,L,M", [(construction.BASE6, 6, 6), (construction.CHEBYSHEV30, 30, 6)])
def test_exact_seed_and_early_lift(seed, L, M):
    H = construction.validate_seed(seed, L, M)
    assert H >= 1
    for K in range(3):
        c = construction.early_lift(seed, L, M, K)
        for q in range(1, 1297):
            value = construction.floor_sum(c, q)
            assert value == sum(construction.floor_sum(seed, q // M**k) for k in range(K + 1))
            if q < M**(K + 1):
                assert value >= 1


@pytest.mark.parametrize("seed,L,M", [({}, 6, 6), ({1: 1}, 6, 6),
    ({1: -1, 2: 1, 3: 1, 6: 1}, 6, 6), ({1: 1, 4: -4}, 6, 6),
    ({1: 1.0, 2: -1, 3: -1, 6: -1}, 6, 6), (construction.BASE6, 6, 7)])
def test_invalid_seed_rejected(seed, L, M):
    with pytest.raises(ValueError):
        construction.validate_seed(seed, L, M)


def test_base6_residues_and_exact_deficit():
    assert [construction.floor_sum(construction.BASE6, q) for q in range(6)] == [0, 1, 1, 1, 1, 2]
    for K in range(3):
        c = construction.early_lift(construction.BASE6, 6, 6, K)
        R = 6**(K + 1)
        for q in range(1, 1297):
            assert max(0, 1 - construction.floor_sum(c, q)) == int(q % R == 0)


@pytest.mark.parametrize("n,r", [(1, 1), (2, 1), (4, 2), (8, 3), (9, 2), (12, 1),
    (36, 2), (64, 6), (1296, 4), (2**120, 120), (3**40, 40)])
def test_integer_perfect_powers(n, r):
    assert construction.perfect_power_exponent(n) == r
    if n > 1:
        a = construction.integer_root(n, r)
        assert a**r == n
    for k in (2, 3, 7):
        root = construction.integer_root(n, k)
        assert root**k <= n < (root + 1)**k


def test_perfect_power_cap_against_independent_factorization():
    for n in range(1, 1297):
        factors = construction.trial_factors(n)
        truth = {factors[0][0]: F(1)} if len(factors) == 1 else {}
        cap = construction.cap_vector(n, "perfect_power")
        assert construction.nonnegative_coefficients(construction.combine((1, cap), (-1, truth)))
        if truth:
            assert cap == truth
    assert construction.cap_vector(1, "perfect_power") == {}


def test_n14_exact_optima_and_dual():
    report = construction.verify_n14()
    assert report["original_excess"] == {2: F(1, 2)}
    assert report["refined_excess"] == {}
    assert report["W"] == {1: 1, 2: 1, 3: F(1, 2), 4: F(1, 2), 7: 1}
    assert report["factorial_moments_checked"] == 3
    assert report["cap_rows_checked"] == 5


def test_dropped_penalty_is_rejected():
    c = {1: F(1), 2: F(-1), 3: F(-3, 2)}
    cost = construction.paid_cost_vectors(14, c)
    assert cost["penalty"] == {2: F(1), 3: F(1, 2)}
    with pytest.raises(ValueError, match="paid cost"):
        construction.require_complete_cost(14, c, cost["factorial"])
    construction.require_complete_cost(14, c, cost["total"])


@pytest.mark.parametrize("backend", ["python-flint", "mpmath.iv"])
def test_interval_bounds_and_precision_restoration(backend):
    mp = pytest.importorskip("mpmath")
    if backend == "python-flint":
        flint = pytest.importorskip("flint")
        old_flint = flint.ctx.prec
    old_mp, old_iv = mp.mp.prec, mp.iv.prec
    cases = [(2, 2), (14, 0), (35, 1), (36, 1), (128, 2), (1296, 2)]
    try:
        mp.mp.prec, mp.iv.prec = 139, 137
        for seed, L in ((construction.BASE6, 6), (construction.CHEBYSHEV30, 30)):
            for N, K in cases:
                with construction.log_intervals(backend, 50) as logarithm:
                    for _, a, v in construction.bound_assertions(seed, L, 6, N, K):
                        lo, hi = construction.enclose_expression(a, v, logarithm)
                        assert 0 <= lo <= hi
                assert (mp.mp.prec, mp.iv.prec) == (139, 137)
        with pytest.raises(RuntimeError):
            with construction.log_intervals(backend, 80):
                raise RuntimeError("planted interruption")
        assert (mp.mp.prec, mp.iv.prec) == (139, 137)
        if backend == "python-flint":
            assert flint.ctx.prec == old_flint
    finally:
        mp.mp.prec, mp.iv.prec = old_mp, old_iv


def test_bound_includes_late_zero_factorials():
    # K exceeds log_6(N); every remainder still contributes its constant 1.
    rows = construction.bound_assertions(construction.BASE6, 6, 6, 2, 2)
    assert rows[0][1:] == (F(0), {})
    assert rows[1][1] == 12
    assert rows[2][1] == 12


@pytest.mark.parametrize("seed,expected", [
    (construction.BASE6, {2: F(4, 5), 3: F(3, 5)}),
    (construction.CHEBYSHEV30, {2: F(14, 25), 3: F(9, 25), 5: F(1, 5)}),
])
def test_displayed_leading_constants_exceed_one(seed, expected):
    actual = construction.leading_constant_vector(seed, 6)
    assert actual == expected
    for backend, module in (("python-flint", "flint"), ("mpmath.iv", "mpmath")):
        pytest.importorskip(module)
        with construction.log_intervals(backend, 70) as logarithm:
            lo, hi = construction.enclose_expression(-1, actual, logarithm)
            assert 0 < lo <= hi


def test_serialized_fractions_round_trip():
    encoded = construction.json_ready(construction.verify_n14())
    assert F(encoded["original_excess"]["2"]) == F(1, 2)
    assert encoded["refined_excess"] == {}
