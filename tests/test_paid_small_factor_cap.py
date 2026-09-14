"""Ordinary-composite exclusion must preserve every true prime-power mass."""

import importlib.util
import hashlib
import json
from pathlib import Path

import pytest


SOURCE = Path(__file__).resolve().parents[1] / "hunts/paid_shortfall_scaling/small_factor.py"
SPEC = importlib.util.spec_from_file_location("small_factor_cap", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


def test_caps_are_nested_and_above_true_weights():
    assert P.check_caps(512) == 1024


def test_single_pass_prime_iterables_preserve_exclusions():
    assert P.small_factor_cap(12, iter([2])) == {}
    assert P.small_factor_cap(15, (p for p in [2, 3])) == {}
    assert P.small_factor_cap(16, iter([2])) == P.S.BASE.mangoldt_vector(16)
    with pytest.raises(ValueError):
        P.small_factor_cap(16, iter([4]))


def test_historical_run_inputs_and_outputs_are_preserved():
    root = SOURCE.parents[2]
    directory = SOURCE.parent / "computations/check-002"
    manifest = json.loads((directory / "manifest.json").read_text())
    for artifact in manifest["input_artifacts"]:
        path = root / artifact["path"]
        if path == SOURCE:
            path = directory / "small_factor.source.txt"
        assert hashlib.sha256(path.read_bytes()).hexdigest() == artifact["sha256_after"]
    for artifact in manifest["outputs"]:
        assert hashlib.sha256((root / artifact["path"]).read_bytes()).hexdigest() == artifact["sha256"]


@pytest.mark.parametrize("n", [2, 4, 8, 16, 64, 256, 3, 9, 27, 81, 5, 25, 7, 49, 121])
def test_prime_powers_are_retained(n):
    for primes in P.PRIME_SETS:
        assert P.small_factor_cap(n, primes) == P.S.BASE.mangoldt_vector(n)


def test_exclusions_have_their_claimed_boundary():
    assert not P.small_factor_cap(12, (2,))
    assert not P.small_factor_cap(36, (2,))
    assert P.small_factor_cap(15, (2,))
    assert not P.small_factor_cap(15, (2, 3, 5, 7))
    assert P.small_factor_cap(143, (2, 3, 5, 7))
    assert P.S.BASE.mangoldt_vector(143) == {}
    assert P.small_factor_cap(1, (2,)) == {}


@pytest.mark.parametrize("bad", [(4,), (1,), (-2,), (2.5,)])
def test_composite_or_invalid_exclusion_divisor_is_rejected(bad):
    with pytest.raises(ValueError):
        P.small_factor_cap(16, bad)


def test_full_costs_remain_above_psi_and_do_not_increase():
    for N in (144, 576):
        case = P.extended_case(N)
        previous = case["totals"]["perfect_power"]
        for name in ("factor_2", "factor_2_3_5_7"):
            assert P.S.BASE.nonnegative_coefficients(P.S.BASE.combine((1, previous), (-1, case["totals"][name])))
            assert P.S.BASE.nonnegative_coefficients(case["excess_over_psi"][name])
            previous = case["totals"][name]
