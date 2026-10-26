"""Focused regressions for the scoped orbit attempt."""
from fractions import Fraction
from math import gcd

import pytest

from hunts.mobius_orbits.probe import check_case, mobius_sieve, rough_count, signed_divisors, trial_mu


def arrays(limit):
    mu = mobius_sieve(limit)
    mertens = [0]
    for value in mu[1:]:
        mertens.append(mertens[-1] + value)
    return mu, mertens


@pytest.mark.parametrize('P', [2, 6, 30, 210])
def test_inclusion_exclusion_at_every_small_integer(P):
    ds = signed_divisors(P)
    for x in range(301):
        assert rough_count(x, ds) == sum(gcd(j, P) == 1 for j in range(1, x + 1))


@pytest.mark.parametrize('P', [0, 1, 4, 12, 18])
def test_non_squarefree_or_trivial_P_refused(P):
    with pytest.raises(ValueError):
        signed_divisors(P)


def test_mobius_against_trial_division():
    mu, _ = arrays(1000)
    assert mu[1:] == [trial_mu(n) for n in range(1, 1001)]


def test_exact_endpoint_identity_and_deliberate_faults():
    mu, mertens = arrays(500)
    for N in range(4, 301):
        for P in (2, 6, 30, 210):
            assert check_case(N, P, mu, mertens)['exact_defect'] == 0
    assert check_case(12, 2, mu, mertens)['missing_boundary_lesion'] == {
        'N': 12, 'P': 2, 'b': 2, 'defect': 1}
    assert check_case(40, 2, mu, mertens)['wrong_complete_sign_lesion'] == {
        'N': 40, 'P': 2, 'b': 2, 'defect': 4}


def test_proposed_constants_computed_exactly():
    expected = {2: Fraction(1, 192), 6: Fraction(1, 432),
                30: Fraction(1, 675), 210: Fraction(4, 3675)}
    for P, value in expected.items():
        c = Fraction(sum(gcd(j, P) == 1 for j in range(1, P + 1)), P)
        assert c * c / 48 == value
