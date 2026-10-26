"""Regression checks for controlled block energy and misleading descent."""
from fractions import Fraction

import pytest
from flint import arb

from hunts.mobius_orbits.energy_probe import one_precision, plateau_control


@pytest.mark.parametrize('N', [4, 8, 16, 32, 64])
def test_predeclared_shell_and_block_identities(N):
    row = one_precision([N], 128)[0]
    assert row['E_2N']['mid'] < row['shell_energy']['mid'] < row['E_N']['mid']
    assert row['shell_gain']['mid'] > 0
    assert arb(row['schur_identity_defect']['ball']).contains(0)
    assert arb(row['line_update_identity_defect']['ball']).contains(0)
    assert row['wrong_sign_increase']['mid'] > 0
    assert not arb(row['omitted_cross_identity_defect']['ball']).contains(0)
    assert arb(row['adaptive_update_identity_defect']['ball']).contains(0)
    assert row['trace_S']['mid'] < row['trace_D']['mid'] < row['uniform_trace_cap']['mid']
    assert 0 < row['trace_gain_lower_bound']['mid'] < row['adaptive_gain']['mid']
    assert row['selected_gain']['mid'] == max(row['adaptive_gain']['mid'], row['shell_gain']['mid'])


def test_monotone_error_is_not_zero_limit():
    rows = plateau_control()
    assert all(Fraction(row['E']) > Fraction(1, 4) for row in rows)
    assert all(Fraction(row['gain']) > 0 for row in rows)
    assert Fraction(rows[-1]['gain_over_E_squared']) < Fraction(rows[0]['gain_over_E_squared'])


def test_reciprocal_contraction_implication_on_exact_inputs():
    # Test the algebra only. These rational inputs are not zeta measurements.
    for E in [Fraction(1, 2), Fraction(1, 10), Fraction(1, 100)]:
        for kappa in [Fraction(1, 2), Fraction(1)]:
            next_E = E - kappa * E * E
            assert 1 / next_E >= 1 / E + kappa


def test_residual_matched_fallback_catches_directional_blindness():
    # Synthetic Hilbert-space control, not a zeta measurement: S=I_2.
    u = (Fraction(1, 2), Fraction(0))
    v = (Fraction(0), Fraction(1))
    fixed_gain = sum(x * y for x, y in zip(u, v)) ** 2 / sum(x * x for x in v)
    M = sum(x * x for x in u)
    adaptive_gain = M ** 2 / M
    assert fixed_gain == 0 < M / 2 < adaptive_gain == Fraction(1, 4)
