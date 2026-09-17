"""Normalization and enclosure checks for the odd heat flow."""

import mpmath as mp

from hunts.dh_minus_heat import pilot


def test_zero_time_matches_completed_series():
    with mp.workdps(40):
        z = mp.mpc('2', '0.4')
        value = pilot.heat_mp(z, mp.mpf(0))
        reference = -1j * pilot.completed(mp.mpf('0.5') + 1j*z)
        assert abs(value-reference) < mp.mpf('1e-34')
        assert abs(value-reference/2) > mp.mpf('0.01')


def test_odd_modular_sign():
    with mp.workdps(40):
        x = mp.mpf('1.2')
        left = pilot.theta(1/x)
        right = x**mp.mpf('1.5') * pilot.theta(x)
        assert abs(left+right) < mp.mpf('1e-35')
        assert abs(left-right) > mp.mpf('0.01')


def test_ball_matches_independent_zero_time_value():
    from hunts.dh_minus_heat import odd_ball
    from flint import acb, arb, ctx

    with ctx.workprec(128):
        value = odd_ball.heat(('2', '0.4'), '0', prec=128)
        s = acb(arb('0.1'), 2)
        tau = -(1+arb(5).sqrt())/2
        tau -= (1+tau*tau).sqrt()
        a = [arb(1), tau, -tau, arb(-1)]
        f = sum(a[n-1]*s.zeta(acb(arb(n)/5)) for n in range(1, 5)) / acb(5)**s
        ref = -acb(0,1)*(acb(5)/arb.pi())**((s+1)/2)*((s+1)/2).gamma()*f
        assert value.overlaps(ref)
        assert value.real.rad() < arb('1e-25')
        assert value.imag.rad() < arb('1e-25')


def test_time_one_rouche_margin_is_positive():
    from fractions import Fraction
    from hunts.dh_minus_heat import odd_ball

    row = odd_ball.rouche(('7.646830873064', '0.425938287679'), '1/10000000')
    assert row['decided']
    assert Fraction(row['margin']['lower']) > 0
    assert Fraction(row['linear_lower']['lower']) > (
        Fraction(row['constant_upper']['upper'])
        + Fraction(row['remainder_upper']['upper']))


def test_time_217_over_200_rouche_margin_is_positive():
    from fractions import Fraction
    from hunts.dh_minus_heat import odd_ball

    row = odd_ball.rouche(
        ('7.543145542463', '0.072646330251'),
        '1/10000000',
        t='217/200',
    )
    assert row['decided']
    assert Fraction(row['margin']['lower']) > 0
    assert Fraction(row['H_abs_upper']['upper']) < Fraction('1e-14')
    assert Fraction(row['Hprime_abs_lower']['lower']) > Fraction('0.0028')
    assert Fraction(row['M2_upper']['upper']) < Fraction('1.9')


def test_phase_upper_bound_on_two_backends():
    from fractions import Fraction
    from hunts.dh_minus_heat import phase_bound

    rows = phase_bound.check()
    assert {r['backend'] for r in rows} == {'arb', 'mpmath.iv'}
    for row in rows:
        assert Fraction(row['margin']['lower']) > 0
        assert row['sigma'] == '953/400'
        assert Fraction(row['heat_upper']) == Fraction(753, 400)**2/2


def test_first_function_has_independent_half_unit_upper_bound():
    from fractions import Fraction
    from hunts.dh_minus_heat import phase_bound

    for row in phase_bound.first_function_check():
        assert Fraction(row['coefficient_sum_upper']['upper']) < 1
        assert row['heat_upper'] == '1/2'


def test_underresolved_tail_cannot_decide_zero():
    from hunts.dh_minus_heat import odd_ball
    row = odd_ball.rouche(('7.646830873064', '0.425938287679'), '1e-7', nmax=2)
    assert not row['decided']


def test_displaced_centre_cannot_inherit_decision():
    from hunts.dh_minus_heat import odd_ball
    row = odd_ball.rouche(('7.646930873064', '0.425938287679'), '1e-7')
    assert not row['decided']


def test_imprecise_inputs_and_invalid_domains_refused():
    import pytest
    from hunts.dh_minus_heat import odd_ball
    with pytest.raises(TypeError):
        odd_ball.heat((2.0, '0.4'), '0')
    with pytest.raises(ValueError):
        odd_ball.heat(('2', '0.4'), '-1')
    with pytest.raises(ValueError):
        odd_ball.heat(('2', '0.4'), '0', upper='1/2')
    with pytest.raises(ValueError):
        odd_ball.rouche(('2', '0.4'), '1/2')


def test_precision_context_is_restored_on_success_and_failure():
    import pytest
    from flint import ctx
    from mpmath import iv
    from hunts.dh_minus_heat import odd_ball, phase_bound
    before = ctx.prec
    odd_ball.heat(('2', '0.4'), '0', prec=96)
    assert ctx.prec == before
    with pytest.raises(ValueError):
        odd_ball.heat(('2', '0.4'), '-1', prec=128)
    assert ctx.prec == before
    before_iv = iv.dps
    phase_bound.check(cutoff=100)
    assert iv.dps == before_iv


def test_written_margin_exact_and_frame_factor():
    from fractions import Fraction as F
    margin = F('1e-7')*F('.015')-F('1e-14')-F('1e-14')*F('2.35')/2
    assert margin == F(5999913, 4000000000000000)
    assert margin > 0
    upper = F(753,400)**2/2
    assert upper == F('1.771903125')
    assert 4*upper == F('7.0876125')
    later_margin = F('1e-7')*F('0.0028')-F('1e-14')-F('1e-14')*F('1.9')/2
    assert later_margin == F(559961, 2000000000000000)
    assert later_margin > 0
    assert 4*F(217, 200) == F(217, 50)
