import math
from mpmath import mp
import pytest

from zeta.detectors import lesion_li_lambda, lesion_weil_gaussian, lesion_weil_fejer
from zeta.epstein import OFFLINE_ZERO_RE, OFFLINE_ZERO_IM

def test_li_lambda_zero_sum():
    """Verify the lesion_li_lambda function exactly matches the zero-sum for the quad."""
    with mp.workdps(50):
        delta = mp.mpf('0.1')
        T = mp.mpf('14.13')
        n = 10
        
        # Explicit zero sum
        rho1 = mp.mpc(mp.mpf(0.5) + delta, T)
        rho2 = mp.mpc(mp.mpf(0.5) + delta, -T)
        rho3 = mp.mpc(mp.mpf(0.5) - delta, T)
        rho4 = mp.mpc(mp.mpf(0.5) - delta, -T)
        
        term = lambda rho: 1 - mp.power(1 - 1/rho, n)
        expected = mp.re(term(rho1) + term(rho2) + term(rho3) + term(rho4))
        
        actual = lesion_li_lambda(n, delta, T, dps=50)
        assert abs(actual - expected) < 1e-45

def test_weil_gaussian_closed_form():
    """Verify lesion_weil_gaussian closed form matches the direct zero sum."""
    with mp.workdps(50):
        delta = mp.mpf('0.1')
        T = mp.mpf('14.13')
        a = mp.mpf('0.05')
        
        # gamma values corresponding to rho = 1/2 + i gamma
        # rho = 1/2 +/- delta +/- iT => gamma = +/- T -/+ i delta
        g1 = mp.mpc(T, -delta)
        g2 = mp.mpc(T, delta)
        g3 = mp.mpc(-T, -delta)
        g4 = mp.mpc(-T, delta)
        
        h = lambda r: mp.exp(-a * r**2)
        expected = mp.re(h(g1) + h(g2) + h(g3) + h(g4))
        
        actual = lesion_weil_gaussian(a, delta, T, dps=50)
        assert abs(actual - expected) < 1e-45

def test_weil_gaussian_deepest_dip():
    """Verify the deepest detectable dip for Gaussian matches the analytic derivative root."""
    with mp.workdps(50):
        delta = mp.mpf('0.25')
        T = mp.mpf('14.13')
        
        # deepest dip occurs at a = pi / (2 T delta)
        a_dip = mp.pi / (2 * T * delta)
        
        actual_dip = lesion_weil_gaussian(a_dip, delta, T, dps=50)
        expected_dip = -4 * mp.exp(-mp.pi * (T**2 - delta**2) / (2 * T * delta))
        
        assert abs(actual_dip - expected_dip) < 1e-45

def test_weil_fejer_closed_form():
    """Verify lesion_weil_fejer matches the direct zero sum."""
    with mp.workdps(50):
        delta = mp.mpf('0.1')
        T = mp.mpf('14.13')
        b = mp.mpf('2.0')
        
        g1 = mp.mpc(T, -delta)
        g2 = mp.mpc(T, delta)
        g3 = mp.mpc(-T, -delta)
        g4 = mp.mpc(-T, delta)
        
        def h(r):
            x = b * r
            return mp.power(mp.sin(x) / x, 2)
            
        expected = mp.re(h(g1) + h(g2) + h(g3) + h(g4))
        
        actual = lesion_weil_fejer(b, delta, T, dps=50)
        assert abs(actual - expected) < 1e-45

