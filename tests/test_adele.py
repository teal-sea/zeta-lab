"""Tests for zeta.adele, primitives for Non-Commutative Geometry."""

import pytest
import math
from fractions import Fraction
from zeta.adele import (
    PAdic,
    Adele,
    Idele,
    check_product_formula,
    padic_fractional_part,
    padic_additive_character,
    adelic_additive_character,
)

def test_padic_valuation_and_norm():
    """Test valuation v_p and absolute value |x|_p."""
    # x = 12 = 2^2 * 3
    p2 = PAdic(2, 12)
    assert p2.valuation() == 2
    assert p2.norm() == 0.25

    p3 = PAdic(3, 12)
    assert p3.valuation() == 1
    assert p3.norm() == pytest.approx(1.0 / 3.0)

    p5 = PAdic(5, 12)
    assert p5.valuation() == 0
    assert p5.norm() == 1.0

    # x = 5/14 = 5 * 2^-1 * 7^-1
    p2_frac = PAdic(2, Fraction(5, 14))
    assert p2_frac.valuation() == -1
    assert p2_frac.norm() == 2.0

    p7_frac = PAdic(7, Fraction(5, 14))
    assert p7_frac.valuation() == -1
    assert p7_frac.norm() == 7.0

def test_padic_fractional_part():
    """Test the fractional part {x}_p mapping to Q[1/p]/Z."""
    # 5/14 in Q_2. 14 = 2 * 7. We need to find c such that 
    # 5/14 - c/2 is in Z_2.
    # 5/14 - 1/2 = -2/14 = -1/7 which is in Z_2. So {5/14}_2 = 1/2.
    assert padic_fractional_part(2, Fraction(5, 14)) == 0.5

    # 1/3 in Q_3. {1/3}_3 = 1/3
    assert padic_fractional_part(3, Fraction(1, 3)) == pytest.approx(1.0 / 3.0)

def test_artin_product_formula():
    """Test that prod_v |q|_v = 1 for any non-zero rational q."""
    primes = [2, 3, 5, 7, 11, 13]
    
    # q = 12
    # |12|_inf = 12
    # |12|_2 = 1/4
    # |12|_3 = 1/3
    # |12|_p = 1 for p > 3
    # Product = 12 * (1/4) * (1/3) = 1
    assert check_product_formula(12, primes) == pytest.approx(1.0)
    
    # q = -5/14
    # |-5/14|_inf = 5/14
    # |-5/14|_2 = 2
    # |-5/14|_5 = 1/5
    # |-5/14|_7 = 7
    # Product = (5/14) * 2 * (1/5) * 7 = 1
    assert check_product_formula(Fraction(-5, 14), primes) == pytest.approx(1.0)

def test_adelic_additive_character_q_triviality():
    """Test that the global character psi(q) = 1 for all q in Q."""
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    
    test_cases = [
        Fraction(1, 1),
        Fraction(1, 2),
        Fraction(-3, 4),
        Fraction(15, 7),
        Fraction(1, 16)
    ]
    
    for q in test_cases:
        adele = Adele.from_rational(q, primes)
        psi_q = adelic_additive_character(adele)
        # psi_q should be 1.0 + 0.0j
        assert psi_q.real == pytest.approx(1.0, abs=1e-12)
        assert psi_q.imag == pytest.approx(0.0, abs=1e-12)
