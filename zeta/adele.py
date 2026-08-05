"""The Adele Ring and Ideles as Computational Objects.

This module begins the laboratory's transition from classical analysis 
(which we have rigorously proven to be computationally blind to off-line zeros 
in the computable regime) to Non-Commutative Geometry and the Spectral 
realization of the Riemann zeros (Connes, 1999).

To construct a Hilbert-Polya operator whose spectrum is the Riemann zeros, 
the classical real line is insufficient. One must use the Adeles A_Q: 
the restricted product of the reals R and all p-adic fields Q_p.

This module provides the primitive computational structures for p-adic 
numbers and basic Adelic vectors, laying the groundwork for a computational 
Adelic Trace Formula.
"""

import math
from fractions import Fraction
from typing import Dict, Union

class PAdic:
    """A computational representation of a p-adic number over Q_p.
    
    For a rational x = p^v * (a/b) where p does not divide a or b,
    the p-adic valuation is v, and the p-adic absolute value is |x|_p = p^(-v).
    """
    def __init__(self, p: int, q: Union[int, Fraction]):
        if p < 2:
            raise ValueError("p must be a prime >= 2")
        self.p = p
        self.q = Fraction(q)
        
    def valuation(self) -> Union[int, float]:
        """The p-adic valuation v_p(x)."""
        if self.q == 0:
            return math.inf
            
        num, den = abs(self.q.numerator), self.q.denominator
        v = 0
        
        while num % self.p == 0:
            v += 1
            num //= self.p
            
        while den % self.p == 0:
            v -= 1
            den //= self.p
            
        return v

    def norm(self) -> float:
        """The p-adic absolute value |x|_p."""
        if self.q == 0:
            return 0.0
        return float(self.p ** (-self.valuation()))

class Adele:
    """A computational representation of an Adele over Q.
    
    An adele a = (a_inf, a_2, a_3, a_5, ...) where a_inf is a real number,
    and a_p is a p-adic number, with |a_p|_p <= 1 for all but finitely many p.
    """
    def __init__(self, real_part: float, padic_parts: Dict[int, PAdic]):
        self.real_part = float(real_part)
        self.padic_parts = padic_parts

    @classmethod
    def from_rational(cls, q: Union[int, Fraction], primes: list[int]) -> 'Adele':
        """Embed a rational number q into the Adele ring.
        
        The embedding is diagonal: q -> (q, q, q, q, ...).
        We only store the p-adic components for the primes provided.
        """
        padics = {p: PAdic(p, q) for p in primes}
        return cls(float(q), padics)

    def norm(self) -> float:
        """The Adelic absolute value (product of all local norms)."""
        res = abs(self.real_part)
        for p_adic in self.padic_parts.values():
            res *= p_adic.norm()
        return res

def check_product_formula(q: Union[int, Fraction], primes: list[int]) -> float:
    """
    Artin's Product Formula: For any non-zero rational q, the product of 
    its absolute values over all places (real and all primes) is exactly 1.
    
    prod_{v} |q|_v = 1
    
    This function embeds q into the Adeles and computes its global norm.
    The primes list should be large enough to cover all prime factors 
    in the numerator and denominator of q.
    """
    q_frac = Fraction(q)
    if q_frac == 0:
        raise ValueError("Product formula only applies to non-zero rationals.")
        
    adele = Adele.from_rational(q_frac, primes)
    return adele.norm()

