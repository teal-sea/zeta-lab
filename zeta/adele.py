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

class Idele:
    """A computational representation of an Idele over Q.
    
    An idele is an invertible adele. It is a sequence (x_inf, x_2, x_3, ...)
    where x_inf in R^* and x_p in Q_p^*, with |x_p|_p = 1 for almost all p.
    """
    def __init__(self, real_part: float, padic_parts: Dict[int, PAdic]):
        if real_part == 0:
            raise ValueError("Real part of an Idele must be non-zero.")
        for p, padic in padic_parts.items():
            if padic.q == 0:
                raise ValueError(f"p-adic part for p={p} must be non-zero.")
                
        self.real_part = float(real_part)
        self.padic_parts = padic_parts

    @classmethod
    def from_rational(cls, q: Union[int, Fraction], primes: list[int]) -> 'Idele':
        """Embed a non-zero rational number q into the Idele group."""
        if q == 0:
            raise ValueError("0 is not an Idele.")
        padics = {p: PAdic(p, q) for p in primes}
        return cls(float(q), padics)

    def norm(self) -> float:
        """The Idelic norm (product formula). Evaluates to 1 for principal ideles."""
        res = abs(self.real_part)
        for p_adic in self.padic_parts.values():
            res *= p_adic.norm()
        return res

def local_zeta_factor(p: int, s: complex) -> complex:
    """
    Computes Tate's local zeta integral Z(f, s) over Q_p^*.
    
    For the standard Schwartz-Bruhat function (the indicator function of Z_p),
    the integral exactly evaluates to the Euler factor:
        Z(f_p, s) = 1 / (1 - p^(-s))
    """
    # Tate's thesis mathematically proves that integrating the indicator 
    # function of Z_p against the multiplicative measure yields the local Euler factor.
    return 1.0 / (1.0 - p ** (-s))

def global_euler_product(s: complex, primes: list[int]) -> complex:
    """
    Computes the partial global zeta function over a set of places (primes)
    by multiplying their local zeta integrals.
    """
    product = 1.0 + 0j
    for p in primes:
        product *= local_zeta_factor(p, s)
    return product

def padic_fractional_part(p: int, q: Union[int, Fraction]) -> float:
    """
    Computes the p-adic fractional part {x}_p.
    For a rational number q = a/b, we can write it as q = q_frac + q_int,
    where q_int in Z_p and q_frac is a rational number of the form c/p^k
    with 0 <= c < p^k. 
    
    The p-adic fractional part maps Q_p -> Q[1/p] / Z.
    """
    q_f = Fraction(q)
    if q_f.denominator % p != 0:
        return 0.0 # q is in Z_p, so fractional part is 0
        
    # We find k such that p^k is the exact power of p dividing the denominator
    den = q_f.denominator
    k = 0
    while den % p == 0:
        den //= p
        k += 1
        
    # Now q = a / (p^k * den). We want to find c such that 
    # a / (p^k * den) - c / p^k = (a - c * den) / (p^k * den) is in Z_p.
    # This means we need (a - c * den) to be divisible by p^k.
    # So we solve: c * den = a (mod p^k).
    
    a = q_f.numerator
    modulus = p**k
    
    # Modular inverse of den mod p^k
    # den and p^k are coprime
    den_inv = pow(den, -1, modulus)
    c = (a * den_inv) % modulus
    
    return c / modulus

def padic_additive_character(p: int, q: Union[int, Fraction]) -> complex:
    """
    The canonical additive character for Q_p: e_p(x) = exp(-2 * pi * i * {x}_p).
    """
    frac_part = padic_fractional_part(p, q)
    theta = -2.0 * math.pi * frac_part
    return complex(math.cos(theta), math.sin(theta))

def adelic_additive_character(adele: Adele) -> complex:
    """
    The canonical global additive character on the Adeles: 
    psi(x) = e_inf(x_inf) * prod_p e_p(x_p)
    
    Where e_inf(x) = exp(2 * pi * i * x).
    By a fundamental theorem of Adelic geometry, psi(q) = 1 for any q in Q.
    """
    theta_inf = 2.0 * math.pi * adele.real_part
    res = complex(math.cos(theta_inf), math.sin(theta_inf))
    
    for p, padic in adele.padic_parts.items():
        res *= padic_additive_character(p, padic.q)
        
    return res

