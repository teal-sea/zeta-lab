"""A coarse second-DH zero strip, independently enclosed on two backends.

The proof uses only Euler factors and an integral tail over all integers.
This is intentionally less sharp and less involved than strip2.py.
"""

from fractions import Fraction
from math import isqrt

from flint import arb, ctx, fmpq
from mpmath import iv

from hunts.dh_minus_heat.odd_ball import endpoints


def primes_to(limit):
    flags = bytearray(b'\x01')*(limit+1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit)+1):
        if flags[p]:
            for multiple in range(p*p, limit+1, p):
                flags[multiple] = 0
    return [p for p in range(2, limit+1) if flags[p]]


def _iv_ends(x):
    def convert(v):
        sign, man, exp, bc = v
        if not man and exp:
            raise ArithmeticError('nonfinite interval endpoint')
        return str((-1 if sign else 1)*Fraction(man)*Fraction(2)**exp)
    return {'lower': convert(x._mpi_[0]), 'upper': convert(x._mpi_[1])}


def _atan_iv(x, terms=60):
    """Alternating Taylor sum with absolute geometric remainder."""
    if not (x >= 0 and x < 1):
        raise ValueError('arctangent series requires 0<=x<1')
    total = iv.mpf(0)
    power = x
    for k in range(terms):
        total += (-1 if k % 2 else 1)*power/(2*k+1)
        power *= x*x
    error = power/(2*terms+1)
    return total + iv.mpf([-1, 1])*error


def check(sigma=Fraction(953, 400), cutoff=10000):
    """Enclose target minus an upper bound for the infinite prime phase.

    Theta=2 sum_{p=2,3 mod5} atan(p^-sigma). Beyond integer P,
    atan(x)<=x gives tail<=2 sum_{n>P}n^-sigma
    <=2 P^(1-sigma)/(sigma-1), sigma>1.
    For tau_minus=-1/kappa, the required phase is 2 atan(kappa).
    """
    sigma = Fraction(sigma)
    if sigma <= 1 or not isinstance(cutoff, int) or cutoff < 2:
        raise ValueError('need sigma>1 and integer cutoff>=2')
    primes = [p for p in primes_to(cutoff) if p % 5 in (2, 3)]
    output = []
    with ctx.workprec(128):
        s = arb(fmpq(sigma.numerator, sigma.denominator))
        phi = (1+arb(5).sqrt())/2
        kappa = (1+phi*phi).sqrt()-phi
        target = 2*kappa.atan()
        head = sum(2*(arb(p)**(-s)).atan() for p in primes)
        tail = 2*arb(cutoff)**(1-s)/(s-1)
        output.append({'backend': 'arb', 'precision_bits': 128,
                       'margin': endpoints(target-head-tail),
                       'target': endpoints(target), 'head': endpoints(head),
                       'tail': endpoints(tail)})
    old_dps = iv.dps
    try:
        iv.dps = 45
        s = iv.mpf(sigma.numerator)/sigma.denominator
        phi = (1+iv.sqrt(5))/2
        kappa = iv.sqrt(1+phi*phi)-phi
        target = 2*_atan_iv(kappa)
        head = sum(2*_atan_iv(iv.exp(-s*iv.log(p))) for p in primes)
        tail = 2*iv.exp((1-s)*iv.log(cutoff))/(s-1)
        output.append({'backend': 'mpmath.iv', 'precision_dps': 45,
                       'margin': _iv_ends(target-head-tail),
                       'target': _iv_ends(target), 'head': _iv_ends(head),
                       'tail': _iv_ends(tail)})
    finally:
        iv.dps = old_dps
    for row in output:
        row.update({'sigma': str(sigma), 'cutoff': cutoff,
                    'included_primes': len(primes),
                    'heat_upper': str((sigma-Fraction(1, 2))**2/2)})
    return output


def first_function_check(cutoff=20):
    """Enclose a coarse first-DH strip at sigma=3/2 on two backends.

    For the plus parameter 0<kappa<1, every coefficient has magnitude at
    most one. Splitting after N gives

        sum_{n>=2}|a_n|n^(-3/2)
        <= sum_{n=2}^N |a_n|n^(-3/2) + 2/sqrt(N).

    A value below one makes the n=1 term dominate in Re(s)>=3/2.
    """
    if not isinstance(cutoff, int) or isinstance(cutoff, bool) or cutoff < 2:
        raise ValueError('cutoff must be an integer >=2')
    output = []
    with ctx.workprec(128):
        phi = (1+arb(5).sqrt())/2
        kappa = (1+phi*phi).sqrt()-phi
        pattern = [arb(0), arb(1), kappa, -kappa, arb(-1)]
        exponent = arb(fmpq(-3, 2))
        head = sum(pattern[n % 5].abs_upper()*arb(n)**exponent
                   for n in range(2, cutoff+1))
        tail = 2/arb(cutoff).sqrt()
        output.append({'backend': 'arb', 'precision_bits': 128,
                       'cutoff': cutoff, 'head_upper': endpoints(head),
                       'tail_upper': endpoints(tail),
                       'coefficient_sum_upper': endpoints(head+tail),
                       'heat_upper': '1/2'})
    old_dps = iv.dps
    try:
        iv.dps = 45
        phi = (iv.mpf(1)+iv.sqrt(5))/2
        kappa = iv.sqrt(1+phi*phi)-phi
        pattern = [iv.mpf(0), iv.mpf(1), kappa, -kappa, iv.mpf(-1)]
        head = sum(abs(pattern[n % 5])*iv.exp(iv.mpf('-1.5')*iv.log(n))
                   for n in range(2, cutoff+1))
        tail = 2/iv.sqrt(cutoff)
        output.append({'backend': 'mpmath.iv', 'precision_dps': 45,
                       'cutoff': cutoff, 'head_upper': _iv_ends(head),
                       'tail_upper': _iv_ends(tail),
                       'coefficient_sum_upper': _iv_ends(head+tail),
                       'heat_upper': '1/2'})
    finally:
        iv.dps = old_dps
    return output
