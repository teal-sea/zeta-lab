"""Exact controls and quantitative barriers for the URMS1/URMS2 attack.

The right-half-plane coefficient algebra is the weighted Wiener algebra

    ||a||_(1,sigma) = sum_n |a(n)| n^-sigma.

Its natural mean-square companion is

    ||a||_(2,sigma)^2 = sum_n |a(n)|^2 n^(-2 sigma).

Dirichlet convolution satisfies the Young bound
``||a*b||_2 <= ||a||_1 ||b||_2``.  This module records the exact scalar
resolvent bounds that follow, the failure of multiplicativity, the elementary
resummed envelopes at levels one and two, and the logarithmic projection scale
forced by the remaining square-sum problem.

None of these finite checks identifies a zero form factor.  The missing
analytic estimate is stated in ``URMS2-ATTACK.md``.
"""

from __future__ import annotations

from fractions import Fraction
from typing import TypeVar

import numpy as np
import sympy as sp

from dirichlet_recurrence import (
    dirichlet_convolution as numeric_dirichlet_convolution,
    next_log_derivative,
    smallest_prime_factors,
    von_mangoldt,
)
from exact_c2 import closed_form_route


F = Fraction
Scalar = TypeVar("Scalar")


def dirichlet_convolution(
    left: list[Scalar], right: list[Scalar], limit: int
) -> list[Scalar]:
    """Finite exact Dirichlet convolution, with index zero unused."""

    if limit < 1 or len(left) <= limit or len(right) <= limit:
        raise ValueError("both inputs must contain indices through limit")
    zero = left[1] * 0
    result = [zero for _ in range(limit + 1)]
    for divisor in range(1, limit + 1):
        if left[divisor] == zero:
            continue
        for quotient in range(1, limit // divisor + 1):
            result[divisor * quotient] += left[divisor] * right[quotient]
    return result


def dirichlet_inverse(coefficients: list[Scalar], limit: int) -> list[Scalar]:
    """Return the formal convolution inverse through ``limit``."""

    if limit < 1 or len(coefficients) <= limit:
        raise ValueError("coefficients must contain indices through limit")
    if coefficients[1] == 0:
        raise ValueError("coefficient at one must be nonzero")
    zero = coefficients[1] * 0
    result = [zero for _ in range(limit + 1)]
    result[1] = 1 / coefficients[1]
    for integer in range(2, limit + 1):
        subtotal = zero
        for divisor in range(2, integer + 1):
            if integer % divisor == 0:
                subtotal += coefficients[divisor] * result[integer // divisor]
        result[integer] = -subtotal / coefficients[1]
    return result


def convolution_inverse_defect(limit: int = 24) -> list[Fraction]:
    """A rational toy denominator times its inverse minus the identity."""

    coefficients = [F(0) for _ in range(limit + 1)]
    coefficients[1] = F(7)
    coefficients[2] = F(-3)
    coefficients[3] = F(2)
    coefficients[4] = F(5)
    inverse = dirichlet_inverse(coefficients, limit)
    product = dirichlet_convolution(coefficients, inverse, limit)
    identity = [F(0) for _ in range(limit + 1)]
    identity[1] = F(1)
    return [product[index] - identity[index] for index in range(limit + 1)]


def level_two_multiplicativity_defect() -> sp.Expr:
    """Return ``b(6)-b(2)b(3)`` for the normalized frozen inverse.

    Here ``A(2)=l2``, ``A(3)=l3``, ``B(p)=log(p) A(p)`` and ``z=1/L``.
    The denominator is ``(1-Az)^2+Bz^2``.  The nonzero result shows that
    the convolution inverse is not multiplicative even on the first coprime
    pair.
    """

    z, l2, l3 = sp.symbols("z l2 l3")
    f2 = -2 * z * l2 + z**2 * l2**2
    f3 = -2 * z * l3 + z**2 * l3**2
    f6 = 2 * z**2 * l2 * l3
    b2 = -f2
    b3 = -f3
    b6 = -f6 + 2 * f2 * f3
    return sp.factor(b6 - b2 * b3)


def inverse_wiener_bound(a0_lower: Fraction, aplus_norm: Fraction) -> Fraction:
    """Neumann/resolvent bound ``||(A0+A+)^-1||_1``."""

    if a0_lower <= aplus_norm or aplus_norm < 0:
        raise ValueError("a positive Wiener gap is required")
    return 1 / (a0_lower - aplus_norm)


def inverse_difference_bound(
    first_inverse_norm: Fraction,
    second_inverse_norm: Fraction,
    denominator_difference_norm: Fraction,
) -> Fraction:
    """Resolvent-identity bound for two convolution inverses."""

    if min(first_inverse_norm, second_inverse_norm, denominator_difference_norm) < 0:
        raise ValueError("norms must be nonnegative")
    return first_inverse_norm * denominator_difference_norm * second_inverse_norm


def inverse_height_derivative_bound(
    inverse_norm: Fraction, denominator_derivative_norm: Fraction
) -> Fraction:
    """Bound from ``partial_t b = -b*(partial_t A)*b``."""

    if min(inverse_norm, denominator_derivative_norm) < 0:
        raise ValueError("norms must be nonnegative")
    return inverse_norm**2 * denominator_derivative_norm


def young_multiplier_bound(l1_norm: Fraction, l2_norm: Fraction) -> Fraction:
    """Weighted Dirichlet-convolution Young bound."""

    if min(l1_norm, l2_norm) < 0:
        raise ValueError("norms must be nonnegative")
    return l1_norm * l2_norm


def level_one_envelope(ratio: Fraction) -> Fraction:
    """Pointwise envelope after exact level-one resummation."""

    if not F(0) <= ratio < F(1):
        raise ValueError("level-one ratio must lie in [0,1)")
    return 1 / (1 - ratio)


def level_two_envelope(ratio: Fraction) -> Fraction:
    """Pointwise envelope from the exact level-two word masses."""

    if not F(0) <= ratio < F(1, 2):
        raise ValueError("level-two ratio must lie in [0,1/2)")
    return 1 + 2 * ratio + 3 * ratio**2 / (1 - 2 * ratio)


def normalized_trivial_square_bound(log_x: Fraction, envelope: Fraction) -> Fraction:
    """Elementary bound divided by the desired ``x log x`` scale.

    The pointwise estimate ``|a(n)| <= log(x)*envelope`` gives
    ``sum_(n<=x)|a(n)|^2 <= x log(x)^2 envelope^2``.  Dividing by the
    required ``x log(x)`` scale leaves the returned factor.
    """

    if log_x < 0 or envelope < 0:
        raise ValueError("inputs must be nonnegative")
    return log_x * envelope**2


def projection_order_for_square_tail(log_t: int, contraction: Fraction) -> int:
    """Smallest J with ``log(T)*rho^(2(J+1)) <= 1/log(T)``.

    ``log_t`` represents the positive number ``log(T)``.  This quantifies the
    slowly growing projection needed to turn the elementary one-log loss into
    an ``o(1)`` tail while the full inverse remains the primary object.
    """

    if log_t < 2:
        raise ValueError("log_t must be at least two")
    if not F(0) < contraction < F(1):
        raise ValueError("contraction must lie in (0,1)")
    order = 0
    while F(log_t) * contraction ** (2 * (order + 1)) > F(1, log_t):
        order += 1
    return order


def resummed_projection_errors(
    *, limit: int = 80, ell: float = 20.0, max_order: int = 10
) -> list[float]:
    """Compare the exact finite inverse with its corrected Taylor projections.

    This is a falsification control only.  The finite Dirichlet recurrence and
    the operator-word projection use separate implementations already present
    in the hunt.
    """

    if limit < 2 or ell <= 0 or max_order < 0:
        raise ValueError("require limit>=2, ell>0, and max_order>=0")
    factors = smallest_prime_factors(limit)
    mangoldt = von_mangoldt(limit, factors)
    exact = np.zeros(limit + 1, dtype=complex)
    exact[1] = ell
    exact[2:] = -mangoldt[2:]
    for _level in range(2):
        exact = next_log_derivative(exact, factors)

    integers = np.arange(2, limit + 1)
    atoms: dict[int, np.ndarray] = {}
    words: dict[tuple[int, ...], np.ndarray] = {}

    def atom(exponent: int) -> np.ndarray:
        if exponent not in atoms:
            result = np.zeros(limit + 1, dtype=complex)
            result[2:] = mangoldt[2:] * np.log(integers) ** exponent
            atoms[exponent] = result
        return atoms[exponent]

    def word_value(word: tuple[int, ...]) -> np.ndarray:
        if word not in words:
            result = np.zeros(limit + 1, dtype=complex)
            result[1] = 1
            for exponent in word:
                result = numeric_dirichlet_convolution(result, atom(exponent))
            words[word] = result
        return words[word]

    projection = np.zeros(limit + 1, dtype=complex)
    errors = []
    for power, expression in closed_form_route(max_order + 1).items():
        for word, coefficient in expression.items():
            projection += float(coefficient) * word_value(word) / ell**power
        errors.append(float(np.max(np.abs(projection[2:] - exact[2:]))))
    return errors


def audit() -> dict[str, object]:
    ratio = F(2, 5)
    return {
        "inverse_defect": convolution_inverse_defect(),
        "level_two_multiplicativity_defect": level_two_multiplicativity_defect(),
        "level_one_envelope_at_ratio_2_5": level_one_envelope(ratio),
        "level_two_envelope_at_ratio_2_5": level_two_envelope(ratio),
        "projection_order_logT_1e6_rho_4_5": projection_order_for_square_tail(
            10**6, F(4, 5)
        ),
        "finite_resummed_projection_errors": resummed_projection_errors(),
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
