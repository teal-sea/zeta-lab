"""Exact controls for the finite-height xi-double-prime bridge obstruction.

The first failed analytic estimate is the treatment of the geometric-tail
contour integral on Bian thesis pages 32-33.  For a fixed cutoff ``V`` and a
height ``t >= V``, the integration interval contains ``[t,t+1]``.  Therefore

    integral_V^infinity dv / (1 + (v-t)^2) >= 1/2,

not ``O((t+2)^-2)``.  The lower bound uses only
``1 / (1+u^2) >= 1/2`` for ``0 <= u <= 1``.

This module also pins the finite-B uniqueness obstruction at derivative level
one and the endpoint behavior of the target rational window.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt

import sympy as sp

from exact_c2 import derive_level_one
from window_certificate import WINDOW_COEFFICIENTS


F = Fraction


def kernel_interval_lower_bound() -> Fraction:
    """Lower bound from the unit interval ``v in [t,t+1]``."""

    return F(1, 2)


def counterexample_height(constant: Fraction, cutoff: int) -> int:
    """Return an integer t where ``1/2 > constant/(t+2)^2`` and t >= cutoff."""

    if constant < 0 or cutoff < 0:
        raise ValueError("constant and cutoff must be nonnegative")
    numerator = 2 * constant.numerator
    denominator = constant.denominator
    root_floor = isqrt(numerator // denominator) if numerator >= denominator else 0
    height = max(cutoff, root_floor + 1)
    while constant / (height + 2) ** 2 >= kernel_interval_lower_bound():
        height += 1
    return height


def claimed_decay_upper(constant: Fraction, height: int) -> Fraction:
    if constant < 0 or height < 0:
        raise ValueError("constant and height must be nonnegative")
    return constant / (height + 2) ** 2


def level_one_fixed_b_value(order: int, alpha: Fraction) -> Fraction:
    """The finite polynomial printed by the fixed-order source argument."""

    if order < 1:
        raise ValueError("order must be positive")
    coefficients = derive_level_one(2 * order + 1)
    return sum(value * alpha**index for index, value in coefficients.items())


def target_window_endpoint() -> Fraction:
    """Value of the rational even-Legendre window at both endpoints."""

    return sum(WINDOW_COEFFICIENTS)


def target_overlap_boundary_coefficient() -> Fraction:
    """Coefficient of u in A_v(1-u) as u tends to zero from above."""

    return target_window_endpoint() ** 2


def computed_overlap_boundary_coefficient() -> Fraction:
    """Compute the linear edge coefficient by exact polynomial integration."""

    x, alpha, edge = sp.symbols("x alpha edge")
    coefficients = [
        sp.Rational(value.numerator, value.denominator)
        for value in WINDOW_COEFFICIENTS
    ]
    window = sp.expand(
        sum(
            coefficient * sp.legendre(2 * index, x)
            for index, coefficient in enumerate(coefficients)
        )
    )
    overlap = sp.expand(
        sp.integrate(
            window * window.subs(x, x - 2 * alpha) / 2,
            (x, -1 + 2 * alpha, 1),
        )
    )
    coefficient = sp.expand(overlap.subs(alpha, 1 - edge)).coeff(edge, 1)
    return F(int(coefficient.p), int(coefficient.q))
