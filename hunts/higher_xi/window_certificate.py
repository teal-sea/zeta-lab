"""Small exact checker for one corrected xi-double-prime window.

The window is

    v(s) = sum_(k=0)^3 a_k P_(2k)(2s),   -1/2 <= s <= 1/2,

with rational ``a_k`` and ``a_0=1``.  Legendre orthogonality gives
``integral v = 1``.  The triangle inequality and ``|P_n(x)| <= 1`` show that
the window is positive, so its L1 norm is also one.

Every polynomial integral is evaluated in exact SymPy rationals.  The only
infinite-series allowance is the rational bound from
``corrected_form_factor.tail_bound``.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache

import numpy as np
import sympy as sp

from corrected_form_factor import corrected_coefficients, tail_bound


F = Fraction
WINDOW_COEFFICIENTS = (F(1), F(-185616, 10**6), F(-111471, 10**6), F(-20783, 10**6))


def positivity_floor() -> Fraction:
    return WINDOW_COEFFICIENTS[0] - sum(
        abs(coefficient) for coefficient in WINDOW_COEFFICIENTS[1:]
    )


def _fraction(value: sp.Rational) -> Fraction:
    return F(int(value.p), int(value.q))


@lru_cache(maxsize=1)
def exact_window_check() -> dict[str, Fraction | str]:
    x, alpha = sp.symbols("x alpha")
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
    diagonal = sum(
        coefficient**2 / (4 * index + 1)
        for index, coefficient in enumerate(coefficients)
    )
    denominator = diagonal
    for index, coefficient in corrected_coefficients(40).items():
        rational = sp.Rational(coefficient.numerator, coefficient.denominator)
        denominator += 2 * rational * sp.integrate(
            alpha**index * overlap, (alpha, 0, 1)
        )

    finite_denominator = _fraction(sp.factor(denominator))
    tail_loss = tail_bound()
    denominator_upper = finite_denominator + tail_loss
    lower_bound = F(2) - denominator_upper
    return {
        "window_polynomial": str(window),
        "positivity_floor": positivity_floor(),
        "finite_denominator": finite_denominator,
        "tail_loss": tail_loss,
        "denominator_upper": denominator_upper,
        "simplicity_lower_bound": lower_bound,
    }


def numerical_optimum(basis_count: int = 8) -> dict[str, float | list[float]]:
    """Discovery optimum from the exact truncated Legendre Gram matrix."""

    x, alpha = sp.symbols("x alpha")
    basis = [sp.legendre(2 * index, x) for index in range(basis_count)]
    form_factor = sum(
        sp.Rational(value.numerator, value.denominator) * alpha**index
        for index, value in corrected_coefficients(40).items()
    )
    gram = np.zeros((basis_count, basis_count), dtype=float)
    for left in range(basis_count):
        for right in range(left, basis_count):
            forward = sp.integrate(
                basis[left] * basis[right].subs(x, x - 2 * alpha) / 2,
                (x, -1 + 2 * alpha, 1),
            )
            reverse = forward
            if left != right:
                reverse = sp.integrate(
                    basis[right] * basis[left].subs(x, x - 2 * alpha) / 2,
                    (x, -1 + 2 * alpha, 1),
                )
            entry = sp.integrate(
                form_factor * (forward + reverse), (alpha, 0, 1)
            )
            if left == right:
                entry += sp.Rational(1, 4 * left + 1)
            gram[left, right] = gram[right, left] = float(entry)
    tail = gram[1:, 1:]
    coefficients = np.r_[1.0, np.linalg.solve(tail, -gram[1:, 0])]
    denominator = float(coefficients @ gram @ coefficients)
    return {
        "basis_count": float(basis_count),
        "coefficients": coefficients.tolist(),
        "denominator": denominator,
        "simplicity_value": 2.0 - denominator,
    }


if __name__ == "__main__":
    result = exact_window_check()
    for key, value in result.items():
        if isinstance(value, Fraction):
            print(f"{key}: {value} = {float(value):.15g}")
        else:
            print(f"{key}: {value}")
    optimum = numerical_optimum()
    print(f"raw numerical optimum: {optimum['simplicity_value']:.15g}")
    print(f"raw coefficients: {optimum['coefficients']}")
