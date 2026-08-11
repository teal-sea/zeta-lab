"""Exact algebraic controls for the untruncated level-two resolvent.

Put ``U = xi'/xi``.  Differentiating before expanding gives

    xi'''/xi'' = U + (2 U U' + U'') / (U^2 + U').

This representation has no geometric order.  On a right half-plane its
Dirichlet coefficients can be obtained by convolution-inverting the full
denominator.  Freezing the archimedean derivatives and writing
``U = L - A``, ``U' = B``, ``U'' = -C`` reproduces the rational ``Q(z)``
object used by the corrected coefficient calculation.

The helpers here check only exact algebra and combinatorics.  They make no
claim about the finite-height zero-statistics limit.
"""

from __future__ import annotations

from fractions import Fraction

import sympy as sp

from exact_c2 import closed_form_route


F = Fraction


def level_two_resolvent_defect() -> sp.Expr:
    """Return the symbolic defect in the exact ``xi'''/xi''`` identity."""

    u, du, ddu = sp.symbols("u du ddu")
    direct = (u**3 + 3 * u * du + ddu) / (u**2 + du)
    resolvent = u + (2 * u * du + ddu) / (u**2 + du)
    return sp.factor(direct - resolvent)


def frozen_q_defect() -> sp.Expr:
    """Return the defect between the exact frozen resolvent and ``Q(z)``."""

    z, a, b, c = sp.symbols("z a b c")
    ell = 1 / z
    exact_arithmetic = -a + (2 * (ell - a) * b - c) / ((ell - a) ** 2 + b)
    q = -a + (2 * b * z - (2 * a * b + c) * z**2) / (
        (1 - a * z) ** 2 + b * z**2
    )
    return sp.factor(exact_arithmetic - q)


def absolute_word_mass(power: int) -> int:
    """Return the sum of absolute coefficients in the exact ``q_power``."""

    if power < 0:
        raise ValueError("power must be nonnegative")
    expression = closed_form_route(power + 1)[power]
    return sum(abs(value) for value in expression.values())


def closed_absolute_word_mass(power: int) -> int:
    """Closed value of :func:`absolute_word_mass`."""

    if power < 0:
        raise ValueError("power must be nonnegative")
    if power == 0:
        return 1
    if power == 1:
        return 2
    return 3 * 2 ** (power - 2)


def coefficientwise_ratio(alpha: Fraction) -> Fraction:
    """Asymptotic ratio in the elementary absolute coefficient majorant.

    The exact word mass doubles at each order from order two onward.  Combining
    that growth with ``log(n)/L_T <= 2 alpha + o(1)`` for ``n <= T^alpha``
    gives ratio ``4 alpha``.  This is a diagnostic boundary, not a finite-T
    pair-correlation estimate.
    """

    if alpha < 0:
        raise ValueError("alpha must be nonnegative")
    return 4 * alpha


def exact_denominator_split_defect() -> sp.Expr:
    """Check the archimedean/arithmetic split of ``U^2+U'``."""

    ell, dell, d = sp.symbols("ell dell d")
    full = (ell + d) ** 2 + dell + sp.Symbol("dd")
    base = ell**2 + dell
    arithmetic = 2 * ell * d + d**2 + sp.Symbol("dd")
    return sp.expand(full - base - arithmetic)


def exact_numerator_split_defect() -> sp.Expr:
    """Check the split of ``2 U U' + U''`` used in the report."""

    ell, dell, ddell, d, dd, ddd = sp.symbols(
        "ell dell ddell d dd ddd"
    )
    full = 2 * (ell + d) * (dell + dd) + ddell + ddd
    base = 2 * ell * dell + ddell
    arithmetic = 2 * ell * dd + 2 * d * dell + 2 * d * dd + ddd
    return sp.expand(full - base - arithmetic)


def audit() -> dict[str, object]:
    """Return the exact closure controls in a small machine-readable payload."""

    return {
        "level_two_resolvent_defect": level_two_resolvent_defect(),
        "denominator_split_defect": exact_denominator_split_defect(),
        "numerator_split_defect": exact_numerator_split_defect(),
        "frozen_q_defect": frozen_q_defect(),
        "absolute_word_masses_0_19": [
            absolute_word_mass(power) for power in range(20)
        ],
        "absolute_resummation_ratio_at_one_quarter": coefficientwise_ratio(
            F(1, 4)
        ),
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
