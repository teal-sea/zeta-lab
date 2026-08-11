"""Exact corrected xi-double-prime coefficient object and uniform tail bound.

The candidate regular series is

    F2(alpha) = sum_{i >= 1} C_i |alpha|^i.

The first 40 ``C_i`` are generated twice in :mod:`exact_c2`.  This module
controls the infinite remainder.  Its majorant keeps the word length instead
of replacing every factorial-permanent entry by one worst-case constant.

For word exponents ``a,b in {0,1,2}``, put

    w_0 = 1,  w_1 = 5/2,  w_2 = 11.

Then ``(a+b+1)! <= w_a w_b`` in all nine cases.  A length-r factorial
permanent is therefore at most ``r! w(beta) w(delta)``.  The finite majorant
uses this inequality exactly through index 101.  A closed coarse majorant and
an exact two-step ratio bound control the rest.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import factorial, prod

from exact_c2 import closed_form_route, derive_c2


F = Fraction
EXACT_CUTOFF = 40
MAJORANT_CUTOFF = 101
WORD_WEIGHTS = {0: F(1), 1: F(5, 2), 2: F(11)}
K_WEIGHT = F(47, 4)  # w_1^2 + w_2/2
TWO_STEP_RATIO = F(5202, 64375)


@lru_cache(maxsize=None)
def corrected_coefficients(cutoff: int = EXACT_CUTOFF) -> dict[int, Fraction]:
    return derive_c2(cutoff)["coefficients"]  # type: ignore[return-value]


def truncated_value(alpha: Fraction, cutoff: int = EXACT_CUTOFF) -> Fraction:
    if not F(0) <= alpha <= F(1):
        raise ValueError("alpha must lie in [0,1]")
    return sum(
        (coefficient * alpha**index)
        for index, coefficient in corrected_coefficients(cutoff).items()
    )


def truncated_integral(alpha: Fraction, cutoff: int = EXACT_CUTOFF) -> Fraction:
    if not F(0) <= alpha <= F(1):
        raise ValueError("alpha must lie in [0,1]")
    return sum(
        coefficient * alpha ** (index + 1) / (index + 1)
        for index, coefficient in corrected_coefficients(cutoff).items()
    )


def word_sign(power: int, length: int) -> int:
    """The common sign of every length-``length`` word in ``q_power``."""

    return -1 if (power - length) % 2 else 1


def sign_coherence_holds(cutoff: int) -> bool:
    for power, expression in closed_form_route(cutoff).items():
        for word, coefficient in expression.items():
            if coefficient == 0 or (1 if coefficient > 0 else -1) != word_sign(
                power, len(word)
            ):
                return False
    return True


def gram_weight_inequalities() -> dict[tuple[int, int], tuple[int, Fraction]]:
    return {
        (left, right): (
            factorial(left + right + 1),
            WORD_WEIGHTS[left] * WORD_WEIGHTS[right],
        )
        for left in range(3)
        for right in range(3)
    }


@lru_cache(maxsize=None)
def _weighted_length_norms(max_power: int) -> dict[int, dict[int, Fraction]]:
    result: dict[int, dict[int, Fraction]] = {}
    for power, expression in closed_form_route(max_power + 1).items():
        lengths: dict[int, Fraction] = {}
        for word, coefficient in expression.items():
            weight = prod(WORD_WEIGHTS[exponent] for exponent in word)
            lengths[len(word)] = lengths.get(len(word), F(0)) + abs(coefficient) * weight
        result[power] = lengths
    return result


@lru_cache(maxsize=None)
def fock_upper_coefficient(index: int) -> Fraction:
    """Upper bound for ``|C_index|`` retaining every word length exactly."""

    if index < 1 or index > MAJORANT_CUTOFF:
        raise ValueError(f"index must lie in [1,{MAJORANT_CUTOFF}]")
    lengths = _weighted_length_norms(MAJORANT_CUTOFF)
    numerator = F(0)
    for left_power in range(index):
        right_power = index - 1 - left_power
        for length, left_value in lengths[left_power].items():
            numerator += (
                factorial(length)
                * left_value
                * lengths[right_power].get(length, F(0))
            )
    return F(2 ** (index - 1), factorial(index)) * numerator


def coarse_upper_coefficient(index: int) -> Fraction:
    """Closed upper bound for ``|C_index|`` when ``index >= 26``."""

    if index < 26:
        raise ValueError("coarse bound requires index >= 26")
    total_power = index - 1
    largest_length = total_power // 2
    smallest_length = (total_power + 3) // 4
    length_count = largest_length - smallest_length + 1
    return (
        F(
            (total_power - 1)
            * length_count
            * 4**total_power
            * factorial(largest_length),
            factorial(total_power + 1),
        )
        * K_WEIGHT**2
        * WORD_WEIGHTS[1] ** (total_power - 2 - 2 * largest_length)
    )


def coarse_two_step_ratio(index: int) -> Fraction:
    if index < 26:
        raise ValueError("ratio bound requires index >= 26")
    return coarse_upper_coefficient(index + 2) / coarse_upper_coefficient(index)


def ratio_residue_formula(residue: int, m: int) -> Fraction:
    """Closed form for B_(n+3)/B_(n+1), where n=4m+residue."""

    if residue == 0:
        return F(8 * (4 * m + 1), (4 * m - 1) * (4 * m + 3))
    if residue == 1:
        return F(2 * (2 * m + 1) ** 2, m**2 * (4 * m + 3))
    if residue == 2:
        return F(
            8 * (m + 2) * (4 * m + 3),
            (m + 1) * (4 * m + 1) * (4 * m + 5),
        )
    if residue == 3:
        return F(
            32 * (m + 1) ** 2,
            (2 * m + 1) * (2 * m + 3) * (4 * m + 5),
        )
    raise ValueError("residue must be 0, 1, 2, or 3")


def tail_bound(alpha: Fraction = F(1), cutoff: int = EXACT_CUTOFF) -> Fraction:
    """Bound ``sum_(i>cutoff) |C_i| alpha^i`` for rational alpha in [0,1]."""

    if not F(0) <= alpha <= F(1):
        raise ValueError("alpha must lie in [0,1]")
    if not 1 <= cutoff <= MAJORANT_CUTOFF:
        raise ValueError(f"cutoff must lie in [1,{MAJORANT_CUTOFF}]")
    finite_end = MAJORANT_CUTOFF
    finite = sum(
        fock_upper_coefficient(index) * alpha**index
        for index in range(cutoff + 1, finite_end + 1)
    )
    if cutoff >= finite_end:
        finite = F(0)

    first = max(finite_end + 1, cutoff + 1)
    if first % 2:
        odd_start, even_start = first, first + 1
    else:
        even_start, odd_start = first, first + 1
    ratio = TWO_STEP_RATIO * alpha**2
    coarse = (
        coarse_upper_coefficient(even_start) * alpha**even_start
        + coarse_upper_coefficient(odd_start) * alpha**odd_start
    ) / (1 - ratio)
    return finite + coarse


def value_interval(
    alpha: Fraction, cutoff: int = EXACT_CUTOFF
) -> tuple[Fraction, Fraction]:
    center = truncated_value(alpha, cutoff)
    radius = tail_bound(alpha, cutoff)
    return center - radius, center + radius


def integrated_tail_bound(
    alpha: Fraction = F(1), cutoff: int = EXACT_CUTOFF
) -> Fraction:
    """Bound the absolute tail after integration from zero to ``alpha``."""

    return alpha * tail_bound(alpha, cutoff)


def bilinear_tail_bound(
    window_l1_norm: Fraction, cutoff: int = EXACT_CUTOFF
) -> Fraction:
    """Uniform error for a bandwidth-one bilinear window functional."""

    if window_l1_norm < 0:
        raise ValueError("window_l1_norm must be nonnegative")
    return tail_bound(F(1), cutoff) * window_l1_norm**2


if __name__ == "__main__":
    bound = tail_bound()
    lower, upper = value_interval(F(1))
    print(f"tail after {EXACT_CUTOFF}: {bound} = {float(bound):.15g}")
    print(f"F2(1) interval: [{float(lower):.15g}, {float(upper):.15g}]")
