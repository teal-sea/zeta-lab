"""Two independent exact derivations of the xi-double-prime form-factor coefficients.

The arithmetic basis element ``beta = (b_1, ..., b_r)`` denotes the Dirichlet
convolution

    (Lambda log^b_1) * ... * (Lambda log^b_r).

Tuples are sorted because Dirichlet convolution is commutative.  The empty
tuple is the convolution identity.  All coefficients are rational.

Route A iterates the logarithmic-derivative identity

    R_next = R + D(R) / R

as a formal Dirichlet series in x = 1/L.

Route B starts independently from zeta^(j)/zeta for j=1,2 and expands the
geometric series for xi'''/xi''.  It has separate expression and power-series
operations so that a defect in Route A's coefficient generator is not shared.

The leading mean-square constant is also evaluated twice: Route A enumerates
relative permutations, while Route B computes the same factorial permanent by
subset dynamic programming.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial
from typing import TypeAlias


F = Fraction
Beta: TypeAlias = tuple[int, ...]
Expression: TypeAlias = dict[Beta, Fraction]
Series: TypeAlias = dict[int, Expression]


def _clean(expression: Expression) -> Expression:
    return {beta: value for beta, value in expression.items() if value}


# ---------------------------------------------------------------------------
# Route A: formal logarithmic-derivative recurrence
# ---------------------------------------------------------------------------


def _a_add(left: Expression, right: Expression) -> Expression:
    result: defaultdict[Beta, Fraction] = defaultdict(F)
    for beta, value in left.items():
        result[beta] += value
    for beta, value in right.items():
        result[beta] += value
    return _clean(dict(result))


def _a_scale(expression: Expression, scalar: Fraction | int) -> Expression:
    return _clean({beta: F(scalar) * value for beta, value in expression.items()})


def _a_convolve(left: Expression, right: Expression) -> Expression:
    result: defaultdict[Beta, Fraction] = defaultdict(F)
    for beta, left_value in left.items():
        for delta, right_value in right.items():
            result[tuple(sorted(beta + delta))] += left_value * right_value
    return _clean(dict(result))


def _a_derivative(expression: Expression) -> Expression:
    """Dirichlet-series derivative D(a)(n) = -log(n) a(n)."""

    result: defaultdict[Beta, Fraction] = defaultdict(F)
    for beta, value in expression.items():
        for index in range(len(beta)):
            raised = list(beta)
            raised[index] += 1
            result[tuple(sorted(raised))] -= value
    return _clean(dict(result))


def _a_series_product(left: Series, right: Series, degree: int) -> Series:
    result: dict[int, Expression] = {}
    for left_power, left_expression in left.items():
        for right_power, right_expression in right.items():
            power = left_power + right_power
            if power > degree:
                continue
            product = _a_convolve(left_expression, right_expression)
            result[power] = _a_add(result.get(power, {}), product)
    return {power: expression for power, expression in result.items() if expression}


def _a_series_inverse(series: Series, degree: int) -> Series:
    if series.get(0) != {(): F(1)}:
        raise ValueError("series must have convolution identity as constant term")
    inverse: Series = {0: {(): F(1)}}
    for power in range(1, degree + 1):
        subtotal: Expression = {}
        for left_power in range(1, power + 1):
            if left_power not in series or power - left_power not in inverse:
                continue
            subtotal = _a_add(
                subtotal,
                _a_convolve(series[left_power], inverse[power - left_power]),
            )
        inverse[power] = _a_scale(subtotal, -1)
    return inverse


def recurrence_route(
    max_index: int = 11, *, derivative_level: int = 2
) -> dict[int, Expression]:
    """Return q_p in R_k = L + sum q_p L^-p via Route A."""

    if max_index < 1:
        raise ValueError("max_index must be positive")
    degree = max_index
    # S = x R_0 = 1 - x Lambda.
    series: Series = {0: {(): F(1)}, 1: {(0,): F(-1)}}
    if derivative_level < 0:
        raise ValueError("derivative_level must be nonnegative")
    for _level in range(derivative_level):
        inverse = _a_series_inverse(series, degree)
        derivative = {
            power: _a_derivative(expression)
            for power, expression in series.items()
            if power > 0
        }
        quotient = _a_series_product(derivative, inverse, degree - 1)
        next_series = dict(series)
        for power, expression in quotient.items():
            shifted = power + 1
            next_series[shifted] = _a_add(next_series.get(shifted, {}), expression)
        series = next_series
    return {power - 1: series[power] for power in range(1, degree + 1)}


# ---------------------------------------------------------------------------
# Route B: direct c-series / operator-word expansion
# ---------------------------------------------------------------------------


def _b_sum(*expressions: Expression) -> Expression:
    totals: dict[Beta, Fraction] = {}
    for expression in expressions:
        for word, coefficient in expression.items():
            totals[word] = totals.get(word, F(0)) + coefficient
    return {word: coefficient for word, coefficient in totals.items() if coefficient}


def _b_multiple(expression: Expression, scalar: Fraction | int) -> Expression:
    answer: Expression = {}
    for word, coefficient in expression.items():
        product = coefficient * F(scalar)
        if product:
            answer[word] = product
    return answer


def _b_product(left: Expression, right: Expression) -> Expression:
    answer: dict[Beta, Fraction] = {}
    for left_word, left_coefficient in left.items():
        for right_word, right_coefficient in right.items():
            word = tuple(sorted((*left_word, *right_word)))
            answer[word] = answer.get(word, F(0)) + left_coefficient * right_coefficient
    return {word: coefficient for word, coefficient in answer.items() if coefficient}


def _b_times_log(expression: Expression) -> Expression:
    answer: dict[Beta, Fraction] = {}
    for word, coefficient in expression.items():
        for position, exponent in enumerate(word):
            raised = list(word)
            raised[position] = exponent + 1
            new_word = tuple(sorted(raised))
            answer[new_word] = answer.get(new_word, F(0)) + coefficient
    return {word: coefficient for word, coefficient in answer.items() if coefficient}


def _b_series_sum(left: Series, right: Series) -> Series:
    answer = dict(left)
    for power, expression in right.items():
        answer[power] = _b_sum(answer.get(power, {}), expression)
    return {power: expression for power, expression in answer.items() if expression}


def _b_series_product(left: Series, right: Series, degree: int) -> Series:
    answer: Series = {}
    for left_power, left_expression in left.items():
        for right_power, right_expression in right.items():
            power = left_power + right_power
            if power > degree:
                continue
            expression = _b_product(left_expression, right_expression)
            answer[power] = _b_sum(answer.get(power, {}), expression)
    return {power: expression for power, expression in answer.items() if expression}


def operator_word_route(max_index: int = 11) -> dict[int, Expression]:
    """Return q_p via the independent geometric expansion of c."""

    if max_index < 1:
        raise ValueError("max_index must be positive")
    # b_1 = -Lambda and b_2 = Lambda*Lambda + Lambda log.
    b1: Expression = {(0,): F(-1)}
    b2: Expression = {(0, 0): F(1), (1,): F(1)}
    c: Series = {1: _b_multiple(b1, 2), 2: b2}
    c_log: Series = {power: _b_times_log(expression) for power, expression in c.items()}

    # a = sum_{ell>=0} (-1)^(ell+1) c^ell * (c log).
    a_series: Series = {}
    c_power: Series = {0: {(): F(1)}}
    for ell in range(max_index):
        term = _b_series_product(c_power, c_log, max_index - 1)
        signed = {
            power: _b_multiple(expression, -1 if ell % 2 == 0 else 1)
            for power, expression in term.items()
        }
        a_series = _b_series_sum(a_series, signed)
        c_power = _b_series_product(c_power, c, max_index - 1)

    result: dict[int, Expression] = {0: b1}
    for power in range(1, max_index):
        result[power] = a_series.get(power, {})
    return result


# ---------------------------------------------------------------------------
# Two independent leading mean-square calculations
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def _mean_constant_permutations(beta: Beta, delta: Beta) -> Fraction:
    """Route A constant by explicit relative-permutation enumeration."""

    if len(beta) != len(delta):
        return F(0)
    size = len(beta)
    denominator = factorial(2 * size + sum(beta) + sum(delta) - 1)
    numerator = 0
    for permutation in permutations(delta):
        product = 1
        for left, right in zip(beta, permutation):
            product *= factorial(left + right + 1)
        numerator += product
    return F(numerator, denominator)


@lru_cache(maxsize=None)
def _mean_constant_permanent(beta: Beta, delta: Beta) -> Fraction:
    """Route B constant by subset-DP evaluation of a factorial permanent."""

    if len(beta) != len(delta):
        return F(0)
    size = len(beta)
    row = [[factorial(left + right + 1) for right in delta] for left in beta]
    states = {0: 1}
    for row_index in range(size):
        following: dict[int, int] = {}
        for mask, value in states.items():
            for column in range(size):
                bit = 1 << column
                if mask & bit:
                    continue
                new_mask = mask | bit
                following[new_mask] = (
                    following.get(new_mask, 0) + value * row[row_index][column]
                )
        states = following
    numerator = states[(1 << size) - 1]
    denominator = factorial(2 * size + sum(beta) + sum(delta) - 1)
    return F(numerator, denominator)


def _form_factor_by_permutations(
    coefficients: dict[int, Expression], max_index: int
) -> dict[int, Fraction]:
    constants: dict[int, Fraction] = {}
    for index in range(1, max_index + 1):
        leading = F(0)
        for left_power in range(index):
            right_power = index - 1 - left_power
            for beta, left_coefficient in coefficients[left_power].items():
                for delta, right_coefficient in coefficients[right_power].items():
                    leading += (
                        left_coefficient
                        * right_coefficient
                        * _mean_constant_permutations(beta, delta)
                    )
        constants[index] = 2 ** (index - 1) * leading
    return constants


def _form_factor_by_permanents(
    coefficients: dict[int, Expression], max_index: int
) -> dict[int, Fraction]:
    constants: dict[int, Fraction] = {}
    for index in range(1, max_index + 1):
        total = F(0)
        for left_power, left_expression in coefficients.items():
            right_power = index - 1 - left_power
            if right_power not in coefficients:
                continue
            for left_word, left_value in left_expression.items():
                for right_word, right_value in coefficients[right_power].items():
                    total += (
                        left_value
                        * right_value
                        * _mean_constant_permanent(left_word, right_word)
                    )
        constants[index] = (1 << (index - 1)) * total
    return constants


def derive_level_one(max_index: int = 11) -> dict[int, Fraction]:
    """Independent normalization control against Farmer-Gonek-Lee."""

    coefficients = recurrence_route(max_index, derivative_level=1)
    return _form_factor_by_permutations(coefficients, max_index)


def derive_c2(max_index: int = 11) -> dict[str, object]:
    """Derive C_2,i twice and require exact agreement at every layer."""

    recurrence = recurrence_route(max_index, derivative_level=2)
    operator_words = operator_word_route(max_index)
    if recurrence != operator_words:
        differing = [
            power
            for power in range(max_index)
            if recurrence.get(power) != operator_words.get(power)
        ]
        raise ArithmeticError(f"Dirichlet coefficient routes differ at powers {differing}")

    permutation_values = _form_factor_by_permutations(recurrence, max_index)
    permanent_values = _form_factor_by_permanents(operator_words, max_index)
    if permutation_values != permanent_values:
        differing = [
            index
            for index in range(1, max_index + 1)
            if permutation_values[index] != permanent_values[index]
        ]
        raise ArithmeticError(f"mean-square routes differ at indices {differing}")

    return {
        "coefficients": permutation_values,
        "dirichlet_coefficients": recurrence,
    }


if __name__ == "__main__":
    derived = derive_c2(11)
    for index, value in derived["coefficients"].items():
        print(f"C2[{index}] = {value} = {float(value):.15g}")
