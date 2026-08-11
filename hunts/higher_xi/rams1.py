"""Exact support decomposition for the level-one resummed square density.

For the frozen parameter ``z = 1/L`` write

    a_z(n) = alpha_0(n) + sum_{k>=1} z^k alpha_k(n),
    alpha_0 = -Lambda,
    alpha_k = Lambda_{k-1} * (Lambda log).

The sum is finite at every integer: ``alpha_k(n)=0`` for ``k>Omega(n)``.
This module keeps those convolution depths separate, classifies their square
contributions by prime support, and supplies an independent formal-polynomial
control for the squarefree identity used in ``RAMS1-ATTACK.md``.

The finite ladders are diagnostics.  They do not supply the order-uniform
prime-sum estimate needed by RAMS1.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass

import numpy as np
import sympy as sp

from dirichlet_recurrence import (
    dirichlet_convolution,
    next_log_derivative,
    smallest_prime_factors,
    von_mangoldt,
)


def factorization(integer: int, factors: np.ndarray) -> tuple[tuple[int, int], ...]:
    """Return the prime factorization using an existing SPF table."""

    if integer < 1 or integer >= len(factors):
        raise ValueError("integer must lie inside the SPF table")
    result: list[tuple[int, int]] = []
    while integer > 1:
        prime = int(factors[integer])
        exponent = 0
        while integer % prime == 0:
            integer //= prime
            exponent += 1
        result.append((prime, exponent))
    return tuple(result)


def support_statistics(limit: int, factors: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Return ``omega(n)`` and ``Omega(n)`` through ``limit``."""

    omega = np.zeros(limit + 1, dtype=np.int16)
    big_omega = np.zeros(limit + 1, dtype=np.int16)
    for integer in range(2, limit + 1):
        quotient = integer
        prime = int(factors[integer])
        exponent = 0
        while quotient % prime == 0:
            quotient //= prime
            exponent += 1
        omega[integer] = omega[quotient] + 1
        big_omega[integer] = big_omega[quotient] + exponent
    return omega, big_omega


def level_one_layers(limit: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return all nonzero ``alpha_k`` layers and support statistics.

    Row zero is ``-Lambda``.  The maximum possible convolution depth is
    ``floor(log_2(limit))``, so this is the exact finite resummed coefficient
    object rather than a chosen geometric truncation.
    """

    if limit < 2:
        raise ValueError("limit must be at least two")
    factors = smallest_prime_factors(limit)
    mangoldt = von_mangoldt(limit, factors)
    integers = np.arange(limit + 1, dtype=float)
    mangoldt_log = np.zeros(limit + 1, dtype=complex)
    mangoldt_log[2:] = mangoldt[2:] * np.log(integers[2:])

    max_depth = int(math.log(limit, 2))
    layers = np.zeros((max_depth + 1, limit + 1), dtype=float)
    layers[0] = -mangoldt

    lambda_power = np.zeros(limit + 1, dtype=complex)
    lambda_power[1] = 1.0
    mangoldt_complex = mangoldt.astype(complex)
    for depth in range(1, max_depth + 1):
        layers[depth] = np.real(
            dirichlet_convolution(lambda_power, mangoldt_log)
        )
        lambda_power = dirichlet_convolution(lambda_power, mangoldt_complex)

    omega, big_omega = support_statistics(limit, factors)
    return layers, omega, big_omega


def independent_resolvent_defect(limit: int = 80, ell: float = 12.0) -> float:
    """Compare all depth layers with the independent log-derivative inverse."""

    if ell <= 0:
        raise ValueError("ell must be positive")
    layers, _omega, _big_omega = level_one_layers(limit)
    reconstructed = np.sum(
        ell ** (-np.arange(layers.shape[0]))[:, None] * layers, axis=0
    )
    factors = smallest_prime_factors(limit)
    mangoldt = von_mangoldt(limit, factors)
    base = np.zeros(limit + 1, dtype=complex)
    base[1] = ell
    base[2:] = -mangoldt[2:]
    independent = next_log_derivative(base, factors)
    return float(np.max(np.abs(reconstructed[2:] - independent[2:])))


def _formal_level_one_data(
    limit: int, max_depth: int
) -> tuple[
    list[list[sp.Expr]], dict[int, sp.Symbol], list[list[sp.Expr]]
]:
    """Internal formal-polynomial layers and Lambda convolution powers.

    Each ``log(p)`` is an independent symbol.  This route is deliberately
    separate from the floating sieve used by ``level_one_layers``.
    """

    factors = smallest_prime_factors(limit)
    primes = [integer for integer in range(2, limit + 1) if factors[integer] == integer]
    logs = {prime: sp.Symbol(f"l{prime}", positive=True) for prime in primes}
    mangoldt = [sp.Integer(0) for _ in range(limit + 1)]
    mangoldt_log = [sp.Integer(0) for _ in range(limit + 1)]
    for integer in range(2, limit + 1):
        parts = factorization(integer, factors)
        if len(parts) == 1:
            prime, exponent = parts[0]
            mangoldt[integer] = logs[prime]
            mangoldt_log[integer] = exponent * logs[prime] ** 2

    def convolve(left: list[sp.Expr], right: list[sp.Expr]) -> list[sp.Expr]:
        result = [sp.Integer(0) for _ in range(limit + 1)]
        for divisor in range(1, limit + 1):
            if left[divisor] == 0:
                continue
            for quotient in range(1, limit // divisor + 1):
                if right[quotient] != 0:
                    result[divisor * quotient] += left[divisor] * right[quotient]
        return [sp.expand(value) for value in result]

    layers = [[sp.Integer(0) for _ in range(limit + 1)] for _ in range(max_depth + 1)]
    layers[0] = [-value for value in mangoldt]
    lambda_power = [sp.Integer(0) for _ in range(limit + 1)]
    lambda_power[1] = sp.Integer(1)
    lambda_powers = [list(lambda_power)]
    for depth in range(1, max_depth + 1):
        layers[depth] = convolve(lambda_power, mangoldt_log)
        lambda_power = convolve(lambda_power, mangoldt)
        lambda_powers.append(list(lambda_power))
    return layers, logs, lambda_powers


def formal_level_one_layers(
    limit: int, max_depth: int
) -> tuple[list[list[sp.Expr]], dict[int, sp.Symbol]]:
    """Independent exact formal-polynomial coefficient generator."""

    layers, logs, _lambda_powers = _formal_level_one_data(limit, max_depth)
    return layers, logs


def alpha_symmetry_defects(limit: int = 45) -> list[sp.Expr]:
    """Return defects in ``k alpha_k(n) = log(n) Lambda_k(n)``."""

    max_depth = int(math.log(limit, 2))
    layers, logs, lambda_powers = _formal_level_one_data(limit, max_depth)
    factors = smallest_prime_factors(limit)
    defects: list[sp.Expr] = []
    for integer in range(2, limit + 1):
        log_integer = sum(
            exponent * logs[prime]
            for prime, exponent in factorization(integer, factors)
        )
        for depth in range(1, max_depth + 1):
            defects.append(
                sp.expand(
                    depth * layers[depth][integer]
                    - log_integer * lambda_powers[depth][integer]
                )
            )
    return defects


def borel_multiplicativity_defects(limit: int = 35) -> list[sp.Expr]:
    """Check multiplicativity of the exponential convolution generator.

    ``E_tau(n)=sum_k tau^k Lambda_k(n)/k!`` is the coefficient family of
    ``exp(tau*A(s))`` and is multiplicative even though the ordinary
    resolvent coefficients are not.
    """

    max_depth = int(math.log(limit, 2))
    _layers, _logs, lambda_powers = _formal_level_one_data(limit, max_depth)
    tau = sp.Symbol("tau")
    borel = [sp.Integer(0) for _ in range(limit + 1)]
    for integer in range(1, limit + 1):
        borel[integer] = sp.expand(
            sum(
                tau**depth
                * lambda_powers[depth][integer]
                / sp.factorial(depth)
                for depth in range(max_depth + 1)
            )
        )
    defects: list[sp.Expr] = []
    for left in range(1, limit + 1):
        for right in range(1, limit // left + 1):
            if math.gcd(left, right) == 1:
                defects.append(sp.expand(borel[left * right] - borel[left] * borel[right]))
    return defects


def powerful_squarefree_split(
    integer: int, factors: np.ndarray
) -> tuple[int, int]:
    """Return the unique ``integer = powerful * squarefree`` support split.

    Prime powers of exponent at least two go into the powerful factor.  Primes
    of exponent one go into the squarefree factor.
    """

    powerful = 1
    squarefree = 1
    for prime, exponent in factorization(integer, factors):
        if exponent == 1:
            squarefree *= prime
        else:
            powerful *= prime**exponent
    return powerful, squarefree


def powerful_squarefree_defects(limit: int = 80) -> list[int]:
    """Check reconstruction, coprimality, and both support properties."""

    factors = smallest_prime_factors(limit)
    defects: list[int] = []
    for integer in range(1, limit + 1):
        powerful, squarefree = powerful_squarefree_split(integer, factors)
        squarefree_parts = factorization(squarefree, factors)
        powerful_parts = factorization(powerful, factors)
        defects.extend(
            (
                integer - powerful * squarefree,
                math.gcd(powerful, squarefree) - 1,
                sum(exponent != 1 for _prime, exponent in squarefree_parts),
                sum(exponent < 2 for _prime, exponent in powerful_parts),
            )
        )
    return defects


def powerful_factorization(integer: int, factors: np.ndarray) -> tuple[int, int]:
    """Represent a powerful integer as ``a^2 b^3`` with squarefree ``b``."""

    first = 1
    second = 1
    for prime, exponent in factorization(integer, factors):
        if exponent < 2:
            raise ValueError("integer is not powerful")
        if exponent % 2:
            first *= prime ** ((exponent - 3) // 2)
            second *= prime
        else:
            first *= prime ** (exponent // 2)
    return first, second


def powerful_factorization_defects(limit: int = 250) -> list[int]:
    """Check the ``a^2 b^3`` representation for every powerful integer."""

    factors = smallest_prime_factors(limit)
    defects: list[int] = []
    for integer in range(1, limit + 1):
        parts = factorization(integer, factors)
        if any(exponent == 1 for _prime, exponent in parts):
            continue
        first, second = powerful_factorization(integer, factors)
        second_parts = factorization(second, factors)
        defects.append(integer - first**2 * second**3)
        defects.append(sum(exponent != 1 for _prime, exponent in second_parts))
    return defects


def powerful_split_coefficient_defects(limit: int = 55) -> list[sp.Expr]:
    """Check the exact resummed coefficient after the support split.

    If ``n=q*m``, ``q`` is powerful, ``m`` is squarefree and
    ``j=omega(m)>0``, then the positive part of ``a_z(n)`` equals

    ``(j-1)! z^j log(n) product_(p|m)log(p) B_(q,j)(z)``,

    where ``B_(q,j)`` is the coefficient at ``q`` of ``(1-z*A)^(-j)``.
    """

    max_depth = int(math.log(limit, 2))
    layers, logs, lambda_powers = _formal_level_one_data(limit, max_depth)
    factors = smallest_prime_factors(limit)
    z = sp.Symbol("z")
    defects: list[sp.Expr] = []
    for integer in range(2, limit + 1):
        powerful, squarefree = powerful_squarefree_split(integer, factors)
        squarefree_parts = factorization(squarefree, factors)
        depth = len(squarefree_parts)
        if depth == 0:
            continue
        log_integer = sum(
            exponent * logs[prime]
            for prime, exponent in factorization(integer, factors)
        )
        squarefree_weight = sp.prod(logs[prime] for prime, _ in squarefree_parts)
        powerful_multiplier = sum(
            sp.binomial(depth + power - 1, power)
            * z**power
            * lambda_powers[power][powerful]
            for power in range(max_depth + 1)
        )
        predicted = (
            sp.factorial(depth - 1)
            * z**depth
            * log_integer
            * squarefree_weight
            * powerful_multiplier
        )
        actual = sum(
            z**power * layers[power][integer]
            for power in range(1, max_depth + 1)
        )
        defects.append(sp.expand(actual - predicted))
    return defects


def squarefree_closed_form(
    integer: int, depth: int, factors: np.ndarray, logs: dict[int, sp.Symbol]
) -> sp.Expr:
    """Closed value of ``alpha_depth(integer)`` on squarefree support."""

    parts = factorization(integer, factors)
    if any(exponent != 1 for _prime, exponent in parts) or len(parts) != depth:
        return sp.Integer(0)
    log_integer = sum(logs[prime] for prime, _exponent in parts)
    prime_product = sp.prod(logs[prime] for prime, _exponent in parts)
    return sp.factorial(depth - 1) * log_integer * prime_product


def prime_power_layer(exponent: int, depth: int, log_prime: Scalar) -> Scalar:
    """Exact ``alpha_depth(p^exponent)`` for depth at least one."""

    if exponent < 1 or depth < 1:
        raise ValueError("exponent and depth must be positive")
    if depth > exponent:
        return log_prime * 0
    return math.comb(exponent, depth) * log_prime ** (depth + 1)


def prime_power_resummed(
    exponent: int, z: Scalar, log_prime: Scalar
) -> Scalar:
    """Exact full coefficient ``a_z(p^exponent)``."""

    if exponent < 1:
        raise ValueError("exponent must be positive")
    return log_prime * ((1 + z * log_prime) ** exponent - 2)


def squarefree_identity_defects(limit: int = 70) -> list[sp.Expr]:
    """Check every squarefree integer and depth through a small exact table."""

    max_depth = int(math.log(limit, 2))
    layers, logs = formal_level_one_layers(limit, max_depth)
    factors = smallest_prime_factors(limit)
    defects: list[sp.Expr] = []
    for integer in range(2, limit + 1):
        parts = factorization(integer, factors)
        if any(exponent != 1 for _prime, exponent in parts):
            continue
        for depth in range(1, max_depth + 1):
            expected = squarefree_closed_form(integer, depth, factors, logs)
            defects.append(sp.expand(layers[depth][integer] - expected))
    return defects


def phi1(rescaled_log: float, tolerance: float = 1e-16) -> float:
    """Regular level-one square-density factor from the fixed-depth mains."""

    value = 1.0 - 2.0 * rescaled_log
    power = rescaled_log * rescaled_log
    factorial_ratio = 1.0 / 2.0
    depth = 1
    while True:
        term = 2.0 * factorial_ratio * power
        value += term
        if abs(term) < tolerance:
            return value
        depth += 1
        power *= rescaled_log * rescaled_log
        factorial_ratio *= (depth - 1) / ((2 * depth - 1) * (2 * depth))
        if depth > 10000:
            raise RuntimeError("phi1 series did not converge")


def support_loss_control(limit: int) -> dict[str, float]:
    """Contrast genuine prime support with a planted dense-support failure.

    The prime-supported numerator is ``sum Lambda(n)^2``.  The dense toy puts
    the same logarithmic envelope on every integer and therefore really has
    the larger ``x log(x)^2`` scale.
    """

    if limit < 2:
        raise ValueError("limit must be at least two")
    factors = smallest_prime_factors(limit)
    mangoldt = von_mangoldt(limit, factors)
    logs = np.log(np.arange(2, limit + 1, dtype=float))
    scale = limit * math.log(limit)
    return {
        "prime_supported_over_x_log_x": float(
            np.dot(mangoldt[2:], mangoldt[2:]) / scale
        ),
        "dense_toy_over_x_log_x": float(np.dot(logs, logs) / scale),
    }


def cauchy_partial_fraction_defect() -> sp.Expr:
    """Exact defect in the early-smoothed right-line kernel split."""

    sigma, contour, frequency = sp.symbols(
        "sigma contour frequency", real=True
    )
    left_distance = sigma - sp.Rational(1, 2) - contour
    right_distance = sigma - sp.Rational(1, 2) + contour
    kernel = (2 * sigma - 1) / (
        (-left_distance + sp.I * frequency)
        * (right_distance + sp.I * frequency)
    )
    split = 1 / (-left_distance + sp.I * frequency) - 1 / (
        right_distance + sp.I * frequency
    )
    return sp.factor(kernel - split)


def cauchy_two_range_exponent_defects() -> tuple[sp.Expr, sp.Expr]:
    """Check the two exponents selected by the Fourier transform.

    The contour variable has real part ``contour`` before the extra
    ``n^(-1/2)`` in the logarithmic-derivative Dirichlet series is included.
    """

    sigma, contour = sp.symbols("sigma contour", real=True)
    left_distance = sigma - sp.Rational(1, 2) - contour
    right_distance = sigma - sp.Rational(1, 2) + contour
    below_x = sp.expand(contour + sp.Rational(1, 2) - right_distance)
    above_x = sp.expand(contour + sp.Rational(1, 2) + left_distance)
    return sp.expand(below_x - (1 - sigma)), sp.expand(above_x - sigma)


def commutator_local_mass(radius: sp.Expr) -> sp.Expr:
    """Exact first-moment mass of ``1/(1+u^2)`` on ``[-radius,radius]``."""

    return sp.log(1 + radius**2)


@dataclass(frozen=True)
class SquareDensityDecomposition:
    limit: int
    rescaled_log: float
    total: float
    x_log_x_prediction: float
    categories: dict[str, float]
    depth_diagonal: float
    depth_cross_positive: float
    depth_cross_negative: float

    def as_dict(self) -> dict[str, object]:
        return {
            "limit": self.limit,
            "rescaled_log": self.rescaled_log,
            "total": self.total,
            "total_over_x_log_x": self.total / (self.limit * math.log(self.limit)),
            "x_log_x_prediction": self.x_log_x_prediction,
            "categories": self.categories,
            "depth_diagonal": self.depth_diagonal,
            "depth_cross_positive": self.depth_cross_positive,
            "depth_cross_negative": self.depth_cross_negative,
        }


def square_density_decomposition(
    limit: int, rescaled_log: float
) -> SquareDensityDecomposition:
    """Compute the exact finite resummed diagonal split by arithmetic support.

    ``rescaled_log`` is ``log(x)/L`` and hence ``z=rescaled_log/log(x)``.
    The returned values use floating logarithms, but every convolution depth
    through the exact support ceiling ``Omega(n)`` is included.
    """

    if limit < 2 or rescaled_log < 0:
        raise ValueError("require limit>=2 and a nonnegative rescaled logarithm")
    layers, omega, big_omega = level_one_layers(limit)
    z = rescaled_log / math.log(limit)
    powers = z ** np.arange(layers.shape[0])
    terms = powers[:, None] * layers
    coefficient = np.sum(terms, axis=0)
    integers = np.arange(limit + 1)
    squarefree = omega == big_omega
    prime_power = omega == 1
    masks = {
        "primes": (omega == 1) & (big_omega == 1),
        "higher_prime_powers": prime_power & (big_omega > 1),
        "squarefree_distinct_composites": squarefree & (omega >= 2),
        "repeated_prime_mixed": (~squarefree) & (omega >= 2),
    }
    categories = {
        name: float(np.dot(coefficient[mask], coefficient[mask]))
        for name, mask in masks.items()
    }
    matrix = terms[:, 2:] @ terms[:, 2:].T
    depth_diagonal = float(np.trace(matrix))
    upper = matrix[np.triu_indices_from(matrix, k=1)] * 2.0
    depth_cross_positive = float(np.sum(upper[upper > 0]))
    depth_cross_negative = float(np.sum(upper[upper < 0]))
    total = float(np.dot(coefficient[2:], coefficient[2:]))
    if not math.isclose(total, sum(categories.values()), rel_tol=2e-12, abs_tol=1e-8):
        raise AssertionError("support categories do not partition the square density")
    if not math.isclose(
        total,
        depth_diagonal + depth_cross_positive + depth_cross_negative,
        rel_tol=2e-12,
        abs_tol=1e-8,
    ):
        raise AssertionError("depth matrix does not reconstruct the square density")
    return SquareDensityDecomposition(
        limit=limit,
        rescaled_log=rescaled_log,
        total=total,
        x_log_x_prediction=phi1(rescaled_log),
        categories=categories,
        depth_diagonal=depth_diagonal,
        depth_cross_positive=depth_cross_positive,
        depth_cross_negative=depth_cross_negative,
    )


def run_ladder(
    limits: tuple[int, ...] = (1000, 10000, 100000),
    rescaled_logs: tuple[float, ...] = (0.25, 0.5, 0.8),
) -> dict[str, object]:
    return {
        "rows": [
            square_density_decomposition(limit, ratio).as_dict()
            for limit in limits
            for ratio in rescaled_logs
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limits", default="1000,10000,100000")
    parser.add_argument("--ratios", default="0.25,0.5,0.8")
    args = parser.parse_args()
    limits = tuple(int(value) for value in args.limits.split(","))
    ratios = tuple(float(value) for value in args.ratios.split(","))
    print(json.dumps(run_ladder(limits, ratios), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
