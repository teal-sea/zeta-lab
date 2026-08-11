"""Direct finite Dirichlet recurrence for higher logarithmic derivatives.

Freeze the archimedean term at

    L_* = ell/2 + i*pi/4

and represent ``xi'/xi`` by the finite Dirichlet coefficient array

    r_0(1) = L_*,     r_0(n) = -Lambda(n).

If ``D(a)(n) = -log(n) a(n)`` and ``*`` is Dirichlet convolution, then

    r_(j+1) = r_j + D(r_j) * inverse(r_j)

is the finite coefficient recurrence coming from
``f''/f' = f'/f + (f'/f)'/(f'/f)``.  Level one is the known ``xi'`` control;
level two is the discovery object for ``xi''``.

This is a frozen finite model, not a tail theorem.  Its purpose is to expose a
second arithmetic route to the full-band curve and compare its convergence
with the completed-CUE oracle.
"""

from __future__ import annotations

import argparse
import json
import math

import numpy as np
from scipy.integrate import quad

from bian_audit import FIGURE_10_1
from cue_oracle import f1_closed


def smallest_prime_factors(limit: int) -> np.ndarray:
    factors = np.arange(limit + 1, dtype=np.int32)
    if limit >= 1:
        factors[1] = 1
    for prime in range(2, math.isqrt(limit) + 1):
        if factors[prime] == prime:
            multiples = np.arange(prime * prime, limit + 1, prime)
            untouched = factors[multiples] == multiples
            factors[multiples[untouched]] = prime
    return factors


def von_mangoldt(limit: int, factors: np.ndarray) -> np.ndarray:
    result = np.zeros(limit + 1, dtype=float)
    for integer in range(2, limit + 1):
        prime = int(factors[integer])
        quotient = integer
        while quotient % prime == 0:
            quotient //= prime
        if quotient == 1:
            result[integer] = math.log(prime)
    return result


def divisors(integer: int, factors: np.ndarray) -> list[int]:
    result = [1]
    while integer > 1:
        prime = int(factors[integer])
        old = tuple(result)
        prime_power = 1
        while integer % prime == 0:
            integer //= prime
            prime_power *= prime
            result.extend(divisor * prime_power for divisor in old)
    return result


def dirichlet_inverse(coefficients: np.ndarray, factors: np.ndarray) -> np.ndarray:
    limit = len(coefficients) - 1
    result = np.zeros(limit + 1, dtype=complex)
    result[1] = 1.0 / coefficients[1]
    for integer in range(2, limit + 1):
        subtotal = 0.0j
        for divisor in divisors(integer, factors):
            if divisor > 1:
                subtotal += coefficients[divisor] * result[integer // divisor]
        result[integer] = -subtotal / coefficients[1]
    return result


def dirichlet_convolution(left: np.ndarray, right: np.ndarray) -> np.ndarray:
    limit = len(left) - 1
    result = np.zeros(limit + 1, dtype=complex)
    support = np.flatnonzero(left[1:]) + 1
    for divisor in support:
        result[divisor::divisor] += left[divisor] * right[1 : limit // divisor + 1]
    return result


def next_log_derivative(coefficients: np.ndarray, factors: np.ndarray) -> np.ndarray:
    limit = len(coefficients) - 1
    derivative = np.zeros_like(coefficients)
    derivative[2:] = -np.log(np.arange(2, limit + 1)) * coefficients[2:]
    return coefficients + dirichlet_convolution(
        derivative, dirichlet_inverse(coefficients, factors)
    )


def bian_integral(kappa: int, alpha: float) -> float:
    return sum(
        float(coefficient) * alpha ** (index + 1) / (index + 1)
        for index, coefficient in enumerate(FIGURE_10_1[kappa], start=1)
    )


def f1_integral(alpha: float) -> float:
    return quad(lambda value: float(f1_closed(np.array([value]))[0]), 0.0, alpha)[0]


def coefficient_measures(ell: int, max_level: int = 2) -> list[tuple[np.ndarray, np.ndarray]]:
    """Return ``(log(n)/ell, |r_level(n)|^2/(n ell^2))`` for each level."""

    limit = int(math.exp(ell))
    factors = smallest_prime_factors(limit)
    mangoldt = von_mangoldt(limit, factors)
    coefficients = np.zeros(limit + 1, dtype=complex)
    coefficients[1] = ell / 2.0 + 1j * math.pi / 4.0
    coefficients[2:] = -mangoldt[2:]

    integers = np.arange(2, limit + 1)
    locations = np.log(integers) / ell
    measures = []
    for _level in range(1, max_level + 1):
        coefficients = next_log_derivative(coefficients, factors)
        weights = np.abs(coefficients[2:]) ** 2 / integers / ell**2
        measures.append((locations, weights))
    return measures


def run_ell(ell: int, alphas: tuple[float, ...]) -> dict[str, object]:
    limit = int(math.exp(ell))
    measures = coefficient_measures(ell, max_level=2)

    levels: dict[str, list[float]] = {}
    for level, (_locations, weights) in enumerate(measures, start=1):
        cumulative = np.concatenate(([0.0], np.cumsum(weights)))
        values = []
        for alpha in alphas:
            cutoff = min(limit, int(math.exp(alpha * ell)))
            values.append(float(cumulative[max(0, cutoff - 1)]))
        levels[str(level)] = values

    return {
        "ell": ell,
        "limit": limit,
        "alpha": list(alphas),
        "cumulative": levels,
        "controls": {
            "fgl_level1_integral": [f1_integral(alpha) for alpha in alphas],
            "bian_level2_11_term_integral": [
                bian_integral(2, alpha) for alpha in alphas
            ],
        },
    }


def run_ladder(
    ells: tuple[int, ...] = (8, 10, 12, 14),
    alphas: tuple[float, ...] = (0.125, 0.25, 0.375, 0.5),
) -> dict[str, object]:
    return {"results": [run_ell(ell, alphas) for ell in ells]}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ells", default="8,10,12,14")
    parser.add_argument("--alphas", default="0.125,0.25,0.375,0.5")
    args = parser.parse_args()
    ells = tuple(int(value) for value in args.ells.split(","))
    alphas = tuple(float(value) for value in args.alphas.split(","))
    print(json.dumps(run_ladder(ells, alphas), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
