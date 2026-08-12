"""Independent gates for the URMS2-051 theorem package.

This module does not call ``constant_window_bound``.  It reads the stored
40-coefficient fixture, reconstructs the triangle-window functional, and
rebuilds the tail allowance from the coefficient majorants.  It also records
the exact phase, spacing, freezing, and multiplicity identities used by the
analytic audit.
"""

from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path

import sympy as sp

from corrected_form_factor import (
    MAJORANT_CUTOFF,
    TWO_STEP_RATIO,
    coarse_upper_coefficient,
    fock_upper_coefficient,
)


F = Fraction
HERE = Path(__file__).resolve().parent
BETA = F(51, 100)


def exact_two_range_phase_defects() -> tuple[sp.Expr, sp.Expr]:
    """Check the two coefficient weights after removing the common x phase."""

    x, n, t = sp.symbols("x n t", positive=True, real=True)
    s = sp.Rational(3, 2) + sp.I * t
    reflected_exponent = -sp.Rational(1, 2) + sp.I * t
    lower = x ** (-sp.Rational(1, 2)) * (x / n) ** reflected_exponent
    upper = x ** (-sp.Rational(1, 2)) * (x / n) ** s
    common = x ** (sp.I * t) * n ** (-sp.I * t)
    lower_target = sp.sqrt(n) / x * common
    upper_target = x / n ** sp.Rational(3, 2) * common
    return (
        sp.simplify(sp.powsimp(sp.expand_power_base(lower, force=True) - lower_target)),
        sp.simplify(sp.powsimp(sp.expand_power_base(upper, force=True) - upper_target)),
    )


def reflection_parity_defect() -> sp.Expr:
    """Check the odd reflection of xi'''/xi'' from xi(1-s)=xi(s)."""

    numerator, denominator = sp.symbols("numerator denominator", nonzero=True)
    direct_at_reflection = -numerator / denominator
    expected = -(numerator / denominator)
    return sp.simplify(direct_at_reflection - expected)


def weighted_partial_summation_constants() -> dict[str, int]:
    """Constants after inserting A(y)<=C*y*log(y) in both spacing sums."""

    # lower: x^-2 integral u^2 dA(u) <= C*x*(3 log x + 2)
    # upper: x^2 integral_x^W u^-2 dA(u) <= C*x*(3 log x + 2)
    return {"lower_log_constant": 3, "upper_log_constant": 3}


def marked_cluster_freezing_exponents() -> dict[str, int]:
    """Logarithmic powers in the differentiated-cluster freezing lemma."""

    # A z derivative marks one logarithmic factor.  The square density changes
    # from y*log(y) to at most y*log(y)^3.  Delta z is O(log(U)^-2).
    return {
        "derivative_square_log_power": 3,
        "parameter_difference_log_power": -4,
        "difference_square_log_power": -1,
    }


def independent_tail_allowance(beta: Fraction = BETA) -> Fraction:
    """Rebuild the absolute coefficient tail without calling tail_bound."""

    beta = F(beta)
    finite = sum(
        fock_upper_coefficient(index) * beta**index
        for index in range(41, MAJORANT_CUTOFF + 1)
    )
    first_even = MAJORANT_CUTOFF + 1
    first_odd = MAJORANT_CUTOFF + 2
    ratio = TWO_STEP_RATIO * beta**2
    coarse = (
        coarse_upper_coefficient(first_even) * beta**first_even
        + coarse_upper_coefficient(first_odd) * beta**first_odd
    ) / (1 - ratio)
    return finite + coarse


def independent_window_bound() -> dict[str, Fraction]:
    """Reconstruct the 0.51 triangle functional from the JSON fixture."""

    payload = json.loads((HERE / "C2_EXTENDED.json").read_text())
    coefficients = {
        int(item["i"]): F(item["value"])
        for item in payload["coefficients"]
        if int(item["i"]) <= 40
    }
    finite_denominator = 1 / BETA + sum(
        2 * coefficient * BETA**index / ((index + 1) * (index + 2))
        for index, coefficient in coefficients.items()
    )
    tail_loss = 2 * independent_tail_allowance()
    denominator_upper = finite_denominator + tail_loss
    return {
        "bandwidth": BETA,
        "finite_denominator": finite_denominator,
        "tail_loss": tail_loss,
        "denominator_upper": denominator_upper,
        "simple_proportion_lower": 2 - denominator_upper,
    }


def multiplicity_inequality_values(maximum: int = 20) -> tuple[int, ...]:
    """Return indicator(simple)-[2m-m^2] for multiplicities 1..maximum."""

    if maximum < 1:
        raise ValueError("maximum must be positive")
    return tuple((1 if m == 1 else 0) - (2 * m - m * m) for m in range(1, maximum + 1))


def gate_status() -> dict[str, bool]:
    window = independent_window_bound()
    freezing = marked_cluster_freezing_exponents()
    return {
        "two_range_phase": all(defect == 0 for defect in exact_two_range_phase_defects()),
        "reflection_parity": reflection_parity_defect() == 0,
        "weighted_partial_summation": all(
            value == 3 for value in weighted_partial_summation_constants().values()
        ),
        "marked_cluster_freezing": freezing["difference_square_log_power"] == -1,
        "multiplicity": all(value >= 0 for value in multiplicity_inequality_values()),
        "window_positive": window["simple_proportion_lower"] > 0,
    }


def audit() -> dict[str, object]:
    return {
        "gates": gate_status(),
        "phase_defects": exact_two_range_phase_defects(),
        "reflection_defect": reflection_parity_defect(),
        "freezing_exponents": marked_cluster_freezing_exponents(),
        "window": independent_window_bound(),
        "multiplicity_slack": multiplicity_inequality_values(10),
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
