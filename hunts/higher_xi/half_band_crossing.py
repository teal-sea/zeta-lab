"""Exact bookkeeping for the RC2 half-band crossing.

At sigma=3/2 the reflected and upper ranges form one Dirichlet polynomial
with weights sqrt(n)/x and x/n^(3/2).  The spacing-sensitive
Montgomery-Vaughan error is governed by sum n*|c_n|^2, not by the largest
integer in the polynomial.  RAMS2 bounds that weighted sum by O(x log x),
uniformly for every fixed polynomial cutoff ratio.
"""

from __future__ import annotations

from fractions import Fraction
import math

import numpy as np
import sympy as sp

from bandwidth_forensics import constant_window_bound
from dirichlet_recurrence import coefficient_measures


F = Fraction
TARGET_ALPHA = F(51, 100)
DYADIC_DELTA = F(3, 4)
FAR_CUTOFF_GAMMA = F(21, 20)
CONTOUR_EPSILON = F(1, 100)


def smoothing_fourier_transform(frequency: sp.Expr) -> sp.Expr:
    """Fourier transform of 4/(4+u^2) under integral exp(-i*u*xi) du."""

    return 2 * sp.pi * sp.exp(-2 * sp.Abs(frequency))


def two_range_square_weight(n: int, x: int) -> Fraction:
    """Squared magnitude weight on the frozen coefficient at sigma=3/2."""

    if n < 1 or x < 1:
        raise ValueError("n and x must be positive")
    if n <= x:
        return F(n, x * x)  # squared magnitude of sqrt(n)/x
    return F(x * x, n**3)  # squared magnitude of x/n^(3/2)


def spacing_weight(n: int, x: int) -> Fraction:
    """The n*|weight|^2 term in the spacing-sensitive mean-value error."""

    return n * two_range_square_weight(n, x)


def log_spacing_inverse_majorant(n: int) -> int:
    """Integer majorant for 1/(log(n+1)-log(n)) when n>=2."""

    if n < 2:
        raise ValueError("n must be at least two")
    return 2 * n


def current_half_band_deficit(alpha: Fraction = TARGET_ALPHA) -> Fraction:
    """Zero-epsilon exponent missing from gamma<1 and gamma>2*alpha."""

    alpha = F(alpha)
    return max(F(0), 2 * alpha - 1)


def urms2_051_witness() -> dict[str, Fraction]:
    """Rational margins for the spacing-sensitive RC2 proof at alpha=0.51."""

    alpha = TARGET_ALPHA
    delta = DYADIC_DELTA
    gamma = FAR_CUTOFF_GAMMA
    epsilon = CONTOUR_EPSILON
    return {
        "alpha": alpha,
        "delta": delta,
        "gamma": gamma,
        "epsilon": epsilon,
        "target_rho_on_lowest_block": 2 * alpha / delta,
        "far_cutoff_rho_on_lowest_block": 2 * gamma / delta,
        "initial_interval_margin": 1 - delta,
        "mean_value_margin": delta - alpha,
        "far_tail_margin": gamma * (1 - 2 * epsilon) - 2 * alpha,
        "central_segment_margin": 1 - alpha * (F(1, 2) + epsilon),
    }


def urms2_051_margins_positive() -> bool:
    witness = urms2_051_witness()
    return all(
        witness[key] > 0
        for key in (
            "initial_interval_margin",
            "mean_value_margin",
            "far_tail_margin",
            "central_segment_margin",
        )
    )


def endpoint_status(alpha: Fraction) -> dict[str, Fraction | bool]:
    """Apply the fixed 0.51 witness to one requested endpoint lesion."""

    alpha = F(alpha)
    delta = DYADIC_DELTA
    gamma = FAR_CUTOFF_GAMMA
    epsilon = CONTOUR_EPSILON
    mean_value_margin = delta - alpha
    far_tail_margin = gamma * (1 - 2 * epsilon) - 2 * alpha
    return {
        "alpha": alpha,
        "mean_value_margin": mean_value_margin,
        "far_tail_margin": far_tail_margin,
        "reached": mean_value_margin > 0 and far_tail_margin > 0,
    }


def generic_length_lesion(alpha: Fraction = TARGET_ALPHA) -> dict[str, Fraction]:
    """Recover the old contradiction after replacing spacing by max length."""

    alpha = F(alpha)
    return {
        "required_gamma_lower": 2 * alpha,
        "generic_gamma_upper": F(1),
        "deficit": current_half_band_deficit(alpha),
    }


def corrected_simplicity_bound() -> dict[str, Fraction]:
    """Exact rational lower bound from the bandwidth-0.51 constant window."""

    result = constant_window_bound(TARGET_ALPHA)
    return {
        "bandwidth": TARGET_ALPHA,
        "denominator_upper": result["denominator_upper"],
        "simple_proportion_lower": result["simplicity_lower_bound"],
    }


def finite_height_spacing_experiment(ell: int, alpha: float = 0.51) -> dict[str, float]:
    """Compare actual spacing cost with the generic maximum-length lesion."""

    if ell < 4 or not 0 < alpha < 1:
        raise ValueError("require ell >= 4 and 0 < alpha < 1")
    _locations, normalized = coefficient_measures(ell, max_level=2)[1]
    integers = np.arange(2, len(normalized) + 2, dtype=float)
    coefficient_squares = normalized * integers * ell**2
    x = math.exp(alpha * ell)
    lower = integers <= x
    diagonal = float(
        np.sum(coefficient_squares[lower] * integers[lower] / x**2)
        + np.sum(coefficient_squares[~lower] * x**2 / integers[~lower] ** 3)
    )
    spacing_cost = float(
        np.sum(coefficient_squares[lower] * integers[lower] ** 2 / x**2)
        + np.sum(coefficient_squares[~lower] * x**2 / integers[~lower] ** 2)
    )
    maximum_length_cost = len(integers) * diagonal
    return {
        "ell": float(ell),
        "alpha": alpha,
        "x": x,
        "diagonal": diagonal,
        "spacing_cost": spacing_cost,
        "spacing_over_x_log_x": spacing_cost / (x * math.log(x)),
        "generic_to_spacing_ratio": maximum_length_cost / spacing_cost,
    }


def audit() -> dict[str, object]:
    return {
        "half_band_deficit": current_half_band_deficit(),
        "witness": urms2_051_witness(),
        "endpoint_status": tuple(
            endpoint_status(alpha)
            for alpha in (F(499, 1000), F(1, 2), F(501, 1000), F(51, 100))
        ),
        "generic_length_lesion": generic_length_lesion(),
        "finite_height_ell_8": finite_height_spacing_experiment(8),
        "simplicity": corrected_simplicity_bound(),
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
