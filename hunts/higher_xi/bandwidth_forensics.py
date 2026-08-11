"""Exact bandwidth bookkeeping for the rebuilt level-two bridge.

The published ``1/100`` band used one convenient triple of dyadic parameters.
This module separates that choice from the strict inequalities in the proof,
then records the first tail improvement: insert the existing pointwise
coefficient envelope between the RAMS2 range and the far Hilbert tail.
Finite-prime peeling then removes the fixed-rho Cauchy-radius restriction and
leaves ``alpha=1/2`` as the contour architecture's strict endpoint.

It also records the first downstream obstruction.  For an arbitrary real
spectral factor, Cauchy-Schwarz bounds the signed autocorrelation by its
diagonal norm.  Combined with the exact corrected series, this excludes every
bandwidth through ``1227/2500``.  A completion-of-squares argument closes the
remaining gap through ``1/2`` for arbitrary real spectral factors.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import comb

import numpy as np
import sympy as sp
from scipy.linalg import solve

from corrected_form_factor import (
    MAJORANT_CUTOFF,
    TWO_STEP_RATIO,
    coarse_upper_coefficient,
    corrected_coefficients,
    fock_upper_coefficient,
    integrated_tail_bound,
    tail_bound,
    truncated_integral,
)


F = Fraction
RAMS_RHO = F(1, 10)
POINTWISE_RHO = F(1, 2)
PROMOTED_ALPHA = F(1, 100)
ORIGINAL_ENDPOINT = F(1, 40)
IMPROVED_ENDPOINT = F(1, 20)
PRIME_SPLIT_ENDPOINT = F(1, 2)
SQRT_TWO = sp.sqrt(2)
OPTIMIZED_GAUSSIAN_RATE_LINEAR = 2 + 2 * SQRT_TWO
OPTIMIZED_GAUSSIAN_RATE_QUADRATIC = 7 + 5 * SQRT_TWO


def _as_fraction(value: Fraction | int) -> Fraction:
    return value if isinstance(value, Fraction) else F(value)


def original_architecture_feasible(alpha: Fraction) -> bool:
    """Whether the old RAMS-cutoff-plus-Hilbert-tail split has parameters."""

    alpha = _as_fraction(alpha)
    return F(0) < alpha < ORIGINAL_ENDPOINT


def original_parameter_witness(alpha: Fraction) -> dict[str, Fraction]:
    """Construct strict ``delta,beta,epsilon`` for every ``alpha<1/40``."""

    alpha = _as_fraction(alpha)
    if not original_architecture_feasible(alpha):
        raise ValueError("the original architecture requires 0 < alpha < 1/40")
    delta = (40 * alpha + 1) / 2
    beta = (2 * alpha + RAMS_RHO * delta / 2) / 2
    epsilon = (1 - 2 * alpha / beta) / 4
    return {
        "alpha": alpha,
        "delta": delta,
        "beta": beta,
        "epsilon": epsilon,
        "target_rho_margin": RAMS_RHO - 2 * alpha / delta,
        "cutoff_rho_margin": RAMS_RHO - 2 * beta / delta,
        "far_tail_margin": beta * (1 - 2 * epsilon) - 2 * alpha,
    }


def improved_architecture_feasible(alpha: Fraction) -> bool:
    """Whether the intermediate-envelope tail split has parameters."""

    alpha = _as_fraction(alpha)
    return F(0) < alpha < IMPROVED_ENDPOINT


def improved_parameter_witness(alpha: Fraction) -> dict[str, Fraction]:
    """Construct strict parameters for the improved ``alpha<1/20`` band."""

    alpha = _as_fraction(alpha)
    if not improved_architecture_feasible(alpha):
        raise ValueError("the improved architecture requires 0 < alpha < 1/20")
    delta = (20 * alpha + 1) / 2
    beta = (alpha + RAMS_RHO * delta / 2) / 2
    gamma = (2 * alpha + POINTWISE_RHO * delta / 2) / 2
    epsilon = min(F(1, 16), (1 - 2 * alpha / gamma) / 4)
    return {
        "alpha": alpha,
        "delta": delta,
        "rams_cutoff_beta": beta,
        "envelope_cutoff_gamma": gamma,
        "epsilon": epsilon,
        "target_rho_margin": RAMS_RHO - 2 * alpha / delta,
        "rams_cutoff_margin": RAMS_RHO - 2 * beta / delta,
        "shell_decay_margin": beta - alpha,
        "envelope_rho_margin": POINTWISE_RHO - 2 * gamma / delta,
        "far_tail_margin": gamma * (1 - 2 * epsilon) - 2 * alpha,
    }


def gaussian_powerful_rate(rho: sp.Expr, radius: sp.Expr) -> sp.Expr:
    """Laplace exponent spent by the powerful-core Cauchy majorant."""

    first = radius / (1 - radius)
    second = radius / (1 - radius) ** 2
    return sp.expand(2 * first * rho + (second + first**2) * rho**2)


def optimized_gaussian_rho() -> sp.Expr:
    """Supremal rho from optimizing the Cauchy radius above ``1/sqrt(2)``."""

    rho = sp.Symbol("rho")
    roots = sp.solve(
        OPTIMIZED_GAUSSIAN_RATE_QUADRATIC * rho**2
        + OPTIMIZED_GAUSSIAN_RATE_LINEAR * rho
        - 1,
        rho,
    )
    return next(root for root in roots if root.evalf() > 0)


def optimized_cluster_feasible(alpha: Fraction) -> bool:
    """Whether optimized powerful-core control can cover the target alpha."""

    alpha = _as_fraction(alpha)
    rho = 2 * _rational(alpha)
    rate = (
        OPTIMIZED_GAUSSIAN_RATE_LINEAR * rho
        + OPTIMIZED_GAUSSIAN_RATE_QUADRATIC * rho**2
    )
    return bool(rate < 1)


def split_powerful_witness(rho: Fraction) -> dict[str, Fraction | int]:
    """Choose a tail-prime Cauchy radius with a subcritical Laplace rate."""

    rho = _as_fraction(rho)
    if rho <= 0:
        raise ValueError("rho must be positive")
    denominator = 2
    while True:
        radius = F(1, denominator)
        first = radius / (1 - radius)
        second = radius / (1 - radius) ** 2
        rate = 2 * first * rho + (second + first**2) * rho**2
        if rate < F(1, 2):
            break
        denominator += 1
    return {
        "rho": rho,
        "tail_radius": radius,
        "small_prime_cutoff": denominator**2,
        "laplace_rate": rate,
        "laplace_margin": 1 - rate,
    }


def prime_split_architecture_feasible(alpha: Fraction) -> bool:
    """Whether arbitrary compact RAMS2 control closes the current RC2 tail."""

    alpha = _as_fraction(alpha)
    return F(0) < alpha < PRIME_SPLIT_ENDPOINT


def prime_split_parameter_witness(alpha: Fraction) -> dict[str, Fraction]:
    """Strict RC2 parameters for every ``alpha<1/2`` after the prime split."""

    alpha = _as_fraction(alpha)
    if not prime_split_architecture_feasible(alpha):
        raise ValueError("the prime-split architecture requires 0 < alpha < 1/2")
    delta = (2 * alpha + 1) / 2
    gamma = (2 * alpha + delta) / 2
    beta = (alpha + gamma) / 2
    epsilon = (1 - 2 * alpha / gamma) / 4
    return {
        "alpha": alpha,
        "delta": delta,
        "rams_cutoff_beta": beta,
        "far_tail_cutoff_gamma": gamma,
        "epsilon": epsilon,
        "target_rho": 2 * alpha / delta,
        "rams_cutoff_rho": 2 * beta / delta,
        "far_cutoff_rho": 2 * gamma / delta,
        "shell_decay_margin": beta - alpha,
        "far_tail_margin": gamma * (1 - 2 * epsilon) - 2 * alpha,
        "mean_value_margin": delta - gamma,
        "dyadic_margin": 1 - delta,
    }


def optimized_parameter_witness(alpha: Fraction) -> dict[str, sp.Expr]:
    """Give one rational Cauchy-radius witness for the ``alpha=0.07`` milestone."""

    alpha = _as_fraction(alpha)
    radius = F(71, 100)
    rho_bound = F(143, 1000)
    if gaussian_powerful_rate(_rational(rho_bound), _rational(radius)) >= 1:
        raise AssertionError("the rational Gaussian witness lost its Laplace gap")
    if not 2 * alpha < rho_bound:
        raise ValueError("this fixed rational witness does not cover alpha")
    delta = (2 * alpha / rho_bound + 1) / 2
    beta = (alpha + rho_bound * delta / 2) / 2
    gamma = (2 * alpha + POINTWISE_RHO * delta / 2) / 2
    epsilon = min(F(1, 16), (1 - 2 * alpha / gamma) / 4)
    return {
        "alpha": _rational(alpha),
        "cauchy_radius": _rational(radius),
        "rho_bound": _rational(rho_bound),
        "laplace_margin": sp.factor(
            1 - gaussian_powerful_rate(_rational(rho_bound), _rational(radius))
        ),
        "delta": _rational(delta),
        "rams_cutoff_beta": _rational(beta),
        "envelope_cutoff_gamma": _rational(gamma),
        "epsilon": _rational(epsilon),
        "target_rho_margin": _rational(rho_bound - 2 * alpha / delta),
        "rams_cutoff_margin": _rational(rho_bound - 2 * beta / delta),
        "shell_decay_margin": _rational(beta - alpha),
        "envelope_rho_margin": _rational(POINTWISE_RHO - 2 * gamma / delta),
        "far_tail_margin": _rational(gamma * (1 - 2 * epsilon) - 2 * alpha),
    }


def dependency_graph() -> tuple[dict[str, str], ...]:
    """Machine-readable list of the bandwidth-bearing proof obligations."""

    return (
        {
            "lemma": "RAMS2 target range",
            "inequality": "2*alpha/delta < rho_RAMS",
            "proved_range": "every fixed compact rho_RAMS after prime peeling",
            "classification": "nonbinding",
        },
        {
            "lemma": "RAMS2 upper cutoff",
            "inequality": "2*beta/delta < rho_RAMS",
            "proved_range": "every fixed compact rho_RAMS after prime peeling",
            "classification": "nonbinding",
        },
        {
            "lemma": "RAMS2 far cutoff",
            "inequality": "2*gamma/delta < rho_RAMS",
            "proved_range": "every fixed compact rho_RAMS after prime peeling",
            "classification": "nonbinding",
        },
        {
            "lemma": "old far Hilbert tail",
            "inequality": "2*alpha < beta*(1-2*epsilon)",
            "proved_range": "beta < rho_RAMS*delta/2",
            "classification": "non-sharp tail majorant",
        },
        {
            "lemma": "intermediate coefficient shell",
            "inequality": "alpha < beta",
            "proved_range": "A_2(u) <= C*u*log(u)^2 for rho < 1/2",
            "classification": "current pointwise envelope",
        },
        {
            "lemma": "far Hilbert tail after shell",
            "inequality": "2*alpha < gamma*(1-2*epsilon)",
            "proved_range": "2*gamma/delta < 1/2",
            "classification": "nonbinding for alpha < 1/20",
        },
        {
            "lemma": "dyadic initial interval",
            "inequality": "0 < delta < 1",
            "proved_range": "O(H^delta log(H)^3) = o(H log H)",
            "classification": "strict endpoint only",
        },
        {
            "lemma": "height commutator",
            "inequality": "alpha*(1/2+epsilon) < 1",
            "proved_range": "pointwise O(x^(1/2+epsilon) log(T)/T)",
            "classification": "nonbinding",
        },
        {
            "lemma": "Montgomery-Vaughan finite ranges",
            "inequality": "max(alpha,beta,gamma) < delta",
            "proved_range": "relative errors O(x/U), O(Y/U), O(W/U)",
            "classification": "binding with the far tail at alpha = 1/2",
        },
        {
            "lemma": "Borel/Laplace and cluster sum",
            "inequality": "E_R(rho) < 1 with p > R^-2 on the tail-prime product",
            "proved_range": "every compact rho band after finite-prime peeling",
            "classification": "nonbinding after the prime split",
        },
    )


def continuation_scan() -> tuple[dict[str, str], ...]:
    """Classify the directive's alpha checkpoints before and after the fix."""

    checkpoints = (
        F(1, 100),
        F(1, 50),
        F(1, 40),
        F(1, 20),
        F(3, 40),
        F(1, 10),
        F(3, 20),
        F(1, 5),
        F(3, 10),
        F(1, 2),
        F(68213, 100000),
    )
    rows = []
    for alpha in checkpoints:
        if alpha <= PROMOTED_ALPHA:
            old = "PROVED"
        elif original_architecture_feasible(alpha):
            old = "PROVABLE WITH CURRENT LEMMA"
        else:
            old = "FAILS"
        improved = "PROVED" if improved_architecture_feasible(alpha) else "FAILS"
        optimized = "PROVED" if optimized_cluster_feasible(alpha) else "FAILS"
        split = "PROVED" if prime_split_architecture_feasible(alpha) else "FAILS"
        rows.append(
            {
                "alpha": str(alpha),
                "old_architecture": old,
                "after_shell_split": improved,
                "after_cauchy_optimization": optimized,
                "after_prime_split": split,
                "first_failed_obligation": (
                    "none"
                    if prime_split_architecture_feasible(alpha)
                    else "far-tail cutoff must be shorter than the dyadic height"
                ),
            }
        )
    return tuple(rows)


def shell_stieltjes_bound(log_y: sp.Expr) -> sp.Expr:
    """Bound the shell tail after retaining prime-support density.

    If ``A(u) <= C*u*log(u)^2``, partial summation gives

        integral_[Y,infinity] u^-3 dA(u)
        <= C*Y^-2*(3/2 log(Y)^2 + 3/2 log(Y) + 3/4).

    The returned expression is the parenthesized polynomial.
    """

    return sp.Rational(3, 2) * log_y**2 + sp.Rational(3, 2) * log_y + sp.Rational(3, 4)


def _rational(value: Fraction) -> sp.Rational:
    return sp.Rational(value.numerator, value.denominator)


@lru_cache(maxsize=1)
def f2_half_band_bernstein_floor() -> Fraction:
    """Exact Bernstein floor showing ``F2(alpha)>0`` on ``0<alpha<=1/2``."""

    x, t = sp.symbols("x t")
    polynomial = sum(
        _rational(coefficient) * x**index
        for index, coefficient in corrected_coefficients(40).items()
    )
    finite_tail = sum(
        _rational(fock_upper_coefficient(index)) * x**index
        for index in range(41, MAJORANT_CUTOFF + 1)
    )
    first_even = MAJORANT_CUTOFF + 1
    first_odd = MAJORANT_CUTOFF + 2
    ratio = _rational(TWO_STEP_RATIO)
    coarse_tail = (
        _rational(coarse_upper_coefficient(first_even)) * x**first_even
        + _rational(coarse_upper_coefficient(first_odd)) * x**first_odd
    ) / (1 - ratio * x**2)
    numerator = sp.cancel(
        (polynomial - finite_tail - coarse_tail) * (1 - ratio * x**2) / x
    )
    power = sp.Poly(sp.expand(numerator), x)
    degree = power.degree()
    on_unit = sp.Poly(sp.expand(power.as_expr().subs(x, t / 2)), t)
    coefficients = [on_unit.nth(index) for index in range(degree + 1)]
    bernstein = [
        sum(
            coefficients[index]
            * sp.Rational(comb(order, index), comb(degree, index))
            for index in range(order + 1)
        )
        for order in range(degree + 1)
    ]
    floor = min(bernstein)
    if floor <= 0:
        raise AssertionError("the exact Bernstein positivity check failed")
    return F(int(floor.p), int(floor.q))


def constant_window_bound(beta: Fraction) -> dict[str, Fraction]:
    """Exact downstream bound for the normalized constant bandwidth-beta window."""

    beta = _as_fraction(beta)
    if not F(0) < beta <= F(1):
        raise ValueError("beta must lie in (0,1]")
    finite_denominator = 1 / beta + sum(
        2 * coefficient * beta**index / ((index + 1) * (index + 2))
        for index, coefficient in corrected_coefficients(40).items()
    )
    tail_loss = 2 * tail_bound(beta)
    return {
        "beta": beta,
        "finite_denominator": finite_denominator,
        "tail_loss": tail_loss,
        "denominator_upper": finite_denominator + tail_loss,
        "simplicity_lower_bound": 2 - finite_denominator - tail_loss,
    }


def universal_window_denominator_floor(beta: Fraction) -> dict[str, Fraction]:
    """Lower bound for every normalized real spectral factor at bandwidth beta."""

    beta = _as_fraction(beta)
    if not F(0) < beta <= F(1, 2):
        raise ValueError("beta must lie in (0,1/2]")
    integral_upper = truncated_integral(beta) + integrated_tail_bound(beta)
    multiplier_floor = 1 - 2 * integral_upper
    return {
        "beta": beta,
        "form_factor_integral_upper": integral_upper,
        "quadratic_multiplier_floor": multiplier_floor,
        "denominator_floor": multiplier_floor / beta,
    }


def half_band_coercivity_margin() -> dict[str, Fraction]:
    """Exact completion-of-squares margin excluding every beta through 1/2."""

    lower_endpoint = F(1227, 2500)
    half = F(1, 2)
    interaction_center = sum(
        2
        * coefficient
        * lower_endpoint ** (index + 2)
        / ((index + 1) * (index + 2))
        for index, coefficient in corrected_coefficients(40).items()
    )
    interaction_lower = (
        interaction_center - lower_endpoint**2 * tail_bound(lower_endpoint)
    )
    integral_upper = truncated_integral(half) + integrated_tail_bound(half)
    operator_norm_upper = 2 * integral_upper
    correction_upper = (
        4
        * integral_upper**2
        / (lower_endpoint * (1 - operator_norm_upper))
    )
    margin = 4 * interaction_lower - correction_upper
    if margin <= 0:
        raise AssertionError("the half-band coercivity margin must be positive")
    return {
        "lower_endpoint": lower_endpoint,
        "interaction_lower": interaction_lower,
        "operator_norm_upper": operator_norm_upper,
        "completion_correction_upper": correction_upper,
        "denominator_margin_over_two": margin,
    }


def useful_bandwidth_bounds() -> dict[str, Fraction]:
    """Rigorous current bounds for the first useful downstream bandwidth."""

    initial_lower = F(1227, 2500)
    obstruction = universal_window_denominator_floor(initial_lower)
    if obstruction["denominator_floor"] <= 2:
        raise AssertionError("the bandwidth-0.4908 universal obstruction must hold")
    coercivity = half_band_coercivity_margin()
    upper = F(51, 100)
    candidate = constant_window_bound(upper)
    if candidate["simplicity_lower_bound"] <= 0:
        raise AssertionError("the bandwidth-0.51 constant window must be useful")
    return {
        "lower_bound": F(1, 2),
        "initial_cauchy_lower_bound": initial_lower,
        "lower_bound_denominator_floor": obstruction["denominator_floor"],
        "half_band_coercivity_margin": coercivity["denominator_margin_over_two"],
        "upper_bound": upper,
        "upper_bound_simplicity": candidate["simplicity_lower_bound"],
    }


def numerical_window_optimum(beta: float, nodes: int = 400) -> dict[str, float]:
    """Exploratory midpoint discretization of the unrestricted spectral factor."""

    if not 0 < beta <= 1 or nodes < 20:
        raise ValueError("require 0 < beta <= 1 and at least 20 nodes")
    step = beta / nodes
    points = (np.arange(nodes) + 0.5) * step - beta / 2
    distances = np.abs(points[:, None] - points[None, :])
    form_factor = np.zeros_like(distances)
    for index, coefficient in corrected_coefficients(40).items():
        form_factor += float(coefficient) * distances**index
    matrix = step * np.eye(nodes) + step**2 * form_factor
    constraint = np.full(nodes, step)
    direction = solve(matrix, constraint, assume_a="sym")
    minimum = 1 / float(constraint @ direction)
    window = direction / float(constraint @ direction)
    return {
        "beta": beta,
        "nodes": float(nodes),
        "denominator": minimum,
        "simplicity_value": 2 - minimum,
        "window_minimum": float(window.min()),
        "window_maximum": float(window.max()),
    }


def audit() -> dict[str, object]:
    return {
        "dependency_graph": dependency_graph(),
        "continuation_scan": continuation_scan(),
        "witness_alpha_0_011": original_parameter_witness(F(11, 1000)),
        "witness_alpha_0_049": improved_parameter_witness(F(49, 1000)),
        "optimized_gaussian_rho": optimized_gaussian_rho(),
        "witness_alpha_0_07": optimized_parameter_witness(F(7, 100)),
        "prime_split_rho_2_1": split_powerful_witness(F(21, 10)),
        "witness_alpha_0_499": prime_split_parameter_witness(F(499, 1000)),
        "f2_half_band_bernstein_floor": f2_half_band_bernstein_floor(),
        "half_band_coercivity_margin": half_band_coercivity_margin(),
        "useful_bandwidth_bounds": useful_bandwidth_bounds(),
        "numerical_window_alpha_0_499": numerical_window_optimum(0.499),
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
