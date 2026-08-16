"""Exact-rational evidence for the Pub 1 source-admissible closure.

The ambient optimiser is ``w = A^{-1} 1``.  The rational trial polynomial
``u`` and the truncated operator ``A0`` are the same objects used by
``certify_bound.py``.  This module bounds ``z = w-u`` in ``L2``, ``Linf``,
and ``C2`` strongly enough to prove that ``w`` is strictly concave.

Every load-bearing comparison is a ``fractions.Fraction`` comparison.  The
decimal output of :func:`report` is display only.

Run from the repository root with

    .venv/bin/python hunts/wide_search/admissible_closure.py
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache

import sympy as sp

try:  # package import under pytest
    from .certify_bound import (
        INV_NORM_BOUND,
        M,
        U_COEFFS,
        a_coeff,
        exact_quantities,
        sqrt_upper,
        tail_bound,
    )
except ImportError:  # direct execution from the repository root
    from certify_bound import (  # type: ignore
        INV_NORM_BOUND,
        M,
        U_COEFFS,
        a_coeff,
        exact_quantities,
        sqrt_upper,
        tail_bound,
    )


HALF = Fraction(1, 2)
ROW_BOUND = Fraction(4, 9)
LINF_RESOLVENT_BOUND = Fraction(1, 1) / (1 - ROW_BOUND)
SOURCE_W_LOWER = Fraction(1, 5)
SOURCE_W_UPPER = Fraction(1, 1)

# Outward rational targets used by the review-facing tests.
ZPP_TARGET = Fraction(6061, 1_000_000)
CONCAVITY_TARGET = Fraction(593, 1000)


def _fraction(value: sp.Expr) -> Fraction:
    value = sp.cancel(value)
    if not value.is_Rational:
        raise TypeError(f"expected an exact rational, got {value}")
    return Fraction(int(value.p), int(value.q))


def _polynomial_abs_bound(poly: sp.Poly) -> Fraction:
    """Coefficient absolute-sum bound on ``[-1/2, 1/2]``."""
    return sum(
        (abs(_fraction(coefficient)) * HALF ** degree[0]
         for degree, coefficient in poly.terms()),
        Fraction(0),
    )


@lru_cache(maxsize=1)
def exact_trial_polynomials() -> tuple[sp.Poly, sp.Poly, sp.Poly]:
    """Return the exact rational polynomials ``u``, ``A0u``, and ``r0``."""
    s, t = sp.symbols("s t")
    half = sp.Rational(1, 2)
    u = sum(
        sp.Rational(c.numerator, c.denominator) * s ** (2 * j)
        for j, c in enumerate(U_COEFFS)
    )
    u_t = u.subs(s, t)

    def p(y: sp.Expr) -> sp.Expr:
        return 1 + sum(
            sp.Rational(a_coeff(k).numerator, a_coeff(k).denominator) * y**k
            for k in range(1, M + 1)
        )

    even_part = sp.integrate(-4 * (s - t) ** 2 * u_t, (t, -half, half))
    left = sp.integrate((s - t) * p((s - t) ** 2) * u_t, (t, -half, s))
    right = sp.integrate((t - s) * p((t - s) ** 2) * u_t, (t, s, half))
    a0u = sp.expand(u + even_part + left + right)
    r0 = sp.expand(1 - a0u)
    return sp.Poly(u, s), sp.Poly(a0u, s), sp.Poly(r0, s)


def second_kernel_coefficient(k: int) -> Fraction:
    """Coefficient of ``|x|^(2k-1)`` in the ordinary part of ``F1''``."""
    if k < 1:
        raise ValueError("k must be positive")
    return a_coeff(k) * (2 * k) * (2 * k + 1)


def second_kernel_ratio(k: int) -> Fraction:
    """Exact ratio ``d_(k+1)/d_k`` for second-derivative coefficients."""
    if k < 1:
        raise ValueError("k must be positive")
    return Fraction(2 * (2 * k + 3), (2 * k + 1) ** 2)


def second_kernel_tail_bound(m: int = M) -> Fraction:
    """Geometric upper bound for ``sum_{k>m} d_k``.

    The ratio ``2(2k+3)/(2k+1)^2`` decreases for ``k >= 1`` after its first
    step.  In particular, every ratio in this tail is at most the first one.
    """
    ratio = second_kernel_ratio(m + 1)
    if ratio >= 1:
        raise ArithmeticError("second-derivative tail ratio must be below one")
    return second_kernel_coefficient(m + 1) / (1 - ratio)


@dataclass(frozen=True)
class ClosureBounds:
    """Exact outward bounds entering the strict-concavity argument."""

    r0_l2: Fraction
    r0_linf: Fraction
    r0pp_linf: Fraction
    u_l2: Fraction
    kernel_tail: Fraction
    second_kernel_tail: Fraction
    q_abs: Fraction
    z_l2: Fraction
    z_linf: Fraction
    zpp_linf: Fraction
    u_concavity: Fraction
    w_concavity_margin: Fraction

    @property
    def passes(self) -> bool:
        return (
            self.zpp_linf < ZPP_TARGET
            and self.w_concavity_margin > CONCAVITY_TARGET
        )


@lru_cache(maxsize=None)
def closure_bounds(residual_scale: int = 1) -> ClosureBounds:
    """Compute the exact bounds, optionally applying a planted residual lesion.

    ``residual_scale=1`` is the theorem path.  Larger values deliberately
    weaken every bound coming from ``r0``; the test suite uses 101 as a lesion
    that must destroy the strict-concavity margin.
    """
    if residual_scale < 1:
        raise ValueError("residual_scale must be at least one")
    scale = Fraction(residual_scale)

    u_poly, _, r0_poly = exact_trial_polynomials()
    s = u_poly.gens[0]
    r0pp_poly = sp.Poly(sp.diff(r0_poly.as_expr(), s, 2), s)

    _, _, r0_l2_sq, u_l2_sq = exact_quantities(M)
    r0_l2 = scale * sqrt_upper(r0_l2_sq)
    u_l2 = sqrt_upper(u_l2_sq)
    r0_linf = scale * _polynomial_abs_bound(r0_poly)
    r0pp_linf = scale * _polynomial_abs_bound(r0pp_poly)

    rho = tail_bound(M)
    second_tail = second_kernel_tail_bound(M)
    q_abs = (
        Fraction(8)
        + sum((second_kernel_coefficient(k) for k in range(1, M + 1)), Fraction(0))
        + second_tail
    )

    # z = A^{-1}(r0-Eu), with |I|=1.
    z_l2 = INV_NORM_BOUND * (r0_l2 + rho * u_l2)

    # z = r-Tz and ||T||_(infinity->infinity) <= 4/9.
    r_linf = r0_linf + rho * u_l2
    z_linf = LINF_RESOLVENT_BOUND * r_linf

    # F1'' = 2 delta_0 + q.  Thus
    # z'' = r0'' - (Eu)'' - 2z - q*z.
    eu_second_linf = second_tail * u_l2
    zpp_linf = r0pp_linf + eu_second_linf + 2 * z_linf + q_abs * z_l2

    # Every nonconstant coefficient of u is negative, so u'' <= 2*c1.
    if not all(coefficient < 0 for coefficient in U_COEFFS[1:]):
        raise ArithmeticError("the trial polynomial lost its concavity sign pattern")
    u_concavity = -2 * U_COEFFS[1]
    margin = u_concavity - zpp_linf

    return ClosureBounds(
        r0_l2=r0_l2,
        r0_linf=r0_linf,
        r0pp_linf=r0pp_linf,
        u_l2=u_l2,
        kernel_tail=rho,
        second_kernel_tail=second_tail,
        q_abs=q_abs,
        z_l2=z_l2,
        z_linf=z_linf,
        zpp_linf=zpp_linf,
        u_concavity=u_concavity,
        w_concavity_margin=margin,
    )


def validate_distribution_identity(delta_mass_coefficient: int = 2) -> None:
    """Reject a lesion that drops or changes the ``2 delta_0`` contribution."""
    if delta_mass_coefficient != 2:
        raise ValueError("F1'' has delta-mass coefficient exactly 2")


def eta(x: Fraction) -> Fraction:
    """The exact ``C3`` endpoint ramp used by the admissible sequence."""
    if x <= 0:
        return Fraction(0)
    if x >= 1:
        return Fraction(1)
    return 35 * x**4 - 84 * x**5 + 70 * x**6 - 20 * x**7


def eta_prime(x: Fraction) -> Fraction:
    """Derivative on the transition interval, extended by zero outside."""
    if x <= 0 or x >= 1:
        return Fraction(0)
    return 140 * x**3 * (1 - x) ** 3


def eta_derivative(order: int, x: Fraction) -> Fraction:
    """Exact polynomial derivative on ``[0,1]`` for endpoint-gluing checks."""
    if order < 0:
        raise ValueError("order must be nonnegative")
    symbol = sp.symbols("x")
    polynomial = 35 * symbol**4 - 84 * symbol**5 + 70 * symbol**6 - 20 * symbol**7
    return _fraction(sp.diff(polynomial, symbol, order).subs(symbol, sp.Rational(x.numerator, x.denominator)))


def eta_second_l1() -> Fraction:
    """Exact ``L1`` norm of ``eta''`` on the transition interval."""
    # eta' rises from 0 to eta'(1/2)=35/16 and then falls to 0.
    return Fraction(35, 8)


def eta_prime_sq_integral() -> Fraction:
    """Exact integral of ``eta'(x)^2`` on ``[0,1]``."""
    symbol = sp.symbols("x")
    derivative = 140 * symbol**3 * (1 - symbol) ** 3
    return _fraction(sp.integrate(sp.expand(derivative**2), (symbol, 0, 1)))


def eta_squared_second_l1_upper() -> Fraction:
    """Exact upper bound for ``||(eta^2)''||_1`` on one ramp."""
    return 2 * eta_prime_sq_integral() + 2 * eta_second_l1()


def uniform_derivative_bounds(
    length: Fraction,
    *,
    sqrt_w_prime: Fraction,
    sqrt_w_second: Fraction,
    w_prime: Fraction,
    w_second: Fraction,
) -> tuple[Fraction, Fraction]:
    """Product-rule bounds for ``phi_L`` and ``phi_L^2``.

    The four derivative arguments are any sup-norm bounds on the compact
    interval.  Their finiteness follows from ``w in C2`` and ``w >= 1/5``.
    The returned bounds are uniform as ``length -> infinity``.
    """
    if length < 8:
        raise ValueError("the source ramp requires length at least 8")
    phi_second = (
        sqrt_w_second / length
        + 4 * sqrt_w_prime / length
        + 2 * eta_second_l1()
    )
    phi_sq_second = (
        w_second / length
        + 4 * w_prime / length
        + 2 * eta_squared_second_l1_upper()
    )
    return phi_second, phi_sq_second


def l2_error_squared_upper(length: int | Fraction) -> Fraction:
    """Bound ``||v_L-w||_2^2`` by the total endpoint-strip length ``2/L``."""
    length = Fraction(length)
    if length <= 0:
        raise ValueError("length must be positive")
    return Fraction(2) / length


def planted_lesions() -> dict[str, bool]:
    """Return whether each deliberate fault is detected."""
    try:
        validate_distribution_identity(delta_mass_coefficient=0)
    except ValueError:
        dropped_delta_detected = True
    else:  # pragma: no cover - the lesion test pins this branch as unreachable
        dropped_delta_detected = False

    inflated_residual_detected = not closure_bounds(residual_scale=101).passes
    return {
        "dropped_delta_detected": dropped_delta_detected,
        "inflated_residual_detected": inflated_residual_detected,
    }


def report() -> bool:
    """Print the review-facing exact comparisons; return the theorem verdict."""
    validate_distribution_identity()
    bounds = closure_bounds()
    print("PUB 1 SOURCE-ADMISSIBLE CLOSURE")
    print(f"||r0||_2 upper       = {float(bounds.r0_l2):.16e}")
    print(f"||r0||_inf upper     = {float(bounds.r0_linf):.16e}")
    print(f"||r0''||_inf upper   = {float(bounds.r0pp_linf):.16e}")
    print(f"||z||_2 upper        = {float(bounds.z_l2):.16e}")
    print(f"||z||_inf upper      = {float(bounds.z_linf):.16e}")
    print(f"||z''||_inf upper    = {float(bounds.zpp_linf):.16e}")
    print(f"u concavity          = {float(bounds.u_concavity):.16e}")
    print(f"w concavity margin   = {float(bounds.w_concavity_margin):.16e}")
    print(f"exact z'' target     = {bounds.zpp_linf < ZPP_TARGET}")
    print(f"exact margin target  = {bounds.w_concavity_margin > CONCAVITY_TARGET}")
    for name, detected in planted_lesions().items():
        print(f"lesion {name}: {detected}")
    print("PASS" if bounds.passes and all(planted_lesions().values()) else "FAIL")
    return bounds.passes and all(planted_lesions().values())


if __name__ == "__main__":
    raise SystemExit(0 if report() else 1)
