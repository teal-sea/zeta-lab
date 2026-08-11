"""Exact audit of Bian's displayed higher-derivative simplicity calculation.

The coefficient rows are transcribed from Figure 10.1 of Ji Bian's 2008
thesis.  Equation (11.5) states that the eleven-term simplicity expression at
the endpoint is

    1 - 2 * sum_i C[kappa,i] / ((i+1)(i+2)).

Every calculation in this module uses ``fractions.Fraction``.
"""

from __future__ import annotations

from fractions import Fraction


F = Fraction


FIGURE_10_1: dict[int, tuple[Fraction, ...]] = {
    1: (
        F(1),
        F(-4),
        F(4),
        F(0),
        F(4, 3),
        F(0),
        F(16, 45),
        F(0),
        F(8, 105),
        F(0),
        F(64, 4725),
    ),
    2: (
        F(1),
        F(-4),
        F(4),
        F(-16),
        F(28),
        F(16),
        F(544, 45),
        F(-512, 45),
        F(-104, 63),
        F(-416, 945),
        F(6688, 1575),
    ),
    3: (
        F(1),
        F(-4),
        F(4),
        F(-16),
        F(332, 5),
        F(-448, 3),
        F(81296, 315),
        F(75512, 315),
        F(17104, 2835),
        F(-219808, 2025),
        F(1350848, 10395),
    ),
}


# Page 93 repeats the kappa=2 row but drops the minus signs in columns 8, 9,
# and 10.  This second transcription tests that typographical variant too.
PAGE_93_KAPPA_2 = FIGURE_10_1[2][:7] + tuple(
    abs(value) for value in FIGURE_10_1[2][7:10]
) + FIGURE_10_1[2][10:]


CLAIMED = {2: F(9544, 10000), 3: F(9774, 10000)}


def weighted_sum(coefficients: tuple[Fraction, ...]) -> Fraction:
    return sum(
        (coefficient / ((index + 1) * (index + 2))
         for index, coefficient in enumerate(coefficients, start=1)),
        F(0),
    )


def endpoint_expression(coefficients: tuple[Fraction, ...]) -> Fraction:
    """The right side of equation (11.5), truncated to the supplied row."""

    return F(1) - 2 * weighted_sum(coefficients)


def required_weighted_tail(
    coefficients: tuple[Fraction, ...], claimed_proportion: Fraction
) -> Fraction:
    """Tail required to reconcile a displayed row with a claimed proportion.

    If ``S`` is the displayed weighted sum and ``R`` is the omitted weighted
    tail, equation (11.5) reads ``claimed = 1 - 2 * (S + R)``.
    """

    return (F(1) - claimed_proportion) / 2 - weighted_sum(coefficients)


def tail_cancellation_ratio(
    coefficients: tuple[Fraction, ...], claimed_proportion: Fraction
) -> Fraction:
    """Absolute required tail divided by the displayed weighted sum."""

    shown = weighted_sum(coefficients)
    if shown == 0:
        raise ZeroDivisionError("the displayed weighted sum is zero")
    return abs(required_weighted_tail(coefficients, claimed_proportion) / shown)


def alpha_expression(coefficients: tuple[Fraction, ...], alpha: Fraction) -> Fraction:
    """The pre-limit expression from equations (11.2)-(11.5).

    Before sending ``alpha`` to one from below, the multiplicity argument gives

        2 - 1/alpha - 2 sum_i C_i alpha^i / ((i+1)(i+2)).
    """

    if not 0 < alpha <= 1:
        raise ValueError("alpha must lie in (0,1]")
    series = sum(
        (
            coefficient * alpha**index / ((index + 1) * (index + 2))
            for index, coefficient in enumerate(coefficients, start=1)
        ),
        F(0),
    )
    return F(2) - 1 / alpha - 2 * series


def audit() -> dict[str, Fraction]:
    result = {
        "kappa1_figure_expression": endpoint_expression(FIGURE_10_1[1]),
        "kappa2_figure_expression": endpoint_expression(FIGURE_10_1[2]),
        "kappa2_page93_expression": endpoint_expression(PAGE_93_KAPPA_2),
        "kappa3_figure_expression": endpoint_expression(FIGURE_10_1[3]),
        "kappa2_claim": CLAIMED[2],
        "kappa3_claim": CLAIMED[3],
        "kappa2_required_tail": required_weighted_tail(
            FIGURE_10_1[2], CLAIMED[2]
        ),
        "kappa2_tail_cancellation_ratio": tail_cancellation_ratio(
            FIGURE_10_1[2], CLAIMED[2]
        ),
        "kappa3_required_tail": required_weighted_tail(
            FIGURE_10_1[3], CLAIMED[3]
        ),
        "kappa3_tail_cancellation_ratio": tail_cancellation_ratio(
            FIGURE_10_1[3], CLAIMED[3]
        ),
    }

    # The kappa=1 row is the normalization control: it gives 0.85840579...,
    # agreeing with the independently known 0.8584 calculation at the
    # precision claimed in the thesis.
    assert abs(result["kappa1_figure_expression"] - F(8584, 10000)) < F(1, 10000)

    # The two higher-derivative headline values do not follow from either
    # occurrence of the displayed coefficients.
    assert result["kappa2_figure_expression"] != result["kappa2_claim"]
    assert result["kappa2_page93_expression"] != result["kappa2_claim"]
    assert result["kappa3_figure_expression"] != result["kappa3_claim"]

    # An unprinted tail cannot be both negligible and reconcile the claims.
    # It would have to cancel over 95% of the shown kappa=2 weighted sum and
    # over 99% of the shown kappa=3 weighted sum.
    assert result["kappa2_tail_cancellation_ratio"] > F(95, 100)
    assert result["kappa3_tail_cancellation_ratio"] > F(99, 100)
    return result


if __name__ == "__main__":
    for name, value in audit().items():
        print(f"{name}: {value} = {float(value):.15f}")
