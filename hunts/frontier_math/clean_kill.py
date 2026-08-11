"""Exact checker for the obstruction that withdraws the 0.672529 candidate.

The pinned upstream zero-side summand is ``m * u * u^T``.  In one matrix
dimension this is the ordinary square ``m * u^2``.  It is not the Hermitian
rank-one term ``m * u * conjugate(u)`` used by the old ``blockpos.py``.

Everything in this file is Gaussian-integer or integer arithmetic.  It checks
both the first false sign claim and a failure of the proposed final additive
inequality.  No optimizer or floating-point operation is involved.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class GaussianInteger:
    re: int
    im: int = 0

    def __add__(self, other: "GaussianInteger") -> "GaussianInteger":
        return GaussianInteger(self.re + other.re, self.im + other.im)

    def __neg__(self) -> "GaussianInteger":
        return GaussianInteger(-self.re, -self.im)

    def __mul__(self, other: "GaussianInteger") -> "GaussianInteger":
        return GaussianInteger(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def conjugate(self) -> "GaussianInteger":
        return GaussianInteger(self.re, -self.im)


ONE = GaussianInteger(1)
I = GaussianInteger(0, 1)


def transpose_rank_one_scalar(u: GaussianInteger) -> GaussianInteger:
    """The actual one-dimensional zero-side summand, ``u * u``."""

    return u * u


def hermitian_rank_one_scalar(u: GaussianInteger) -> GaussianInteger:
    """The incorrect summand formerly used by ``blockpos.py``."""

    return u * u.conjugate()


def audit() -> dict[str, int]:
    """Return the exact obstruction values and assert their identities."""

    off_pair = transpose_rank_one_scalar(I) + transpose_rank_one_scalar(-I)
    wrong_off_pair = hermitian_rank_one_scalar(I) + hermitian_rank_one_scalar(-I)
    cross_trace = (transpose_rank_one_scalar(ONE) * off_pair).re

    # Five simple on-line labels with scalar vector 1, plus the pair i, -i.
    simple_count = 5
    pair_count = 1
    p1 = simple_count
    qprime = off_pair.re
    total = p1 + qprime
    cross11 = p1 * p1 - simple_count
    frobenius_sq = total * total
    proposed_rhs = 4 * total - 3 * simple_count - 4 * pair_count + cross11

    assert off_pair == GaussianInteger(-2)
    assert wrong_off_pair == GaussianInteger(2)
    assert cross_trace == -2
    assert cross11 == 20
    assert frobenius_sq == 9
    assert proposed_rhs == 13
    assert frobenius_sq < proposed_rhs

    return {
        "correct_off_pair": off_pair.re,
        "old_instrument_off_pair": wrong_off_pair.re,
        "cross_trace": cross_trace,
        "frobenius_sq": frobenius_sq,
        "proposed_rhs": proposed_rhs,
        "defect": frobenius_sq - proposed_rhs,
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
