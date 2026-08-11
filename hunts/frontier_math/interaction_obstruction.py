"""Exact obstruction families for retaining positive on-line cross mass.

The paper's unconditional zero-side inputs retain:

* a positive-semidefinite on-line block ``P`` built from vectors of squared
  norm at most one;
* a Hermitian off-line block ``Q`` with positive index at most the number of
  conjugate pairs;
* the trace and Frobenius square of ``A = P + Q``; and
* the zero census ``N = s1 + 2p`` in the all-simple model below.

They do not retain the signed joint incidence between on-line vectors and
off-line hyperbolic blocks.  All calculations here use integers or rational
numbers.  No numerical solver is involved.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class ScalarFamily:
    """One bad scalar block, represented by Gaussian-integer vectors.

    There are ``n = 2m^2 + 2`` unit on-line vectors and one off-line pair
    with vectors ``im`` and ``-im``. Thus ``P=n``, ``Q=-2m^2=-(n-2)``, and
    ``A=2``.
    """

    m: int

    def __post_init__(self) -> None:
        if self.m < 1:
            raise ValueError("m must be positive")

    @property
    def simple_count(self) -> int:
        return 2 * self.m * self.m + 2

    @property
    def pair_count(self) -> int:
        return 1

    @property
    def p(self) -> int:
        return self.simple_count

    @property
    def q(self) -> int:
        return -2 * self.m * self.m

    @property
    def total(self) -> int:
        return self.p + self.q

    @property
    def frobenius_sq(self) -> int:
        return self.total * self.total

    @property
    def baseline_rhs(self) -> int:
        return 4 * self.total - 3 * self.simple_count - 4 * self.pair_count

    @property
    def baseline_slack(self) -> int:
        return self.frobenius_sq - self.baseline_rhs

    @property
    def on_line_cross(self) -> int:
        return self.simple_count * (self.simple_count - 1)

    @property
    def on_off_interaction(self) -> int:
        """The ordered Frobenius cross term ``2 * tr(PQ)``."""

        return 2 * self.p * self.q

    @property
    def maximum_recoverable_coefficient(self) -> Fraction:
        return Fraction(self.baseline_slack, self.on_line_cross)

    @property
    def exact_rank_trace_slack_at_two(self) -> int:
        """Slack using the actual ranks ``rank(P)=1`` and ``n_+(Q)=0``."""

        sharp_rhs = 4 * self.total - 2 * self.p - 1
        return self.frobenius_sq - sharp_rhs


@dataclass(frozen=True)
class MomentMatchedFamily:
    """Direct-sum family matching the paper's two prime-side moments.

    Start with ``ScalarFamily(m)``. Add ``k*n`` orthogonal positive pair
    blocks, each of eigenvalue ``2 + 1/k``, and ``background_simple``
    orthogonal unit on-line blocks. The positive pair blocks exactly repair
    the bad block's trace deficit, so ``tr A = N`` for every member.

    The background count can dilute ``frobSq/N`` to any fixed target in
    ``(1,2)`` while leaving the bad block's cross mass unchanged.
    """

    m: int
    k: int
    background_simple: int

    def __post_init__(self) -> None:
        if self.m < 1 or self.k < 1 or self.background_simple < 0:
            raise ValueError("m and k must be positive; background must be nonnegative")

    @property
    def bad(self) -> ScalarFamily:
        return ScalarFamily(self.m)

    @property
    def positive_pairs(self) -> int:
        return self.k * self.bad.simple_count

    @property
    def positive_pair_eigenvalue(self) -> Fraction:
        return Fraction(2 * self.k + 1, self.k)

    @property
    def simple_count(self) -> int:
        return self.bad.simple_count + self.background_simple

    @property
    def pair_count(self) -> int:
        return 1 + self.positive_pairs

    @property
    def p_rank(self) -> int:
        return 1 + self.background_simple

    @property
    def q_positive_index(self) -> int:
        return self.positive_pairs

    @property
    def zero_count(self) -> int:
        return self.simple_count + 2 * self.pair_count

    @property
    def trace(self) -> Fraction:
        return (
            Fraction(self.bad.total)
            + self.positive_pairs * self.positive_pair_eigenvalue
            + self.background_simple
        )

    @property
    def frobenius_sq(self) -> Fraction:
        return (
            Fraction(self.bad.frobenius_sq)
            + self.positive_pairs * self.positive_pair_eigenvalue**2
            + self.background_simple
        )

    @property
    def baseline_rhs(self) -> Fraction:
        return 4 * self.trace - 3 * self.simple_count - 4 * self.pair_count

    @property
    def baseline_slack(self) -> Fraction:
        return self.frobenius_sq - self.baseline_rhs

    @property
    def exact_rank_trace_slack_at_two(self) -> Fraction:
        rhs = (
            4 * self.trace
            - 2 * self.simple_count
            - self.p_rank
            - 4 * self.q_positive_index
        )
        return self.frobenius_sq - rhs

    @property
    def on_line_cross(self) -> int:
        return self.bad.on_line_cross

    @property
    def moment_ratio(self) -> Fraction:
        return self.frobenius_sq / self.zero_count

    @property
    def slack_density(self) -> Fraction:
        return self.baseline_slack / self.zero_count

    @property
    def cross_density(self) -> Fraction:
        return Fraction(self.on_line_cross, self.zero_count)


def nearest_background(m: int, k: int, target_ratio: Fraction) -> int:
    """Choose the nearest nonnegative background count for a target ratio."""

    base = MomentMatchedFamily(m=m, k=k, background_simple=0)
    if not 1 < target_ratio < base.moment_ratio:
        raise ValueError("target must lie strictly between 1 and the undiluted ratio")
    exact = (base.frobenius_sq - target_ratio * base.zero_count) / (target_ratio - 1)
    floor = exact.numerator // exact.denominator
    candidates = [max(0, floor), max(0, floor + 1)]
    return min(
        candidates,
        key=lambda value: abs(
            MomentMatchedFamily(m=m, k=k, background_simple=value).moment_ratio
            - target_ratio
        ),
    )


def matched_family(m: int, k: int, target_ratio: Fraction) -> MomentMatchedFamily:
    return MomentMatchedFamily(m, k, nearest_background(m, k, target_ratio))


def audit() -> dict[str, Fraction | int]:
    """Check the sharp coefficient and a moment-matched candidate-floor defeat."""

    scalar = ScalarFamily(m=10)
    assert scalar.total == 2
    assert scalar.baseline_slack == 3 * scalar.simple_count
    assert scalar.exact_rank_trace_slack_at_two == 2 * scalar.simple_count - 3
    assert scalar.maximum_recoverable_coefficient == Fraction(
        3, scalar.simple_count - 1
    )

    # Paper's printed second-moment constant, used only as a rational target.
    target = Fraction(1_327_499_296, 1_000_000_000)
    family = matched_family(m=10, k=100_000, target_ratio=target)
    # The LP floor counted unordered pairs.  The Frobenius expansion counts
    # both orders, so the proposed additive term was twice this number.
    unordered_candidate_floor = Fraction(14371, 1_000_000_000)
    additive_candidate_floor = 2 * unordered_candidate_floor

    assert family.trace == family.zero_count
    assert family.exact_rank_trace_slack_at_two == (
        2 * family.bad.simple_count + Fraction(family.bad.simple_count, family.k) - 3
    )
    # The background count is integral.  Nearest-integer dilution misses the
    # requested ratio by less than one part in a billion in this instance.
    assert abs(family.moment_ratio - target) < Fraction(1, 10**9)
    assert family.slack_density < additive_candidate_floor
    assert family.cross_density > additive_candidate_floor

    return {
        "scalar_simple_count": scalar.simple_count,
        "scalar_on_off_interaction": scalar.on_off_interaction,
        "scalar_max_coefficient": scalar.maximum_recoverable_coefficient,
        "matched_zero_count": family.zero_count,
        "matched_background_simple": family.background_simple,
        "matched_moment_ratio": family.moment_ratio,
        "matched_slack_density": family.slack_density,
        "matched_cross_density": family.cross_density,
        "additive_candidate_floor": additive_candidate_floor,
    }


if __name__ == "__main__":
    for key, value in audit().items():
        print(f"{key}: {value}")
