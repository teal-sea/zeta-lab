"""Exact controls for the negative on/off interaction obstruction."""

from fractions import Fraction
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from interaction_obstruction import MomentMatchedFamily, ScalarFamily, audit


def test_scalar_family_identities() -> None:
    for m in (1, 2, 10, 100):
        family = ScalarFamily(m)
        n = 2 * m * m + 2
        assert family.simple_count == n
        assert family.total == 2
        assert family.on_off_interaction == -2 * n * (n - 2)
        assert family.baseline_slack == 3 * n
        assert family.exact_rank_trace_slack_at_two == 2 * n - 3
        assert family.maximum_recoverable_coefficient == Fraction(3, n - 1)


def test_every_fixed_positive_cross_coefficient_eventually_fails() -> None:
    for coefficient in (Fraction(1, 2), Fraction(1, 100), Fraction(1, 10**6)):
        m = 1
        while ScalarFamily(m).maximum_recoverable_coefficient >= coefficient:
            m *= 2
        family = ScalarFamily(m)
        strengthened_rhs = (
            family.baseline_rhs + coefficient * family.on_line_cross
        )
        assert family.frobenius_sq < strengthened_rhs


def test_moment_matched_family_exact_identities() -> None:
    family = MomentMatchedFamily(m=7, k=13, background_simple=29)
    n = family.bad.simple_count
    assert family.trace == family.zero_count
    assert family.baseline_slack == 3 * n + Fraction(n, family.k)
    assert family.exact_rank_trace_slack_at_two == 2 * n + Fraction(n, family.k) - 3
    assert family.on_line_cross == n * (n - 1)


def test_printed_moment_and_full_candidate_floor_can_coexist() -> None:
    result = audit()
    assert result["matched_slack_density"] < result["additive_candidate_floor"]
    assert result["matched_cross_density"] > result["additive_candidate_floor"]
    target = Fraction(1_327_499_296, 1_000_000_000)
    assert abs(result["matched_moment_ratio"] - target) < Fraction(1, 10**9)
