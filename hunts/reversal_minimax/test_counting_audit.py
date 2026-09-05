"""Independent incidence counts and planted over-refunds for the counting audit."""

import importlib.util
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
import pytest

spec = importlib.util.spec_from_file_location("counting_audit", Path(__file__).with_name("counting_audit.py"))
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def test_exact_counterexample_to_the_early_count_being_tight():
    exact, coarse = audit.pressure_coefficients(7, 4, 3)
    assert exact == [1, 3, 4, 4, 3, 1]
    assert coarse == [2, 4, 6, 6, 4, 2]
    assert exact[2] == 4 < coarse[2] == 6


def test_every_gap_basis_vector_respects_the_improved_cap():
    # This verifies all nonnegative gap vectors in each finite case by
    # testing their basis coefficients, rather than sampling gap values.
    for local in range(2, 8):
        for block in range(local, 12):
            for points in (block, block + 1, 2 * block, 3 * block):
                exact, coarse = audit.pressure_coefficients(points, block, local)
                cap = (local - 1) * (block - local + 1)
                assert max(exact) <= cap
                assert all(a <= b for a, b in zip(exact, coarse))
                if points >= 2 * block:
                    assert max(exact) == cap


def test_an_extra_refund_fails_on_an_interior_gap():
    exact, _ = audit.pressure_coefficients(15, 7, 4)
    proposed_cap = (4 - 1) * (7 - 4 + 1)
    assert max(exact) == proposed_cap
    # A single nonzero gap at the maximizing coordinate rejects cap - 1.
    assert max(exact) > proposed_cap - 1


def test_pair_occurrences_are_normalized_not_double_counted():
    for local in range(2, 8):
        block = 3 * local
        got = audit.pair_coefficients(block, local)
        for (i, j), value in got.items():
            span = j - i
            starts = max(0, min(i, block-local) - max(0, j-local+1) + 1)
            expected = Q(2 * starts, local-span) if span < local else Q(0)
            assert value == expected <= 2
            if span < local and local <= i < j < 2 * local:
                assert value == 2


def test_projection_exact_gain_and_registered_four_point_expression():
    three = audit.projection(3, Q(1345, 10**6), 745, 3000)
    four = audit.projection(4, Q(2310, 10**6), 435, 2500)
    assert Q(three["exact_gain"]) == Q(400, 446400399)
    assert Q(four["H_coefficient"]) == Q(906250, 904171)
    assert Q(four["old_subtracted_constant"]) == Q(1085, 904171)
    assert Q(four["new_subtracted_constant"]) == Q(1080, 904171)
    assert Q(four["exact_gain"]) == Q(5, 904171)
    with pytest.raises(ValueError, match="cap"):
        audit.projection(4, Q(2310, 10**6), 436, 2500)


def test_actual_kernel_retains_more_than_separate_blocks():
    for case in audit.report()["actual_kernel_examples_measured"]:
        assert case["minimum_gram_eigenvalue"] > -1e-10
        assert case["pinching_loss"] > 1e-6
        assert case["local_to_block_margin"] >= -1e-10
        assert case["finite_inequality_margin"] >= -1e-10
        assert case["exact_nested_pressure"] <= case["improved_global_pressure_cap"] + 1e-12
        assert case["exact_nested_pressure"] < case["early_coarse_pressure"]


def test_gram_transform_matches_direct_quadrature():
    from mpmath import mp

    gaps = [Q(26, 25), Q(197, 100), Q(1, 4)]
    gram = audit.mt_gram(gaps)
    with mp.workdps(40):
        real = lambda r: mp.mpf(r.numerator) / r.denominator
        positions = [Q(0)]
        for gap in gaps:
            positions.append(positions[-1] + gap)
        k0 = mp.quad(lambda t: mp.cos(mp.sqrt(2) * t), [-mp.mpf("0.5"), 0, mp.mpf("0.5")])
        for i in range(4):
            for j in range(i, 4):
                x = real(positions[j] - positions[i])
                k = mp.quad(lambda t: mp.cos(mp.sqrt(2)*t) * mp.cos(2*mp.pi*x*t),
                            [-mp.mpf("0.5"), 0, mp.mpf("0.5")])
                assert abs(float(k/k0) - gram[i,j]) < 1e-14


def test_zero_interaction_control_has_no_pinching_refund():
    identity = np.eye(4)
    assert audit.defect(identity) == 0
    assert audit.defect(identity[:2,:2]) + audit.defect(identity[2:,2:]) == 0
