"""Tests for zeta.spectral_gate, the falsifiers for a claimed zero spectrum.

Two things need pinning here, and the second matters as much as the first: that
each gate rejects what it is meant to reject, and that the gate set is not
unpassable.  A harness nothing can survive is as useless as one nothing fails.
"""

from __future__ import annotations

import importlib.util
import math
import sys
from collections.abc import Sequence
from pathlib import Path

import mpmath as mp
import numpy as np
import pytest

from zeta.spectral_gate import (
    ABLATION_TOLERANCE,
    FIRST_ORDINATES,
    PERMUTATION_TOLERANCE,
    STABILITY_TOLERANCE,
    TARGET_TOLERANCE,
    ablation_defect,
    positive_frequencies,
    spectral_gate,
    stability_defect,
    target_defect,
)

ROOT = Path(__file__).resolve().parent.parent


def _load_script():
    path = ROOT / "scripts" / "31_spectral_falsifiers.py"
    spec = importlib.util.spec_from_file_location("spectral_falsifiers", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_pinned_ordinates_match_mpmath():
    """The target gate is only as good as the numbers it aims at."""

    with mp.workdps(25):
        for index, value in enumerate(FIRST_ORDINATES, start=1):
            assert value == pytest.approx(float(mp.im(mp.zetazero(index))), rel=1e-13)


def test_positive_frequencies_selects_and_sorts():
    matrix = np.array([[0.0, 3.0], [-3.0, 0.0]])
    assert positive_frequencies(matrix, 1) == pytest.approx([3.0])
    with pytest.raises(ValueError):
        positive_frequencies(matrix, 2)


def test_forged_construction_passes_spectrum_checks_but_fails_ablation():
    """The decisive case: exact ordinates, perfectly stable, still rejected.

    Writing the answer into the matrix reproduces the zeros to machine
    precision.  If the gate set accepted that, it would accept anything.
    """

    module = _load_script()
    verdict = spectral_gate(module.forged, module.PRIMES, module.DECOYS, basis_size=16)

    assert verdict.frequencies[0] == pytest.approx(14.134725141734694, rel=1e-12)
    assert verdict.stability == pytest.approx(0.0, abs=1e-12)
    assert verdict.target == pytest.approx(0.0, abs=1e-12)
    assert verdict.stable and verdict.on_target

    assert verdict.ablation == pytest.approx(0.0, abs=1e-12)
    assert not verdict.arithmetic_dependent
    assert not verdict.passed
    assert len(verdict.failures) == 1
    assert "arithmetic not load-bearing" in verdict.failures[0]


def test_arithmetic_noise_is_caught_by_the_target_gate():
    module = _load_script()
    verdict = spectral_gate(
        module.arithmetic_noise, module.PRIMES, module.DECOYS, basis_size=24
    )
    assert verdict.target > 0.9
    assert not verdict.on_target
    # It does depend on the primes, so the ablation gate correctly does not fire.
    assert verdict.arithmetic_dependent
    # But it reads the prime *list position*, so the permutation gate does.
    assert not verdict.order_independent
    assert not verdict.passed


def test_transcendental_graph_is_caught_as_a_cutoff_artifact():
    """discovery/04's spectrum moves when the basis grows."""

    module = _load_script()
    verdict = spectral_gate(
        module.transcendental, module.PRIMES, module.DECOYS, basis_size=60
    )
    assert verdict.stability > 0.5
    assert not verdict.stable
    assert not verdict.on_target
    assert not verdict.passed


def _synthetic_realisation(basis_size: int, primes: Sequence[int]) -> np.ndarray:
    """A fixture that fakes the profile a genuine realisation would have.

    It returns the ordinates when handed the real primes and a scaled spectrum
    otherwise.  This is not a construction and claims nothing mathematically;
    it exists solely to show the four gates can be passed simultaneously, so
    that a failing verdict elsewhere carries information.
    """

    # Keys on the *set* of places, as any adelic object must: this fixture has
    # to survive the permutation gate to demonstrate the gates are passable.
    genuine = {2, 3, 5, 7, 11} <= set(primes)
    blocks = max(1, basis_size // 2)
    matrix = np.zeros((2 * blocks, 2 * blocks))
    for index in range(blocks):
        base = (
            FIRST_ORDINATES[index]
            if index < len(FIRST_ORDINATES)
            else FIRST_ORDINATES[-1] + 5.0 * (index - len(FIRST_ORDINATES) + 1)
        )
        gamma = base if genuine else base * 2.5
        matrix[2 * index, 2 * index + 1] = gamma
        matrix[2 * index + 1, 2 * index] = -gamma
    return matrix


def test_the_gate_set_is_passable():
    """Mutation teeth in the other direction: something must be able to pass."""

    module = _load_script()
    verdict = spectral_gate(
        _synthetic_realisation, module.PRIMES, module.DECOYS, basis_size=16
    )
    assert verdict.stable and verdict.on_target and verdict.arithmetic_dependent
    assert verdict.order_independent
    assert verdict.passed
    assert verdict.failures == ()


def test_each_threshold_has_teeth():
    """Move each defect just across its threshold and confirm the gate flips."""

    module = _load_script()

    def nudge(scale: float):
        def construct(basis_size: int, primes: Sequence[int]) -> np.ndarray:
            matrix = _synthetic_realisation(basis_size, primes)
            return matrix * (scale if basis_size > 16 else 1.0)

        return construct

    # Stability: make the doubled basis disagree by more than the tolerance.
    drifted = spectral_gate(
        nudge(1.0 + 2 * STABILITY_TOLERANCE), module.PRIMES, module.DECOYS, 16
    )
    assert not drifted.stable and not drifted.passed

    # Target: scale the whole spectrum past the tolerance.
    def off_target(basis_size: int, primes: Sequence[int]) -> np.ndarray:
        return _synthetic_realisation(basis_size, primes) * (1 + 2 * TARGET_TOLERANCE)

    missed = spectral_gate(off_target, module.PRIMES, module.DECOYS, 16)
    assert not missed.on_target and not missed.passed

    # Ablation: make the decoy spectrum nearly identical to the real one.
    def barely_arithmetic(basis_size: int, primes: Sequence[int]) -> np.ndarray:
        genuine = {2, 3, 5, 7, 11} <= set(primes)
        matrix = _synthetic_realisation(basis_size, [2, 3, 5, 7, 11])
        return matrix if genuine else matrix * (1 + ABLATION_TOLERANCE / 2)

    weak = spectral_gate(barely_arithmetic, module.PRIMES, module.DECOYS, 16)
    assert not weak.arithmetic_dependent and not weak.passed

    # Permutation: react to the order the primes arrive in, not just the set.
    def order_sensitive(basis_size: int, primes: Sequence[int]) -> np.ndarray:
        matrix = _synthetic_realisation(basis_size, primes)
        return matrix * (1.0 if list(primes) == sorted(primes) else 1.5)

    ordered = spectral_gate(order_sensitive, module.PRIMES, module.DECOYS, 16)
    assert not ordered.order_independent and not ordered.passed
    assert any("order-dependent" in f for f in ordered.failures)


def test_verdict_reports_every_failure_that_fired():
    module = _load_script()
    verdict = spectral_gate(
        module.arithmetic_noise, module.PRIMES, module.DECOYS, basis_size=24
    )
    assert len(verdict.failures) == 3
    assert any("unstable" in f for f in verdict.failures)
    assert any("off target" in f for f in verdict.failures)
    assert any("order-dependent" in f for f in verdict.failures)


# ---------------------------------------------------------------------------
# Counting gates -- the cokernel's first falsifiable prediction is a dimension
# ---------------------------------------------------------------------------

def test_counting_gate_is_passable():
    """A count obeying the predicted law clears all four counting gates."""
    from zeta.spectral_gate import counting_gate

    module = _load_script()
    verdict = counting_gate(
        module.logarithmic_count, module.PRIMES, module.DECOYS, module.CUTOFFS
    )
    assert verdict.growth_ratio == pytest.approx(2.0, abs=1e-9)
    assert verdict.prediction == pytest.approx(0.0, abs=1e-9)
    assert verdict.logarithmic and verdict.predictive
    assert verdict.arithmetic_dependent and verdict.order_independent
    assert verdict.passed


def test_linear_growth_is_rejected():
    """A count growing with the cutoff, not its logarithm."""
    from zeta.spectral_gate import counting_gate

    module = _load_script()
    verdict = counting_gate(
        module.linear_count, module.PRIMES, module.DECOYS, module.CUTOFFS
    )
    assert verdict.growth_ratio > 4.0
    assert not verdict.logarithmic and not verdict.predictive
    assert not verdict.passed
    assert any("not logarithmic" in f for f in verdict.failures)


def test_prime_blind_count_is_rejected():
    """Right growth law, but the arithmetic never enters."""
    from zeta.spectral_gate import counting_gate

    module = _load_script()
    verdict = counting_gate(
        module.prime_blind_count, module.PRIMES, module.DECOYS, module.CUTOFFS
    )
    assert verdict.logarithmic
    assert verdict.ablation == pytest.approx(0.0, abs=1e-12)
    assert not verdict.arithmetic_dependent
    assert not verdict.passed


def test_order_keyed_count_is_rejected():
    """Prime-dependent, but on list position rather than on the set."""
    from zeta.spectral_gate import counting_gate

    module = _load_script()
    verdict = counting_gate(
        module.order_sensitive_count, module.PRIMES, module.DECOYS, module.CUTOFFS
    )
    assert verdict.arithmetic_dependent
    assert verdict.permutation > 0.05
    assert not verdict.order_independent
    assert not verdict.passed


def test_growth_ratio_needs_no_normalisation_constant():
    """Scaling every count by a constant must not change the growth ratio.

    This is what lets the gate run without a remembered dictionary between the
    cutoff and the height it resolves.
    """
    from zeta.spectral_gate import count_growth_ratio

    module = _load_script()
    plain = count_growth_ratio(module.logarithmic_count, module.PRIMES, 2.0)

    def scaled(cutoff: float, primes: Sequence[int]) -> int:
        return 37 * module.logarithmic_count(cutoff, primes)

    assert count_growth_ratio(scaled, module.PRIMES, 2.0) == pytest.approx(plain)


def test_prediction_gate_scores_a_held_out_cutoff():
    """The last cutoff is never used to fit, so tuning cannot satisfy it."""
    from zeta.spectral_gate import count_prediction_defect

    module = _load_script()

    def breaks_at_the_end(cutoff: float, primes: Sequence[int]) -> int:
        value = module.logarithmic_count(cutoff, primes)
        return value * 2 if cutoff >= module.CUTOFFS[-1] else value

    honest = count_prediction_defect(
        module.logarithmic_count, module.PRIMES, module.CUTOFFS
    )
    tampered = count_prediction_defect(breaks_at_the_end, module.PRIMES, module.CUTOFFS)
    assert honest == pytest.approx(0.0, abs=1e-9)
    assert tampered > 0.4

    with pytest.raises(ValueError):
        count_prediction_defect(module.logarithmic_count, module.PRIMES, (2.0, 4.0))
