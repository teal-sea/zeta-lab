"""Tests for zeta.spectral_gate — the falsifiers for a claimed zero spectrum.

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
    it exists solely to show the three gates can be passed simultaneously, so
    that a failing verdict elsewhere carries information.
    """

    genuine = list(primes[:5]) == [2, 3, 5, 7, 11]
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
        genuine = list(primes[:5]) == [2, 3, 5, 7, 11]
        matrix = _synthetic_realisation(basis_size, [2, 3, 5, 7, 11])
        return matrix if genuine else matrix * (1 + ABLATION_TOLERANCE / 2)

    weak = spectral_gate(barely_arithmetic, module.PRIMES, module.DECOYS, 16)
    assert not weak.arithmetic_dependent and not weak.passed


def test_verdict_reports_every_failure_that_fired():
    module = _load_script()
    verdict = spectral_gate(
        module.arithmetic_noise, module.PRIMES, module.DECOYS, basis_size=24
    )
    assert len(verdict.failures) == 2
    assert any("unstable" in f for f in verdict.failures)
    assert any("off target" in f for f in verdict.failures)
