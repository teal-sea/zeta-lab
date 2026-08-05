"""Demonstrate that the spectral falsifiers actually fire.

A gate nobody has seen fail is not known to be a gate.  This script runs
``zeta.spectral_gate`` against three constructions whose verdicts are known in
advance, so each of the four falsifiers is observed rejecting something:

* a **forged** operator, built by writing the ordinates straight into the
  matrix.  It reproduces the zeros perfectly and is stable under refinement,
  and it is worthless — it never consults a prime.  Only the ablation gate
  catches it, which is exactly why that gate exists.
* an **arithmetic noise** operator, built from prime data but with no reason to
  carry the zeros.  It is caught by the target gate, and also by the
  permutation gate: its entries are indexed by position in the prime list, so
  reordering the same primes moves its spectrum -- the signature of primes used
  as decoration rather than as places.
* the **transcendental antisymmetric matrix** of ``discovery/04``, generalised
  to accept a prime list.  Its spectrum grows with the basis, so the stability
  gate catches it as a cutoff artifact.

Usage::

    .venv/bin/python scripts/31_spectral_falsifiers.py

Nothing here bears on the Riemann Hypothesis.  A construction that passed all
four gates would have survived the cheapest ways of being wrong, and would
still owe an argument that it is not a re-encoding of the explicit formula.
"""

from __future__ import annotations

import math
import sys
from collections.abc import Sequence
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from zeta.spectral_gate import FIRST_ORDINATES, spectral_gate  # noqa: E402

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
#: Same length and rough magnitude as PRIMES, but not the primes: the ablation
#: gate asks whether the construction can tell the difference.
DECOYS = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25]


def forged(basis_size: int, primes: Sequence[int]) -> np.ndarray:
    """Antisymmetric block matrix with the ordinates written straight in.

    The point of including this: it passes every gate that looks only at the
    spectrum.  ``primes`` is accepted and ignored, which is the whole failure
    mode the ablation gate is built to catch.
    """

    blocks = max(1, basis_size // 2)
    matrix = np.zeros((2 * blocks, 2 * blocks))
    for index in range(blocks):
        gamma = (
            FIRST_ORDINATES[index]
            if index < len(FIRST_ORDINATES)
            # Beyond the pinned list, any increasing continuation will do: this
            # matrix is a straw man and never claims to be a realisation.
            else FIRST_ORDINATES[-1] + 5.0 * (index - len(FIRST_ORDINATES) + 1)
        )
        matrix[2 * index, 2 * index + 1] = gamma
        matrix[2 * index + 1, 2 * index] = -gamma
    return matrix


def arithmetic_noise(basis_size: int, primes: Sequence[int]) -> np.ndarray:
    """Antisymmetric matrix whose entries are a deterministic prime function.

    Genuinely depends on the primes, so it survives the ablation gate; it has
    no reason to carry the ordinates, so the target gate rejects it.
    """

    matrix = np.zeros((basis_size, basis_size))
    for row in range(basis_size):
        for col in range(row + 1, basis_size):
            p = primes[(row + col) % len(primes)]
            weight = math.log(p) * math.cos(p * (row - col))
            matrix[row, col] = weight
            matrix[col, row] = -weight
    return matrix


def transcendental(basis_size: int, primes: Sequence[int]) -> np.ndarray:
    """``discovery/04_transcendental_matrix.py``, generalised over the prime set.

    Edge ``u -> u*p`` carries ``+log p`` and its reverse ``-log p``.  The
    spectrum spreads as the node count grows, so the stability gate rejects it.
    """

    matrix = np.zeros((basis_size, basis_size))
    for u in range(1, basis_size + 1):
        for p in primes:
            v = u * p
            if v <= basis_size:
                weight = math.log(p)
                matrix[u - 1, v - 1] = weight
                matrix[v - 1, u - 1] = -weight
    return matrix


def main() -> int:
    cases = (
        ("forged (ordinates written in)", forged, 16),
        ("arithmetic noise", arithmetic_noise, 24),
        ("transcendental graph (discovery/04)", transcendental, 60),
    )
    print("Spectral falsifiers, three constructions with known verdicts.")
    print(
        "Thresholds are module constants in zeta/spectral_gate.py, fixed before "
        "any construction was written.\n"
    )
    for label, construct, basis in cases:
        verdict = spectral_gate(construct, PRIMES, DECOYS, basis_size=basis)
        print(f"{label}   (basis {basis})")
        print(
            f"  lowest frequencies : "
            + ", ".join(f"{value:.4f}" for value in verdict.frequencies)
        )
        print(
            f"  stability {verdict.stability:>8.2%}   "
            f"target {verdict.target:>9.2%}   "
            f"ablation {verdict.ablation:>8.2%}   "
            f"permutation {verdict.permutation:>8.2%}"
        )
        print(f"  passed: {verdict.passed}")
        for failure in verdict.failures:
            print(f"    - {failure}")
        print()

    print(
        "Each gate is observed rejecting a different construction, so none of\n"
        "them is decorative.  Note especially that the forged matrix reproduces\n"
        "the ordinates exactly and is perfectly stable: spectrum agreement alone\n"
        "is not evidence of anything."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
