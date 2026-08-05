"""Falsifiers for a claimed spectral realisation of the Riemann zeros.

A construction that projects some operator onto a finite basis and reports
eigenvalues near the critical line is making a claim that is very easy to make
by accident.  Three failure modes account for most of them:

* the eigenvalues are **cutoff artifacts** — they move when the basis grows,
  because the underlying operator has continuous spectrum and the discreteness
  came from truncation, not from the mathematics;
* the eigenvalues are only checked against *"on the critical line"*, which for
  a self-adjoint or antisymmetric construction is true before any computation
  runs and therefore tests nothing;
* the **arithmetic is not load-bearing** — the same spectrum appears when the
  primes are replaced by an arbitrary set, so the construction never touched
  the zeta function at all.

This module turns each into a measured defect with a pre-declared threshold,
so a sprint reports numbers that can fail rather than a picture that looks
suggestive.  It is deliberately agnostic about what is being tested: supply a
callable ``construct(basis_size, primes) -> matrix`` and the gates apply.

Nothing here can provide evidence for the Riemann Hypothesis.  Passing all
three gates means a construction has survived the cheapest ways of being
wrong; it is a licence to keep working, not a result.  In particular a
construction can pass every gate and still be a rediscovery of the explicit
formula, which already reconstructs zeros from primes (``scripts/03``) — see
:func:`spectral_gate` for what that verdict does and does not license.
"""

from __future__ import annotations

import math
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field

import numpy as np

__all__ = [
    "SpectralVerdict",
    "STABILITY_TOLERANCE",
    "TARGET_TOLERANCE",
    "ABLATION_TOLERANCE",
    "positive_frequencies",
    "stability_defect",
    "target_defect",
    "ablation_defect",
    "spectral_gate",
]

#: Relative drift permitted between a basis and its double before the
#: eigenvalues are called cutoff artifacts.
STABILITY_TOLERANCE: float = 0.05

#: Relative error permitted against the true ordinates before a construction
#: is said to reproduce them.
TARGET_TOLERANCE: float = 0.01

#: Relative spectral change required when the primes are replaced.  *Below*
#: this the arithmetic is not load-bearing and the gate fails: this is the one
#: threshold a construction must exceed rather than stay under.
ABLATION_TOLERANCE: float = 0.10

#: First ordinates of the non-trivial zeros, for the target gate.  Pinned in
#: ``tests/test_spectral_gate.py`` against mpmath's ``zetazero``.
FIRST_ORDINATES: tuple[float, ...] = (
    14.134725141734694,
    21.022039638771555,
    25.010857580145689,
    30.424876125859513,
    32.935061587739190,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
)


def positive_frequencies(matrix: np.ndarray, count: int) -> np.ndarray:
    """The ``count`` smallest positive imaginary parts of the spectrum.

    A realisation of the zeros as eigenvalues is expected to place them at
    ``i*gamma`` (antisymmetric convention) or at ``1/2 + i*gamma``; either way
    the ordinates are the positive imaginary parts, so that is what every gate
    below compares.  Values below ``1e-9`` are treated as numerical zero and
    dropped rather than counted as a frequency.
    """

    eigenvalues = np.linalg.eigvals(np.asarray(matrix))
    imaginary = np.imag(eigenvalues)
    positive = np.sort(imaginary[imaginary > 1e-9])
    if len(positive) < count:
        raise ValueError(
            f"spectrum has {len(positive)} positive frequencies, need {count}"
        )
    return positive[:count]


def stability_defect(
    construct: Callable[[int, Sequence[int]], np.ndarray],
    primes: Sequence[int],
    basis_size: int,
    count: int = 3,
) -> float:
    """Relative drift of the lowest frequencies between ``N`` and ``2N``.

    Eigenvalues produced by truncating an operator with continuous spectrum
    move under refinement; eigenvalues of a genuine discrete spectrum settle.
    This returns the largest relative movement, so a converging construction
    drives it toward zero and an artifact does not.
    """

    coarse = positive_frequencies(construct(basis_size, primes), count)
    fine = positive_frequencies(construct(2 * basis_size, primes), count)
    return float(np.max(np.abs(fine - coarse) / np.abs(coarse)))


def target_defect(
    matrix: np.ndarray, count: int = 3
) -> tuple[float, tuple[float, ...]]:
    """Largest relative error of the lowest frequencies against the ordinates.

    Compared against the *values* 14.1347, 21.0220, 25.0109, ... — never
    against "lies on the critical line", which an antisymmetric or self-adjoint
    construction satisfies by algebra before any arithmetic is involved.
    """

    if count > len(FIRST_ORDINATES):
        raise ValueError(f"only {len(FIRST_ORDINATES)} ordinates are pinned here")
    found = positive_frequencies(matrix, count)
    targets = np.array(FIRST_ORDINATES[:count])
    return float(np.max(np.abs(found - targets) / targets)), tuple(
        float(value) for value in found
    )


def ablation_defect(
    construct: Callable[[int, Sequence[int]], np.ndarray],
    primes: Sequence[int],
    decoys: Sequence[int],
    basis_size: int,
    count: int = 3,
) -> float:
    """Relative spectral change when the primes are swapped for ``decoys``.

    The counterexample move, transposed from :func:`zeta.epstein.battery` to a
    spectral setting: if the construction reports the same frequencies with the
    arithmetic removed, it was never measuring the arithmetic.  A **large**
    value is the healthy outcome here.
    """

    real = positive_frequencies(construct(basis_size, primes), count)
    fake = positive_frequencies(construct(basis_size, decoys), count)
    return float(np.max(np.abs(fake - real) / np.abs(real)))


@dataclass(frozen=True)
class SpectralVerdict:
    """Outcome of the three pre-declared falsifiers."""

    basis_size: int
    frequencies: tuple[float, ...]
    stability: float
    target: float
    ablation: float
    stable: bool
    on_target: bool
    arithmetic_dependent: bool
    failures: tuple[str, ...] = field(default_factory=tuple)

    @property
    def passed(self) -> bool:
        return not self.failures


def spectral_gate(
    construct: Callable[[int, Sequence[int]], np.ndarray],
    primes: Sequence[int],
    decoys: Sequence[int],
    basis_size: int,
    count: int = 3,
) -> SpectralVerdict:
    """Run all three falsifiers and report which, if any, fired.

    The thresholds are module constants declared ahead of any particular
    construction, so they are not chosen after seeing a result.  A verdict of
    ``passed`` means only that the construction is not obviously a cutoff
    artifact, not obviously untethered from the actual ordinates, and not
    obviously independent of the primes.

    What it still does not establish: that the realisation is *natural*.  The
    explicit formula already reconstructs the zeros from the primes, so a
    matrix assembled from prime data whose eigenvalues reproduce the ordinates
    may be a re-encoding of something known rather than a new object.  That
    question is not numerical and this function does not address it.
    """

    matrix = construct(basis_size, primes)
    stability = stability_defect(construct, primes, basis_size, count)
    target, frequencies = target_defect(matrix, count)
    ablation = ablation_defect(construct, primes, decoys, basis_size, count)

    failures = []
    if not stability <= STABILITY_TOLERANCE:
        failures.append(
            f"unstable: frequencies moved {stability:.1%} from N={basis_size} "
            f"to N={2 * basis_size} (limit {STABILITY_TOLERANCE:.0%})"
        )
    if not target <= TARGET_TOLERANCE:
        failures.append(
            f"off target: largest relative error {target:.1%} against the "
            f"ordinates (limit {TARGET_TOLERANCE:.0%})"
        )
    if not ablation >= ABLATION_TOLERANCE:
        failures.append(
            f"arithmetic not load-bearing: replacing the primes moved the "
            f"spectrum only {ablation:.1%} (needs {ABLATION_TOLERANCE:.0%})"
        )

    return SpectralVerdict(
        basis_size=basis_size,
        frequencies=frequencies,
        stability=stability,
        target=target,
        ablation=ablation,
        stable=stability <= STABILITY_TOLERANCE,
        on_target=target <= TARGET_TOLERANCE,
        arithmetic_dependent=ablation >= ABLATION_TOLERANCE,
        failures=tuple(failures),
    )
