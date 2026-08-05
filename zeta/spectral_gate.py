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
  the zeta function at all;
* the primes are present but only as **decoration** — the spectrum reacts to
  the primes *and* to the order they were listed in, which means the entries
  are indexed by list position rather than by a place.  This one is invisible
  to the ablation gate, since swapping the primes out moves such a spectrum
  just as much as it moves a genuine one.

This module turns each of the four into a measured defect with a pre-declared threshold,
so a sprint reports numbers that can fail rather than a picture that looks
suggestive.  It is deliberately agnostic about what is being tested: supply a
callable ``construct(basis_size, primes) -> matrix`` and the gates apply.

Nothing here can provide evidence for the Riemann Hypothesis.  Passing all
four gates means a construction has survived the cheapest ways of being
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
    "permutation_defect",
    "spectral_gate",
    "CountingVerdict",
    "GROWTH_RATIO_TOLERANCE",
    "COUNT_PREDICTION_TOLERANCE",
    "count_growth_ratio",
    "count_prediction_defect",
    "count_ablation_defect",
    "count_permutation_defect",
    "counting_gate",
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

#: Relative spectral change permitted when the *same* primes are reordered.
#: A construction indexed by position in a list will move; one that depends on
#: the set of places, as any adelic object must, will not.  Paired with the
#: ablation gate this is sharp: the spectrum must react to *which* primes are
#: present and ignore *what order* they arrive in.
PERMUTATION_TOLERANCE: float = 0.01

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


def permutation_defect(
    construct: Callable[[int, Sequence[int]], np.ndarray],
    primes: Sequence[int],
    basis_size: int,
    count: int = 3,
    trials: int = 3,
    seed: int = 20260805,
) -> float:
    """Largest relative spectral change when the prime list is reordered.

    The set of places is unordered; a construction that notices the ordering is
    reading the index of a Python list, not the arithmetic.  This is the gate
    that separates a genuine dependence on the primes from an entry-wise
    decoration by prime-valued numbers, which the ablation gate alone cannot
    tell apart -- both move the spectrum when the primes are swapped out.

    A **small** value is the healthy outcome, the opposite of
    :func:`ablation_defect`.
    """

    import random

    reference = positive_frequencies(construct(basis_size, list(primes)), count)
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        shuffled = list(primes)
        rng.shuffle(shuffled)
        moved = positive_frequencies(construct(basis_size, shuffled), count)
        worst = max(
            worst, float(np.max(np.abs(moved - reference) / np.abs(reference)))
        )
    return worst


@dataclass(frozen=True)
class SpectralVerdict:
    """Outcome of the three pre-declared falsifiers."""

    basis_size: int
    frequencies: tuple[float, ...]
    stability: float
    target: float
    ablation: float
    permutation: float
    stable: bool
    on_target: bool
    arithmetic_dependent: bool
    order_independent: bool
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
    """Run all four falsifiers and report which, if any, fired.

    The thresholds are module constants declared ahead of any particular
    construction, so they are not chosen after seeing a result.  A verdict of
    ``passed`` means only that the construction is not obviously a cutoff
    artifact, not obviously untethered from the actual ordinates, not obviously
    independent of the primes, and not merely decorated by them.

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
    permutation = permutation_defect(construct, primes, basis_size, count)

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

    if not permutation <= PERMUTATION_TOLERANCE:
        failures.append(
            f"order-dependent: reordering the same primes moved the spectrum "
            f"{permutation:.1%} (limit {PERMUTATION_TOLERANCE:.0%}) -- the "
            f"construction is reading list position, not arithmetic"
        )

    return SpectralVerdict(
        basis_size=basis_size,
        frequencies=frequencies,
        stability=stability,
        target=target,
        ablation=ablation,
        permutation=permutation,
        stable=stability <= STABILITY_TOLERANCE,
        on_target=target <= TARGET_TOLERANCE,
        arithmetic_dependent=ablation >= ABLATION_TOLERANCE,
        order_independent=permutation <= PERMUTATION_TOLERANCE,
        failures=tuple(failures),
    )


# ---------------------------------------------------------------------------
# Counting gates: the cokernel's first falsifiable prediction is a dimension
#
# In the Connes picture the zeros are an absorption spectrum -- what is missing
# from a continuous spectrum after quotienting -- so the first thing a finite
# model can be asked for is not a list of ordinates but the *number* of them it
# resolves.  That is a matrix rank, and it is checkable against the zero
# counting function the laboratory already computes.
#
# No dictionary between the cutoff and the height it resolves is written down
# here.  Fixing that constant from memory would be exactly the habit the
# repository forbids, and it would also turn the check into a fit.  Instead the
# relation is calibrated on some cutoffs and required to *predict* a held-out
# one, so the constant is derived and the test stays severe.
# ---------------------------------------------------------------------------

#: Permitted departure from the ratio 2 in the increment test below.
GROWTH_RATIO_TOLERANCE: float = 0.15

#: Permitted relative error when the calibrated law predicts a held-out cutoff.
COUNT_PREDICTION_TOLERANCE: float = 0.05


def count_growth_ratio(
    count: Callable[[float, Sequence[int]], int],
    primes: Sequence[int],
    base_cutoff: float,
) -> float:
    """Increment ratio across geometric cutoffs, which must be ``2``.

    Connes' trace formula makes the resolved count grow like ``2 log(Lambda)``.
    Taking cutoffs ``L``, ``L^2``, ``L^4`` doubles ``log Lambda`` at each step,
    so a logarithmic law gives increments in the ratio ``1 : 2`` and this
    returns ``2``.  A count growing linearly in the cutoff returns something
    far larger; a saturating count returns something near zero.

    The virtue of the ratio is that every normalising constant cancels, so no
    remembered dictionary between cutoff and height enters.
    """

    first = count(base_cutoff, primes)
    second = count(base_cutoff ** 2, primes)
    third = count(base_cutoff ** 4, primes)
    lower = float(second - first)
    upper = float(third - second)
    if abs(lower) < 1e-12:
        return float("inf") if abs(upper) > 1e-12 else 0.0
    return upper / lower


def count_prediction_defect(
    count: Callable[[float, Sequence[int]], int],
    primes: Sequence[int],
    cutoffs: Sequence[float],
) -> float:
    """Calibrate ``dim = a log(Lambda) + b`` on all but the last cutoff, predict it.

    The held-out point is never used to fit, so this cannot be satisfied by
    tuning: it is the exposure-scaling discipline the moments programme learned
    to apply after its first attack turned out to be contaminated.
    """

    if len(cutoffs) < 3:
        raise ValueError("need at least three cutoffs: two to calibrate, one held out")
    fit_cutoffs = list(cutoffs[:-1])
    held_out = float(cutoffs[-1])

    logs = np.array([math.log(value) for value in fit_cutoffs])
    dims = np.array([float(count(value, primes)) for value in fit_cutoffs])
    slope, intercept = np.polyfit(logs, dims, 1)

    predicted = slope * math.log(held_out) + intercept
    observed = float(count(held_out, primes))
    if abs(observed) < 1e-12:
        return float("inf")
    return float(abs(predicted - observed) / abs(observed))


def count_ablation_defect(
    count: Callable[[float, Sequence[int]], int],
    primes: Sequence[int],
    decoys: Sequence[int],
    cutoff: float,
) -> float:
    """Relative change in the resolved count when the primes become decoys."""

    real = float(count(cutoff, primes))
    fake = float(count(cutoff, decoys))
    if abs(real) < 1e-12:
        return float("inf") if abs(fake) > 1e-12 else 0.0
    return abs(fake - real) / abs(real)


def count_permutation_defect(
    count: Callable[[float, Sequence[int]], int],
    primes: Sequence[int],
    cutoff: float,
    trials: int = 3,
    seed: int = 20260805,
) -> float:
    """Relative change in the count when the same primes are reordered."""

    import random

    reference = float(count(cutoff, list(primes)))
    if abs(reference) < 1e-12:
        return float("inf")
    rng = random.Random(seed)
    worst = 0.0
    for _ in range(trials):
        shuffled = list(primes)
        rng.shuffle(shuffled)
        worst = max(worst, abs(float(count(cutoff, shuffled)) - reference) / abs(reference))
    return worst


@dataclass(frozen=True)
class CountingVerdict:
    """Outcome of the counting falsifiers for a cokernel-dimension model."""

    counts: tuple[int, ...]
    growth_ratio: float
    prediction: float
    ablation: float
    permutation: float
    logarithmic: bool
    predictive: bool
    arithmetic_dependent: bool
    order_independent: bool
    failures: tuple[str, ...] = field(default_factory=tuple)

    @property
    def passed(self) -> bool:
        return not self.failures


def counting_gate(
    count: Callable[[float, Sequence[int]], int],
    primes: Sequence[int],
    decoys: Sequence[int],
    cutoffs: Sequence[float],
) -> CountingVerdict:
    """Run the counting falsifiers on a cokernel-dimension model.

    ``count(cutoff, primes)`` returns the dimension the model resolves at that
    cutoff -- a matrix rank, not a spectrum.  Four things are asked of it: that
    it grows logarithmically in the cutoff, that a law calibrated on some
    cutoffs predicts a held-out one, that it reacts to which primes are present,
    and that it ignores the order they were listed in.

    Passing does not establish that the model is a realisation of anything.  In
    particular a construction that ingests prime data and returns zero counts
    may be the explicit formula rearranged, which is already in this repository
    twice (``zeta/weil.py``, ``scripts/03``); these gates cannot tell the
    difference and the question is not numerical.
    """

    base = float(cutoffs[0])
    counts = tuple(int(count(float(value), primes)) for value in cutoffs)
    growth = count_growth_ratio(count, primes, base)
    prediction = count_prediction_defect(count, primes, cutoffs)
    ablation = count_ablation_defect(count, primes, decoys, float(cutoffs[-1]))
    permutation = count_permutation_defect(count, primes, float(cutoffs[-1]))

    failures = []
    if not abs(growth - 2.0) <= 2.0 * GROWTH_RATIO_TOLERANCE:
        failures.append(
            f"not logarithmic: increment ratio {growth:.3f} across geometric "
            f"cutoffs, expected 2.0 +/- {2.0 * GROWTH_RATIO_TOLERANCE:.1f}"
        )
    if not prediction <= COUNT_PREDICTION_TOLERANCE:
        failures.append(
            f"not predictive: the calibrated law missed the held-out cutoff by "
            f"{prediction:.1%} (limit {COUNT_PREDICTION_TOLERANCE:.0%})"
        )
    if not ablation >= ABLATION_TOLERANCE:
        failures.append(
            f"arithmetic not load-bearing: replacing the primes changed the "
            f"count only {ablation:.1%} (needs {ABLATION_TOLERANCE:.0%})"
        )
    if not permutation <= PERMUTATION_TOLERANCE:
        failures.append(
            f"order-dependent: reordering the same primes changed the count "
            f"{permutation:.1%} (limit {PERMUTATION_TOLERANCE:.0%})"
        )

    return CountingVerdict(
        counts=counts,
        growth_ratio=growth,
        prediction=prediction,
        ablation=ablation,
        permutation=permutation,
        logarithmic=abs(growth - 2.0) <= 2.0 * GROWTH_RATIO_TOLERANCE,
        predictive=prediction <= COUNT_PREDICTION_TOLERANCE,
        arithmetic_dependent=ablation >= ABLATION_TOLERANCE,
        order_independent=permutation <= PERMUTATION_TOLERANCE,
        failures=tuple(failures),
    )
