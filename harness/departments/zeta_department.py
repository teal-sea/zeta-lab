"""``harness.departments.zeta_department`` — department #1, and the reference wiring.

This module is the subject-coupled side of the seam: it imports the laboratory
freely and owes the protocol nothing but four lists. Read it as the worked
example a second department should copy.

Nothing here is new mathematics. Every instrument below already existed in
``zeta/`` and was already run by hand; the department only states, in one
place and in a machine-checkable form, *which* of them are entitled to kill a
claim made in this department's name.

The four roles, and where each came from
----------------------------------------
* **Rivals** — :func:`zeta.epstein.dh_interface` and two Epstein zeta
  functions of discriminant -23. Each satisfies a Riemann-type functional
  equation, has real Dirichlet coefficients and a real Hardy-style Z, and
  violates the property at issue. They are assembled from legitimate Euler
  products but possess no scalar Euler product of their own, because a linear
  combination destroys primitive multiplicative structure while preserving the
  functional equation. This is gate #3 of ``docs/09``.
* **Decoys** — the ablation move of :func:`zeta.spectral_gate.ablation_defect`
  and :func:`zeta.spectral_gate.permutation_defect`, one substituting numbers
  of the same density for the primes, the other keeping the same primes and
  changing only their order. Paired, they are sharp: a construction must react
  to *which* places are present and ignore *what order* they arrive in.
* **Surrogates** — the three null models of ``zeta/surrogate.py``, built for
  ``NULLCONTROLS.md``: a first-order log-correlated field, the full random
  Euler product, and CUE. None carries any arithmetic input.
* **Lesions** — synthetic zero quadruples at ``1/2 +/- delta +/- iT``, the
  planted violations of ``zeta/detectors.py``. A detector that does not notice
  one at a given ``delta`` is blind at that magnitude, and its silence on real
  data measures that blindness rather than the world.

Registration happens at import time; ``harness.departments.load("zeta")`` is
the supported way in.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import numpy as np
from mpmath import mp

from harness.protocol import (
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
    register_department,
)
from harness.independence import IndependenceReport, VerificationPath, compare
from harness.provenance import Provenance
from zeta import epstein, surrogate
from zeta.detectors import _lesion_zeros

DEPARTMENT_NAME = "zeta"
DEPARTMENT_VERSION = "1.0"

#: Working precision for the rival interfaces. Low on purpose: the battery
#: asks whether a claim *fires*, not what it evaluates to, and a rival run at
#: 50 digits refutes nothing that one run at 25 digits does not.
DPS = 25

#: Discriminant -23 has class number 3; these are the non-principal and the
#: principal form. Both are rivals; see ``docs/09`` SS5.1.
EPSTEIN_FORMS: tuple[tuple[int, int, int], ...] = ((2, 1, 3), (1, 1, 6))

#: Height at which lesion quadruples are planted, and the displacements off
#: the line. The smallest is deliberately below what most of the laboratory's
#: detectors can see: a battery whose lesions are all easy would report power
#: the detectors do not have.
LESION_HEIGHT: float = 40.0
LESION_DELTAS: tuple[float, ...] = (0.1, 0.01, 0.001)

__all__ = [
    "DEPARTMENT_NAME",
    "DEPARTMENT_VERSION",
    "DPS",
    "EPSTEIN_FORMS",
    "LESION_HEIGHT",
    "LESION_DELTAS",
    "BATTERY",
    "DEPARTMENT",
    "REFERENCE_CLAIMS",
    "DETECTORS",
    "LI_PROJECTION_THRESHOLD",
    "InterfaceSubject",
    "PrimeDecoy",
    "IntensitySurrogate",
    "OffLineLesion",
    "li_projection_deviation",
    "li_projection_detector",
    "off_line_scan",
]


# ---------------------------------------------------------------------------
# Subjects: the genuine article and its rivals
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InterfaceSubject:
    """A subject whose payload is one of ``zeta.epstein``'s interface dicts.

    The interface is rebuilt on every ``payload()`` call rather than cached:
    the dicts close over precision and over mpmath state, and a claim that
    mutated one would otherwise silently contaminate every later run of the
    battery — which would flatter exactly the claims the battery exists to
    catch.
    """

    name: str
    _kind: str
    _form: tuple[int, int, int] | None = None
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def payload(self) -> dict:
        if self._kind == "zeta":
            return epstein.zeta_interface(DPS)
        if self._kind == "dh":
            return epstein.dh_interface(DPS)
        if self._kind == "epstein":
            assert self._form is not None
            return epstein.epstein_interface(self._form, DPS)
        raise ValueError(f"unknown subject kind {self._kind!r}")


TARGET = InterfaceSubject(
    name="riemann_zeta",
    _kind="zeta",
    _description="the genuine article: a scalar Euler product, conjecturally with every non-trivial zero on the line",
)

RIVALS: tuple[InterfaceSubject, ...] = (
    InterfaceSubject(
        name="davenport_heilbronn",
        _kind="dh",
        _description="functional equation, real coefficients, real Z — and zeros off the line; no Euler product of its own",
    ),
    *(
        InterfaceSubject(
            name=f"epstein_{a}_{b}_{c}",
            _kind="epstein",
            _form=(a, b, c),
            _description=(
                f"Epstein zeta of the form ({a},{b},{c}), discriminant -23: a linear "
                "combination of Hecke L-functions, so the functional equation survives "
                "and primitive multiplicative structure does not"
            ),
        )
        for (a, b, c) in EPSTEIN_FORMS
    ),
)


# ---------------------------------------------------------------------------
# Decoys: same shape, no arithmetic
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class PrimeDecoy:
    """A substitution acting on a sequence of primes.

    ``substitute`` receives the prime list a construction was built from and
    returns a list of the same length. ``replace`` swaps the values for
    non-primes of comparable size, which must move any spectrum that is really
    reading the primes; ``permute`` keeps the very same values and changes only
    their order, which must *not* move a spectrum that depends on the set of
    places rather than on a position in a Python list.
    """

    name: str
    mode: str
    seed: int = 20260806
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def substitute(self, payload: Any) -> list[int]:
        values = [int(v) for v in payload]
        rng = np.random.default_rng(self.seed)
        if self.mode == "permute":
            order = rng.permutation(len(values))
            return [values[i] for i in order]
        if self.mode == "replace":
            if not values:
                return []
            # Composite stand-ins spanning the same range: the density and the
            # magnitudes survive, the arithmetic does not.
            low, high = min(values), max(values)
            span = max(high - low, len(values))
            draw = rng.integers(low, low + span + 1, size=len(values))
            return [int(v) | 1 if v % 2 else int(v) for v in np.sort(draw)]
        raise ValueError(f"unknown decoy mode {self.mode!r}")


DECOYS: tuple[PrimeDecoy, ...] = (
    PrimeDecoy(
        name="non_prime_replacement",
        mode="replace",
        _description="same count and same range, drawn without regard to primality — a spectrum that does not move was never reading the primes",
    ),
    PrimeDecoy(
        name="prime_permutation",
        mode="permute",
        _description="the same primes in a different order — a spectrum that moves is reading a list index, not a set of places",
    ),
)


# ---------------------------------------------------------------------------
# Surrogates: the observation, from no arithmetic at all
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class IntensitySurrogate:
    """A null model producing an intensity array on a fixed grid.

    Each draws a sample of the same shape as the laboratory's ``|zeta|^2``
    samples and carries no arithmetic input: the first two randomise the phases
    of a prime-indexed sum, which destroys every arithmetic relation while
    keeping the Euler-product *shape*, and the third has no primes in it at all.
    """

    name: str
    kind: str
    points: int = 4096
    prime_limit: int = 1000
    seed: int = 20260806
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def sample(self) -> np.ndarray:
        ts = np.linspace(0.0, 100.0, self.points)
        primes = surrogate.primes_up_to(self.prime_limit)
        if self.kind == "log_correlated":
            return surrogate.sample_intensity(ts, primes, seed=self.seed)
        if self.kind == "random_euler":
            return surrogate.sample_euler_intensity(ts, primes, seed=self.seed)
        if self.kind == "cue":
            return surrogate.sample_cue_intensity(
                dimension=32, matrices=8, points_per_gap=16, seed=self.seed
            )
        raise ValueError(f"unknown surrogate kind {self.kind!r}")


SURROGATES: tuple[IntensitySurrogate, ...] = (
    IntensitySurrogate(
        name="log_correlated_field",
        kind="log_correlated",
        _description="first-order log-correlated surrogate with randomised phases (NULLCONTROLS.md, A1)",
    ),
    IntensitySurrogate(
        name="random_euler_product",
        kind="random_euler",
        _description="full random Euler product, keeping the prime-power terms the first-order model drops (A2)",
    ),
    IntensitySurrogate(
        name="cue",
        kind="cue",
        _description="characteristic polynomials of CUE matrices — no primes in it anywhere (A3)",
    ),
)


# ---------------------------------------------------------------------------
# Lesions: planted violations, so that power is measured and not assumed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class OffLineLesion:
    """Plant a symmetric quadruple of zeros off the critical line.

    ``apply`` receives a sequence of zeros as ``mpc`` and returns it with the
    quadruple ``1/2 +/- delta +/- iT`` appended. The quadruple is symmetric so
    that the lesioned set still satisfies the reflection the functional
    equation forces: a lesion that broke the symmetry would be detectable for a
    reason that has nothing to do with the line, and would overstate every
    detector's power.
    """

    name: str
    magnitude: float
    height: float = LESION_HEIGHT
    _description: str = ""

    def describe(self) -> str:
        return self._description or (
            f"four zeros at 1/2 +/- {self.magnitude} +/- {self.height}i, symmetric under the functional equation"
        )

    def apply(self, payload: Any) -> tuple:
        with mp.workdps(DPS + 10):
            planted = _lesion_zeros(self.magnitude, self.height)
        return (*tuple(payload), *planted)


LESIONS: tuple[OffLineLesion, ...] = tuple(
    OffLineLesion(name=f"off_line_delta_{delta:g}".replace(".", "_"), magnitude=delta)
    for delta in LESION_DELTAS
)


# ---------------------------------------------------------------------------
# Detectors: what the department's silence is staked on, power measured
# ---------------------------------------------------------------------------

#: Working precision for detector arithmetic; matches the lesions' (DPS + 10).
_DETECTOR_DPS = DPS + 10

#: Li/Bombieri–Lagarias orders the criterion detector sums over.
_LI_ORDERS: tuple[int, ...] = (2, 4, 8)

#: Threshold for the criterion detector, placed against the measured response
#: curve: the projection deviation scales like delta² and measures 1.48e-6 at
#: delta = 0.1, 1.48e-8 at 0.01, 1.48e-10 at 0.001 (T = 40, n = 8). 1e-7
#: therefore fires at the largest planted lesion and is *measurably blind* to
#: the two smaller ones — which is the department's docstring made a number:
#: the smallest lesion is deliberately below what the criteria can see.
LI_PROJECTION_THRESHOLD: float = 1e-7


def _clean_zero_probe() -> tuple:
    """The first ten genuine zeros (upper half), the detectors' clean probe."""
    with mp.workdps(_DETECTOR_DPS):
        return tuple(mp.zetazero(k) for k in range(1, 11))


_CLEAN_ZEROS = _clean_zero_probe()


def _li_partial(zeros, n: int):
    total = mp.mpf(0)
    for rho in zeros:
        for z in (rho, 1 - rho):
            total += (1 - (1 - 1 / z) ** n).real
    return total


def li_projection_deviation(zeros) -> float:
    """max_n |λ_n(multiset) − λ_n(its on-line projection)|.

    Comparing against the *projection* rather than against a fixed clean
    background is load-bearing: the raw λ_n deviation is dominated by the
    presence of four extra zeros and barely changes with delta, so a detector
    built on it would fire for a quad planted ON the line — detection for a
    reason that has nothing to do with the property. The projection
    differential isolates exactly the off-line displacement.
    """
    with mp.workdps(_DETECTOR_DPS):
        projected = tuple(mp.mpc(mp.mpf(1) / 2, mp.mpc(z).imag) for z in zeros)
        return float(
            max(abs(_li_partial(zeros, n) - _li_partial(projected, n)) for n in _LI_ORDERS)
        )


def li_projection_detector(zeros) -> bool:
    """Fires when the Li multiset deviates from its on-line projection."""
    return li_projection_deviation(zeros) > LI_PROJECTION_THRESHOLD


def off_line_scan(zeros) -> bool:
    """Fires when any zero in the multiset sits off the critical line.

    Full power by construction — the payload *is* the zero multiset, so this
    reads the property directly. Kept alongside the criterion detector for
    the same reason the compiler department keeps its concrete backend next
    to its model: the power *difference* between the two is the measurement
    of where the criteria go blind.
    """
    with mp.workdps(_DETECTOR_DPS):
        return any(abs(mp.mpc(z).real - mp.mpf(1) / 2) > mp.mpf("1e-9") for z in zeros)


DETECTORS: tuple[NamedDetector, ...] = (
    NamedDetector(
        name="off_line_scan",
        fires=off_line_scan,
        probe=_CLEAN_ZEROS,
        note=(
            "reads Re(rho) directly from the multiset — full power by construction, "
            "the baseline the criterion detector is measured against"
        ),
    ),
    NamedDetector(
        name="li_projection",
        fires=li_projection_detector,
        probe=_CLEAN_ZEROS,
        note=(
            "Bombieri–Lagarias λ_n against the multiset's on-line projection, "
            f"threshold {LI_PROJECTION_THRESHOLD:g}: fires at delta 0.1, measured "
            "blind at 0.01 and 0.001 — the criteria's blindness as a number"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery, and the department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="zeta",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "Gate #3 of docs/09 plus the ablation, null-control and detector-power "
        "instruments of docs/17. A claim that fires for any rival distinguishes "
        "nothing, however many other rivals it excludes."
    ),
)

#: The two calibration claims, both already in ``zeta/epstein.py`` with their
#: verdicts derived there. They pin the battery in both directions: the first
#: is a real, true property of zeta that the battery must nonetheless kill,
#: because every rival has it too; the second is the property the rivals lack.
#: The conformance test re-runs both rather than trusting these labels.
REFERENCE_CLAIMS: tuple[ReferenceClaim, ...] = (
    ReferenceClaim(
        name="functional_equation",
        claim=epstein.claim_functional_equation,
        distinguishes=False,
        note=(
            "true of the target and of every rival — a symmetry shared with functions "
            "that violate the property cannot be the load-bearing step of any argument "
            "that the property follows from the symmetry"
        ),
    ),
    ReferenceClaim(
        name="multiplicativity",
        claim=epstein.claim_multiplicativity,
        distinguishes=True,
        note=(
            "the fingerprint of an Euler product: true of the target, false for every "
            "rival, because linear combination destroys primitive multiplicative "
            "structure while preserving the functional equation"
        ),
    ),
)

DEPARTMENT = Department(
    name=DEPARTMENT_NAME,
    summary=(
        "the Riemann zeta function and RH: the classical machinery implemented at "
        "arbitrary precision, every identity measured as a defect rather than assumed"
    ),
    battery=BATTERY,
    door="docs/doors/zeta.md",
    domain="zeta",
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "a surviving claim distinguishes the target from rivals sharing the "
        "functional-equation structure — nothing more; per docs/08, nothing "
        "here is evidence for or against RH"
    ),
    provenance=Provenance(
        authored_by="the laboratory's own process (same process as the subject modules)",
        authored_on="2026-08-07",
        independent_of_subject_author=False,
        oracle_calls_subject=False,
        notes=(
            "every instrument predates the department and was already run by "
            "hand (docs/09, docs/17, NULLCONTROLS.md); the cross-check oracle "
            "for the laboratory is mpmath's independent implementation"
        ),
    ),
    modules=(
        "zeta.core",
        "zeta.zeros",
        "zeta.explicit",
        "zeta.statistics",
        "zeta.heatflow",
        "zeta.weil",
        "zeta.epstein",
        "zeta.rigor",
        "zeta.li",
        "zeta.criteria",
        "zeta.moments",
    ),
)

register_department(DEPARTMENT, replace=True)


# ---------------------------------------------------------------------------
# The rigor two-backend cross-check, declared as verification paths
# ---------------------------------------------------------------------------
#
# docs/25 measured the lesson these declarations carry: `proven_sign` returned
# a wrong sign on *both* backends because the fault sat in `_exact`, a parsing
# layer the two paths share upstream of everything either one duplicates. The
# shared list below is HANDOFF's own enumeration (the 2026-08-11 director-run
# record): `_exact`, the grid policy, the contour policy, and the final
# S(T)/N(T) interval summation. Only the ball-arithmetic layer is implemented
# twice, so agreement between the backends is evidence about that layer alone.
# `tests/test_harness_independence.py` pins both the structure and the fact
# that the declared anchor (`zeta.rigor._exact`) still exists.

RIGOR_SHARED_LAYERS = (
    "numeric input parsing (zeta.rigor._exact)",
    "evaluation grid policy",
    "contour policy",
)

RIGOR_SHARED_TAIL = ("S(T)/N(T) interval summation",)

RIGOR_BACKEND_PATHS = (
    VerificationPath(
        name="rigor backend: python-flint (Arb)",
        layers=RIGOR_SHARED_LAYERS
        + ("ball arithmetic: python-flint (Arb)",)
        + RIGOR_SHARED_TAIL,
    ),
    VerificationPath(
        name="rigor backend: mpmath.iv",
        layers=RIGOR_SHARED_LAYERS
        + ("ball arithmetic: mpmath.iv",)
        + RIGOR_SHARED_TAIL,
    ),
)


def rigor_backend_independence() -> IndependenceReport:
    """The two-backend cross-check's declared independence structure.

    Radius 3 of 5, one reconvergent layer, and exactly one layer implemented
    twice: the report is the machine-readable form of docs/25's standing
    consequence — a cross-check bounds only what is actually duplicated.
    """

    return compare(*RIGOR_BACKEND_PATHS)
