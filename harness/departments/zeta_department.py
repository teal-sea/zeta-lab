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

from harness.protocol import Battery, Department, ReferenceClaim, register_department
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
    "InterfaceSubject",
    "PrimeDecoy",
    "IntensitySurrogate",
    "OffLineLesion",
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
