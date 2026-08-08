"""Candidate department #2 — LLVM IR rewrites. **Not registered.**

This module deliberately does *not* appear in
:data:`harness.departments.KNOWN_DEPARTMENTS`, and calls no
:func:`~harness.protocol.register_department`. Registration is the graduation
step, not the setup step: it makes a working candidate accountable, and a
candidate that has not yet earned admission would only be borrowing the
legitimacy of the audit it has not passed. ``compiler/FINDINGS.md`` carries the
admission verdict and the evidence behind it.

Everything below is built from ``compiler/``, which is the laboratory this
department refereess. The four roles were derived from the compiler subject
rather than transplanted from department #1; the derivation, including the two
mappings that came out strained, is in the findings document.

The mapping, in one paragraph each
----------------------------------
* **Subject** — a :class:`compiler.catalog.Transformation`: one source program,
  one proposed replacement. The genuine article is a rewrite that agrees with
  its source everywhere in the enumerated domain.
* **Rival** — a rewrite that shares every cheap property the target has, and is
  wrong. All three are transformations competent people have written on
  purpose: divide-by-two as a shift, unsigned-divide as an arithmetic shift, and
  signed comparison via the sign bit of a difference. Each matches the target's
  instruction count exactly, so any claim resting on size is shared with them.
* **Decoy** — a substitution acting on **the set of inputs the verdict was
  measured over**. The substantive input to a test-based claim about a program
  is which inputs were tested; a verdict that does not move when a diverse input
  set is swapped for a degenerate one of the same size was never reading it.
  This is the department's sharpest instrument in practice: it turns "our tests
  pass" into a measurement rather than a reassurance.
* **Surrogate** — a candidate drawn from an unguided mutation generator: the
  same *kind* of generator a search would use, with the part that is supposed to
  know what it is doing removed.
* **Lesion** — a planted corruption of a rewrite already shown to agree
  everywhere, at magnitudes spanning four orders. One of them is invisible to
  the only backend installed, on purpose.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from compiler import catalog, semantics
from harness.protocol import Battery, Department, ReferenceClaim

DEPARTMENT_NAME = "compiler"
DEPARTMENT_VERSION = "0.1-candidate"

#: The input set the ablation baseline is measured over: the whole i8 range.
FULL_DOMAIN: tuple[int, ...] = tuple(range(-128, 128))

#: Seeds for the unguided mutation surrogates. Fixed so the null is
#: reproducible; a surrogate whose value moved run to run could not be quoted.
SURROGATE_SEEDS: tuple[int, ...] = (11, 23, 57)

__all__ = [
    "DEPARTMENT_NAME",
    "DEPARTMENT_VERSION",
    "FULL_DOMAIN",
    "SURROGATE_SEEDS",
    "BATTERY",
    "CANDIDATE",
    "REFERENCE_CLAIMS",
    "RewriteSubject",
    "InputSetDecoy",
    "UnguidedMutationSurrogate",
    "PlantedDefect",
    "agreement_over",
    "concrete_detector",
]


# ---------------------------------------------------------------------------
# Subjects
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RewriteSubject:
    """A subject whose payload is one proposed rewrite."""

    name: str
    transformation: catalog.Transformation

    def describe(self) -> str:
        return self.transformation.describe()

    def payload(self) -> catalog.Transformation:
        return self.transformation


TARGET = RewriteSubject(name=catalog.TARGET.name, transformation=catalog.TARGET)
RIVALS: tuple[RewriteSubject, ...] = tuple(
    RewriteSubject(name=t.name, transformation=t) for t in catalog.RIVALS
)


# ---------------------------------------------------------------------------
# Decoys — substitutions on the input set a verdict was measured over
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InputSetDecoy:
    """Replace a set of test inputs with a same-sized set that covers nothing.

    ``substitute`` takes a list of integers and returns a list of the same
    length. ``narrow`` crushes the values into a small window and ``constant``
    collapses them to a single value; both preserve the *count* of tests, which
    is the number a test suite usually reports, and destroy the coverage, which
    is the thing that was actually doing the work.
    """

    name: str
    mode: str
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def substitute(self, payload: Any) -> list[int]:
        values = [semantics.i8(v) for v in payload]
        if self.mode == "narrow":
            return [semantics.i8(v % 8) for v in values]
        if self.mode == "constant":
            return [0] * len(values)
        raise ValueError(f"unknown decoy mode {self.mode!r}")


DECOYS: tuple[InputSetDecoy, ...] = (
    InputSetDecoy(
        name="narrow_input_window",
        mode="narrow",
        _description="the same number of test inputs, all crowded into [0, 7] — a "
        "verdict that does not move was reading the count of tests, not their reach",
    ),
    InputSetDecoy(
        name="constant_input_set",
        mode="constant",
        _description="the same number of test inputs, all of them zero — the "
        "degenerate suite that every transformation passes",
    ),
)


# ---------------------------------------------------------------------------
# Surrogates — candidates from a generator with no idea what it is doing
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class UnguidedMutationSurrogate:
    """One candidate rewrite drawn from unguided mutation of the target's source."""

    name: str
    seed: int
    _description: str = ""

    def describe(self) -> str:
        return self._description

    def sample(self) -> catalog.Transformation:
        return catalog.random_mutant(catalog.TARGET.source, self.seed)


SURROGATES: tuple[UnguidedMutationSurrogate, ...] = tuple(
    UnguidedMutationSurrogate(
        name=f"unguided_mutation_{seed}",
        seed=seed,
        _description=(
            f"opcode mutation of the target's source under seed {seed}, with no "
            "correctness or optimisation guidance whatsoever"
        ),
    )
    for seed in SURROGATE_SEEDS
)


# ---------------------------------------------------------------------------
# Lesions — planted violations of a rewrite known to agree everywhere
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class PlantedDefect:
    """Wrap a :class:`compiler.catalog.LesionSpec` as a harness lesion.

    ``probe`` is a representative payload of the shape this lesion consumes. It
    exists because the conformance suite must be able to poke an instrument
    without knowing the department's subject, and the payload a lesion operates
    on is not the target's payload and cannot be guessed. See
    ``compiler/FINDINGS.md`` §"what felt forced".
    """

    name: str
    magnitude: float
    spec: catalog.LesionSpec
    probe: catalog.Transformation = field(default=catalog.LESION_HOST)

    def describe(self) -> str:
        return self.spec.describe()

    def apply(self, payload: Any) -> catalog.Transformation:
        return self.spec.apply(payload)


LESIONS: tuple[PlantedDefect, ...] = tuple(
    PlantedDefect(name=spec.name, magnitude=spec.magnitude, spec=spec)
    for spec in catalog.LESIONS
)


# ---------------------------------------------------------------------------
# Measurements the instruments act on
# ---------------------------------------------------------------------------


def agreement_over(transformation: catalog.Transformation):
    """A measure of agreement as a function of the *input set*, for ablation."""

    def measure(values: Any) -> float:
        return catalog.agreement_fraction_of(transformation, list(values))

    measure.__name__ = f"agreement_of_{transformation.name}"
    return measure


def concrete_detector(transformation: Any) -> bool:
    """Fires when the exhaustive concrete run notices a disagreement.

    This is the detector whose power the lesions measure. It fires on
    *disagreement*, so a lesion it misses is a violation it called clean.
    """
    return not semantics.agreement(transformation.source, transformation.target).agrees


def unguided_agreement(transformation: Any) -> float:
    """Agreement fraction over the whole domain — the statistic the nulls test."""
    return semantics.agreement(transformation.source, transformation.target).fraction


# ---------------------------------------------------------------------------
# The battery and the (unregistered) department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="compiler",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "Every rival matches the target's instruction count exactly, so any claim "
        "resting on size is shared with three transformations that are wrong. The "
        "decoys ablate the input set rather than the program, because the "
        "substantive input to a test-based verdict is which inputs were tested. "
        "One lesion is invisible to the only backend installed; that is measured, "
        "not hidden — see compiler/FINDINGS.md."
    ),
)

#: The two calibration claims. The first is real, true of the target, and true
#: of every rival — the compiler domain's version of a property everything in
#: the room happens to share. The second is the one the rivals lack.
REFERENCE_CLAIMS: tuple[ReferenceClaim, ...] = (
    ReferenceClaim(
        name="no_more_instructions",
        claim=catalog.claim_no_more_instructions,
        distinguishes=False,
        note=(
            "true of the target and of all three rivals, whose instruction counts "
            "match it exactly — shorter code is not evidence of a correct rewrite, "
            "and this claim is here to make that a measurement rather than a maxim"
        ),
    ),
    ReferenceClaim(
        name="exhaustive_agreement_i8",
        claim=catalog.claim_exhaustive_agreement,
        distinguishes=True,
        note=(
            "the target returns the same value as its source at all 65536 i8 pairs "
            "and every rival does not. This is agreement over an enumerated finite "
            "domain — not equivalence, not refinement, and blind to poison: see "
            "compiler.semantics.EVIDENCE_EXHAUSTIVE_I8"
        ),
    ),
)

#: Built, validated, and deliberately not registered. Graduation would mean
#: writing ``docs/doors/compiler.md`` and adding one line to
#: ``harness.departments.KNOWN_DEPARTMENTS``.
CANDIDATE = Department(
    name=DEPARTMENT_NAME,
    summary=(
        "LLVM IR rewrites: whether a proposed transformation deserves belief, "
        "separated from whether it is shorter"
    ),
    battery=BATTERY,
    door="docs/doors/compiler.md",
    modules=("compiler.semantics", "compiler.catalog"),
    reference_claims=REFERENCE_CLAIMS,
)
