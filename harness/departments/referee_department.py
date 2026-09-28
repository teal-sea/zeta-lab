"""Department #5: the referee itself, batteries as subjects, audited like one.

The subject of this department is the verification machinery: a
:class:`~harness.protocol.Department` bundle is the payload, and the claims
are about whether such a bundle deserves trust. This is not symmetry for its
own sake. The repository discovered twice, the sham battery commit
``431cc74`` replaced, and the dossier resumption benchmark, that a
structurally complete battery can be epistemically worthless, and the
harness's own admission rule says what follows: work whose claims nothing
can falsify is not a department. Verification claims were exactly such work
until this module, because nothing in the tree could kill "this battery is
trustworthy".

The four roles, derived rather than transplanted
------------------------------------------------
* **Target**: a specimen department in a neutral toy domain, genuinely
  calibrated: real rivals, moving decoys, planting lesions, a detector with
  measured power and specificity, reference claims that re-derive.
* **Rivals**, bundles that share the structure and lack the integrity:
  the **reconstruction of the 431cc74 sham** (rivals carrying a
  ``virtual_a_p`` label field, a surrogate returning ``[1, 2, 3]``,
  placeholder instruments written to the conformance tests' shapes), a
  constant-detector sham, and an inert-instrument sham. The reconstruction
  is this department's held-out element: it was authored by a different
  process, at a different time, with no knowledge of today's audit, the
  closest thing to an externally authored mutant the repository owns.
* **Decoys**: substitutions on the bundle that keep its shape and remove
  the substance an integrity verdict is supposed to read: vacuous
  calibration claims, an undeclared provenance record.
* **Surrogates**, bundles assembled by an unguided generator: structurally
  valid parts, seeded random content, no calibration effort anywhere. If
  the audit's pass-count is reproduced by these, passing checks is a
  property of the bundle class, not evidence of calibration.
* **Lesions** :mod:`harness.shams` mutations planted into the specimen,
  with magnitudes **measured at import** (the fraction of audit checks the
  mutation flips), never asserted, department #4's lesson.
* **Detector**, the integrity audit itself, as a predicate: it fires when
  a bundle's grade is not CALIBRATED. Its specificity is measured on the
  specimen, its power on the planted mutations. This is the recursion, and
  also where it stops: the audit that grades departments is here a declared
  detector whose power is measured by planted battery-corruptions, and the
  conformance suite, deterministic, pinned, re-run on every change, is
  the trusted kernel underneath. There is no meta-meta-referee; there is a
  kernel, and it is documented at the door.

What surviving this battery does NOT mean
-----------------------------------------
The audit's declared blind spots (``integrity.AUDIT_BLIND_SPOTS``) apply to
every verdict this department issues: a bundle whose calibration content was
co-designed with its instruments, or whose payloads encode identity in
values, can pass. The countermeasure is independent authorship, declared in
provenance and unverifiable mechanically. That boundary is stated on the
door rather than hidden inside a passing grade.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any

from harness import shams
from harness.integrity import (
    CALIBRATED,
    audit_department,
)
from harness.protocol import (
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
    department_reasons,
    register_department,
)
from harness.provenance import Provenance

DEPARTMENT_NAME = "referee"
DEPARTMENT_VERSION = "1.0"

__all__ = [
    "DEPARTMENT_NAME",
    "DEPARTMENT_VERSION",
    "BATTERY",
    "DEPARTMENT",
    "REFERENCE_CLAIMS",
    "SPECIMEN",
    "build_specimen",
    "build_sham_431cc74",
    "random_bundle",
    "integrity_pass_count",
    "claim_validates_structurally",
    "claim_audits_calibrated",
    "integrity_flags",
]


# ---------------------------------------------------------------------------
# The toy domain the specimen lives in, deliberately arithmetic-free
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _ToySubject:
    name: str
    value: float
    _blurb: str = ""

    def describe(self) -> str:
        return self._blurb or f"toy subject at value {self.value}"

    def payload(self) -> dict:
        return {"value": self.value}


@dataclass(frozen=True)
class _ToyDecoy:
    name: str = "increment-all"

    def describe(self) -> str:
        return "adds one to every probe entry, shape kept, values moved"

    def substitute(self, probe: Any) -> list:
        return [x + 1 for x in probe]


@dataclass(frozen=True)
class _ToySurrogate:
    name: str = "far-null"

    def describe(self) -> str:
        return "a payload with no relation to the target's"

    def sample(self) -> dict:
        return {"value": 99.0}


@dataclass(frozen=True)
class _ToyLesion:
    name: str
    magnitude: float
    probe: Any = (0.0,)

    def describe(self) -> str:
        return f"appends a violation of size {self.magnitude}"

    def apply(self, payload: Any) -> tuple:
        return (*payload, self.magnitude)


def build_specimen() -> Department:
    """The target: a calibrated department in the toy domain.

    Rebuilt on every call, like every subject payload in this tree: a claim
    that mutated a cached bundle would contaminate every later run.
    """
    battery = Battery(
        name="specimen",
        target=_ToySubject("specimen-target", 1.0, "the genuine toy article"),
        rivals=(
            _ToySubject("specimen-rival-a", 2.0, "shares the shape, sits elsewhere"),
            _ToySubject("specimen-rival-b", 3.0, "shares the shape, sits elsewhere"),
        ),
        decoys=(_ToyDecoy(),),
        surrogates=(_ToySurrogate(),),
        lesions=(
            _ToyLesion("large", 1.0),
            _ToyLesion("medium", 0.1),
            _ToyLesion("small", 0.001),
        ),
        notes="the calibrated specimen the referee department's verdicts are anchored to",
    )
    return Department(
        name="specimen",
        summary="a genuinely calibrated toy department, the referee's reference point",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("shared-everywhere", lambda p: True, distinguishes=False),
            ReferenceClaim("target-only", lambda p: p["value"] == 1.0, distinguishes=True),
        ),
        detectors=(
            NamedDetector(
                "size-scan",
                lambda p: any(x > 0 for x in p),
                probe=(0.0,),
                note="fires when any planted entry is positive; quiet on the clean probe",
            ),
        ),
        scope="distinguishes the toy target from its two toy rivals; nothing else",
        provenance=Provenance(
            authored_by="harness.departments.referee_department",
            authored_on="2026-08-09",
            independent_of_subject_author=False,
            results_visible_when_authored=False,
            frozen_before_execution=True,
        ),
    )


SPECIMEN = build_specimen()


# ---------------------------------------------------------------------------
# The held-out rival: the 431cc74 sham, reconstructed
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _ShamSubject:
    """A subject in the sham's image: counts plus, on rivals, the label leak."""

    name: str
    counts: tuple
    virtual_a_p: int | None = None

    def describe(self) -> str:
        return "a counting profile" + (
            " carrying a virtual_a_p tell" if self.virtual_a_p is not None else ""
        )

    def payload(self) -> dict:
        payload: dict = {"p": 1009, "counts": self.counts}
        if self.virtual_a_p is not None:
            payload["virtual_a_p"] = self.virtual_a_p
        return payload


@dataclass(frozen=True)
class _ShamDecoy:
    """Written to the conformance test's shape: changes the probe, reads nothing."""

    name: str = "reverse-order"
    probe: Any = (1, 2, 3, 4)

    def describe(self) -> str:
        return "reverses its input, enough to pass a change-detection probe, nothing more"

    def substitute(self, probe: Any) -> list:
        return list(reversed(list(probe)))


@dataclass(frozen=True)
class _ShamSurrogate:
    name: str = "placeholder-null"

    def describe(self) -> str:
        return "returns [1, 2, 3], the commit message's own example"

    def sample(self) -> list:
        return [1, 2, 3]


@dataclass(frozen=True)
class _ShamLesion:
    name: str
    magnitude: float
    probe: Any = ()

    def describe(self) -> str:
        return "appends a marker to whatever it is given"

    def apply(self, payload: Any) -> tuple:
        return (*tuple(payload), "planted-marker")


def build_sham_431cc74() -> Department:
    """The sham battery commit ``431cc74`` replaced, reconstructed.

    The original was staged and never committed, so no byte-exact source
    survives; this reconstruction follows the replacing commit's description
    exactly: rivals carrying a ``virtual_a_p`` payload field a claim could
    read as a label, a surrogate returning ``[1, 2, 3]``, decoys and lesions
    written to the conformance tests' shapes of the day. The distinguishing
    reference claim reads the label, which is what made it a sham. One
    modernisation was unavoidable: today's admission rule demands a declared
    detector, so the sham gets one co-designed with its own placeholder
    lesion, the move a sham author would make. Every instrument here passes
    the *structural* checks of its era. What it never had is substance.
    """
    battery = Battery(
        name="sham-431cc74",
        target=_ShamSubject("sham-target", counts=(986, 1018082, 1027243286)),
        rivals=(
            _ShamSubject("sham-rival-70", counts=(940, 1013150, 1026167000), virtual_a_p=70),
            _ShamSubject("sham-rival-200", counts=(810, 978182, 1018019210), virtual_a_p=200),
        ),
        decoys=(_ShamDecoy(),),
        surrogates=(_ShamSurrogate(),),
        lesions=(_ShamLesion("marker-large", 1.0), _ShamLesion("marker-small", 0.1)),
        notes="(reconstruction) the battery that could never fail, per commit 431cc74",
    )
    return Department(
        name="sham-431cc74",
        summary="(reconstruction) the sham finite-survey battery replaced by 431cc74",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("counts-positive", lambda p: all(c > 0 for c in p["counts"]), distinguishes=False),
            # The leak, load-bearing: "distinguishes" by reading the label.
            ReferenceClaim(
                "no-virtual-trace", lambda p: "virtual_a_p" not in p, distinguishes=True
            ),
        ),
        detectors=(
            NamedDetector(
                "marker-scan",
                lambda p: "planted-marker" in tuple(p),
                probe=(),
                note="(co-designed) fires exactly on its own placeholder lesion's marker",
            ),
        ),
        scope="(sham) claims to distinguish genuine from counterfeit counting data",
    )


# ---------------------------------------------------------------------------
# The other rivals: shams built by corruption of a calibrated bundle
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _BundleSubject:
    """A subject whose payload is a department bundle, rebuilt per call."""

    name: str
    build: Any
    _blurb: str = ""

    def describe(self) -> str:
        return self._blurb

    def payload(self) -> Department:
        return self.build()


TARGET = _BundleSubject(
    name="calibrated-specimen",
    build=build_specimen,
    _blurb="a genuinely calibrated department: every audit check passes on its merits",
)

RIVALS: tuple[_BundleSubject, ...] = (
    _BundleSubject(
        name="sham-431cc74-reconstruction",
        build=build_sham_431cc74,
        _blurb=(
            "the held-out rival: the historical sham, authored by another process "
            "before this audit existed, label leak, placeholder instruments"
        ),
    ),
    _BundleSubject(
        name="constant-detector-sham",
        build=lambda: shams.with_constant_detector(build_specimen(), value=True),
        _blurb="the specimen with an always-on alarm: perfect sensitivity, no information",
    ),
    _BundleSubject(
        name="inert-instrument-sham",
        build=lambda: shams.with_inert_lesions(build_specimen()),
        _blurb="the specimen with lesions that plant nothing: power theater",
    ),
)


# ---------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------


def claim_validates_structurally(bundle: Department) -> bool:
    """Fires when the bundle passes structural admission.

    True of the specimen and of every sham rival, including the 431cc74
    reconstruction, whose whole point is that it validated. This is the
    reference claim the battery must kill, and the department's headline
    measurement: **structural completeness is not verification.**
    """
    return department_reasons(bundle) == ()


def claim_audits_calibrated(bundle: Department) -> bool:
    """Fires when the full integrity audit grades the bundle CALIBRATED."""
    return audit_department(bundle).grade == CALIBRATED


def integrity_pass_count(bundle: Department) -> float:
    """The ablation/null statistic: how many audit checks pass on the bundle."""
    report = audit_department(bundle)
    return float(sum(1 for check in report.checks if check.status == "pass"))


# ---------------------------------------------------------------------------
# Decoys: strip the substance an integrity verdict reads
# ---------------------------------------------------------------------------


class _VacuousCalibrationDecoy:
    name = "vacuous-calibration"
    probe = SPECIMEN

    def describe(self) -> str:
        return (
            "replaces the reference claims with a shape-valid pair that cannot "
            "earn its labels, the calibration content is the substance"
        )

    def substitute(self, bundle: Department) -> Department:
        return shams.with_vacuous_calibration(bundle)


class _UndeclaredProvenanceDecoy:
    name = "undeclared-provenance"
    probe = SPECIMEN

    def describe(self) -> str:
        return "removes the provenance record, declared facts become unknowns"

    def substitute(self, bundle: Department) -> Department:
        return replace(bundle, provenance=None)


DECOYS = (_VacuousCalibrationDecoy(), _UndeclaredProvenanceDecoy())


# ---------------------------------------------------------------------------
# Surrogates: bundles from a generator with no calibration knowledge
# ---------------------------------------------------------------------------


def random_bundle(seed: int) -> Department:
    """A structurally plausible department assembled with zero calibration
    effort: every content choice is drawn from a seeded congruential stream.

    The generator knows the *shapes*, including that admission demands one
    reference claim declared in each direction, so its bundles pass the
    structural door on purpose: the null class worth beating is "validates,
    with random content", since every sham in this department's sights
    validates too. What it does not know is which contents would make the
    substantive checks pass: claim content, detector direction, lesion
    behavior and decoy behavior are all random draws. Whatever fraction of
    audit checks such bundles pass is the luck floor the specimen's pass
    count is measured against.
    """
    state = (seed * 1103515245 + 12345) % (2**31)

    def draw() -> float:
        nonlocal state
        state = (state * 1103515245 + 12345) % (2**31)
        return state / 2**31

    target_value = draw() * 4.0
    rival_values = (draw() * 4.0, draw() * 4.0)
    threshold = draw() * 4.0
    claim_direction = draw() < 0.5
    detector_direction = draw() < 0.5
    lesion_inert = draw() < 0.5
    decoy_identity = draw() < 0.5

    @dataclass(frozen=True)
    class _RandomDecoy:
        name: str = "random-decoy"

        def describe(self) -> str:
            return "random draw: identity or increment"

        def substitute(self, probe: Any) -> list:
            values = list(probe)
            return values if decoy_identity else [x + 1 for x in values]

    @dataclass(frozen=True)
    class _RandomLesion:
        name: str
        magnitude: float
        probe: Any = (0.0,)

        def describe(self) -> str:
            return "random draw: plants or does not"

        def apply(self, payload: Any) -> Any:
            return payload if lesion_inert else (*payload, self.magnitude)

    def random_claim(p: dict) -> bool:
        return (p["value"] < threshold) if claim_direction else (p["value"] > threshold)

    battery = Battery(
        name=f"random-bundle-{seed}",
        target=_ToySubject("random-target", target_value),
        rivals=(
            _ToySubject("random-rival-a", rival_values[0]),
            _ToySubject("random-rival-b", rival_values[1]),
        ),
        decoys=(_RandomDecoy(),),
        surrogates=(_ToySurrogate(),),
        lesions=(_RandomLesion("r-large", 1.0), _RandomLesion("r-small", 0.01)),
    )
    return Department(
        name=f"random-bundle-{seed}",
        summary="a bundle assembled with no calibration effort",
        battery=battery,
        door="docs/doors/referee.md",
        reference_claims=(
            ReferenceClaim("random-a", lambda p: True, distinguishes=False),
            ReferenceClaim("random-b", random_claim, distinguishes=True),
        ),
        detectors=(
            NamedDetector(
                "random-scan",
                (lambda p: any(x > 0 for x in p))
                if detector_direction
                else (lambda p: all(x > 0 for x in p)),
                probe=(0.0,),
            ),
        ),
        scope="(random) whatever a pass here would mean was never considered",
    )


@dataclass(frozen=True)
class _RandomBundleSurrogate:
    name: str
    seed: int

    def describe(self) -> str:
        return f"an unguided bundle under seed {self.seed}: shapes without calibration"

    def sample(self) -> Department:
        return random_bundle(self.seed)


SURROGATE_SEEDS: tuple[int, ...] = (3, 17, 41)
SURROGATES = tuple(
    _RandomBundleSurrogate(name=f"unguided-bundle-{seed}", seed=seed)
    for seed in SURROGATE_SEEDS
)


# ---------------------------------------------------------------------------
# Lesions: sham mutations planted in the specimen, magnitudes measured
# ---------------------------------------------------------------------------

_TOTAL_CHECKS = len(audit_department(SPECIMEN).checks)
_SPECIMEN_PASS_COUNT = integrity_pass_count(SPECIMEN)


class _BundleLesion:
    """One sham mutation as a lesion on department bundles.

    ``magnitude`` is the fraction of audit checks the mutation flips on the
    specimen, measured at import, a lesion whose measured magnitude were
    zero would be planting nothing, and the conformance suite would refuse
    it via the plant check.
    """

    probe = SPECIMEN

    def __init__(self, name: str, mutate: Any, blurb: str) -> None:
        self.name = name
        self._mutate = mutate
        self._blurb = blurb
        self.magnitude = round(
            (_SPECIMEN_PASS_COUNT - integrity_pass_count(mutate(SPECIMEN))) / _TOTAL_CHECKS,
            4,
        )

    def describe(self) -> str:
        return f"{self._blurb} (measured: flips {self.magnitude:.0%} of audit checks)"

    def apply(self, bundle: Department) -> Department:
        return self._mutate(bundle)


LESIONS = (
    _BundleLesion(
        "plant-constant-true-detector",
        lambda dep: shams.with_constant_detector(dep, value=True),
        "swap every detector for an always-on alarm",
    ),
    _BundleLesion(
        "plant-target-as-rival",
        shams.with_target_as_rival,
        "replace the rivals with the target under their names",
    ),
    _BundleLesion(
        "plant-inert-lesions",
        shams.with_inert_lesions,
        "make every lesion an identity",
    ),
    _BundleLesion(
        "plant-leaked-label",
        shams.with_leaked_label,
        "give rival payloads a key the target's lack (the 431cc74 leak shape)",
    ),
)


def integrity_flags(bundle: Department) -> bool:
    """The department's detector: fires when the audit grade is not CALIBRATED."""
    return audit_department(bundle).grade != CALIBRATED


DETECTORS = (
    NamedDetector(
        name="integrity-audit",
        fires=integrity_flags,
        probe=SPECIMEN,
        note=(
            "the audit itself as a predicate: quiet on the calibrated specimen, "
            "fires on every planted corruption, the recursion, measured and closed"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery, and the department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="referee",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "the lesion principle applied one level up: batteries are the subjects, "
        "sham modes are the planted violations, and the audit's power is what "
        "gets measured. The held-out rival predates the audit by design."
    ),
)

REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="validates_structurally",
        claim=claim_validates_structurally,
        distinguishes=False,
        note=(
            "true of the specimen and of every sham rival, the 431cc74 "
            "reconstruction included, structural completeness is not "
            "verification, stated as a measurement rather than a maxim"
        ),
    ),
    ReferenceClaim(
        name="audits_calibrated",
        claim=claim_audits_calibrated,
        distinguishes=True,
        note=(
            "the full integrity audit at grade CALIBRATED: fires for the specimen, "
            "for no sham, within the declared blind spots only"
        ),
    ),
)

DEPARTMENT = Department(
    name=DEPARTMENT_NAME,
    summary=(
        "the verification machinery as a subject: batteries audited, sham "
        "batteries killed, and the audit's own power measured against planted "
        "corruptions"
    ),
    battery=BATTERY,
    door="docs/doors/referee.md",
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "a surviving claim distinguishes a calibrated battery from the named sham "
        "classes in SHAM_MODES; it does not certify that a battery measures what "
        "its department believes, value-encoded label leaks and co-designed "
        "calibration are declared blind spots, countered only by independent "
        "authorship, which no mechanical check verifies"
    ),
    provenance=Provenance(
        authored_by=(
            "the laboratory's own process; the audit, the shams and the specimen "
            "share an author"
        ),
        authored_on="2026-08-09",
        independent_of_subject_author=False,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        notes=(
            "the one held-out element is the 431cc74 sham, reconstructed from a "
            "commit message written 2026-08-07, before this audit existed; "
            "everything else is self-authored and says so"
        ),
    ),
    modules=("harness.integrity", "harness.shams", "harness.provenance"),
)

register_department(DEPARTMENT, replace=True)
