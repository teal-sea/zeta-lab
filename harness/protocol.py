"""``harness.protocol`` — four instrument roles, one battery, one department.

This module is **domain-agnostic on purpose**, in the same strict sense as
:mod:`ontology.schema` and :mod:`ontology.registry`: it imports nothing from
any laboratory package, names no quantity any laboratory computes, and would
work unchanged for a chemistry lab or a compiler-optimisation search. It
defines *what it takes to refute a claim*, not what any particular claim says.

Why four roles, and no more
---------------------------
A claim about some subject can fail to be about that subject in exactly four
ways that a machine can check without knowing whether the claim is true. Each
role below is one of them, and each was abstracted from an instrument this
repository already ran by hand before the abstraction existed.

* :class:`Subject` — a thing a claim can be evaluated against. The genuine
  article is one; so is every rival.
* :class:`Rival` is not a separate protocol but a *role*: a
  :class:`Subject` that shares whatever structure the claim leans on and yet
  lacks the property the claim purports to explain. **If the claim holds for a
  rival, it explains nothing** — whatever it is detecting is not the thing that
  distinguishes the target. This is the sharpest of the four, because it needs
  no threshold and no statistics: it is a modus tollens.
* :class:`Decoy` — a substitution that replaces the substantive input with
  something structurally similar and substantively empty. If a measurement
  barely moves when the input is swapped for a decoy, the measurement was
  never reading the input. (Ablation.)
* :class:`Surrogate` — a generator that reproduces the observation from no
  substantive input at all. If a null model matches the observed statistic,
  the observation is a property of the model class, not a discovery. (Null
  control.)
* :class:`Lesion` — a planted, known violation. Applied to the subject, it
  gives a detector something it *must* notice. A detector that misses a
  planted violation cannot be credited with having found nothing; its silence
  measures its blindness, not the world. (Detector power.)

The asymmetry this exists to fix: a plausible structural "explanation" costs
minutes to generate and, traditionally, days to referee. The four instruments
make refereeing cost minutes too, and none of the four requires knowing
whether the claim is true. They adjudicate the weaker, decidable question:
*is this demonstration about its subject at all?*

The admission rule
------------------
A :class:`Department` must declare a :class:`Battery`, and
:func:`validate_battery` refuses one that cannot fail: no rivals means no
modus tollens, no decoy *and* no surrogate means no way to show emptiness, no
lesion means the department's detectors have unmeasured power. Work that
cannot supply these is not a department. It is a probe, and probes are kept
where nobody will mistake one for a result.

Typing style
------------
The roles are :class:`typing.Protocol` classes, so a department may implement
them with plain objects and owes no import to this module. The ``*_reasons``
functions report **every** violation at once, because a battery with three
problems should not need three runs to find them — the same convention
:func:`ontology.registry.domain_reasons` follows.
"""

from __future__ import annotations

import threading
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Final, Protocol, runtime_checkable

__all__ = [
    "HarnessError",
    "BatteryError",
    "DepartmentError",
    "Subject",
    "Decoy",
    "Surrogate",
    "Lesion",
    "Battery",
    "BatteryVerdict",
    "AblationVerdict",
    "NullVerdict",
    "PowerVerdict",
    "ClaimOutcome",
    "Department",
    "ReferenceClaim",
    "battery_reasons",
    "validate_battery",
    "department_reasons",
    "validate_department",
    "register_department",
    "get_department",
    "list_departments",
    "unregister_department",
    "clear_departments",
    "run_battery",
    "run_ablation",
    "run_nulls",
    "run_power",
]


class HarnessError(Exception):
    """Base class for every refusal this module issues."""


class BatteryError(HarnessError):
    """A battery is malformed, or is one that could not fail."""


class DepartmentError(HarnessError):
    """A department is malformed, or its name is already taken."""


# ---------------------------------------------------------------------------
# The four instrument roles
# ---------------------------------------------------------------------------


@runtime_checkable
class Subject(Protocol):
    """Something a claim can be evaluated against.

    Both the genuine article and every rival are subjects; the difference is
    the role each plays in a :class:`Battery`, not the interface. ``payload``
    returns whatever the department's claim functions expect to receive — a
    mapping of callables, an array, a model object. This module never looks
    inside it.
    """

    name: str

    def describe(self) -> str:
        """One line: what this subject is, and what it does or does not have."""
        ...

    def payload(self) -> Any:
        """The object handed to a claim function."""
        ...


@runtime_checkable
class Decoy(Protocol):
    """A substitution that keeps the shape and removes the substance.

    ``substitute`` receives a payload and returns one of the same shape whose
    substantive content has been replaced. The point of a decoy is that a
    measurement which does not move under it was not reading the substance.
    """

    name: str

    def describe(self) -> str:
        """One line: what is replaced, and what is deliberately preserved."""
        ...

    def substitute(self, payload: Any) -> Any:
        """Return a payload of the same shape with the substance swapped out."""
        ...


@runtime_checkable
class Surrogate(Protocol):
    """A generator of observations that carry no substantive input.

    If the statistic under audit is reproduced by a surrogate, it is a
    property of the model class rather than a discovery about the subject.
    """

    name: str

    def describe(self) -> str:
        """One line: what the null model is, and what it deliberately omits."""
        ...

    def sample(self) -> Any:
        """Draw one observation from the null model."""
        ...


@runtime_checkable
class Lesion(Protocol):
    """A planted, known violation, used to measure a detector's power.

    ``magnitude`` records how large the planted violation is, in whatever
    units the department uses, so that a detector's sensitivity can be
    reported as a threshold rather than as a yes or no.
    """

    name: str
    magnitude: float

    def describe(self) -> str:
        """One line: what is broken, and by how much."""
        ...

    def apply(self, payload: Any) -> Any:
        """Return the payload with the violation planted in it."""
        ...


#: A claim is any predicate over a payload. It returns truthy when the claimed
#: structure is present. It is never asked whether the claim is *true* — only
#: whether it fires.
ClaimOutcome = Callable[[Any], Any]


# ---------------------------------------------------------------------------
# The battery
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Battery:
    """The instruments entitled to kill a department's claims.

    ``target`` is the genuine article; ``rivals`` share its claimed structure
    and lack the property at issue. ``decoys``, ``surrogates`` and ``lesions``
    supply ablation, null control and power calibration respectively.

    A battery is not valid unless it could fail — see :func:`battery_reasons`.
    """

    name: str
    target: Subject
    rivals: tuple[Subject, ...] = ()
    decoys: tuple[Decoy, ...] = ()
    surrogates: tuple[Surrogate, ...] = ()
    lesions: tuple[Lesion, ...] = ()
    notes: str = ""

    def describe(self) -> str:
        lines = [f"battery {self.name!r} against target {self.target.name!r}"]
        for role, members in (
            ("rival", self.rivals),
            ("decoy", self.decoys),
            ("surrogate", self.surrogates),
            ("lesion", self.lesions),
        ):
            for member in members:
                lines.append(f"  {role}: {member.name} — {member.describe()}")
        if self.notes:
            lines.append(f"  notes: {self.notes}")
        return "\n".join(lines)


@dataclass(frozen=True)
class BatteryVerdict:
    """Outcome of running one claim against the target and every rival.

    ``distinguishes`` is the only field a reader should act on: it is true
    exactly when the claim fires for the target and for none of the rivals.
    A claim that fires for even one rival is shared with something that lacks
    the property, so it cannot be the load-bearing step of any argument that
    the property follows from the structure.
    """

    claim: str
    target: bool
    rivals: Mapping[str, bool]
    shared_with: tuple[str, ...]
    errors: Mapping[str, str] = field(default_factory=dict)

    @property
    def distinguishes(self) -> bool:
        return bool(self.target) and not self.shared_with and not self.errors

    def summary(self) -> str:
        if self.errors:
            return f"{self.claim}: inconclusive — {len(self.errors)} subject(s) raised"
        if not self.target:
            return f"{self.claim}: does not fire for the target"
        if self.shared_with:
            return f"{self.claim}: shared with {', '.join(self.shared_with)} — distinguishes nothing"
        return f"{self.claim}: distinguishes the target from {len(self.rivals)} rival(s)"


@dataclass(frozen=True)
class AblationVerdict:
    """Outcome of swapping the substantive input for each decoy."""

    measure: str
    baseline: float
    decoys: Mapping[str, float]
    tolerance: float

    @property
    def survives(self) -> bool:
        """True when *every* decoy moves the measurement past ``tolerance``."""
        return bool(self.decoys) and all(
            abs(value - self.baseline) > self.tolerance for value in self.decoys.values()
        )

    @property
    def unmoved_by(self) -> tuple[str, ...]:
        return tuple(
            sorted(
                name
                for name, value in self.decoys.items()
                if abs(value - self.baseline) <= self.tolerance
            )
        )


@dataclass(frozen=True)
class NullVerdict:
    """Outcome of comparing an observed statistic against the null models."""

    statistic: str
    observed: float
    surrogates: Mapping[str, float]
    tolerance: float

    @property
    def survives(self) -> bool:
        """True when no surrogate reproduces the observation within tolerance."""
        return bool(self.surrogates) and all(
            abs(value - self.observed) > self.tolerance for value in self.surrogates.values()
        )

    @property
    def reproduced_by(self) -> tuple[str, ...]:
        return tuple(
            sorted(
                name
                for name, value in self.surrogates.items()
                if abs(value - self.observed) <= self.tolerance
            )
        )


@dataclass(frozen=True)
class PowerVerdict:
    """Outcome of showing a detector a set of planted violations.

    A detector that misses a lesion has not been shown to be wrong; it has
    been shown to be blind at that magnitude, which is what ``blind_to``
    records. Silence from a blind detector is not evidence of anything.
    """

    detector: str
    fired: Mapping[str, bool]
    magnitudes: Mapping[str, float]

    @property
    def blind_to(self) -> tuple[str, ...]:
        return tuple(sorted(name for name, hit in self.fired.items() if not hit))

    @property
    def has_power(self) -> bool:
        return bool(self.fired) and not self.blind_to

    @property
    def smallest_detected(self) -> float | None:
        hits = [self.magnitudes[name] for name, hit in self.fired.items() if hit]
        return min(hits) if hits else None


# ---------------------------------------------------------------------------
# Validation — every violation reported at once
# ---------------------------------------------------------------------------

_SUBJECT_METHODS: Final = ("describe", "payload")
_DECOY_METHODS: Final = ("describe", "substitute")
_SURROGATE_METHODS: Final = ("describe", "sample")
_LESION_METHODS: Final = ("describe", "apply")


def _role_reasons(obj: Any, role: str, methods: Sequence[str], attrs: Sequence[str]) -> list[str]:
    reasons: list[str] = []
    label = getattr(obj, "name", None) or repr(obj)
    for attr in attrs:
        value = getattr(obj, attr, None)
        if value is None:
            reasons.append(f"{role} {label!r} has no {attr}")
        elif attr == "name" and not str(value).strip():
            reasons.append(f"{role} {label!r} has an empty name")
    for method in methods:
        if not callable(getattr(obj, method, None)):
            reasons.append(f"{role} {label!r} has no callable {method}()")
    return reasons


def battery_reasons(battery: Battery) -> tuple[str, ...]:
    """Every reason ``battery`` is not usable, in one pass.

    The three structural requirements are the admission rule in code: a
    battery with no rival has no refutation available to it, one with neither
    decoy nor surrogate cannot show an observation to be empty, and one with
    no lesion leaves its detectors' power unmeasured.
    """
    reasons: list[str] = []
    if not str(battery.name).strip():
        reasons.append("battery has an empty name")

    if battery.target is None:
        reasons.append("battery has no target")
    else:
        reasons.extend(_role_reasons(battery.target, "target", _SUBJECT_METHODS, ("name",)))

    for rival in battery.rivals:
        reasons.extend(_role_reasons(rival, "rival", _SUBJECT_METHODS, ("name",)))
    for decoy in battery.decoys:
        reasons.extend(_role_reasons(decoy, "decoy", _DECOY_METHODS, ("name",)))
    for surrogate in battery.surrogates:
        reasons.extend(_role_reasons(surrogate, "surrogate", _SURROGATE_METHODS, ("name",)))
    for lesion in battery.lesions:
        reasons.extend(_role_reasons(lesion, "lesion", _LESION_METHODS, ("name", "magnitude")))

    if not battery.rivals:
        reasons.append(
            "battery declares no rival: with nothing that shares the structure and "
            "lacks the property, no claim can ever be refuted by it"
        )
    if not battery.decoys and not battery.surrogates:
        reasons.append(
            "battery declares neither decoy nor surrogate: it cannot show an "
            "observation to be empty of substantive content"
        )
    if not battery.lesions:
        reasons.append(
            "battery declares no lesion: the power of its detectors would be "
            "assumed rather than measured, and silence from an untested "
            "detector is not a negative result"
        )

    names = [battery.target.name] if battery.target is not None else []
    names += [m.name for m in (*battery.rivals, *battery.decoys, *battery.surrogates, *battery.lesions)]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    for name in duplicates:
        reasons.append(f"battery has more than one member named {name!r}")

    if battery.target is not None and any(r.name == battery.target.name for r in battery.rivals):
        reasons.append("the target is also listed as a rival")

    return tuple(reasons)


def validate_battery(battery: Battery) -> None:
    """Raise :class:`BatteryError` listing every problem, or return quietly."""
    reasons = battery_reasons(battery)
    if reasons:
        raise BatteryError(f"battery {battery.name!r} is not usable:\n  - " + "\n  - ".join(reasons))


# ---------------------------------------------------------------------------
# The department
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ReferenceClaim:
    """A claim whose verdict is already known, kept as a calibration.

    A battery that returns the same answer for everything is useless in a way
    that is invisible from any single run: one that never distinguishes looks
    exactly like a strict referee, and one that always distinguishes looks
    exactly like a subject full of real structure. Two reference claims — one
    the battery must kill, one it must pass — pin the instrument in both
    directions, and the conformance test re-derives them rather than trusting
    the label.
    """

    name: str
    claim: ClaimOutcome
    distinguishes: bool
    note: str = ""


@dataclass(frozen=True)
class Department:
    """A body of work with a subject, a referee, and a way in.

    * ``domain`` is the *name* of a lead-generating domain, not an imported
      object. Storing the key rather than the module keeps this package
      testable without the department's dependencies, and keeps the two
      plug-in systems independent: a department may register a battery and no
      domain, or a domain and no battery, and the conformance test will say
      exactly which is missing.
    * ``door`` is the repository-relative path of the one document a newcomer
      to this department should read first. A department without a door is
      work only its author can enter.
    * ``modules`` names the code the department owns, so that a reader can
      get from the door to the source without grepping.
    """

    name: str
    summary: str
    battery: Battery
    door: str
    domain: str = ""
    modules: tuple[str, ...] = ()
    reference_claims: tuple[ReferenceClaim, ...] = ()

    def describe(self) -> str:
        lines = [f"department {self.name!r}: {self.summary}", f"  door: {self.door}"]
        if self.domain:
            lines.append(f"  domain: {self.domain}")
        if self.modules:
            lines.append(f"  modules: {', '.join(self.modules)}")
        lines.append(self.battery.describe())
        return "\n".join(lines)


def department_reasons(department: Department) -> tuple[str, ...]:
    """Every reason ``department`` is not admissible, in one pass."""
    reasons: list[str] = []
    if not str(department.name).strip():
        reasons.append("department has an empty name")
    if not str(department.summary).strip():
        reasons.append("department has an empty summary")
    if not str(department.door).strip():
        reasons.append("department declares no door: a reader has no way in")
    elif not str(department.door).endswith(".md"):
        reasons.append(f"department door {department.door!r} is not a document")
    if department.battery is None:
        reasons.append("department declares no battery — that makes it a probe, not a department")
    else:
        reasons.extend(f"battery: {reason}" for reason in battery_reasons(department.battery))

    for reference in department.reference_claims:
        if not str(reference.name).strip():
            reasons.append("a reference claim has an empty name")
        if not callable(reference.claim):
            reasons.append(f"reference claim {reference.name!r} is not callable")
    expected = {bool(r.distinguishes) for r in department.reference_claims}
    if True not in expected:
        reasons.append(
            "department declares no reference claim its battery is expected to pass: "
            "a battery that has never been shown to say yes cannot be told apart "
            "from one that says no to everything"
        )
    if False not in expected:
        reasons.append(
            "department declares no reference claim its battery is expected to kill: "
            "a battery that has never been shown to say no has not been shown to work"
        )
    return tuple(reasons)


def validate_department(department: Department) -> None:
    """Raise :class:`DepartmentError` listing every problem, or return quietly."""
    reasons = department_reasons(department)
    if reasons:
        raise DepartmentError(
            f"department {department.name!r} is not admissible:\n  - " + "\n  - ".join(reasons)
        )


# ---------------------------------------------------------------------------
# The registry — the entire coupling between this package and its subjects
# ---------------------------------------------------------------------------

_LOCK = threading.Lock()
_DEPARTMENTS: dict[str, Department] = {}


def register_department(department: Department, *, replace: bool = False) -> Department:
    """Validate and record ``department`` under its name."""
    validate_department(department)
    with _LOCK:
        if not replace and department.name in _DEPARTMENTS:
            raise DepartmentError(f"a department named {department.name!r} is already registered")
        _DEPARTMENTS[department.name] = department
    return department


def get_department(name: str) -> Department:
    with _LOCK:
        try:
            return _DEPARTMENTS[name]
        except KeyError:
            known = ", ".join(sorted(_DEPARTMENTS)) or "(none)"
            raise DepartmentError(f"no department named {name!r}; registered: {known}") from None


def list_departments() -> tuple[str, ...]:
    with _LOCK:
        return tuple(sorted(_DEPARTMENTS))


def unregister_department(name: str) -> None:
    with _LOCK:
        _DEPARTMENTS.pop(name, None)


def clear_departments() -> None:
    with _LOCK:
        _DEPARTMENTS.clear()


# ---------------------------------------------------------------------------
# Running the instruments
# ---------------------------------------------------------------------------


def run_battery(battery: Battery, claim: ClaimOutcome, *, name: str = "") -> BatteryVerdict:
    """Evaluate ``claim`` against the target and every rival.

    A subject that raises is recorded in ``errors`` rather than silently
    counted as a pass or a fail: an instrument that crashed measured nothing,
    and a verdict that quietly treated a crash as a refutation would be the
    most flattering possible bug.
    """
    validate_battery(battery)
    label = name or getattr(claim, "__name__", None) or repr(claim)
    errors: dict[str, str] = {}

    def _fire(subject: Subject) -> bool:
        try:
            return bool(claim(subject.payload()))
        except Exception as exc:  # noqa: BLE001 - recorded, never swallowed
            errors[subject.name] = f"{type(exc).__name__}: {exc}"
            return False

    target = _fire(battery.target)
    rivals = {rival.name: _fire(rival) for rival in battery.rivals}
    shared = tuple(sorted(n for n, fired in rivals.items() if fired))
    return BatteryVerdict(
        claim=label, target=target, rivals=rivals, shared_with=shared, errors=errors
    )


def run_ablation(
    battery: Battery,
    measure: Callable[[Any], float],
    *,
    tolerance: float,
    payload: Any = None,
    name: str = "",
) -> AblationVerdict:
    """Measure on the target, then on the target with each decoy substituted.

    ``payload`` defaults to the target's, but may be given explicitly: the four
    instruments legitimately consume different objects — a rival is handed the
    whole subject interface, while an ablation usually acts on the one input
    whose substance is in question. Forcing a single payload type across all
    four would make the protocol tidier and the departments dishonest.
    """
    validate_battery(battery)
    label = name or getattr(measure, "__name__", None) or repr(measure)
    if payload is None:
        payload = battery.target.payload()
    baseline = float(measure(payload))
    decoys = {decoy.name: float(measure(decoy.substitute(payload))) for decoy in battery.decoys}
    return AblationVerdict(
        measure=label, baseline=baseline, decoys=decoys, tolerance=float(tolerance)
    )


def run_nulls(
    battery: Battery,
    statistic: Callable[[Any], float],
    *,
    tolerance: float,
    observed: float | None = None,
    name: str = "",
) -> NullVerdict:
    """Compare the observed statistic against one draw from each surrogate."""
    validate_battery(battery)
    label = name or getattr(statistic, "__name__", None) or repr(statistic)
    value = float(statistic(battery.target.payload())) if observed is None else float(observed)
    surrogates = {s.name: float(statistic(s.sample())) for s in battery.surrogates}
    return NullVerdict(
        statistic=label, observed=value, surrogates=surrogates, tolerance=float(tolerance)
    )


def run_power(
    battery: Battery,
    detector: Callable[[Any], Any],
    *,
    payload: Any = None,
    name: str = "",
) -> PowerVerdict:
    """Show ``detector`` every planted violation and record what it noticed.

    ``payload`` defaults to the target's; see :func:`run_ablation` for why it
    may be overridden.
    """
    validate_battery(battery)
    label = name or getattr(detector, "__name__", None) or repr(detector)
    if payload is None:
        payload = battery.target.payload()
    fired = {lesion.name: bool(detector(lesion.apply(payload))) for lesion in battery.lesions}
    magnitudes = {lesion.name: float(lesion.magnitude) for lesion in battery.lesions}
    return PowerVerdict(detector=label, fired=fired, magnitudes=magnitudes)
