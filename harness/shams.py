"""``harness.shams`` — planted corruptions of batteries, for measuring the audit.

The lesion principle, applied one level up. A lesion plants a known violation
in a subject so a detector's power can be measured instead of assumed; this
module plants known corruptions in *departments* so the integrity audit's
power can be measured instead of assumed. Every mutator below reproduces a
sham mode from :data:`harness.integrity.SHAM_MODES`, and the tests assert
that each catchable mode is actually caught — the audit's power measurement,
in exactly the sense ``run_detector`` measures a department's.

Every mutator takes a :class:`~harness.protocol.Department` and returns a
new one with the corruption planted and everything else untouched. The
corrupted bundle remains *structurally* admissible wherever the sham mode
permits — that is the point: these are the batteries that validate and are
hollow, the class the structural audit cannot see.

Like :mod:`harness.protocol`, this module is domain-agnostic and sits under
the same three seam checks.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any

from harness.protocol import Department, NamedDetector, ReferenceClaim, Subject

__all__ = [
    "with_constant_detector",
    "with_target_as_rival",
    "with_inert_lesions",
    "without_hardest_lesion",
    "with_leaked_label",
    "with_vacuous_calibration",
]


# ---------------------------------------------------------------------------
# Wrappers — the corrupted instruments themselves
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _AliasSubject:
    """The target under another name: the rival that can refute nothing."""

    inner: Subject
    name: str

    def describe(self) -> str:
        return f"(planted) {self.inner.name} wearing the name {self.name!r}"

    def payload(self) -> Any:
        return self.inner.payload()


@dataclass(frozen=True)
class _LeakySubject:
    """A subject whose payload gains a field the target's payload lacks.

    The exact shape of the 431cc74 leak: rivals carried ``virtual_a_p`` and
    the target did not, so a claim could read the difference as a label.
    Requires mapping payloads; refuses anything else rather than pretending.
    """

    inner: Subject
    key: str

    @property
    def name(self) -> str:
        return self.inner.name

    def describe(self) -> str:
        return f"(planted) {self.inner.describe()} — payload leaks key {self.key!r}"

    def payload(self) -> Any:
        payload = self.inner.payload()
        if not hasattr(payload, "keys"):
            raise TypeError(
                "with_leaked_label requires mapping payloads; this subject's are not"
            )
        leaked = dict(payload)
        leaked[self.key] = True
        return leaked


@dataclass(frozen=True)
class _InertLesion:
    """A lesion that plants nothing: every detector shown it looks blind."""

    inner: Any

    @property
    def name(self) -> str:
        return self.inner.name

    @property
    def magnitude(self) -> float:
        return self.inner.magnitude

    @property
    def probe(self) -> Any:
        return getattr(self.inner, "probe", ())

    def describe(self) -> str:
        return f"(planted) {self.inner.name}, made inert: apply() returns its input"

    def apply(self, payload: Any) -> Any:
        return payload


def _constant(value: bool):
    def fires(payload: Any) -> bool:
        return value

    fires.__name__ = f"constant_{value}"
    return fires


# ---------------------------------------------------------------------------
# The mutators
# ---------------------------------------------------------------------------


def with_constant_detector(department: Department, *, value: bool = True) -> Department:
    """Replace every declared detector with one that always answers ``value``.

    ``True`` is the constant the old power measurement could not see: it
    notices every lesion and fires on the clean probe too, so its alarms
    carry no information. ``False`` is the mirror: measured blindness to
    everything.
    """
    probe = department.detectors[0].probe if department.detectors else None
    detector = NamedDetector(
        name=f"constant-{str(value).lower()}",
        fires=_constant(value),
        probe=probe,
        note=f"(planted) answers {value} for every payload",
    )
    return replace(department, detectors=(detector,))


def with_target_as_rival(department: Department) -> Department:
    """Replace every rival with the target wearing the rivals' names.

    Structurally valid — the names differ, so the duplicate check passes —
    and epistemically dead: nothing can ever distinguish the target from
    itself, so the battery's strictness is an artifact and its distinguishing
    reference claim stops distinguishing.
    """
    battery = department.battery
    rivals = tuple(
        _AliasSubject(inner=battery.target, name=rival.name) for rival in battery.rivals
    )
    return replace(department, battery=replace(battery, rivals=rivals))


def with_inert_lesions(department: Department) -> Department:
    """Make every lesion an identity: violations that were never planted."""
    battery = department.battery
    lesions = tuple(_InertLesion(inner=lesion) for lesion in battery.lesions)
    return replace(department, battery=replace(battery, lesions=lesions))


def without_hardest_lesion(department: Department) -> Department:
    """Silently drop the smallest-magnitude lesion — the one the detectors
    struggle with — leaving an easier battery under the same name. This is
    the mode :data:`~harness.integrity.SHAM_MODES` records as mechanically
    uncatchable: no audit of the remaining battery can know what was meant
    to be there."""
    battery = department.battery
    if not battery.lesions:
        return department
    hardest = min(battery.lesions, key=lambda lesion: float(lesion.magnitude))
    lesions = tuple(lesion for lesion in battery.lesions if lesion is not hardest)
    return replace(department, battery=replace(battery, lesions=lesions))


def with_leaked_label(department: Department, *, key: str = "virtual_tell") -> Department:
    """Give every rival's payload a key the target's payload lacks — the
    431cc74 leak, reconstructed exactly."""
    battery = department.battery
    rivals = tuple(_LeakySubject(inner=rival, key=key) for rival in battery.rivals)
    return replace(department, battery=replace(battery, rivals=rivals))


def with_vacuous_calibration(department: Department) -> Department:
    """Replace the reference claims with a shape-valid pair that cannot earn
    its labels: both directions declared, neither verdict re-derivable."""
    claims = (
        ReferenceClaim(
            name="vacuous-pass",
            claim=lambda payload: True,
            distinguishes=True,
            note="(planted) declared to distinguish; fires for everything, so it cannot",
        ),
        ReferenceClaim(
            name="vacuous-kill",
            claim=lambda payload: False,
            distinguishes=False,
            note="(planted) declared killed-by-rivals; never fires for the target at all",
        ),
    )
    return replace(department, reference_claims=claims)
