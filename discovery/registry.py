"""discovery.registry — the plug-in seam.

This module is **domain-agnostic on purpose**, in the same strict sense as
:mod:`discovery.schema`: it imports nothing from the laboratory package, names
no quantity the laboratory computes, and would work unchanged for a chemistry
lab or a compiler-optimisation search. It defines *what a lead source is*, not
what any particular lead source knows.

Three plug-in roles, and no more
--------------------------------
* :class:`Generator` — emits :class:`~discovery.schema.Candidate` objects from
  whatever the domain can compute. It is the only role allowed to invent a
  claim. It is *not* allowed to decide one: a generator that hands back an
  already-decided candidate is refused by the funnel, because a lead source
  that grades its own leads has no measurable hit rate.
* :class:`Screen` — looks at one candidate and either passes it on or kills it
  with an earned terminal verdict. Every screen declares its ``cost``
  (``"cheap"`` or ``"expensive"``) so the funnel can order them, and the
  ``checks`` it performs, so the funnel can refuse to call anything a survivor
  of a check that never ran.
* :class:`KnownnessDetector` — the already-known gate. It runs before any
  screen, because "this is in the literature" is the single most likely true
  answer and the cheapest one to obtain.

A :class:`Domain` bundles the three. :func:`register_domain` puts it in a
process-wide table under a name; :func:`get_domain` fetches it. That table is
the entire coupling between this package and its subject matter.

Typing style
------------
The roles are :class:`typing.Protocol` classes, so a domain may implement them
with plain objects and owes no import to this module. Convenience base classes
(:class:`BaseGenerator`, :class:`BaseScreen`, :class:`BaseKnownnessDetector`)
are supplied for the common case. :func:`validate_domain` checks structurally
and reports every violation at once, because a domain with three problems
should not need three runs to find them.
"""

from __future__ import annotations

import threading
from abc import ABC, abstractmethod
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import Any, Final, Literal, Protocol, runtime_checkable

from discovery.schema import (
    REQUIRED_SURVIVAL_CHECKS,
    TERMINAL_STATUSES,
    Candidate,
    Verdict,
    verdict_reasons,
)

__all__ = [
    "SCREEN_COSTS",
    "KNOWN_CHECK",
    "ScreenCost",
    "RegistryError",
    "DomainError",
    "ScreenResult",
    "Generator",
    "Screen",
    "KnownnessDetector",
    "BaseGenerator",
    "BaseScreen",
    "BaseKnownnessDetector",
    "Domain",
    "domain_reasons",
    "validate_domain",
    "register_domain",
    "get_domain",
    "list_domains",
    "unregister_domain",
    "clear_registry",
]

#: A screen is either cheap enough to run on everything, or it is not. Two
#: values, deliberately: a cost *scale* would be re-derived by every reader as
#: a ranking, and the funnel only ever needs the ordering.
SCREEN_COSTS: Final[tuple[str, ...]] = ("cheap", "expensive")

ScreenCost = Literal["cheap", "expensive"]

#: The check name the already-known gate contributes to ``checks_run``. The
#: other two required checks (see ``REQUIRED_SURVIVAL_CHECKS``) must be
#: declared by screens.
KNOWN_CHECK: Final[str] = "known"


class RegistryError(Exception):
    """Base class for every error raised by this module."""


class DomainError(RegistryError):
    """A domain, or one of its plug-ins, does not honour the interface."""


# ---------------------------------------------------------------------------
# What a screen hands back
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class ScreenResult:
    """One screen's opinion of one candidate.

    The shape enforces the asymmetry that makes the funnel honest: *passing*
    costs nothing to say and asserts nothing, while *stopping* a candidate
    requires a terminal verdict that already earns its own status under
    :func:`~discovery.schema.verdict_reasons`. There is no third option — a
    screen may not "flag" a candidate, because a flag is an opinion with no
    decision procedure behind it.

    ``effort`` is what a verification screen spent, on the same scale as
    :meth:`~discovery.schema.Precision.effort_digits`. It is optional, but a
    candidate can only be promoted to ``survives`` if some screen reports an
    effort strictly above the effort the candidate was generated at — the
    schema requires verification to have cost more than generation, and this
    field is the only way the funnel can know that it did.
    """

    screen: str
    passed: bool
    verdict: Verdict | None = None
    detail: str = ""
    effort: float | None = None

    def reasons(self) -> tuple[str, ...]:
        """Every way this result is malformed. Empty tuple means it is usable."""
        bad: list[str] = []
        if not isinstance(self.screen, str) or not self.screen.strip():
            bad.append("screen must be named")
        if not isinstance(self.passed, bool):
            bad.append("passed must be a bool")
        if self.passed:
            if self.verdict is not None:
                bad.append(
                    "a passing screen carries no verdict: it has decided nothing"
                )
        else:
            if not isinstance(self.verdict, Verdict):
                bad.append("a screen that stops a candidate must supply a verdict")
            else:
                if self.verdict.status not in TERMINAL_STATUSES:
                    bad.append(
                        f"a screen may only stop a candidate with a terminal "
                        f"verdict, got {self.verdict.status.value!r}"
                    )
                bad.extend(
                    f"verdict: {reason}" for reason in verdict_reasons(self.verdict)
                )
        if self.effort is not None:
            if isinstance(self.effort, bool) or not isinstance(
                self.effort, (int, float)
            ):
                bad.append("effort must be a number of effort digits")
            elif not self.effort > 0 or self.effort != self.effort:  # NaN-safe
                bad.append("effort must be positive")
            elif self.effort == float("inf"):
                bad.append("effort must be finite: an infinite effort cannot be logged")
        return tuple(bad)

    def validate(self) -> None:
        """Raise :class:`DomainError` unless the result is usable."""
        reasons = self.reasons()
        if reasons:
            raise DomainError(
                f"screen {self.screen!r} returned a malformed result: "
                + "; ".join(reasons)
            )


# ---------------------------------------------------------------------------
# The three roles
# ---------------------------------------------------------------------------


@runtime_checkable
class Generator(Protocol):
    """A lead source: it turns computed objects into candidate observations.

    ``version`` is not decoration. Conversion rates are per generator, and two
    behaviours logged under one name are two populations averaged together —
    bump the version whenever what the generator emits changes.
    """

    name: str
    version: str

    def describe(self) -> str:
        """One paragraph: what it looks at, and what it will emit."""
        ...

    def generate(self, context: Mapping[str, Any]) -> Iterable[Candidate]:
        """Yield candidates. Emitting nothing is a legitimate, logged outcome."""
        ...


@runtime_checkable
class Screen(Protocol):
    """A killer: it removes candidates, or admits that it could not."""

    name: str
    #: ``"cheap"`` screens run on everything; ``"expensive"`` ones run only on
    #: what the cheap ones could not kill.
    cost: ScreenCost
    #: Which of ``REQUIRED_SURVIVAL_CHECKS`` this screen actually performs.
    checks: tuple[str, ...]

    def describe(self) -> str:
        """One paragraph: what it would reject, and what it cannot see."""
        ...

    def apply(self, candidate: Candidate) -> ScreenResult:
        """Pass the candidate on, or stop it with an earned terminal verdict."""
        ...


@runtime_checkable
class KnownnessDetector(Protocol):
    """The already-known gate: the cheapest and likeliest way to be right."""

    name: str
    version: str

    def describe(self) -> str:
        """One paragraph: what catalogue is consulted, and how a match is made."""
        ...

    def check(self, candidate: Candidate) -> Verdict | None:
        """A terminal verdict if the observation is already established, else ``None``."""
        ...


# ---------------------------------------------------------------------------
# Convenience bases (a domain may ignore these entirely)
# ---------------------------------------------------------------------------


class BaseGenerator(ABC):
    """Convenience base for :class:`Generator`. Subclasses set name/version."""

    name: str = ""
    version: str = "0"

    def describe(self) -> str:
        return (self.__doc__ or "").strip()

    @abstractmethod
    def generate(self, context: Mapping[str, Any]) -> Iterable[Candidate]:
        raise NotImplementedError


class BaseScreen(ABC):
    """Convenience base for :class:`Screen`. Subclasses set name/cost/checks."""

    name: str = ""
    cost: ScreenCost = "cheap"
    checks: tuple[str, ...] = ()

    def describe(self) -> str:
        return (self.__doc__ or "").strip()

    @abstractmethod
    def apply(self, candidate: Candidate) -> ScreenResult:
        raise NotImplementedError


class BaseKnownnessDetector(ABC):
    """Convenience base for :class:`KnownnessDetector`."""

    name: str = ""
    version: str = "0"

    def describe(self) -> str:
        return (self.__doc__ or "").strip()

    @abstractmethod
    def check(self, candidate: Candidate) -> Verdict | None:
        raise NotImplementedError


# ---------------------------------------------------------------------------
# The domain bundle
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Domain:
    """Everything the funnel needs to know about a subject, and nothing more.

    The funnel never asks a domain what it is studying. It asks for lead
    sources, killers and a catalogue, runs them in a fixed order and counts
    what happens. That is the whole contract.
    """

    name: str
    version: str
    generators: tuple[Generator, ...] = ()
    screens: tuple[Screen, ...] = ()
    detectors: tuple[KnownnessDetector, ...] = ()
    description: str = ""

    def __post_init__(self) -> None:
        for attr in ("generators", "screens", "detectors"):
            value = getattr(self, attr)
            if isinstance(value, (str, bytes)) or not isinstance(
                value, (Sequence, Iterable)
            ):
                raise DomainError(f"{attr} must be a sequence")
            object.__setattr__(self, attr, tuple(value))

    # -- queries ----------------------------------------------------------
    def screens_by_cost(self, cost: str) -> tuple[Screen, ...]:
        """The screens declaring this cost, in registration order."""
        if cost not in SCREEN_COSTS:
            raise DomainError(f"cost must be one of {SCREEN_COSTS}, got {cost!r}")
        return tuple(s for s in self.screens if getattr(s, "cost", None) == cost)

    def cheap_screens(self) -> tuple[Screen, ...]:
        return self.screens_by_cost("cheap")

    def expensive_screens(self) -> tuple[Screen, ...]:
        return self.screens_by_cost("expensive")

    def generator(self, name: str) -> Generator:
        for gen in self.generators:
            if getattr(gen, "name", None) == name:
                return gen
        raise DomainError(f"domain {self.name!r} has no generator {name!r}")

    def checks_available(self) -> frozenset[str]:
        """Which of ``REQUIRED_SURVIVAL_CHECKS`` this domain can actually run.

        A domain missing one of them cannot produce a survivor, by design, and
        the funnel will say so in the record rather than promoting anyway.
        """
        available: set[str] = set()
        if self.detectors:
            available.add(KNOWN_CHECK)
        for screen in self.screens:
            available.update(str(c) for c in getattr(screen, "checks", ()) or ())
        return frozenset(available)

    def missing_checks(self) -> tuple[str, ...]:
        """The required checks no plug-in in this domain performs."""
        return tuple(
            c for c in REQUIRED_SURVIVAL_CHECKS if c not in self.checks_available()
        )

    def describe(self) -> str:
        """A human-readable inventory of the plug-ins."""
        lines = [f"domain {self.name} v{self.version}"]
        if self.description:
            lines.append(f"  {self.description}")
        lines.append(f"  generators ({len(self.generators)}):")
        for gen in self.generators:
            lines.append(f"    - {gen.name} v{getattr(gen, 'version', '?')}")
        lines.append(f"  screens ({len(self.screens)}):")
        for screen in self.screens:
            checks = ",".join(getattr(screen, "checks", ()) or ()) or "-"
            lines.append(
                f"    - {screen.name} [{getattr(screen, 'cost', '?')}] checks={checks}"
            )
        lines.append(f"  detectors ({len(self.detectors)}):")
        for det in self.detectors:
            lines.append(f"    - {det.name} v{getattr(det, 'version', '?')}")
        missing = self.missing_checks()
        if missing:
            lines.append(
                "  cannot produce a survivor: no plug-in performs "
                + ", ".join(missing)
            )
        return "\n".join(lines)


def _role_reasons(obj: Any, role: str, methods: Sequence[str], attrs: Sequence[str]) -> list[str]:
    bad: list[str] = []
    for attr in attrs:
        value = getattr(obj, attr, None)
        if not isinstance(value, str) or not value.strip():
            bad.append(f"{role} {obj!r}: {attr} must be a non-empty string")
    for method in methods:
        if not callable(getattr(obj, method, None)):
            bad.append(f"{role} {getattr(obj, 'name', obj)!r}: {method}() is missing")
    return bad


def domain_reasons(domain: Domain) -> tuple[str, ...]:
    """Every way ``domain`` violates the plug-in interface, in one pass."""
    bad: list[str] = []
    if not isinstance(domain, Domain):
        return (f"not a Domain: {type(domain).__name__}",)
    if not domain.name.strip():
        bad.append("domain name must be non-empty")
    if not domain.version.strip():
        bad.append("domain version must be non-empty")
    if not domain.generators:
        bad.append("a domain with no generator can produce nothing")
    for gen in domain.generators:
        bad.extend(_role_reasons(gen, "generator", ("describe", "generate"), ("name", "version")))
    for screen in domain.screens:
        bad.extend(_role_reasons(screen, "screen", ("describe", "apply"), ("name",)))
        cost = getattr(screen, "cost", None)
        if cost not in SCREEN_COSTS:
            bad.append(
                f"screen {getattr(screen, 'name', screen)!r}: cost must be one of "
                f"{SCREEN_COSTS}, got {cost!r}"
            )
        checks = getattr(screen, "checks", ())
        if isinstance(checks, (str, bytes)) or not isinstance(checks, Sequence):
            bad.append(
                f"screen {getattr(screen, 'name', screen)!r}: checks must be a "
                "sequence of check names"
            )
        else:
            for check in checks:
                if check not in REQUIRED_SURVIVAL_CHECKS:
                    bad.append(
                        f"screen {getattr(screen, 'name', screen)!r}: unknown check "
                        f"{check!r}; must be one of {list(REQUIRED_SURVIVAL_CHECKS)}"
                    )
    for det in domain.detectors:
        bad.extend(_role_reasons(det, "detector", ("describe", "check"), ("name", "version")))
    for role, items in (
        ("generator", domain.generators),
        ("screen", domain.screens),
        ("detector", domain.detectors),
    ):
        names = [getattr(i, "name", None) for i in items]
        duplicates = sorted({n for n in names if names.count(n) > 1 and n is not None})
        if duplicates:
            bad.append(
                f"{role} names must be unique (conversion rates are per name): "
                f"{duplicates}"
            )
    return tuple(bad)


def validate_domain(domain: Domain) -> None:
    """Raise :class:`DomainError` listing every interface violation, or return."""
    reasons = domain_reasons(domain)
    if reasons:
        raise DomainError("malformed domain: " + "; ".join(reasons))


# ---------------------------------------------------------------------------
# The process-wide table
# ---------------------------------------------------------------------------

_REGISTRY: dict[str, Domain] = {}
_LOCK = threading.RLock()


def register_domain(domain: Domain, *, replace: bool = False) -> Domain:
    """Put ``domain`` in the table under its own name.

    Refuses to overwrite silently: two domains registered under one name would
    mix two populations into one set of conversion rates.
    """
    validate_domain(domain)
    with _LOCK:
        if domain.name in _REGISTRY and not replace:
            raise DomainError(
                f"domain {domain.name!r} is already registered; "
                "pass replace=True if that is deliberate"
            )
        _REGISTRY[domain.name] = domain
    return domain


def get_domain(name: str) -> Domain:
    """Fetch a registered domain, naming the alternatives if it is absent."""
    with _LOCK:
        try:
            return _REGISTRY[name]
        except KeyError:
            raise DomainError(
                f"no domain {name!r} is registered; known: {sorted(_REGISTRY)}"
            ) from None


def list_domains() -> tuple[str, ...]:
    """The registered domain names, sorted."""
    with _LOCK:
        return tuple(sorted(_REGISTRY))


def unregister_domain(name: str) -> None:
    """Remove one domain; a no-op if it was never registered."""
    with _LOCK:
        _REGISTRY.pop(name, None)


def clear_registry() -> None:
    """Empty the table. Exists for tests; nothing else should need it."""
    with _LOCK:
        _REGISTRY.clear()
