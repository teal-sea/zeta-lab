"""The intervention ledger, the second laboratory's primary instrument.

This laboratory studies a mathematical object.  It also, increasingly, studies
the research system attempting to study it.  This module records the second kind
of evidence: **what a human had to do that the system could not.**

The quantity of interest is not autonomy.  It is *legitimate research output per
unit of scarce human judgment*.  So the ledger records interventions with their
missing capability attached, and it deliberately makes some things hard:

* **There is no autonomy score.**  ``Ledger`` has no ``__bool__``, no
  ``progress``, no single number.  Following ``dossier/status.py``, any of those
  would let a caller write ``if ledger.improving:`` and lose the distinction the
  ledger exists for.  :meth:`Ledger.render` prints every category instead.
* **A ratio must name its numerator.**  :meth:`Ledger.ratio` refuses to divide
  until the caller says *which* externally checkable output class it means.
  "Research output" is not a number; kernel-checked theorems and accepted
  upstream contributions are.
* **Claiming automation costs evidence.**  ``AUTOMATED`` requires a named
  artifact, a test, a commit, a script.  Without one the entry is refused,
  because "we automated that" is the cheapest thing in the world to assert.
* **A flattering ledger is reported as suspicious.**  A log with no
  owner-authority interventions, or one where nothing was caught by a human, is
  more likely to be under-recording than to be a triumph.  :meth:`Ledger.render`
  says so.

Domain-agnostic on purpose, and pinned by ``tests/test_meta_ledger.py`` the same
way ``ontology/schema.py`` and ``dossier/status.py`` are: this module names no
quantity the laboratory computes.  A ledger of interventions in a chemistry
laboratory should need no changes here.

Reading the data is the point, so the file format is dull: one JSON object per
line in ``meta/interventions.jsonl``.
"""

from __future__ import annotations

import json
import os
from collections import Counter
from dataclasses import dataclass, field
from enum import Enum
from typing import Iterable

LEDGER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "interventions.jsonl")


class Category(str, Enum):
    """What kind of scarcity the intervention consumed.

    The four are not a spectrum.  ``AUTOMATABLE`` and ``ASSISTABLE`` are
    engineering debt; ``DOMAIN_JUDGMENT`` and ``OWNER_AUTHORITY`` are the
    denominator that matters, and an honest ledger is mostly the latter two
    early on.
    """

    AUTOMATABLE = "automatable"
    ASSISTABLE = "assistable"
    DOMAIN_JUDGMENT = "domain-judgment"
    OWNER_AUTHORITY = "owner-authority"


class Automatability(str, Enum):
    """How far the *automation* of this intervention has actually got."""

    NO = "no"                    # inherent to the role, not a gap
    SPECULATIVE = "speculative"  # someone thinks it could be
    DESIGNED = "designed"        # a specific mechanism is written down
    AUTOMATED = "automated"      # shipped, with a named artifact


class CaughtBy(str, Enum):
    """Who or what noticed.

    This field exists so the ledger also feeds the verification-asymmetry
    question: ``TEST`` and ``ORACLE`` are architecture working, ``HUMAN`` and
    ``OUTSIDER`` are architecture failing to.
    """

    HUMAN = "human"          # the operator noticed
    TEST = "test"            # a standing check in this tree fired
    ORACLE = "oracle"        # an independent implementation disagreed
    OUTSIDER = "outsider"    # someone or something outside the project
    NOBODY = "nobody"        # found later; nothing was watching


@dataclass(frozen=True)
class Intervention:
    """One human intervention that materially changed the research process."""

    session: str
    date: str
    what_required_intervention: str
    why_the_system_stopped: str
    missing_capability: str
    category: Category
    automatability: Automatability
    caught_by: CaughtBy
    #: Named artifact proving the automation exists. Required for AUTOMATED.
    automation_evidence: str = ""
    #: What would demonstrate success. Required unless automatability is NO.
    evidence_that_would_demonstrate: str = ""
    notes: str = ""

    def reasons_invalid(self) -> list[str]:
        """Why this entry may not be admitted. Empty means admissible."""
        bad: list[str] = []
        if not self.what_required_intervention.strip():
            bad.append("no intervention described")
        if not self.why_the_system_stopped.strip():
            bad.append("no reason the system stopped")
        if self.automatability is Automatability.AUTOMATED and not self.automation_evidence.strip():
            bad.append(
                "automatability=AUTOMATED without a named artifact, the one claim "
                "in this schema that is free to assert and therefore must be paid for"
            )
        if self.automatability is not Automatability.NO:
            if not self.missing_capability.strip():
                bad.append(
                    "a capability gap is claimed automatable but not named; you "
                    "cannot automate a gap you cannot state"
                )
            if not self.evidence_that_would_demonstrate.strip():
                bad.append("no evidence named that would demonstrate the automation")
        return bad


@dataclass(frozen=True)
class MetaObservation:
    """Evidence about the research *system*, produced by ordinary research work.

    Every sufficiently interesting run yields two classes of evidence.  The
    mathematical class lives in ``docs/``, ``hunts/`` and the tests.  This is the
    other one, and failures are the valuable half.
    """

    session: str
    date: str
    observation: str
    #: The mathematical work that produced it, meta-evidence with no research
    #: attached is an opinion.
    arose_from: str
    supports: str = ""
    undercuts: str = ""

    def reasons_invalid(self) -> list[str]:
        bad: list[str] = []
        if not self.observation.strip():
            bad.append("empty observation")
        if not self.arose_from.strip():
            bad.append(
                "no research work named, a meta-observation that arose from no "
                "actual work is an opinion, not evidence"
            )
        if not (self.supports.strip() or self.undercuts.strip()):
            bad.append("observation neither supports nor undercuts anything stated")
        return bad


class OperatorFunction(str, Enum):
    """The functions a decomposition of the operator's role turned up.

    See ``meta/operator-functions.md``.  ``AUTHORITY`` is here so it can be
    recorded as permanently open rather than quietly dropped.
    """

    SEVERITY = "severity-calibration"
    SCOPE = "scope-discipline"
    SKEPTICISM = "skepticism-routing"
    PRIORITISATION = "prioritisation"
    AUTHORITY = "authority"


class Resolution(str, Enum):
    SYSTEM_RIGHT = "system-right"
    OPERATOR_RIGHT = "operator-right"
    BOTH_WRONG = "both-wrong"
    UNRESOLVED = "unresolved"


class Party(str, Enum):
    SYSTEM = "system"
    OPERATOR = "operator"
    OUTSIDER = "outsider"
    OUTCOME = "outcome"  # reality settled it and nobody had to adjudicate


@dataclass(frozen=True)
class Judgment:
    """One case where the system's assessment differed from the operator's.

    "Automate the operator" is unfalsifiable.  *Assessments*, though, can be
    scored: record the two positions and what turned out to be true, and
    convergence becomes measurable instead of a matter of impression.

    Three guards keep this from becoming a progress report:

    * **The system may not resolve a disagreement it is party to.** The system
      always holds one of the two positions here, so ``resolved_by=SYSTEM`` is
      refused outright.  This is the co-designed-verification failure applied to
      calibration, and without the guard the record is worthless.
    * **``UNRESOLVED`` cannot be scored.**  An open disagreement is not a draw.
    * **A resolution costs evidence** unless it is ``UNRESOLVED``.
    """

    session: str
    date: str
    assessed: str
    system_assessment: str
    operator_assessment: str
    function: OperatorFunction
    resolution: Resolution
    resolved_by: Party
    evidence: str = ""
    notes: str = ""

    def reasons_invalid(self) -> list[str]:
        bad: list[str] = []
        if not self.assessed.strip():
            bad.append("nothing named as being assessed")
        if not self.system_assessment.strip():
            bad.append("no system assessment recorded")
        if not self.operator_assessment.strip():
            bad.append("no operator assessment recorded")
        if self.resolved_by is Party.SYSTEM:
            bad.append(
                "resolved_by=SYSTEM: the system holds one of the two positions, so "
                "it may not adjudicate its own disagreement"
            )
        if self.resolution is not Resolution.UNRESOLVED and not self.evidence.strip():
            bad.append("a resolution other than UNRESOLVED costs named evidence")
        return bad

    def scorable(self) -> bool:
        return self.resolution is not Resolution.UNRESOLVED


@dataclass
class Ledger:
    """A cohort of interventions and observations.

    Deliberately absent: ``__bool__``, ``autonomy``, ``score``, any ordering
    between categories.  If you want one, the thing you actually want is to name
    which category you mean.
    """

    interventions: list[Intervention] = field(default_factory=list)
    observations: list[MetaObservation] = field(default_factory=list)
    judgments: list[Judgment] = field(default_factory=list)

    def calibration_by_function(self) -> dict[str, dict[str, int]]:
        """Agreement per function. Deliberately not averaged across functions.

        Averaging severity calibration against scope discipline would hide the
        one thing the measurement exists to show, which is *which* function has
        transferred.
        """
        out: dict[str, dict[str, int]] = {}
        for j in self.judgments:
            row = out.setdefault(j.function.value, {r.value: 0 for r in Resolution})
            row[j.resolution.value] += 1
        return out

    def __bool__(self) -> bool:  # pragma: no cover - the raise is the point
        raise TypeError(
            "Ledger has no truth value: 'is the lab autonomous yet' is not one "
            "question. Ask for a category count, or ratio(output_class=...)."
        )

    def by_category(self) -> dict[str, int]:
        return dict(Counter(i.category.value for i in self.interventions))

    def by_caught_by(self) -> dict[str, int]:
        return dict(Counter(i.caught_by.value for i in self.interventions))

    def by_automatability(self) -> dict[str, int]:
        return dict(Counter(i.automatability.value for i in self.interventions))

    def scarce_judgment_count(self) -> int:
        """The denominator: interventions that consumed judgment or authority."""
        return sum(
            1
            for i in self.interventions
            if i.category in (Category.DOMAIN_JUDGMENT, Category.OWNER_AUTHORITY)
        )

    def ratio(self, output_class: str, count: int) -> str:
        """Output per unit of scarce human judgment, for **one named** class.

        The caller must say what it is counting.  There is no ``ratio()`` without
        an ``output_class`` because "research output" is not a measurable
        quantity and pretending otherwise is how this ledger would start
        flattering itself.
        """
        if not output_class.strip():
            raise ValueError("name the output class; 'research output' is not a number")
        if count < 0:
            raise ValueError("negative output count")
        d = self.scarce_judgment_count()
        if d == 0:
            return f"{output_class}: {count} / 0 scarce-judgment interventions (undefined)"
        return f"{output_class}: {count} per {d} scarce-judgment interventions = {count / d:.3f}"

    def suspicions(self) -> list[str]:
        """Reasons to distrust this ledger as a self-report.

        The standing principle is that the laboratory should examine its own
        operation without becoming self-validating.  These are the shapes a
        self-validating ledger takes.
        """
        out: list[str] = []
        if not self.interventions:
            return ["empty ledger: absence of recorded interventions is not autonomy"]
        cats = self.by_category()
        caught = self.by_caught_by()
        if not cats.get(Category.OWNER_AUTHORITY.value):
            out.append(
                "no owner-authority interventions recorded, in a one-operator lab "
                "that is more likely under-recording than independence"
            )
        if not caught.get(CaughtBy.HUMAN.value) and not caught.get(CaughtBy.OUTSIDER.value):
            out.append(
                "nothing was caught by a human or an outsider, either the "
                "architecture is better than every prior measurement suggests, or "
                "the ledger only records what the architecture already catches"
            )
        auto = self.by_automatability()
        if auto.get(Automatability.AUTOMATED.value, 0) > self.scarce_judgment_count():
            out.append(
                "more interventions marked AUTOMATED than consumed scarce judgment, "
                "check that automation claims are not being recorded more eagerly "
                "than the judgment calls they were supposed to replace"
            )
        if len(self.observations) == 0:
            out.append(
                "no meta-observations recorded: ordinary research work is supposed to "
                "produce the second class of evidence, so zero suggests it is not "
                "being looked for"
            )
        if not self.judgments:
            out.append(
                "no judgment disagreements recorded: either the system's assessments "
                "match the operator's on everything, which no prior cohort supports, "
                "or the disagreements are not being written down"
            )
        else:
            scored = [j for j in self.judgments if j.scorable()]
            wins = sum(1 for j in scored if j.resolution is Resolution.SYSTEM_RIGHT)
            losses = sum(1 for j in scored if j.resolution is Resolution.OPERATOR_RIGHT)
            if wins > losses and len(scored) < 10:
                out.append(
                    f"the system is ahead on calibration ({wins}-{losses}) on only "
                    f"{len(scored)} scored cases, too few to read as transfer, and "
                    "exactly the shape a self-serving record takes early"
                )
        return out

    def reasons_invalid(self) -> list[str]:
        bad = []
        for n, i in enumerate(self.interventions):
            bad += [f"intervention[{n}]: {r}" for r in i.reasons_invalid()]
        for n, o in enumerate(self.observations):
            bad += [f"observation[{n}]: {r}" for r in o.reasons_invalid()]
        for n, j in enumerate(self.judgments):
            bad += [f"judgment[{n}]: {r}" for r in j.reasons_invalid()]
        return bad

    def render(self) -> str:
        """Every category, no aggregate."""
        lines = [
            f"interventions: {len(self.interventions)}   "
            f"meta-observations: {len(self.observations)}",
            "",
            "by category (the last two are the denominator that matters):",
        ]
        for c in Category:
            lines.append(f"  {c.value:<16} {self.by_category().get(c.value, 0)}")
        lines += ["", "by what noticed (test/oracle = architecture; human/outsider = not):"]
        for c in CaughtBy:
            lines.append(f"  {c.value:<16} {self.by_caught_by().get(c.value, 0)}")
        lines += ["", "by automation status:"]
        for a in Automatability:
            lines.append(f"  {a.value:<16} {self.by_automatability().get(a.value, 0)}")
        lines += ["", f"scarce-judgment interventions: {self.scarce_judgment_count()}"]
        cal = self.calibration_by_function()
        lines += ["", "calibration, per function (no aggregate on purpose):"]
        if not cal:
            lines.append("  (no disagreements recorded)")
        for fn, row in sorted(cal.items()):
            counts = ", ".join(f"{k}={v}" for k, v in row.items() if v)
            lines.append(f"  {fn:<22} {counts}")
        s = self.suspicions()
        lines += ["", "suspicions about this ledger as a self-report:"]
        lines += [f"  - {x}" for x in s] if s else ["  (none flagged, which is itself worth checking)"]
        return "\n".join(lines)


def _entry(d: dict):
    kind = d.pop("kind", "intervention")
    if kind == "observation":
        return MetaObservation(**d)
    if kind == "judgment":
        d["function"] = OperatorFunction(d["function"])
        d["resolution"] = Resolution(d["resolution"])
        d["resolved_by"] = Party(d["resolved_by"])
        return Judgment(**d)
    d["category"] = Category(d["category"])
    d["automatability"] = Automatability(d["automatability"])
    d["caught_by"] = CaughtBy(d["caught_by"])
    return Intervention(**d)


def load(path: str = LEDGER_PATH) -> Ledger:
    """Read the ledger. Blank lines and ``#`` comments are skipped."""
    led = Ledger()
    if not os.path.exists(path):
        return led
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            e = _entry(json.loads(line))
            if isinstance(e, MetaObservation):
                led.observations.append(e)
            elif isinstance(e, Judgment):
                led.judgments.append(e)
            else:
                led.interventions.append(e)
    return led


def validate(led: Ledger) -> None:
    """Raise if any entry is inadmissible."""
    bad = led.reasons_invalid()
    if bad:
        raise ValueError("ledger has inadmissible entries:\n  " + "\n  ".join(bad))


def iter_sessions(led: Ledger) -> Iterable[str]:
    seen: list[str] = []
    for i in led.interventions:
        if i.session not in seen:
            seen.append(i.session)
    return seen


if __name__ == "__main__":  # pragma: no cover
    led = load()
    validate(led)
    print(led.render())
