"""ontology.historical_cases — the falsification test for the ontology itself.

A classification system that cannot correctly bin things whose outcomes are
**already settled** is not ready to classify anything new. Before a funnel is
pointed at an unexamined question, it must reproduce history: given the
evidence that was actually available when a famous claim was made, it must
reach the disposition that the following century turned out to justify.

This module is the harness, and it is **domain-agnostic** in exactly the sense
:mod:`ontology.schema`, :mod:`ontology.funnel`, :mod:`ontology.metrics` and
:mod:`ontology.registry` are. It knows what a settled historical case *is*, how
to replay one through a pipeline, and how to decide whether the pipeline got it
right. It knows nothing whatsoever about the subject being studied. A laboratory
supplies its own cases from its ``domains/`` package; a chemistry laboratory
would supply polywater and cold fusion where a mathematics laboratory supplies
its own famous corrections.

Why the harness owns the rules, and not the case author
-------------------------------------------------------
Anyone writing a case wants it to pass. So the case author does **not** get the
final word on what counts as a correct answer: :data:`IMPOSSIBLE_DISPOSITIONS`
maps each historical outcome to the dispositions the pipeline may never assign
to it, and :func:`case_reasons` refuses a case whose declared expectations
overlap that set. A case saying "this statement is false, and I expect the
funnel to record it as a survivor" cannot be registered. That is the one rule a
validation suite must not be able to relax in order to go green.

The two modes, and why both are needed
--------------------------------------
Each case is replayed twice.

``full``
    The whole pipeline, catalogue included. This is what the laboratory would
    actually do today.
``uncatalogued``
    The identical pipeline with the catalogue replaced by one that contains
    nothing (:class:`NullKnownnessDetector`). This is what the laboratory would
    have done *before* the fact was established — the position the original
    author was in. It is the more searching of the two, because it measures how
    much of the correct answer was carried by the catalogue rather than by
    anything the system computed.

    The gate is emptied rather than deleted, and the difference is the whole
    experiment. Deleting it would make ``survives`` structurally unreachable —
    the schema will not promote an observation whose knownness check never ran —
    so every case would come back ``inconclusive`` and the run would prove
    nothing. With a gate that runs and finds nothing, promotion is available,
    and a case that still fails to reach it was stopped by something that
    actually looked at the mathematics. A suite using this mode must therefore
    include a positive control showing that ``survives`` is reachable in it; an
    unreachable outcome is not evidence when it does not occur.

The difference between the two modes is the measurement
:func:`gate_dependence` reports: a case that is only classified correctly
because a human had already written the answer into the catalogue tells you the
funnel's screens are not doing the work, and a laboratory that has not measured
that is guessing about its own instrument.

What a failure here means
-------------------------
Every case carries ``if_it_fails``, a sentence stating what a wrong answer would
imply about the pipeline. That field is mandatory: a validation case that does
not say what its own failure would mean is decoration, not a test.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from enum import StrEnum
from pathlib import Path
from typing import Any, Final

from ontology.funnel import DISPOSITIONS, FunnelRun, run_funnel
from ontology.ledger import Ledger
from ontology.registry import Domain, DomainError
from ontology.schema import Candidate, VerdictStatus

__all__ = [
    "HISTORY_VERSION",
    "MODES",
    "HistoryError",
    "HistoricalOutcome",
    "IMPOSSIBLE_DISPOSITIONS",
    "KILLING_DISPOSITIONS",
    "HistoricalCase",
    "case_reasons",
    "validate_case",
    "register_case",
    "get_case",
    "list_cases",
    "unregister_case",
    "clear_cases",
    "CaseGenerator",
    "NullKnownnessDetector",
    "case_domain",
    "CaseReplay",
    "replay",
    "CaseResult",
    "check_case",
    "run_case",
    "run_history",
    "gate_dependence",
    "render_text",
]

#: Bump when the adjudication rules change: a suite that changed its own
#: standard between two runs has compared two different measurements.
HISTORY_VERSION: Final[str] = "1.0"

#: The two replays. ``full`` is the pipeline as it stands; ``uncatalogued`` is
#: the same pipeline with the already-known gate taken out, which is the
#: position whoever first made the claim was actually in.
MODES: Final[tuple[str, ...]] = ("full", "uncatalogued")


class HistoryError(Exception):
    """A case, or a replay of one, does not honour this module's contract."""


# ---------------------------------------------------------------------------
# What history said
# ---------------------------------------------------------------------------


class HistoricalOutcome(StrEnum):
    """What later work established about a claim. Five states, no shading.

    The vocabulary deliberately separates *true* from *proved*: a system that
    cannot tell "believed on strong evidence and still open" from "settled" will
    quietly promote the first into the second, which is the single most common
    way a numerical laboratory misleads its own operator.
    """

    #: Later proved. The claim is a theorem.
    TRUE_AND_PROVEN = "true_and_proven"
    #: Believed true on strong evidence, and still not proved. Not the same
    #: thing as the state above, and the distinction is the point.
    TRUE_BUT_UNPROVEN = "true_but_unproven"
    #: Later disproved — however much finite evidence supported it.
    FALSE = "false"
    #: Known to be equivalent to a question nobody has settled. Neither
    #: supported nor refuted by any finite computation, ever.
    EQUIVALENT_TO_AN_OPEN_PROBLEM = "equivalent_to_an_open_problem"
    #: Never true: an artefact of limited precision or a small search, which a
    #: better computation dissolves. The negative control.
    SPURIOUS = "spurious"


#: Dispositions a pipeline may **never** assign, given what history settled.
#: This is the harness's own standard, and a case may not widen it: see
#: :func:`case_reasons`. Every entry is a statement about accounting, not about
#: mathematics — "refuted" means *this system produced a counterexample*, and a
#: system that produces a counterexample to a theorem has found a bug in itself.
IMPOSSIBLE_DISPOSITIONS: Final[Mapping[HistoricalOutcome, frozenset[str]]] = {
    # A theorem cannot be refuted by a computation; if it is, the computation
    # is wrong. It also must not be promoted as an unsettled lead.
    HistoricalOutcome.TRUE_AND_PROVEN: frozenset({"refuted", "survives"}),
    # True, so nothing may refute it; unproved, so nothing may treat it as
    # settled either — but it is legitimately a lead if no catalogue holds it.
    HistoricalOutcome.TRUE_BUT_UNPROVEN: frozenset({"refuted"}),
    # The case that matters most. Finite evidence supported this for a century,
    # and a funnel that would have endorsed it endorses anything.
    HistoricalOutcome.FALSE: frozenset({"survives"}),
    # Equivalent to an open question: no finite computation is evidence either
    # way, so neither a promotion nor a refutation can be honest.
    HistoricalOutcome.EQUIVALENT_TO_AN_OPEN_PROBLEM: frozenset(
        {"survives", "refuted"}
    ),
    # The negative control must die. If it lives, every screen is decorative.
    HistoricalOutcome.SPURIOUS: frozenset({"survives"}),
}

#: Dispositions that mean *something stopped this*, as opposed to *nothing
#: could decide it*. ``inconclusive`` is deliberately absent: it is an honest
#: answer, but it is not a kill, and counting it as one is how a suite of
#: screens that never fire comes to look effective.
KILLING_DISPOSITIONS: Final[frozenset[str]] = frozenset(
    {"known", "trivial", "refuted", "invalid"}
)


# ---------------------------------------------------------------------------
# A case
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class HistoricalCase:
    """One settled claim, the evidence behind it, and the answer history gave.

    ``build`` returns the candidate as the pipeline will see it: constructed
    from the laboratory's own computed objects, at the precision and over the
    range that were actually available. It is called inside the replay so that
    its cost is charged to generation, exactly as a real lead source is.
    """

    #: Short identifier. Conversion rates and report rows are keyed on it.
    key: str
    #: One line, in the form a reader would recognise.
    title: str
    #: Year the claim was first stated.
    proposed: int
    #: What later work established.
    outcome: HistoricalOutcome
    #: How the observation is put in front of the pipeline.
    build: Callable[[], Candidate]
    #: Dispositions that are correct answers with the whole pipeline running.
    expect_full: frozenset[str]
    #: Dispositions that are correct answers with the already-known gate gone.
    expect_uncatalogued: frozenset[str]
    #: What a wrong answer here would mean. Mandatory.
    if_it_fails: str
    #: Year it was settled, when it was.
    settled: int | None = None
    #: Who settled it, and how.
    settled_by: str = ""
    #: With the gate removed, must some screen actually stop this? True only
    #: for cases a working set of screens should kill on the arithmetic alone.
    expect_screens_kill: bool = False
    #: Substrings that must appear among the references the verdict cites.
    must_cite: tuple[str, ...] = ()
    #: Substrings that must appear nowhere in the record's own text. This is
    #: how "known, but not proved" is asserted while the schema has no field
    #: for it: the record may not contain the word.
    must_not_say: tuple[str, ...] = ()
    #: Free commentary for the report.
    note: str = ""

    def expected(self, mode: str) -> frozenset[str]:
        if mode == "full":
            return self.expect_full
        if mode == "uncatalogued":
            return self.expect_uncatalogued
        raise HistoryError(f"mode must be one of {MODES}, got {mode!r}")


def case_reasons(case: HistoricalCase) -> tuple[str, ...]:
    """Every way ``case`` fails this module's standard. Empty means usable.

    The load-bearing check is the last one: a case may not declare that it
    expects a disposition history has already ruled out. Without it, a red
    validation suite could always be made green by editing the expectation, and
    a suite that can be edited into agreement measures nothing.
    """
    bad: list[str] = []
    if not isinstance(case, HistoricalCase):
        return (f"not a HistoricalCase: {type(case).__name__}",)
    if not isinstance(case.key, str) or not case.key.strip():
        bad.append("key must be non-empty")
    elif not case.key.replace("-", "_").isidentifier():
        bad.append(f"key must be an identifier-like slug, got {case.key!r}")
    for name in ("title", "if_it_fails"):
        text = getattr(case, name)
        if not isinstance(text, str) or not text.strip():
            bad.append(f"{name} must be written out")
    if not isinstance(case.proposed, int) or isinstance(case.proposed, bool):
        bad.append("proposed must be a year")
    if case.settled is not None:
        if not isinstance(case.settled, int) or isinstance(case.settled, bool):
            bad.append("settled must be a year or None")
        elif isinstance(case.proposed, int) and case.settled < case.proposed:
            bad.append("settled precedes proposed")
        elif not case.settled_by.strip():
            bad.append("a settled case must say who settled it")
    if not callable(case.build):
        bad.append("build must be callable")
    try:
        outcome = HistoricalOutcome(case.outcome)
    except ValueError:
        return tuple(bad + [f"outcome must be one of {[o.value for o in HistoricalOutcome]}"])
    if outcome is HistoricalOutcome.TRUE_AND_PROVEN and case.settled is None:
        bad.append("a proved claim must record when, and by whom, it was proved")
    for name in ("expect_full", "expect_uncatalogued"):
        wanted = getattr(case, name)
        if not isinstance(wanted, (frozenset, set)) or not wanted:
            bad.append(f"{name} must be a non-empty set of dispositions")
            continue
        unknown = sorted(set(map(str, wanted)) - set(DISPOSITIONS))
        if unknown:
            bad.append(f"{name} names dispositions outside the vocabulary: {unknown}")
        forbidden = sorted(set(map(str, wanted)) & IMPOSSIBLE_DISPOSITIONS[outcome])
        if forbidden:
            bad.append(
                f"{name} expects {forbidden}, which history rules out for an "
                f"outcome of {outcome.value!r}: a case may not lower the bar it "
                "is being measured against"
            )
    if case.expect_screens_kill and not (
        set(map(str, case.expect_uncatalogued)) <= KILLING_DISPOSITIONS
    ):
        bad.append(
            "expect_screens_kill=True but expect_uncatalogued admits a "
            "disposition that is not a kill"
        )
    for name in ("must_cite", "must_not_say"):
        group = getattr(case, name)
        if not isinstance(group, tuple) or any(
            not isinstance(s, str) or not s.strip() for s in group
        ):
            bad.append(f"{name} must be a tuple of non-empty strings")
    return tuple(bad)


def validate_case(case: HistoricalCase) -> None:
    """Raise :class:`HistoryError` listing every violation, or return."""
    reasons = case_reasons(case)
    if reasons:
        raise HistoryError(f"malformed case {getattr(case, 'key', case)!r}: " + "; ".join(reasons))


# ---------------------------------------------------------------------------
# The table of cases
# ---------------------------------------------------------------------------

_CASES: dict[str, HistoricalCase] = {}


def register_case(case: HistoricalCase, *, replace: bool = False) -> HistoricalCase:
    """Put ``case`` in the process-wide table under its key."""
    validate_case(case)
    if case.key in _CASES and not replace:
        raise HistoryError(
            f"case {case.key!r} is already registered; pass replace=True if that "
            "is deliberate"
        )
    _CASES[case.key] = case
    return case


def get_case(key: str) -> HistoricalCase:
    try:
        return _CASES[key]
    except KeyError:
        raise HistoryError(
            f"no case {key!r} is registered; known: {sorted(_CASES)}"
        ) from None


def list_cases() -> tuple[str, ...]:
    return tuple(sorted(_CASES))


def unregister_case(key: str) -> None:
    _CASES.pop(key, None)


def clear_cases() -> None:
    """Empty the table. Exists for tests; nothing else should need it."""
    _CASES.clear()


# ---------------------------------------------------------------------------
# Putting a case in front of a pipeline
# ---------------------------------------------------------------------------


class CaseGenerator:
    """A lead source that emits exactly one recorded observation.

    It satisfies :class:`~ontology.registry.Generator` structurally, so the
    pipeline treats a replay exactly as it treats a real run — the same
    validation, the same dispositions, the same conservation invariant. Nothing
    about a case gets a shortcut through the machinery it is testing.
    """

    def __init__(self, case: HistoricalCase) -> None:
        validate_case(case)
        self.case = case
        self.name = f"history:{case.key}"
        self.version = HISTORY_VERSION

    def describe(self) -> str:
        return (
            f"Replays the observation behind {self.case.title!r} ({self.case.proposed}) "
            "as a candidate, so that a pipeline can be measured against an answer "
            "that is already settled."
        )

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        candidate = self.case.build()
        if not isinstance(candidate, Candidate):
            raise HistoryError(
                f"case {self.case.key!r} built {type(candidate).__name__}, "
                "not a Candidate"
            )
        yield candidate


class NullKnownnessDetector:
    """A catalogue that runs, consults nothing, and recognises nothing.

    It exists so that the ``uncatalogued`` replay is a *counterfactual* rather
    than a crippled pipeline. The pipeline requires the knownness check to have
    run before anything may be promoted; a domain with no detector therefore
    records every candidate ``inconclusive`` whatever the screens found, and a
    suite built on that would conclude "nothing was endorsed" from a rule of
    bookkeeping instead of from a measurement.

    Returning ``None`` is not a claim of novelty and must never be read as one:
    it is this object saying that it looked in an empty drawer.
    """

    name = "null-catalogue"
    version = HISTORY_VERSION

    def describe(self) -> str:
        return (
            "An empty catalogue. It performs the already-known check and never "
            "matches, which is the position of anyone examining a question "
            "before the answer has been written down."
        )

    def check(self, candidate: Candidate) -> None:
        return None


def case_domain(case: HistoricalCase, domain: Domain, mode: str = "full") -> Domain:
    """``domain``'s screens and catalogue, driven by one case's observation.

    ``mode='uncatalogued'`` swaps the catalogue for an empty one and changes
    nothing else. That is the whole experiment: same screens, same order, same
    budget, with the one component that encodes hindsight emptied out.
    """
    if mode not in MODES:
        raise HistoryError(f"mode must be one of {MODES}, got {mode!r}")
    if not isinstance(domain, Domain):
        raise HistoryError(f"domain must be a Domain, got {type(domain).__name__}")
    return Domain(
        name=f"{domain.name}-history-{case.key}-{mode}",
        version=f"{domain.version}+history{HISTORY_VERSION}",
        generators=(CaseGenerator(case),),
        screens=domain.screens,
        detectors=(
            domain.detectors if mode == "full" else (NullKnownnessDetector(),)
        ),
        description=(
            f"Historical validation replay of {case.title!r} against the "
            f"{domain.name} pipeline"
            + ("" if mode == "full" else ", with the already-known gate removed")
            + ". Nothing this replay produces is a result about the subject; it "
            "is a measurement of the pipeline."
        ),
    )


@dataclass(frozen=True)
class CaseReplay:
    """What the pipeline did with one case, in one mode."""

    case_key: str
    mode: str
    candidate_id: str
    kind: str
    stage: str
    disposition: str
    screen: str
    detail: str
    status: str
    references: tuple[str, ...]
    verdict_evidence: Mapping[str, Any] = field(default_factory=dict)
    verdict_notes: str = ""
    label: str = ""
    seconds: float = 0.0

    @property
    def killed(self) -> bool:
        """Did anything actually stop this, as opposed to failing to decide?"""
        return self.disposition in KILLING_DISPOSITIONS

    def record_text(self) -> str:
        """Every piece of prose the record carries, lower-cased, in one string.

        Used for the ``must_not_say`` check: while the schema has no field for
        "believed, not proved", the next best enforceable thing is that no text
        in the record claims more than the literature does.
        """
        parts = [
            self.detail,
            self.status,
            self.verdict_notes,
            self.label,
            " ".join(self.references),
            " ".join(f"{k}={v}" for k, v in self.verdict_evidence.items()),
        ]
        return " ".join(str(p) for p in parts).lower()

    def to_dict(self) -> dict[str, Any]:
        return {
            "case": self.case_key,
            "mode": self.mode,
            "candidate_id": self.candidate_id,
            "kind": self.kind,
            "stage": self.stage,
            "disposition": self.disposition,
            "screen": self.screen,
            "detail": self.detail,
            "status": self.status,
            "references": list(self.references),
            "seconds": round(self.seconds, 6),
        }


def _references_of(evidence: Mapping[str, Any]) -> tuple[str, ...]:
    refs = evidence.get("references")
    if isinstance(refs, (str, bytes)) or not isinstance(refs, Sequence):
        return ()
    return tuple(str(r) for r in refs)


def replay(
    case: HistoricalCase,
    domain: Domain,
    *,
    mode: str = "full",
    ledger: Ledger | str | Path,
) -> CaseReplay:
    """Run one case through ``domain``'s pipeline and report where it left.

    ``ledger`` is mandatory and has no default. A replay writes candidate and
    run records exactly as a real pass does, and writing test traffic into the
    laboratory's own private ledger would corrupt every conversion rate it
    reports. Point it at a temporary path.
    """
    if mode not in MODES:
        raise HistoryError(f"mode must be one of {MODES}, got {mode!r}")
    validate_case(case)
    store = ledger if isinstance(ledger, Ledger) else Ledger(ledger)
    run: FunnelRun = run_funnel(case_domain(case, domain, mode), ledger=store)
    if len(run.outcomes) != 1:
        raise HistoryError(
            f"case {case.key!r} produced {len(run.outcomes)} outcomes; a case is "
            "one observation, so exactly one was expected"
        )
    outcome = run.outcomes[0]
    stored = store.latest().get(outcome.candidate_id)
    verdict = stored.verdict if stored is not None else None
    evidence: Mapping[str, Any] = dict(verdict.evidence) if verdict is not None else {}
    return CaseReplay(
        case_key=case.key,
        mode=mode,
        candidate_id=outcome.candidate_id,
        kind=outcome.kind,
        stage=outcome.stage,
        disposition=outcome.disposition,
        screen=outcome.screen,
        detail=outcome.detail,
        status=(verdict.status.value if verdict is not None else VerdictStatus.OPEN.value),
        references=_references_of(evidence),
        verdict_evidence=evidence,
        verdict_notes=(verdict.notes if verdict is not None else ""),
        label=(stored.label if stored is not None else ""),
        seconds=run.seconds,
    )


# ---------------------------------------------------------------------------
# Adjudication
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CaseResult:
    """Whether the pipeline reproduced history for one case, and why not."""

    case_key: str
    title: str
    outcome: str
    full: CaseReplay
    uncatalogued: CaseReplay | None = None
    reasons: tuple[str, ...] = ()

    @property
    def passed(self) -> bool:
        return not self.reasons

    @property
    def critical(self) -> tuple[str, ...]:
        """The subset of failures that are misclassifications, not shortfalls."""
        return tuple(r for r in self.reasons if r.startswith("CRITICAL"))

    def to_dict(self) -> dict[str, Any]:
        return {
            "case": self.case_key,
            "title": self.title,
            "historical_outcome": self.outcome,
            "passed": self.passed,
            "reasons": list(self.reasons),
            "full": self.full.to_dict(),
            "uncatalogued": (
                None if self.uncatalogued is None else self.uncatalogued.to_dict()
            ),
        }


def _text_reasons(case: HistoricalCase, rep: CaseReplay) -> list[str]:
    bad: list[str] = []
    blob = rep.record_text()
    for wanted in case.must_cite:
        if wanted.lower() not in blob:
            bad.append(
                f"[{rep.mode}] the record does not cite {wanted!r}; a "
                "verdict of 'known' that cannot name what it matched is an opinion"
            )
    for forbidden in case.must_not_say:
        if forbidden.lower() in blob:
            bad.append(
                f"CRITICAL [{rep.mode}] the record contains {forbidden!r}, which "
                "claims more than the literature does for this case"
            )
    return bad


def check_case(
    case: HistoricalCase,
    full: CaseReplay,
    uncatalogued: CaseReplay | None = None,
) -> CaseResult:
    """Compare what the pipeline did against what history settled."""
    validate_case(case)
    outcome = HistoricalOutcome(case.outcome)
    impossible = IMPOSSIBLE_DISPOSITIONS[outcome]
    bad: list[str] = []

    for rep in (r for r in (full, uncatalogued) if r is not None):
        if rep.disposition in impossible:
            bad.append(
                f"CRITICAL [{rep.mode}] disposition {rep.disposition!r} is "
                f"impossible for a claim history recorded as {outcome.value!r}"
            )
        elif rep.disposition not in case.expected(rep.mode):
            bad.append(
                f"[{rep.mode}] disposition {rep.disposition!r} is not among the "
                f"expected {sorted(case.expected(rep.mode))}"
            )

    bad.extend(_text_reasons(case, full))

    if uncatalogued is not None and case.expect_screens_kill and not uncatalogued.killed:
        bad.append(
            f"CRITICAL [uncatalogued] nothing stopped this: disposition "
            f"{uncatalogued.disposition!r}. With the already-known gate removed, "
            "the screens were expected to kill it on the arithmetic alone"
        )
    return CaseResult(
        case_key=case.key,
        title=case.title,
        outcome=outcome.value,
        full=full,
        uncatalogued=uncatalogued,
        reasons=tuple(bad),
    )


def gate_dependence(result: CaseResult) -> bool:
    """Was the correct answer carried entirely by the already-known gate?

    ``True`` when the full pipeline settled the case and, with the catalogue
    removed, nothing else did. That is not a defect — a catalogue is *supposed*
    to be the cheapest way to be right, and this package's whole premise is that
    it will dominate — but it is a fact about the instrument that must be
    measured rather than assumed. A laboratory whose every correct answer is
    gate-dependent has screens that are decorative.
    """
    if result.uncatalogued is None:
        return False
    return result.full.killed and not result.uncatalogued.killed


def run_case(
    case: HistoricalCase,
    domain: Domain,
    *,
    ledger_dir: str | Path,
    modes: Iterable[str] = MODES,
) -> CaseResult:
    """Replay one case in each requested mode and adjudicate the result.

    Each mode gets its own ledger file: a shared one would deduplicate the
    second replay against the first, and a case that was silently skipped is
    worse than one that failed.
    """
    wanted = tuple(dict.fromkeys(str(m) for m in modes))
    unknown = sorted(set(wanted) - set(MODES))
    if unknown:
        raise HistoryError(f"unknown modes {unknown}; the modes are {list(MODES)}")
    if "full" not in wanted:
        raise HistoryError("'full' cannot be omitted: it is the pipeline as it stands")
    root = Path(ledger_dir)
    root.mkdir(parents=True, exist_ok=True)
    replays: dict[str, CaseReplay] = {}
    for mode in wanted:
        path = root / f"{case.key}.{mode}.jsonl"
        replays[mode] = replay(case, domain, mode=mode, ledger=path)
    return check_case(case, replays["full"], replays.get("uncatalogued"))


def run_history(
    cases: Iterable[HistoricalCase],
    domain: Domain,
    *,
    ledger_dir: str | Path,
    modes: Iterable[str] = MODES,
) -> tuple[CaseResult, ...]:
    """Every case, in registration order."""
    mode_tuple = tuple(modes)
    return tuple(
        run_case(case, domain, ledger_dir=ledger_dir, modes=mode_tuple)
        for case in cases
    )


def render_text(results: Sequence[CaseResult]) -> str:
    """A one-screen report. Failures are printed in full, never summarised.

    There is no score and no percentage: a validation suite that reports "4 of 5"
    invites its reader to accept the fifth. Either the pipeline reproduced a
    settled answer or it did not, and the one it did not is the whole content of
    the report.
    """
    if not results:
        return "no historical cases were replayed — nothing was validated"
    width = max(len(r.case_key) for r in results)
    lines = [
        f"historical validation  v{HISTORY_VERSION}   {len(results)} case(s)",
        f"  {'case':<{width}}  {'history':<30}{'full':<14}{'uncatalogued':<14}  verdict",
    ]
    for r in results:
        un = "-" if r.uncatalogued is None else r.uncatalogued.disposition
        mark = "ok" if r.passed else ("MISCLASSIFIED" if r.critical else "unexpected")
        lines.append(
            f"  {r.case_key:<{width}}  {r.outcome:<30}{r.full.disposition:<14}{un:<14}  {mark}"
        )
    dependent = [r.case_key for r in results if gate_dependence(r)]
    lines.append(
        "  carried by the already-known gate alone: "
        + (", ".join(dependent) if dependent else "none")
    )
    failures = [r for r in results if not r.passed]
    if failures:
        lines.append("  failures:")
        for r in failures:
            lines.append(f"    {r.case_key}:")
            lines.extend(f"      - {reason}" for reason in r.reasons)
    return "\n".join(lines)
