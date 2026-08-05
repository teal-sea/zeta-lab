"""discovery.funnel — the pipeline, and the accounting that justifies it.

Domain-agnostic, in the same strict sense as :mod:`discovery.schema` and
:mod:`discovery.registry`: it runs plug-ins fetched from the registry, counts
what happens to every observation, and knows nothing about what any of them are
about.

The pipeline
------------
``generate → deduplicate → knownness → cheap screens → expensive screens →
terminal``. Each stage may only *remove* candidates, and removal always costs a
terminal verdict that already earns its own status. The order is not
negotiable and it is not an optimisation detail:

* deduplication runs against **the whole ledger**, not just this run, because a
  generator re-finding last month's observation has found nothing, and a funnel
  that counts it again is reporting its operator's persistence;
* the already-known gate runs before any screen, because "this is in the
  literature" is the likeliest true answer and the cheapest one to obtain;
* expensive screens run only on what survived the cheap ones, so the compute is
  spent where the cheap tests could not decide.

The invariant
-------------
**In a run that completes, every candidate that enters leaves with a recorded
terminal disposition.** Not "usually", not "unless a screen was slow": the count
in equals the count out, it is asserted in code (:class:`FunnelError` if it ever
fails) and pinned by a test. A funnel that silently drops observations cannot
have a conversion rate, because the denominator is a guess. The seven
dispositions are :data:`DISPOSITIONS`; five of them are schema verdict statuses
and two (``duplicate``, ``invalid``) are funnel outcomes with no verdict, since
neither is a statement about the world.

The one exception is stated rather than hidden, because it is real: a plug-in
that **raises** ends the run, and the candidates queued behind the failure never
reach a disposition. They are not dropped silently — the crash record carries
``entered`` and ``undecided``, and :func:`discovery.metrics.funnel_report`
keeps ``undecided`` in the emitted denominator and reports its own non-terminal
rate, so a crash cannot flatter the remaining conversions. Re-running decides
them.

Zero-yield work
---------------
``discovery/README.md`` §7.1 states the schema's largest gap: a candidate record
needs a candidate, so a lead source that ran and emitted nothing leaves no
trace, and every conversion rate computed without it has the wrong denominator.
This module closes that gap in the run stream of the ledger: **every generator
invocation is recorded, with its wall-clock cost, whether or not it produced
anything**, and the run record is written once at the start and again at the
end, so a run that died is still counted.

Resumability
------------
A candidate is checkpointed to the ledger with an ``open`` verdict the moment it
is admitted, and its terminal record is appended when it is decided. If the
process dies in between, the next run finds an ``open`` record for that id and
*resumes* it — screens it and decides it — instead of treating it as a
duplicate. A candidate already decided is a duplicate and is not written again.
So re-running an interrupted funnel neither duplicates ledger entries nor
strands observations in ``open`` forever.

When a plug-in raises, the exception is re-raised — a broken screen is a defect,
not a verdict — but not before the run record is written with
``state="crashed"`` and **every outcome decided up to that point**. Losing that
work from the log would take the work out of every conversion rate too, which is
the one thing this module exists to prevent: a run that died after screening
four hundred observations still screened four hundred observations.

What this module will not do
----------------------------
It will not promote anything to ``survives`` on its own authority. That status
requires all three of ``known``/``trivial``/``refutation`` to have actually run
(the domain declares which screen performs which) *and* a verification effort
strictly above the effort the candidate was generated at. When either is
missing the honest record is ``inconclusive`` with the ceiling that was hit,
and that is what gets written. A survivor is a lead, not a result.
"""

from __future__ import annotations

import datetime as _dt
import time
import uuid
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final

from discovery.ledger import Ledger
from discovery.registry import (
    KNOWN_CHECK,
    Domain,
    ScreenResult,
    get_domain,
    validate_domain,
)
from discovery.schema import (
    REQUIRED_SURVIVAL_CHECKS,
    TERMINAL_STATUSES,
    Candidate,
    InconclusiveReason,
    Verdict,
    VerdictStatus,
    candidate_reasons,
    validate_verdict,
)

__all__ = [
    "FUNNEL_VERSION",
    "STAGES",
    "DISPOSITIONS",
    "VERDICT_DISPOSITIONS",
    "FUNNEL_ONLY_DISPOSITIONS",
    "FunnelError",
    "Outcome",
    "GeneratorReport",
    "StageTally",
    "ScreenTally",
    "FunnelRun",
    "run_funnel",
    "default_proof_gap",
]

#: Bump whenever the pipeline's behaviour changes: run records carry it, and
#: two behaviours logged under one version are two populations averaged.
FUNNEL_VERSION: Final[str] = "1.1"

#: The pipeline, in order. A stage may be omitted from a run; it may not be
#: reordered, because the order is the argument for the design.
STAGES: Final[tuple[str, ...]] = (
    "generate",
    "deduplicate",
    "knownness",
    "cheap_screens",
    "expensive_screens",
    "terminal",
)

#: Dispositions that are schema verdict statuses — a statement about the world.
VERDICT_DISPOSITIONS: Final[tuple[str, ...]] = (
    "known",
    "trivial",
    "refuted",
    "survives",
    "inconclusive",
)

#: Dispositions that are funnel bookkeeping, not statements about the world.
#: ``duplicate``: this observation is already in the ledger. ``invalid``: the
#: payload was never a candidate (the schema refused it), which is a defect in
#: the generator and is counted against it.
FUNNEL_ONLY_DISPOSITIONS: Final[tuple[str, ...]] = ("duplicate", "invalid")

#: Exhaustive: every candidate that enters leaves with exactly one of these.
DISPOSITIONS: Final[tuple[str, ...]] = (
    *FUNNEL_ONLY_DISPOSITIONS,
    *VERDICT_DISPOSITIONS,
)


class FunnelError(Exception):
    """The pipeline could not honour its own invariants."""


def _utc_now() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def _nonnegative_int(value: Any) -> int:
    """Best-effort count parsing for hand-edited or older run records."""
    try:
        return max(0, int(value or 0))
    except (TypeError, ValueError):
        return 0


def default_proof_gap(screens: Sequence[str], effort: float) -> str:
    """The proof gap the funnel writes when nothing killed a candidate.

    It says the only true thing available: a finite computation happened and
    no proof is attached. The schema requires this field to be non-empty
    precisely so that a survivor cannot be recorded without someone — here, the
    machine — stating what is missing.
    """
    names = ", ".join(screens) if screens else "no screen"
    return (
        f"No proof is attached. This observation survived {names} at verification "
        f"effort {effort:g}, over the finite range recorded in its evidence. "
        "Nothing here establishes the claim beyond that range, and nothing here "
        "is evidence for any conjecture the claim resembles: a survivor is a "
        "lead to be examined by hand, not a result."
    )


# ---------------------------------------------------------------------------
# What the run records
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Outcome:
    """Where one candidate left the funnel, and how.

    One of these exists for **every** candidate a generator emitted in a
    completed run. A crashed run may have fewer outcomes than generator output;
    :class:`FunnelRun` records that difference as ``undecided`` so conversion
    denominators do not shrink around failures.
    """

    candidate_id: str
    generator: str
    generator_version: str
    kind: str
    stage: str
    disposition: str
    screen: str = ""
    detail: str = ""
    seconds: float = 0.0
    resumed: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_id": self.candidate_id,
            "generator": self.generator,
            "generator_version": self.generator_version,
            "kind": self.kind,
            "stage": self.stage,
            "disposition": self.disposition,
            "screen": self.screen,
            "detail": self.detail,
            "seconds": round(self.seconds, 6),
            "resumed": self.resumed,
        }

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "Outcome":
        return cls(
            candidate_id=str(record.get("candidate_id", "")),
            generator=str(record.get("generator", "")),
            generator_version=str(record.get("generator_version", "")),
            kind=str(record.get("kind", "")),
            stage=str(record.get("stage", "")),
            disposition=str(record.get("disposition", "")),
            screen=str(record.get("screen", "")),
            detail=str(record.get("detail", "")),
            seconds=float(record.get("seconds", 0.0) or 0.0),
            resumed=bool(record.get("resumed", False)),
        )


@dataclass(frozen=True, slots=True)
class GeneratorReport:
    """One generator invocation — **including the ones that yielded nothing**."""

    generator: str
    version: str
    produced: int
    seconds: float
    error: str = ""
    skipped: bool = False

    @property
    def zero_yield(self) -> bool:
        return self.produced == 0 and not self.skipped

    def to_dict(self) -> dict[str, Any]:
        return {
            "generator": self.generator,
            "version": self.version,
            "produced": self.produced,
            "seconds": round(self.seconds, 6),
            "error": self.error,
            "skipped": self.skipped,
        }

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "GeneratorReport":
        return cls(
            generator=str(record.get("generator", "")),
            version=str(record.get("version", "")),
            produced=int(record.get("produced", 0) or 0),
            seconds=float(record.get("seconds", 0.0) or 0.0),
            error=str(record.get("error", "")),
            skipped=bool(record.get("skipped", False)),
        )


@dataclass(frozen=True, slots=True)
class StageTally:
    """How many candidates entered a stage, and how many it removed."""

    stage: str
    entered: int = 0
    left: int = 0
    seconds: float = 0.0

    @property
    def passed(self) -> int:
        return self.entered - self.left

    @property
    def pass_rate(self) -> float | None:
        """``None`` when nothing entered — a rate with an empty denominator is
        not zero, it is undefined, and reporting it as zero is a lie."""
        return None if self.entered == 0 else self.passed / self.entered

    def to_dict(self) -> dict[str, Any]:
        return {
            "stage": self.stage,
            "entered": self.entered,
            "left": self.left,
            "seconds": round(self.seconds, 6),
        }


@dataclass(frozen=True, slots=True)
class ScreenTally:
    """How often one screen was consulted, what it cost and what it killed."""

    screen: str
    cost: str
    calls: int = 0
    stopped: int = 0
    seconds: float = 0.0

    @property
    def stop_rate(self) -> float | None:
        return None if self.calls == 0 else self.stopped / self.calls

    @property
    def seconds_per_call(self) -> float | None:
        return None if self.calls == 0 else self.seconds / self.calls

    def to_dict(self) -> dict[str, Any]:
        return {
            "screen": self.screen,
            "cost": self.cost,
            "calls": self.calls,
            "stopped": self.stopped,
            "seconds": round(self.seconds, 6),
        }


@dataclass(frozen=True, slots=True)
class FunnelRun:
    """The whole record of one pass through the pipeline."""

    run_id: str
    domain: str
    domain_version: str
    started_at: str
    finished_at: str = ""
    seconds: float = 0.0
    dry_run: bool = False
    state: str = "finished"
    stages: tuple[str, ...] = STAGES
    limit: int | None = None
    limit_reached: bool = False
    generators: tuple[GeneratorReport, ...] = ()
    outcomes: tuple[Outcome, ...] = ()
    entered: int = 0
    undecided: int = 0
    stage_tallies: tuple[StageTally, ...] = ()
    screen_tallies: tuple[ScreenTally, ...] = ()
    written: int = 0
    resumed: int = 0
    ledger_path: str | None = None
    errors: tuple[str, ...] = ()
    funnel_version: str = FUNNEL_VERSION

    # -- queries ----------------------------------------------------------
    @property
    def generated(self) -> int:
        """Candidates emitted by generators in this run."""
        reported = sum(g.produced for g in self.generators if not g.skipped)
        # Old or hand-built records may carry outcomes but no generator report.
        return max(reported, len(self.outcomes))

    def dispositions(self) -> dict[str, int]:
        """Counts by disposition; every key is present, empty ones included."""
        counts = {name: 0 for name in DISPOSITIONS}
        for outcome in self.outcomes:
            counts[outcome.disposition] = counts.get(outcome.disposition, 0) + 1
        return counts

    def survivors(self) -> tuple[str, ...]:
        return tuple(o.candidate_id for o in self.outcomes if o.disposition == "survives")

    def stage_tally(self, stage: str) -> StageTally:
        for tally in self.stage_tallies:
            if tally.stage == stage:
                return tally
        return StageTally(stage)

    # -- serialisation ----------------------------------------------------
    def to_dict(self) -> dict[str, Any]:
        return {
            "record": "funnel_run",
            "funnel_version": self.funnel_version,
            "run_id": self.run_id,
            "state": self.state,
            "domain": self.domain,
            "domain_version": self.domain_version,
            "started_at": self.started_at,
            "finished_at": self.finished_at,
            "seconds": round(self.seconds, 6),
            "dry_run": self.dry_run,
            "stages": list(self.stages),
            "limit": self.limit,
            "limit_reached": self.limit_reached,
            "generators": [g.to_dict() for g in self.generators],
            "outcomes": [o.to_dict() for o in self.outcomes],
            "entered": self.entered,
            "undecided": self.undecided,
            "stage_tallies": [s.to_dict() for s in self.stage_tallies],
            "screen_tallies": [s.to_dict() for s in self.screen_tallies],
            "dispositions": self.dispositions(),
            "written": self.written,
            "resumed": self.resumed,
            "ledger_path": self.ledger_path,
            "errors": list(self.errors),
        }

    @classmethod
    def from_dict(cls, record: Mapping[str, Any]) -> "FunnelRun":
        return cls(
            run_id=str(record.get("run_id", "")),
            domain=str(record.get("domain", "")),
            domain_version=str(record.get("domain_version", "")),
            started_at=str(record.get("started_at", "")),
            finished_at=str(record.get("finished_at", "")),
            seconds=float(record.get("seconds", 0.0) or 0.0),
            dry_run=bool(record.get("dry_run", False)),
            state=str(record.get("state", "finished")),
            stages=tuple(record.get("stages", STAGES) or ()),
            limit=record.get("limit"),
            limit_reached=bool(record.get("limit_reached", False)),
            generators=tuple(
                GeneratorReport.from_dict(g) for g in record.get("generators", []) or []
            ),
            outcomes=tuple(
                Outcome.from_dict(o) for o in record.get("outcomes", []) or []
            ),
            entered=_nonnegative_int(record.get("entered", 0)),
            undecided=_nonnegative_int(record.get("undecided", 0)),
            stage_tallies=tuple(
                StageTally(
                    stage=str(s.get("stage", "")),
                    entered=int(s.get("entered", 0) or 0),
                    left=int(s.get("left", 0) or 0),
                    seconds=float(s.get("seconds", 0.0) or 0.0),
                )
                for s in record.get("stage_tallies", []) or []
            ),
            screen_tallies=tuple(
                ScreenTally(
                    screen=str(s.get("screen", "")),
                    cost=str(s.get("cost", "")),
                    calls=int(s.get("calls", 0) or 0),
                    stopped=int(s.get("stopped", 0) or 0),
                    seconds=float(s.get("seconds", 0.0) or 0.0),
                )
                for s in record.get("screen_tallies", []) or []
            ),
            written=int(record.get("written", 0) or 0),
            resumed=int(record.get("resumed", 0) or 0),
            ledger_path=record.get("ledger_path"),
            errors=tuple(str(e) for e in record.get("errors", []) or []),
            funnel_version=str(record.get("funnel_version", FUNNEL_VERSION)),
        )

    def render_text(self) -> str:
        """A one-screen summary of this run."""
        lines = [
            f"run {self.run_id}  domain={self.domain} v{self.domain_version}"
            f"{'  [DRY RUN — nothing written]' if self.dry_run else ''}",
            f"  started {self.started_at}   {self.seconds:.3f} s"
            f"   stages: {'>'.join(self.stages)}",
        ]
        lines.append(f"  {'generator':<28}{'produced':>9}{'seconds':>10}")
        for gen in self.generators:
            note = "  (error)" if gen.error else ("  (skipped)" if gen.skipped else "")
            lines.append(
                f"  {gen.generator + ' v' + gen.version:<28}{gen.produced:>9}"
                f"{gen.seconds:>10.3f}{note}"
            )
        lines.append(f"  {'stage':<28}{'entered':>9}{'left':>10}{'pass':>9}")
        for tally in self.stage_tallies:
            rate = tally.pass_rate
            shown = "     —" if rate is None else f"{rate:>8.1%}"
            lines.append(
                f"  {tally.stage:<28}{tally.entered:>9}{tally.left:>10}{shown}"
            )
        counts = self.dispositions()
        summary = "  ".join(f"{k}={counts[k]}" for k in DISPOSITIONS if counts[k])
        if self.undecided:
            summary = (summary + "  " if summary else "") + f"undecided={self.undecided}"
        lines.append(f"  dispositions: {summary or 'nothing generated'}")
        if self.errors:
            lines.append("  errors:")
            lines.extend(f"    - {e}" for e in self.errors)
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# The pipeline
# ---------------------------------------------------------------------------


def _normalise_stages(stages: Iterable[str] | None) -> tuple[str, ...]:
    if stages is None:
        return STAGES
    requested = {str(s) for s in stages}
    unknown = sorted(requested - set(STAGES))
    if unknown:
        raise FunnelError(f"unknown stages {unknown}; the pipeline is {list(STAGES)}")
    if not requested:
        raise FunnelError("a run with no stages would generate nothing")
    if "generate" not in requested:
        raise FunnelError("'generate' cannot be omitted: nothing would enter the funnel")
    return tuple(s for s in STAGES if s in requested)


def _check_conservation(entered: int, outcomes: Sequence[Outcome]) -> None:
    """The funnel's one hard invariant: what enters must leave, and be named.

    Extracted so it can be exercised directly by the test suite: a guard nobody
    has seen fail is a guard nobody has tested.
    """
    if len(outcomes) != entered:
        raise FunnelError(
            f"{entered} candidates entered but {len(outcomes)} left: the funnel "
            "dropped observations, so no conversion rate it reports is meaningful"
        )
    unknown = sorted({o.disposition for o in outcomes} - set(DISPOSITIONS))
    if unknown:
        raise FunnelError(
            f"outcomes carry dispositions outside the vocabulary: {unknown}"
        )


def _as_ledger(ledger: "Ledger | str | Path | None") -> Ledger:
    if isinstance(ledger, Ledger):
        return ledger
    return Ledger(ledger)


def _relative_ledger_path(path: Path) -> str | None:
    """The ledger location, relative to the checkout when it is inside it.

    A machine-local absolute path must never reach a record (the schema refuses
    them outright), and the run stream deserves the same discipline even though
    it lives in a gitignored directory.
    """
    root = Path(__file__).resolve().parent.parent
    try:
        return str(path.resolve().relative_to(root))
    except ValueError:
        return path.name


def _inconclusive(
    reason: InconclusiveReason,
    detail: str,
    ceiling: Mapping[str, Any],
    *,
    decided_by: str,
) -> Verdict:
    return Verdict(
        status=VerdictStatus.INCONCLUSIVE,
        decided_by=decided_by,
        decided_by_version=FUNNEL_VERSION,
        decided_at=_utc_now(),
        evidence={
            "reason": reason.value,
            "detail": detail,
            "ceiling": dict(ceiling),
        },
    )


def run_funnel(
    domain: "Domain | str",
    stages: Iterable[str] | None = None,
    limit: int | None = None,
    ledger: "Ledger | str | Path | None" = None,
    dry_run: bool = False,
    *,
    context: Mapping[str, Any] | None = None,
    reopen: Iterable[str] = (),
    checkpoint: bool = True,
    run_id: str | None = None,
) -> FunnelRun:
    """Run one pass of the discovery pipeline and record all of it.

    Parameters
    ----------
    domain:
        A :class:`~discovery.registry.Domain`, or the name of a registered one.
    stages:
        A subset of :data:`STAGES`; omitted stages are skipped, and anything
        still undecided at the end is recorded ``inconclusive`` with reason
        ``budget_exhausted`` rather than quietly promoted. ``generate`` may not
        be omitted.
    limit:
        Maximum candidates drawn from generators in this run. Generators are
        consulted in order and consumption stops when the budget is spent;
        ``limit_reached`` records that it was.
    ledger:
        A :class:`~discovery.ledger.Ledger`, a path, or ``None`` for the default
        (private, gitignored) location.
    dry_run:
        Generate and screen exactly as normal, write nothing at all — neither
        candidates nor the run record. The returned :class:`FunnelRun` is
        complete, so a dry run is how you find out what a run *would* cost.
    context:
        Passed unchanged to every generator.
    reopen:
        Terminal statuses that should be re-examined rather than deduplicated.
        Only ``inconclusive`` and ``survives`` are re-openable per the schema;
        anything else is refused.
    checkpoint:
        Write each admitted candidate to the ledger with an ``open`` verdict
        before screening it, so a crash mid-run is resumable. Turning it off
        halves the log and loses that.
    run_id:
        Identify this run explicitly instead of generating an id. Run records
        collapse by ``run_id`` (last write wins), so one that is already in the
        stream is **refused**: re-using it would delete the earlier run's
        outcomes from every conversion rate. Checking costs one pass over the
        run stream, and only when the id is supplied.

    Notes
    -----
    Each generator is drained into memory before screening begins, so that the
    wall time attributed to generation is generation's alone. A generator that
    would produce more than fits in memory must be bounded with ``limit``.

    If a plug-in raises, the exception propagates — a screen that throws is a
    defect, not a verdict — but the run record is written first, with
    ``state="crashed"`` and every outcome decided up to that point, so the work
    that was done stays in the denominators.
    """
    resolved: Domain = get_domain(domain) if isinstance(domain, str) else domain
    validate_domain(resolved)
    stage_set = _normalise_stages(stages)
    if limit is not None and (isinstance(limit, bool) or not isinstance(limit, int) or limit < 0):
        raise FunnelError(f"limit must be a non-negative integer or None, got {limit!r}")
    reopen_set = frozenset(str(s) for s in reopen)
    from discovery.schema import REOPENABLE_STATUSES  # local: keeps __all__ tidy

    bad_reopen = sorted(reopen_set - {s.value for s in REOPENABLE_STATUSES})
    if bad_reopen:
        raise FunnelError(
            f"only {sorted(s.value for s in REOPENABLE_STATUSES)} may be re-opened, "
            f"got {bad_reopen}"
        )
    store = _as_ledger(ledger)
    ctx: Mapping[str, Any] = {} if context is None else context

    run = run_id or "run-" + uuid.uuid4().hex[:12]
    if run_id is not None:
        # The metrics layer collapses the run stream by ``run_id`` (last record
        # per id wins), so reusing one would erase an earlier run's outcomes
        # from every denominator without anything failing. Refuse it here,
        # where it is still a caller error rather than a silent miscount.
        taken = {str(r.get("run_id", "")) for r in store.runs()}
        if run in taken:
            raise FunnelError(
                f"run_id {run!r} is already in {store.runs_path.name}: re-using one "
                "would erase the earlier run from every conversion rate"
            )
    started_at = _utc_now()
    t0 = time.perf_counter()
    decided_by = f"discovery.funnel[{resolved.name}]"

    # The ledger is read once: dedup is against the whole log, not this run.
    existing: dict[str, Candidate] = store.latest()
    ledger_name = _relative_ledger_path(store.path)

    if not dry_run:
        store.append_run(
            {
                "record": "funnel_run",
                "funnel_version": FUNNEL_VERSION,
                "run_id": run,
                "state": "started",
                "domain": resolved.name,
                "domain_version": resolved.version,
                "started_at": started_at,
                "dry_run": False,
                "stages": list(stage_set),
                "limit": limit,
                "ledger_path": ledger_name,
            }
        )

    errors: list[str] = []

    # Everything the run record needs is initialised before any plug-in is
    # called, so that a crash can still be written up with the work it did.
    batch: list[tuple[Any, Candidate]] = []
    reports: list[GeneratorReport] = []
    outcomes: list[Outcome] = []
    stage_seconds: dict[str, float] = {s: 0.0 for s in STAGES}
    stage_left: dict[str, int] = {s: 0 for s in STAGES}
    screen_tallies: dict[str, ScreenTally] = {}
    seen: dict[str, str] = {}
    written = 0
    resumed_count = 0
    limit_reached = False

    def _assemble(
        state: str,
        *,
        entered: int,
        attempted: int | None = None,
        undecided: int = 0,
    ) -> FunnelRun:
        """The run record as it stands — usable mid-crash as well as at the end.

        ``entered`` is what the stage flow is reconstructed from: the whole
        batch for a completed run, and only what actually left for a crashed
        one, so the record never claims a candidate reached a stage it did not.
        """
        seconds_by_stage = dict(stage_seconds)
        # Generation wall time belongs to the ``generate`` stage in the cost
        # table: a stage-cost report that charged generation nothing would
        # point every optimisation at the screens.
        seconds_by_stage["generate"] += sum(r.seconds for r in reports)
        tallies: list[StageTally] = []
        remaining = entered
        for stage in STAGES:
            runs_here = stage in stage_set or stage in ("generate", "terminal")
            here = remaining if runs_here else 0
            left = stage_left[stage]
            tallies.append(
                StageTally(stage=stage, entered=here, left=left,
                           seconds=seconds_by_stage[stage])
            )
            if runs_here:
                remaining = here - left
        return FunnelRun(
            run_id=run,
            domain=resolved.name,
            domain_version=resolved.version,
            started_at=started_at,
            finished_at=_utc_now(),
            seconds=time.perf_counter() - t0,
            dry_run=dry_run,
            state=state,
            stages=stage_set,
            limit=limit,
            limit_reached=limit_reached,
            generators=tuple(reports),
            outcomes=tuple(outcomes),
            entered=entered if attempted is None else attempted,
            undecided=undecided,
            stage_tallies=tuple(tallies),
            screen_tallies=tuple(screen_tallies.values()),
            written=written,
            resumed=resumed_count,
            ledger_path=ledger_name,
            errors=tuple(errors),
        )

    def _pipeline() -> FunnelRun:
        nonlocal written, resumed_count, limit_reached
        # ---- stage 1: generate -------------------------------------------
        for gen in resolved.generators:
            if limit is not None and len(batch) >= limit:
                limit_reached = True
                reports.append(GeneratorReport(gen.name, str(gen.version), 0, 0.0, skipped=True))
                continue
            produced = 0
            error = ""
            g0 = time.perf_counter()
            try:
                for candidate in gen.generate(ctx):
                    if not isinstance(candidate, Candidate):
                        raise FunnelError(
                            f"generator {gen.name!r} yielded {type(candidate).__name__}, "
                            "not a Candidate"
                        )
                    batch.append((gen, candidate))
                    produced += 1
                    if limit is not None and len(batch) >= limit:
                        limit_reached = True
                        break
            except FunnelError:
                raise
            except Exception as exc:  # a broken lead source must not kill the run
                error = f"{type(exc).__name__}: {exc}"
                errors.append(f"generator {gen.name}: {error}")
            reports.append(
                GeneratorReport(
                    generator=gen.name,
                    version=str(gen.version),
                    produced=produced,
                    seconds=time.perf_counter() - g0,
                    error=error,
                )
            )

        # ---- stages 2..6: one candidate at a time --------------------------
        cheap = resolved.cheap_screens()
        expensive = resolved.expensive_screens()

        def _tally(name: str, cost: str, *, stopped: bool, seconds: float) -> None:
            current = screen_tallies.get(name, ScreenTally(name, cost))
            screen_tallies[name] = ScreenTally(
                screen=name,
                cost=cost,
                calls=current.calls + 1,
                stopped=current.stopped + (1 if stopped else 0),
                seconds=current.seconds + seconds,
            )

        def _leave(
            stage: str,
            disposition: str,
            *,
            gen: Any,
            candidate: Candidate,
            screen: str = "",
            detail: str = "",
            seconds: float = 0.0,
            resumed: bool = False,
        ) -> None:
            stage_left[stage] += 1
            outcomes.append(
                Outcome(
                    candidate_id=candidate.id,
                    generator=str(getattr(gen, "name", "")),
                    generator_version=str(getattr(gen, "version", "")),
                    kind=candidate.kind.value,
                    stage=stage,
                    disposition=disposition,
                    screen=screen,
                    detail=detail[:400],
                    seconds=seconds,
                    resumed=resumed,
                )
            )

        for gen, candidate in batch:
            spent = 0.0
            mark = time.perf_counter()

            def _lap(stage: str) -> float:
                """Seconds since the last lap, charged to ``stage``."""
                nonlocal mark, spent
                now = time.perf_counter()
                secs = now - mark
                mark = now
                stage_seconds[stage] += secs
                spent += secs
                return secs

            # -- stage 1 (continued): is it even a candidate? -----------------
            reasons = candidate_reasons(candidate)
            if candidate.verdict.status is not VerdictStatus.OPEN:
                reasons = reasons + (
                    "a generator may not decide its own candidate: verdict must be 'open'",
                )
            if reasons:
                _lap("generate")
                _leave(
                    "generate",
                    "invalid",
                    gen=gen,
                    candidate=candidate,
                    detail="; ".join(reasons),
                    seconds=spent,
                )
                continue
            _lap("generate")

            # -- stage 2: deduplicate, against the whole ledger ---------------
            is_resumed = False
            if "deduplicate" in stage_set:
                prior = existing.get(candidate.id)
                if candidate.id in seen:
                    _lap("deduplicate")
                    _leave(
                        "deduplicate",
                        "duplicate",
                        gen=gen,
                        candidate=candidate,
                        detail=f"already emitted this run by {seen[candidate.id]}",
                        seconds=spent,
                    )
                    continue
                if prior is not None:
                    status = prior.verdict.status
                    if status is VerdictStatus.OPEN:
                        is_resumed = True
                    elif status.value not in reopen_set:
                        _lap("deduplicate")
                        _leave(
                            "deduplicate",
                            "duplicate",
                            gen=gen,
                            candidate=candidate,
                            detail=f"already in the ledger with status {status.value}",
                            seconds=spent,
                        )
                        continue
                seen[candidate.id] = str(getattr(gen, "name", ""))
            _lap("deduplicate")
            if is_resumed:
                resumed_count += 1

            # Checkpoint on admission: this is what makes a dead run resumable.
            if checkpoint and not dry_run and not is_resumed:
                store.append(candidate)
                written += 1

            checks_run: set[str] = set()
            verified_effort: float | None = None
            screens_passed: list[str] = []
            gen_effort = candidate.provenance.precision.effort_digits()
            decided = False

            # -- stage 3: the already-known gate ------------------------------
            if "knownness" in stage_set:
                mark = time.perf_counter()
                for detector in resolved.detectors:
                    checks_run.add(KNOWN_CHECK)
                    verdict = detector.check(candidate)
                    secs = _lap("knownness")
                    _tally(detector.name, "detector", stopped=verdict is not None, seconds=secs)
                    if verdict is None:
                        continue
                    if verdict.status not in TERMINAL_STATUSES:
                        raise FunnelError(
                            f"detector {detector.name!r} returned a non-terminal verdict "
                            f"{verdict.status.value!r}"
                        )
                    try:
                        validate_verdict(verdict)
                    except Exception as exc:
                        raise FunnelError(
                            f"detector {detector.name!r} returned an unearned verdict: {exc}"
                        ) from exc
                    if not dry_run:
                        store.append(candidate.with_verdict(verdict))
                        written += 1
                    _leave(
                        "knownness",
                        verdict.status.value,
                        gen=gen,
                        candidate=candidate,
                        screen=detector.name,
                        detail=verdict.notes,
                        seconds=spent,
                        resumed=is_resumed,
                    )
                    decided = True
                    break
            if decided:
                continue

            # -- stages 4 and 5: cheap then expensive screens -----------------
            for stage_name, screens in (
                ("cheap_screens", cheap),
                ("expensive_screens", expensive),
            ):
                if stage_name not in stage_set or decided:
                    continue
                mark = time.perf_counter()
                for screen in screens:
                    result = screen.apply(candidate)
                    secs = _lap(stage_name)
                    if not isinstance(result, ScreenResult):
                        raise FunnelError(
                            f"screen {screen.name!r} returned "
                            f"{type(result).__name__}, not a ScreenResult"
                        )
                    try:
                        result.validate()
                    except Exception as exc:
                        raise FunnelError(str(exc)) from exc
                    checks_run.update(str(c) for c in getattr(screen, "checks", ()) or ())
                    if result.effort is not None:
                        verified_effort = (
                            result.effort
                            if verified_effort is None
                            else max(verified_effort, float(result.effort))
                        )
                    _tally(screen.name, str(screen.cost), stopped=not result.passed, seconds=secs)
                    if not result.passed:
                        verdict = result.verdict
                        assert verdict is not None  # guaranteed by ScreenResult.validate
                        if not dry_run:
                            store.append(candidate.with_verdict(verdict))
                            written += 1
                        _leave(
                            stage_name,
                            verdict.status.value,
                            gen=gen,
                            candidate=candidate,
                            screen=screen.name,
                            detail=result.detail,
                            seconds=spent,
                            resumed=is_resumed,
                        )
                        decided = True
                        break
                    screens_passed.append(screen.name)
            if decided:
                continue

            # -- stage 6: the terminal verdict --------------------------------
            mark = time.perf_counter()
            skipped_stages = [s for s in ("knownness", "cheap_screens", "expensive_screens")
                              if s not in stage_set]
            missing = [c for c in REQUIRED_SURVIVAL_CHECKS if c not in checks_run]
            if "terminal" not in stage_set or skipped_stages:
                verdict = _inconclusive(
                    InconclusiveReason.BUDGET_EXHAUSTED,
                    "the run did not execute every stage, so nothing about this "
                    "observation was decided",
                    {"stages_run": list(stage_set), "stages_skipped": skipped_stages or ["terminal"]},
                    decided_by=decided_by,
                )
            elif missing:
                verdict = _inconclusive(
                    InconclusiveReason.DEPENDENCY_UNAVAILABLE,
                    "no plug-in in this domain performs "
                    + ", ".join(missing)
                    + ": a candidate may not survive a check that never ran",
                    {
                        "checks_run": sorted(checks_run),
                        "checks_required": list(REQUIRED_SURVIVAL_CHECKS),
                    },
                    decided_by=decided_by,
                )
            elif verified_effort is None or not verified_effort > gen_effort:
                verdict = _inconclusive(
                    InconclusiveReason.PRECISION_INSUFFICIENT,
                    "verification did not cost more than generation "
                    f"(generated at effort {gen_effort:g}, verified at "
                    f"{'nothing reported' if verified_effort is None else format(verified_effort, 'g')})"
                    ": the schema reserves 'survives' for observations that were "
                    "re-examined more expensively than they were found",
                    {
                        "effort": "exact" if gen_effort == float("inf") else gen_effort,
                        "verified_effort": verified_effort,
                    },
                    decided_by=decided_by,
                )
            else:
                verdict = Verdict(
                    status=VerdictStatus.SURVIVES,
                    decided_by=decided_by,
                    decided_by_version=FUNNEL_VERSION,
                    decided_at=_utc_now(),
                    evidence={
                        "checks_run": sorted(checks_run),
                        "effort": gen_effort,
                        "verified_effort": float(verified_effort),
                        "effort_unit": "decimal digits (Precision.effort_digits)",
                        "screens_passed": list(screens_passed),
                        "proof_gap": default_proof_gap(screens_passed, float(verified_effort)),
                    },
                )
            validate_verdict(verdict)
            _lap("terminal")
            if not dry_run:
                store.append(candidate.with_verdict(verdict))
                written += 1
            _leave(
                "terminal",
                verdict.status.value,
                gen=gen,
                candidate=candidate,
                detail=str(verdict.evidence.get("detail", "")),
                seconds=spent,
                resumed=is_resumed,
            )

        # ---- stage tallies, derived from where candidates actually left ----
        # ``generate`` and ``terminal`` always run: everything is validated on
        # the way in, and everything still undecided at the end must leave.
        _check_conservation(len(batch), outcomes)
        result_run = _assemble("finished", entered=len(batch))
        if not dry_run:
            store.append_run(result_run.to_dict())
        return result_run

    try:
        return _pipeline()
    except BaseException as exc:  # re-raised below; a plug-in defect is loud
        # The exception must propagate — a screen that throws is a defect, not a
        # verdict — but the work already done is a *measurement*, and dropping
        # it would drop it out of every conversion rate too. The record is
        # written with the outcomes decided so far and ``state="crashed"``,
        # which the metrics layer counts as an incomplete run.
        if not dry_run:
            missing = len(batch) - len(outcomes)
            crashed = _assemble(
                "crashed",
                entered=len(outcomes),
                attempted=len(batch),
                undecided=missing,
            )
            record = crashed.to_dict()
            record["errors"] = list(crashed.errors) + [
                f"run aborted: {type(exc).__name__}: {exc}"
            ]
            record["aborted_by"] = f"{type(exc).__name__}: {exc}"
            try:
                store.append_run(record)
            except Exception:  # pragma: no cover - the original error wins
                pass
        raise
