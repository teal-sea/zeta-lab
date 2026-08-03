"""discovery.metrics — conversion analytics over the ledger.

Domain-agnostic, like the rest of this layer. It reads records and divides.

Why this module is the point
----------------------------
A discovery funnel without conversion rates is a machine for producing
anecdotes: the operator remembers the two observations that looked exciting and
forgets the four hundred that were already in a textbook. The tables here are
built so the unflattering numbers are the *default* ones — ``already-known`` and
``trivial`` sit next to ``survives`` in the same column, ``cost per survivor``
is computed from recorded wall time, and a lead source that has produced
nothing appears in the table with its cost, rather than not appearing at all.

Where the numbers come from
---------------------------
Everything countable is derived from the **run stream** (``ledger.runs.jsonl``),
because that is the only place a *zero-yield* invocation exists: a generator
that ran for an hour and emitted nothing leaves no candidate record, and a
conversion rate computed without it has the wrong denominator. The candidate
stream supplies the standing *inventory* — what the ledger currently holds, by
verdict — which is a different question and is reported separately.

Two arithmetic rules, applied everywhere
----------------------------------------
1. **An empty denominator gives ``None``, never ``0.0``.** A rate over nothing
   is undefined; reporting it as zero would state that nothing converted, which
   is a claim about a population that does not exist. :func:`rate` is the only
   place division happens, and ``render_text`` prints ``—`` for ``None``.
2. **Deduplication is a lower bound.** Two records of the same observation at
   different resolutions do not collide (``discovery/README.md`` §4, failure
   mode 1), so ``duplicate`` counts are a floor and ``unique`` counts are a
   ceiling. Every report that shows them says so.
"""

from __future__ import annotations

import datetime as _dt
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Final

from discovery.funnel import DISPOSITIONS, STAGES, FunnelRun
from discovery.ledger import Ledger, LedgerView
from discovery.schema import VerdictStatus

__all__ = [
    "rate",
    "StageStat",
    "ScreenStat",
    "GeneratorStat",
    "FunnelReport",
    "CostReport",
    "TimeBucket",
    "funnel_report",
    "generator_scorecard",
    "stage_costs",
    "time_series",
    "render_text",
]

_DASH: Final[str] = "—"


def rate(numerator: float, denominator: float) -> float | None:
    """``numerator / denominator``, or ``None`` when the denominator is empty.

    The single place this module divides. A rate over an empty population is
    undefined, not zero: a funnel that has run nothing has not converted 0 % of
    its leads, it has no leads to have converted.
    """
    if not denominator:
        return None
    return numerator / denominator


def _pct(value: float | None) -> str:
    return _DASH if value is None else f"{value:.1%}"


def _num(value: float | None, spec: str = ".3g") -> str:
    return _DASH if value is None else format(value, spec)


def _coerce(source: "Ledger | LedgerView | str | Path | None") -> LedgerView:
    """Accept a store, a snapshot, a path, or nothing at all."""
    if isinstance(source, LedgerView):
        return source
    if isinstance(source, Ledger):
        return source.view()
    if source is None or isinstance(source, (str, Path)):
        return Ledger(source).view()
    raise TypeError(f"not a ledger, view or path: {type(source).__name__}")


def _finished_runs(view: LedgerView) -> tuple[FunnelRun, ...]:
    """Run records in their final state, parsed. Unfinished runs included.

    A run that never got past ``started`` was killed outright — no record of
    what it did survives, and it contributes only itself to the denominator. A
    run whose plug-in raised writes a ``crashed`` record carrying the outcomes
    it had already decided, so the work it *did* do is counted. Both are kept:
    a run that died is still work that happened.
    """
    return tuple(FunnelRun.from_dict(r) for r in view.latest_runs())


# ---------------------------------------------------------------------------
# The funnel report
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class StageStat:
    """One stage, aggregated over every run in the ledger."""

    stage: str
    entered: int = 0
    left: int = 0
    seconds: float = 0.0

    @property
    def passed(self) -> int:
        return self.entered - self.left

    @property
    def pass_rate(self) -> float | None:
        return rate(self.passed, self.entered)

    @property
    def kill_rate(self) -> float | None:
        return rate(self.left, self.entered)

    @property
    def seconds_per_candidate(self) -> float | None:
        return rate(self.seconds, self.entered)

    def to_dict(self) -> dict[str, Any]:
        return {
            "stage": self.stage,
            "entered": self.entered,
            "left": self.left,
            "passed": self.passed,
            "pass_rate": self.pass_rate,
            "seconds": self.seconds,
        }


def _stage_flow(
    run_stages: Sequence[str], lefts: Mapping[str, int], generated: int
) -> dict[str, tuple[int, int]]:
    """``{stage: (entered, left)}`` for one run, from where candidates left.

    Mirrors :func:`discovery.funnel.run_funnel` exactly: ``generate`` and
    ``terminal`` always run, every other stage runs only if the run asked for
    it, and each stage receives whatever the one before it did not remove.
    """
    flow: dict[str, tuple[int, int]] = {}
    remaining = generated
    stages = set(run_stages) if run_stages else set(STAGES)
    for stage in STAGES:
        runs_here = stage in stages or stage in ("generate", "terminal")
        entered = remaining if runs_here else 0
        left = int(lefts.get(stage, 0))
        flow[stage] = (entered, left)
        if runs_here:
            remaining = entered - left
    return flow


@dataclass(frozen=True, slots=True)
class FunnelReport:
    """Counts and rates at every stage, over the whole ledger."""

    runs: int = 0
    runs_incomplete: int = 0
    dry_runs: int = 0
    invocations: int = 0
    zero_yield_invocations: int = 0
    errored_invocations: int = 0
    skipped_invocations: int = 0
    generated: int = 0
    stages: tuple[StageStat, ...] = ()
    dispositions: Mapping[str, int] = field(default_factory=dict)
    inventory: Mapping[str, int] = field(default_factory=dict)
    seconds: float = 0.0
    generation_seconds: float = 0.0
    screening_seconds: float = 0.0
    unresolved: int = 0
    #: Candidates that entered a run which then crashed and never reached a
    #: disposition **in that run**. The count is reported separately because a
    #: funnel that lost observations has a denominator it cannot justify, and a
    #: report that did not say so would be flattering itself.
    #:
    #: It is a *cumulative, historical* figure read off the crash records, and
    #: it never clears: a crash record cannot be revised, and the queued
    #: candidates were never written, so nothing in the ledger can say whether a
    #: later run re-generated and decided them. So the honest reading is "at
    #: least this much work has at some point fallen out of a run"; where a
    #: later run did re-decide them they *are* counted in ``generated``, and the
    #: two figures then overlap. Over-warning, never under-warning, is the
    #: deliberate direction.
    undecided: int = 0

    # -- derived ----------------------------------------------------------
    @property
    def rates(self) -> dict[str, float | None]:
        """Each disposition as a share of everything generated."""
        return {
            name: rate(self.dispositions.get(name, 0), self.generated)
            for name in DISPOSITIONS
        }

    @property
    def zero_yield_rate(self) -> float | None:
        """Share of invocations that produced no candidate at all.

        A lead source that *raised* produced no candidate either, so it is in
        this numerator as well as in ``errored_invocations``. The two are
        reported side by side rather than netted off: "found nothing" and
        "broke" are different problems and one must not hide inside the other.
        """
        return rate(self.zero_yield_invocations, self.invocations)

    @property
    def candidates_per_invocation(self) -> float | None:
        return rate(self.generated, self.invocations)

    @property
    def survivors(self) -> int:
        return self.dispositions.get("survives", 0)

    @property
    def survival_rate(self) -> float | None:
        return rate(self.survivors, self.generated)

    @property
    def seconds_per_survivor(self) -> float | None:
        return rate(self.seconds, self.survivors)

    def stage(self, name: str) -> StageStat:
        for stat in self.stages:
            if stat.stage == name:
                return stat
        return StageStat(name)

    def to_dict(self) -> dict[str, Any]:
        return {
            "runs": self.runs,
            "runs_incomplete": self.runs_incomplete,
            "dry_runs": self.dry_runs,
            "invocations": self.invocations,
            "zero_yield_invocations": self.zero_yield_invocations,
            "errored_invocations": self.errored_invocations,
            "skipped_invocations": self.skipped_invocations,
            "generated": self.generated,
            "stages": [s.to_dict() for s in self.stages],
            "dispositions": dict(self.dispositions),
            "rates": self.rates,
            "inventory": dict(self.inventory),
            "seconds": self.seconds,
            "generation_seconds": self.generation_seconds,
            "screening_seconds": self.screening_seconds,
            "unresolved": self.unresolved,
            "undecided": self.undecided,
        }

    def render_text(self) -> str:
        lines = ["FUNNEL", "=" * 72]
        if not self.runs and not self.generated:
            lines.append("  no run has been recorded: nothing to report, and no rate")
            lines.append("  is defined over an empty population.")
            if self.inventory:
                inv = "  ".join(f"{k}={v}" for k, v in sorted(self.inventory.items()))
                lines.append(f"  ledger inventory: {inv}")
            if self.unresolved:
                lines.append(
                    f"  {self.unresolved} candidate(s) still 'open' in the ledger: a "
                    "run died before deciding them; re-run to resume."
                )
            return "\n".join(lines)
        lines.append(
            f"  runs {self.runs} ({self.runs_incomplete} incomplete, "
            f"{self.dry_runs} dry)   invocations {self.invocations} "
            f"({self.zero_yield_invocations} yielded nothing = "
            f"{_pct(self.zero_yield_rate)}, of which "
            f"{self.errored_invocations} raised)"
        )
        lines.append(
            f"  total {self.seconds:.2f} s   generation {self.generation_seconds:.2f} s"
            f"   screening {self.screening_seconds:.2f} s"
        )
        lines.append("")
        header = f"  {'stage':<20}{'entered':>9}{'left':>8}{'passed':>8}{'pass %':>9}{'seconds':>10}"
        lines.append(header)
        lines.append("  " + "-" * (len(header) - 2))
        for stat in self.stages:
            lines.append(
                f"  {stat.stage:<20}{stat.entered:>9}{stat.left:>8}{stat.passed:>8}"
                f"{_pct(stat.pass_rate):>9}{stat.seconds:>10.3f}"
            )
        lines.append("")
        lines.append(f"  {'disposition':<20}{'count':>9}{'share':>9}")
        lines.append("  " + "-" * 36)
        rates = self.rates
        # Any key outside the vocabulary is shown, not hidden: a disposition
        # this version does not know is a data error, and a table whose rows do
        # not add up to its own total is how it announces itself.
        shown = (*DISPOSITIONS, *sorted(set(self.dispositions) - set(DISPOSITIONS)))
        for name in shown:
            count = self.dispositions.get(name, 0)
            share = rates.get(name, rate(count, self.generated))
            lines.append(f"  {name:<20}{count:>9}{_pct(share):>9}")
        total_share = "100.0%" if self.generated else _DASH
        lines.append(f"  {'TOTAL generated':<20}{self.generated:>9}{total_share:>9}")
        if self.unresolved:
            lines.append(
                f"  {self.unresolved} candidate(s) still 'open' in the ledger: a run "
                "died before deciding them; re-run to resume."
            )
        if self.undecided:
            lines.append(
                f"  {self.undecided} candidate(s) entered a run that then crashed and "
                "never reached a\n  disposition in that run: they are in no count or "
                "rate above unless a later\n  run re-generated and decided them. The "
                "figure is cumulative and never clears.\n  Re-run to decide them."
            )
        lines.append(
            "  duplicate counts are a lower bound: two records of one observation "
            "at different\n  resolutions do not collide (README §4)."
        )
        if self.inventory:
            inv = "  ".join(f"{k}={v}" for k, v in sorted(self.inventory.items()))
            lines.append(f"  ledger inventory: {inv}")
        return "\n".join(lines)


def funnel_report(ledger: "Ledger | LedgerView | str | Path | None" = None) -> FunnelReport:
    """Counts and rates at every stage of the funnel, over the whole ledger.

    Safe on an empty ledger (every count 0, every rate ``None``) and on a
    single-entry one.
    """
    view = _coerce(ledger)
    runs = _finished_runs(view)
    # ``undecided`` lives only on the raw crash record: ``FunnelRun`` has no
    # field for it, because a completed run never has any. Read it straight
    # off the run stream so a crash cannot quietly shrink the denominator.
    undecided = 0
    for record in view.latest_runs():
        try:
            undecided += max(0, int(record.get("undecided", 0) or 0))
        except (TypeError, ValueError):
            continue

    stage_entered: dict[str, int] = {s: 0 for s in STAGES}
    stage_left: dict[str, int] = {s: 0 for s in STAGES}
    stage_seconds: dict[str, float] = {s: 0.0 for s in STAGES}
    dispositions: dict[str, int] = {name: 0 for name in DISPOSITIONS}

    runs_incomplete = dry_runs = 0
    invocations = zero_yield = errored = skipped = generated = 0
    total_seconds = generation_seconds = screening_seconds = 0.0

    for run in runs:
        if run.state != "finished":
            runs_incomplete += 1
        if run.dry_run:
            dry_runs += 1
        total_seconds += run.seconds
        for report in run.generators:
            if report.skipped:
                skipped += 1
                continue
            invocations += 1
            generation_seconds += report.seconds
            if report.error:
                errored += 1
            if report.produced == 0:
                zero_yield += 1
        lefts: dict[str, int] = {s: 0 for s in STAGES}
        for outcome in run.outcomes:
            generated += 1
            dispositions[outcome.disposition] = (
                dispositions.get(outcome.disposition, 0) + 1
            )
            lefts[outcome.stage] = lefts.get(outcome.stage, 0) + 1
            screening_seconds += outcome.seconds
            stage_left[outcome.stage] = stage_left.get(outcome.stage, 0) + 1
        flow = _stage_flow(run.stages, lefts, len(run.outcomes))
        for stage, (entered, _left) in flow.items():
            stage_entered[stage] = stage_entered.get(stage, 0) + entered
        for tally in run.stage_tallies:
            stage_seconds[tally.stage] = (
                stage_seconds.get(tally.stage, 0.0) + tally.seconds
            )

    inventory: dict[str, int] = {}
    unresolved = 0
    for candidate in view.latest().values():
        status = candidate.verdict.status.value
        inventory[status] = inventory.get(status, 0) + 1
        if candidate.verdict.status is VerdictStatus.OPEN:
            unresolved += 1

    return FunnelReport(
        runs=len(runs),
        runs_incomplete=runs_incomplete,
        dry_runs=dry_runs,
        invocations=invocations,
        zero_yield_invocations=zero_yield,
        errored_invocations=errored,
        skipped_invocations=skipped,
        generated=generated,
        # STAGES first, then anything a hand-edited record named that this
        # version does not know. A stage nobody recognises is a data error, but
        # dropping its count would be a worse one: ``sum(left)`` has to stay
        # equal to ``generated`` or the flow is fiction.
        stages=tuple(
            StageStat(
                stage=s,
                entered=stage_entered.get(s, 0),
                left=stage_left.get(s, 0),
                seconds=stage_seconds.get(s, 0.0),
            )
            for s in (*STAGES, *sorted((set(stage_left) | set(stage_seconds)) - set(STAGES)))
        ),
        dispositions=dispositions,
        inventory=inventory,
        seconds=total_seconds,
        generation_seconds=generation_seconds,
        screening_seconds=screening_seconds,
        unresolved=unresolved,
        undecided=undecided,
    )


# ---------------------------------------------------------------------------
# The scorecard: which lead sources are worth compute
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class GeneratorStat:
    """One lead source, and what its output actually turned into.

    **Every rate has ``produced`` as its denominator** — everything the
    generator emitted *that reached a disposition*, duplicates and malformed
    payloads included. That is the honest denominator for the question the table
    answers ("is this worth the compute?"): a generator that re-emits last
    month's observations has done no work worth counting, and hiding its
    duplicates behind a smaller denominator would flatter it.

    The qualification matters in exactly one case. ``produced`` is counted from
    the run's *outcomes*, not from the generator's own report, and in a run that
    completed those are the same number by the funnel's conservation invariant.
    In a run that **crashed** they are not: candidates queued behind the failure
    reached no disposition, so they are in no rate here. That shortfall is
    reported by :attr:`FunnelReport.undecided`, which is deliberately outside
    every rate and printed beside them — but it is a whole-ledger figure and is
    not attributed per generator, so this column can understate a lead source
    that was interrupted. ``zero_yield`` and ``errored`` come from the generator
    reports and are unaffected.
    """

    generator: str
    versions: tuple[str, ...] = ()
    invocations: int = 0
    zero_yield: int = 0
    errored: int = 0
    produced: int = 0
    duplicate: int = 0
    invalid: int = 0
    known: int = 0
    trivial: int = 0
    refuted: int = 0
    survives: int = 0
    inconclusive: int = 0
    generation_seconds: float = 0.0
    screening_seconds: float = 0.0
    rank: int = 0

    @property
    def seconds(self) -> float:
        """All wall time attributable to this source: generating and screening."""
        return self.generation_seconds + self.screening_seconds

    @property
    def unique(self) -> int:
        """Candidates that were not already in the ledger and were well formed.

        A ceiling, not an exact count: deduplication is a lower bound.
        """
        return self.produced - self.duplicate - self.invalid

    @property
    def duplicate_rate(self) -> float | None:
        return rate(self.duplicate, self.produced)

    @property
    def invalid_rate(self) -> float | None:
        return rate(self.invalid, self.produced)

    @property
    def known_rate(self) -> float | None:
        return rate(self.known, self.produced)

    @property
    def trivial_rate(self) -> float | None:
        return rate(self.trivial, self.produced)

    @property
    def refuted_rate(self) -> float | None:
        return rate(self.refuted, self.produced)

    @property
    def survival_rate(self) -> float | None:
        return rate(self.survives, self.produced)

    @property
    def inconclusive_rate(self) -> float | None:
        return rate(self.inconclusive, self.produced)

    @property
    def unsettled_rate(self) -> float | None:
        """Share that no check which ran managed to settle.

        Deliberately **not** called a novelty rate. The numerator is the
        residue of the checks that were actually performed: a catalogue that
        found no match has established nothing about the wider literature, and
        a share of unmatched payloads is a statement about the catalogue, not
        about the world. It is the tie-break the ranking falls back on when
        nothing has survived anywhere; it is a residue, not an outcome, and an
        unsettled observation can still be refuted and worthless.
        """
        unsettled = (
            self.produced - self.duplicate - self.invalid - self.known - self.trivial
        )
        return rate(unsettled, self.produced)

    @property
    def cost_per_survivor(self) -> float | None:
        """Wall-clock seconds spent per surviving lead. ``None`` if none survived."""
        return rate(self.seconds, self.survives)

    @property
    def survivors_per_second(self) -> float | None:
        return rate(self.survives, self.seconds)

    @property
    def seconds_per_candidate(self) -> float | None:
        return rate(self.seconds, self.produced)

    def to_dict(self) -> dict[str, Any]:
        return {
            "generator": self.generator,
            "versions": list(self.versions),
            "rank": self.rank,
            "invocations": self.invocations,
            "zero_yield": self.zero_yield,
            "errored": self.errored,
            "produced": self.produced,
            "unique": self.unique,
            "duplicate": self.duplicate,
            "invalid": self.invalid,
            "known": self.known,
            "trivial": self.trivial,
            "refuted": self.refuted,
            "survives": self.survives,
            "inconclusive": self.inconclusive,
            "known_rate": self.known_rate,
            "trivial_rate": self.trivial_rate,
            "refuted_rate": self.refuted_rate,
            "survival_rate": self.survival_rate,
            "unsettled_rate": self.unsettled_rate,
            "seconds": self.seconds,
            "generation_seconds": self.generation_seconds,
            "screening_seconds": self.screening_seconds,
            "cost_per_survivor": self.cost_per_survivor,
        }


def generator_scorecard(
    ledger: "Ledger | LedgerView | str | Path | None" = None,
) -> tuple[GeneratorStat, ...]:
    """Per generator: what it produced, what became of it, and what it cost.

    Ranking, stated plainly so nobody has to guess: **survivors per second**,
    descending; ties broken by ``unsettled_rate``, then by name. When no source
    has produced a survivor — which is the expected state — the first key is
    zero everywhere and the table is ranked by the share nothing settled, which
    is a residue of the checks that ran and not a measurement of usefulness.
    """
    view = _coerce(ledger)
    runs = _finished_runs(view)

    acc: dict[str, dict[str, Any]] = {}

    def _slot(name: str) -> dict[str, Any]:
        return acc.setdefault(
            name,
            {
                "versions": set(),
                "invocations": 0,
                "zero_yield": 0,
                "errored": 0,
                "produced": 0,
                "generation_seconds": 0.0,
                "screening_seconds": 0.0,
                **{d: 0 for d in DISPOSITIONS},
            },
        )

    for run in runs:
        for report in run.generators:
            if report.skipped:
                continue
            slot = _slot(report.generator)
            slot["versions"].add(report.version)
            slot["invocations"] += 1
            slot["generation_seconds"] += report.seconds
            if report.error:
                slot["errored"] += 1
            if report.produced == 0:
                slot["zero_yield"] += 1
        for outcome in run.outcomes:
            slot = _slot(outcome.generator)
            if outcome.generator_version:
                slot["versions"].add(outcome.generator_version)
            slot["produced"] += 1
            slot["screening_seconds"] += outcome.seconds
            slot[outcome.disposition] = slot.get(outcome.disposition, 0) + 1

    stats = [
        GeneratorStat(
            generator=name,
            versions=tuple(sorted(str(v) for v in slot["versions"] if v)),
            invocations=slot["invocations"],
            zero_yield=slot["zero_yield"],
            errored=slot["errored"],
            produced=slot["produced"],
            duplicate=slot["duplicate"],
            invalid=slot["invalid"],
            known=slot["known"],
            trivial=slot["trivial"],
            refuted=slot["refuted"],
            survives=slot["survives"],
            inconclusive=slot["inconclusive"],
            generation_seconds=slot["generation_seconds"],
            screening_seconds=slot["screening_seconds"],
        )
        for name, slot in acc.items()
    ]
    stats.sort(
        key=lambda s: (
            -(s.survivors_per_second or 0.0),
            -(s.unsettled_rate or 0.0),
            s.generator,
        )
    )
    from dataclasses import replace as _replace

    return tuple(_replace(s, rank=i + 1) for i, s in enumerate(stats))


def _render_scorecard(stats: Sequence[GeneratorStat]) -> str:
    lines = ["GENERATOR SCORECARD  (which lead sources are worth compute)", "=" * 96]
    if not stats:
        lines.append("  no generator invocation has been recorded.")
        return "\n".join(lines)
    header = (
        f"  {'#':>2} {'generator':<22}{'runs':>5}{'empty':>6}{'made':>6}"
        f"{'dup':>6}{'known':>7}{'triv':>6}{'refut':>7}{'incon':>6}{'surv':>6}"
        f"{'sec':>8}{'sec/surv':>10}"
    )
    lines.append(header)
    lines.append("  " + "-" * (len(header) - 2))
    for stat in stats:
        lines.append(
            f"  {stat.rank:>2} {stat.generator[:22]:<22}{stat.invocations:>5}"
            f"{stat.zero_yield:>6}{stat.produced:>6}"
            f"{_pct(stat.duplicate_rate):>6}{_pct(stat.known_rate):>7}"
            f"{_pct(stat.trivial_rate):>6}{_pct(stat.refuted_rate):>7}"
            f"{_pct(stat.inconclusive_rate):>6}{_pct(stat.survival_rate):>6}"
            f"{stat.seconds:>8.2f}{_num(stat.cost_per_survivor, '.1f'):>10}"
        )
    lines.append(
        "  rates are shares of 'made' (everything emitted, repeats and malformed\n"
        "  payloads included). Ranked by survivors per second, then by the share\n"
        "  no check settled."
    )
    if not any(s.survives for s in stats):
        lines.append(
            "  no source has produced a survivor: the ranking is on the share that\n"
            "  no check settled, which is a residue of the checks that ran — not a\n"
            "  claim that anything is new."
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Where the compute went
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class ScreenStat:
    """One screen or detector: how often, how long, how much it killed."""

    screen: str
    cost: str = ""
    calls: int = 0
    stopped: int = 0
    seconds: float = 0.0

    @property
    def stop_rate(self) -> float | None:
        return rate(self.stopped, self.calls)

    @property
    def seconds_per_call(self) -> float | None:
        return rate(self.seconds, self.calls)

    @property
    def seconds_per_kill(self) -> float | None:
        return rate(self.seconds, self.stopped)

    def to_dict(self) -> dict[str, Any]:
        return {
            "screen": self.screen,
            "cost": self.cost,
            "calls": self.calls,
            "stopped": self.stopped,
            "seconds": self.seconds,
            "stop_rate": self.stop_rate,
            "seconds_per_call": self.seconds_per_call,
        }


@dataclass(frozen=True, slots=True)
class CostReport:
    """Wall time by stage and by screen: where the compute actually went."""

    stages: tuple[StageStat, ...] = ()
    screens: tuple[ScreenStat, ...] = ()
    total_seconds: float = 0.0

    def to_dict(self) -> dict[str, Any]:
        return {
            "stages": [s.to_dict() for s in self.stages],
            "screens": [s.to_dict() for s in self.screens],
            "total_seconds": self.total_seconds,
        }

    def render_text(self) -> str:
        lines = ["STAGE AND SCREEN COSTS", "=" * 72]
        if self.total_seconds == 0.0 and not self.screens:
            lines.append("  nothing has been screened yet.")
            return "\n".join(lines)
        lines.append(f"  {'stage':<20}{'entered':>9}{'seconds':>10}{'s/cand':>10}{'share':>9}")
        lines.append("  " + "-" * 56)
        for stat in self.stages:
            share = rate(stat.seconds, self.total_seconds)
            lines.append(
                f"  {stat.stage:<20}{stat.entered:>9}{stat.seconds:>10.3f}"
                f"{_num(stat.seconds_per_candidate, '.4f'):>10}{_pct(share):>9}"
            )
        if self.screens:
            lines.append("")
            lines.append(
                f"  {'screen':<24}{'cost':>10}{'calls':>7}{'stopped':>9}"
                f"{'stop %':>8}{'seconds':>10}"
            )
            lines.append("  " + "-" * 66)
            for stat in self.screens:
                lines.append(
                    f"  {stat.screen[:24]:<24}{stat.cost:>10}{stat.calls:>7}"
                    f"{stat.stopped:>9}{_pct(stat.stop_rate):>8}{stat.seconds:>10.3f}"
                )
        return "\n".join(lines)


def stage_costs(ledger: "Ledger | LedgerView | str | Path | None" = None) -> CostReport:
    """Wall time by stage and by screen, aggregated over the ledger."""
    view = _coerce(ledger)
    runs = _finished_runs(view)
    report = funnel_report(view)

    screens: dict[str, dict[str, Any]] = {}
    for run in runs:
        for tally in run.screen_tallies:
            slot = screens.setdefault(
                tally.screen, {"cost": tally.cost, "calls": 0, "stopped": 0, "seconds": 0.0}
            )
            slot["cost"] = tally.cost or slot["cost"]
            slot["calls"] += tally.calls
            slot["stopped"] += tally.stopped
            slot["seconds"] += tally.seconds

    ordered = sorted(
        screens.items(), key=lambda kv: (-kv[1]["seconds"], kv[0])
    )
    return CostReport(
        stages=report.stages,
        screens=tuple(
            ScreenStat(
                screen=name,
                cost=str(slot["cost"]),
                calls=int(slot["calls"]),
                stopped=int(slot["stopped"]),
                seconds=float(slot["seconds"]),
            )
            for name, slot in ordered
        ),
        total_seconds=sum(s.seconds for s in report.stages),
    )


# ---------------------------------------------------------------------------
# How it moved over time
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class TimeBucket:
    """One period of the log: what ran, what came out."""

    bucket: str
    runs: int = 0
    invocations: int = 0
    generated: int = 0
    dispositions: Mapping[str, int] = field(default_factory=dict)
    seconds: float = 0.0

    @property
    def survivors(self) -> int:
        return self.dispositions.get("survives", 0)

    @property
    def survival_rate(self) -> float | None:
        return rate(self.survivors, self.generated)

    @property
    def known_rate(self) -> float | None:
        return rate(self.dispositions.get("known", 0), self.generated)

    def to_dict(self) -> dict[str, Any]:
        return {
            "bucket": self.bucket,
            "runs": self.runs,
            "invocations": self.invocations,
            "generated": self.generated,
            "dispositions": dict(self.dispositions),
            "seconds": self.seconds,
            "survival_rate": self.survival_rate,
        }


_BUCKETS: Final[Mapping[str, int]] = {"day": 10, "month": 7, "year": 4, "hour": 13}


def time_series(
    ledger: "Ledger | LedgerView | str | Path | None" = None,
    *,
    bucket: str = "day",
) -> tuple[TimeBucket, ...]:
    """The funnel over time, bucketed by the run's start timestamp.

    ``bucket`` is one of ``hour``, ``day``, ``month``, ``year``. Runs with no
    usable timestamp are collected under ``"unknown"`` rather than dropped.
    Returns an empty tuple for an empty ledger.
    """
    if bucket not in _BUCKETS:
        raise ValueError(f"bucket must be one of {sorted(_BUCKETS)}, got {bucket!r}")
    width = _BUCKETS[bucket]
    view = _coerce(ledger)
    runs = _finished_runs(view)

    acc: dict[str, dict[str, Any]] = {}
    for run in runs:
        stamp = run.started_at or ""
        try:
            _dt.datetime.fromisoformat(stamp)
            key = stamp[:width]
        except ValueError:
            key = "unknown"
        slot = acc.setdefault(
            key,
            {
                "runs": 0,
                "invocations": 0,
                "generated": 0,
                "seconds": 0.0,
                "dispositions": {d: 0 for d in DISPOSITIONS},
            },
        )
        slot["runs"] += 1
        slot["invocations"] += sum(1 for g in run.generators if not g.skipped)
        slot["generated"] += len(run.outcomes)
        slot["seconds"] += run.seconds
        for outcome in run.outcomes:
            slot["dispositions"][outcome.disposition] = (
                slot["dispositions"].get(outcome.disposition, 0) + 1
            )
    return tuple(
        TimeBucket(
            bucket=key,
            runs=slot["runs"],
            invocations=slot["invocations"],
            generated=slot["generated"],
            dispositions=slot["dispositions"],
            seconds=slot["seconds"],
        )
        for key, slot in sorted(acc.items())
    )


def _render_time_series(buckets: Sequence[TimeBucket]) -> str:
    lines = ["OVER TIME", "=" * 72]
    if not buckets:
        lines.append("  no dated run has been recorded.")
        return "\n".join(lines)
    header = (
        f"  {'bucket':<14}{'runs':>6}{'made':>7}{'known':>7}{'refut':>7}"
        f"{'surv':>6}{'surv %':>9}{'seconds':>10}"
    )
    lines.append(header)
    lines.append("  " + "-" * (len(header) - 2))
    for slot in buckets:
        lines.append(
            f"  {slot.bucket:<14}{slot.runs:>6}{slot.generated:>7}"
            f"{slot.dispositions.get('known', 0):>7}"
            f"{slot.dispositions.get('refuted', 0):>7}{slot.survivors:>6}"
            f"{_pct(slot.survival_rate):>9}{slot.seconds:>10.2f}"
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# The console view
# ---------------------------------------------------------------------------


def render_text(
    ledger: "Ledger | LedgerView | str | Path | None" = None,
    *,
    bucket: str = "day",
) -> str:
    """Every table in this module, as one readable console report.

    Safe on an empty ledger: it says so, in each section, rather than printing
    a grid of undefined rates.
    """
    view = _coerce(ledger)
    parts = [
        funnel_report(view).render_text(),
        "",
        _render_scorecard(generator_scorecard(view)),
        "",
        stage_costs(view).render_text(),
        "",
        _render_time_series(time_series(view, bucket=bucket)),
    ]
    if view.path:
        parts.append("")
        parts.append(
            f"  source: {view.path} (private: the ledger is gitignored and holds "
            "unreviewed leads)"
        )
    return "\n".join(parts)
