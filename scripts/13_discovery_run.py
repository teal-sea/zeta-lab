#!/usr/bin/env python
"""The conjecture factory: run the discovery funnel and print what it converted.

What this is
------------
``discovery/`` is a *lead pipeline*, not a proof engine.  Generators mine the
laboratory's already-computed objects for candidate observations; a catalogue
and a battery of screens try to kill them; every step is logged.  This script is
the operator console for one pass of that pipeline:

    generate -> deduplicate -> already-known -> cheap screens -> expensive
    screens -> terminal verdict

The premise the whole design serves is unflattering and load-bearing: **most
numerical "discoveries" are already known or trivial, and a system that does not
measure its own hit rate is measuring its operator's enthusiasm.**  So the
interesting output of this script is not the survivor list.  It is the
*conversion table* — how many candidates each generator produced, what share the
catalogue recognised instantly, what share the screens refuted, and how many
seconds of compute each surviving lead cost.  A generator whose already-known
rate is 100 % is not broken; it is being honest about what a small laboratory
rediscovers.

What a survivor is, and is not
------------------------------
A survivor is an observation that this laboratory's own screens could not kill
with the effort they were given.  It is a **lead**.  It is not a result, not a
theorem, not evidence for the Riemann Hypothesis, and not evidence that anything
is new — every survivor record carries a machine-written ``proof_gap`` saying so.
There is no network here, so nothing was looked up in OEIS, arXiv or
Zentralblatt: "not recognised offline" is the absence of a match, not the
presence of novelty, and the metrics deliberately report an *unsettled* residue
rather than a novelty rate (``discovery/knownness.py``, the integrity rule).

The ledger
----------
Candidates and run records are appended to ``conjectures/`` — a **private,
gitignored** notebook of unreviewed leads.  ``--dry-run`` performs the whole
pass and writes nothing; ``--report`` writes nothing either and simply renders
the dashboard over whatever the ledger already holds.  Deduplication is against
the *whole* ledger, so re-running a generator over ground it has already covered
shows up as a duplicate rate rather than as fresh production — which is the
measurement the ledger exists to make.

Honest scope (docs/08, ``discovery/README.md``).  Nothing this pipeline produces
is evidence for RH.  If a run appears to settle something open, the correct
inference is a bug.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import sys
import time
from pathlib import Path
from typing import Any, Iterator, Mapping, Sequence

# The editable install maps only ``zeta``; ``discovery`` is imported from the
# checkout.  The root is derived from ``__file__`` so that no machine-local path
# is ever baked into a committed file.
REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from ontology.funnel import DISPOSITIONS, FunnelRun, run_funnel  # noqa: E402
from ontology.ledger import Ledger, LedgerView  # noqa: E402
from ontology.metrics import (  # noqa: E402
    funnel_report,
    generator_scorecard,
    render_text,
)
from ontology.registry import Domain  # noqa: E402
from ontology.schema import Candidate  # noqa: E402

__all__ = ["main"]

RULE = "=" * 78

#: The stages, in pipeline order, with the label the waterfall prints for each.
STAGE_LABELS: tuple[tuple[str, str], ...] = (
    ("generate", "generated   emitted by the generators"),
    ("deduplicate", "deduped     already in the ledger"),
    ("knownness", "known       the catalogue recognised it"),
    ("cheap_screens", "screened    cheap screens"),
    ("expensive_screens", "screened    expensive screens"),
    ("terminal", "terminal    promote, or record why not"),
)


def _under(header: str) -> str:
    """A rule as wide as the header it sits under, indented to match it."""
    stripped = header.lstrip()
    pad = len(header) - len(stripped)
    return " " * pad + "-" * len(stripped)


# ---------------------------------------------------------------------------
# small formatting helpers
# ---------------------------------------------------------------------------


def _pct(numerator: float, denominator: float) -> str:
    """A share, or an em dash: a rate over an empty population is undefined."""
    if not denominator:
        return "—"
    return f"{numerator / denominator:.1%}"


def _opt_pct(value: float | None) -> str:
    return "—" if value is None else f"{value:.1%}"


def _opt_num(value: Any, spec: str = ".1f") -> str:
    """A number, an em dash for ``None``, and anything else spelled out.

    A record may legitimately carry a non-numeric effort (``"exact"``), and a
    console that raised on it would hide the record rather than show it.
    """
    if value is None:
        return "—"
    try:
        return format(float(value), spec)
    except (TypeError, ValueError):
        return str(value)


def _short(text: Any, width: int) -> str:
    s = str(text)
    return s if len(s) <= width else s[: width - 1] + "…"


def _wrap(text: str, width: int, indent: str) -> list[str]:
    """Greedy wrap; used for the proof gap and other long prose."""
    words = str(text).split()
    lines: list[str] = []
    current = ""
    for word in words:
        if current and len(current) + 1 + len(word) > width:
            lines.append(indent + current)
            current = word
        else:
            current = f"{current} {word}".strip()
    if current:
        lines.append(indent + current)
    return lines


def _display_path(path: Path) -> str:
    """The ledger location relative to the checkout when it lies inside it."""
    try:
        return str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _is_default_ledger(path: Path) -> bool:
    """Is this the private ``conjectures/`` notebook the .gitignore excludes?"""
    try:
        return Path(path).resolve().parent == (REPO_ROOT / "conjectures").resolve()
    except OSError:  # pragma: no cover - unresolvable path
        return False


# ---------------------------------------------------------------------------
# generator selection and the capturing proxy
# ---------------------------------------------------------------------------


class CapturingGenerator:
    """A generator wrapper that keeps every candidate it passed on.

    The funnel never hands candidate *objects* back — only outcomes — because
    the ledger is where they belong.  A dry run writes no ledger, so without
    this the console could not print a survivor's provenance in the one mode
    where nothing was recorded.  The proxy is written against the
    :class:`~ontology.registry.Generator` protocol alone and knows nothing
    about any subject matter.
    """

    def __init__(self, inner: Any, sink: dict[str, Candidate]) -> None:
        self._inner = inner
        self._sink = sink
        self.name = str(inner.name)
        self.version = str(inner.version)

    def describe(self) -> str:
        return self._inner.describe()

    def generate(self, context: Mapping[str, Any]) -> Iterator[Candidate]:
        for candidate in self._inner.generate(context):
            self._sink[candidate.id] = candidate
            yield candidate

    def refused(self) -> tuple[str, ...]:
        """Payloads built and never emitted, if the generator records them.

        Optional in the plug-in interface, so it is read defensively: a domain
        that does not track its own drops simply reports none.
        """
        return tuple(str(r) for r in (getattr(self._inner, "refused", ()) or ()))


def select_generators(domain: Domain, spec: str) -> tuple[Any, ...]:
    """The generators named by ``spec``; ``all`` means every one of them.

    Names may be given in full (``zeta_constants``) or with the domain prefix
    dropped (``constants``).  An unknown name is an error that lists the
    alternatives — silently running fewer generators than asked for would put a
    wrong denominator into every conversion rate below.
    """
    available = tuple(domain.generators)
    if spec.strip().lower() in ("all", ""):
        return available
    wanted = [part.strip() for part in spec.replace(",", " ").split() if part.strip()]
    by_name: dict[str, Any] = {}
    for gen in available:
        by_name[gen.name] = gen
        prefix = f"{domain.name}_"
        if gen.name.startswith(prefix):
            by_name.setdefault(gen.name[len(prefix) :], gen)
    chosen: list[Any] = []
    unknown: list[str] = []
    for name in wanted:
        gen = by_name.get(name)
        if gen is None:
            unknown.append(name)
        elif gen not in chosen:
            chosen.append(gen)
    if unknown:
        raise SystemExit(
            f"error: no generator named {unknown} in domain {domain.name!r}.\n"
            "       available: " + ", ".join(g.name for g in available)
        )
    if not chosen:
        raise SystemExit("error: --generators selected nothing to run")
    return tuple(chosen)


def parse_context(pairs: Sequence[str]) -> dict[str, Any]:
    """``KEY=VALUE`` pairs into generator knobs.

    ``12`` is an int, ``1.5`` a float, ``true``/``false`` a bool, ``0,1,2`` a
    tuple, anything starting with ``[`` or ``{`` is JSON, and everything else is
    text.  The knobs a domain understands are its own business; this parser
    knows only the syntax.
    """
    context: dict[str, Any] = {}
    for pair in pairs:
        if "=" not in pair:
            raise SystemExit(f"error: --context expects KEY=VALUE, got {pair!r}")
        key, _, raw = pair.partition("=")
        context[key.strip()] = _atom(raw.strip())
    return context


def _atom(raw: str) -> Any:
    if raw[:1] and raw[0] in "[{":  # note: "" is a substring of everything
        try:
            return json.loads(raw)
        except json.JSONDecodeError as exc:
            raise SystemExit(f"error: --context value is not JSON: {raw!r} ({exc})")
    if "," in raw:
        return tuple(_scalar(part.strip()) for part in raw.split(","))
    return _scalar(raw)


def _scalar(raw: str) -> Any:
    low = raw.lower()
    if low in ("true", "false"):
        return low == "true"
    for cast in (int, float):
        try:
            return cast(raw)
        except ValueError:
            continue
    return raw


# ---------------------------------------------------------------------------
# section 0: the header
# ---------------------------------------------------------------------------


def section_header(
    domain: Domain,
    store: Ledger,
    view: LedgerView,
    *,
    mode: str,
    generators: Sequence[Any],
    seed: int,
    limit: int | None,
    context: Mapping[str, Any],
) -> None:
    print(RULE)
    print("THE CONJECTURE FACTORY — a discovery funnel that measures its own hit rate")
    print(RULE)
    print(f"  domain      : {domain.name} v{domain.version}")
    for line in _wrap(domain.description, 62, ""):
        print(f"                {line}")
    print(
        f"  ledger      : {_display_path(store.path)}   "
        f"({len(view.candidates)} candidate records, "
        f"{len(view.latest_runs())} runs on file)"
    )
    if _is_default_ledger(store.path):
        print(
            "                private and gitignored: unreviewed leads, most of "
            "them wrong"
        )
    else:
        print("                (not the default ledger — check it is not committed)")
    print(f"  mode        : {mode}")
    if not mode.startswith("REPORT"):
        names = ", ".join(g.name for g in generators)
        print(f"  generators  : {len(generators)} of {len(domain.generators)}")
        for line in _wrap(names, 60, ""):
            print(f"                {line}")
        print(
            f"  seed        : {seed}     limit: "
            f"{'none' if limit is None else limit}"
        )
        extra = {k: v for k, v in context.items() if k != "seed"}
        if extra:
            print(f"  context     : {extra}")
        missing = domain.missing_checks()
        if missing:
            print(
                "  NOTE        : this domain performs no "
                + ", ".join(missing)
                + " check, so nothing can survive"
            )
    print()


# ---------------------------------------------------------------------------
# section 1: what was generated
# ---------------------------------------------------------------------------


def section_generated(run: FunnelRun, proxies: Sequence[CapturingGenerator]) -> None:
    print("1)  WHAT WAS GENERATED")
    header = (f"    {'generator':<24}{'ver':>6}{'produced':>10}{'refused':>9}"
              f"{'seconds':>10}{'sec/cand':>10}")
    print(header)
    print(_under(header))
    # A generator skipped for the limit never ran, so whatever its ``refused``
    # list holds belongs to an earlier pass and must not be charged to this one.
    refused_by_name = {
        p.name: p.refused()
        for p in proxies
        if not any(r.generator == p.name and r.skipped for r in run.generators)
    }
    total_refused = 0
    for report in run.generators:
        refused = refused_by_name.get(report.generator, ())
        total_refused += len(refused)
        per = report.seconds / report.produced if report.produced else None
        note = ""
        if report.error:
            note = "  RAISED"
        elif report.skipped:
            note = "  skipped (limit)"
        elif report.produced == 0:
            note = "  yielded nothing"
        print(
            f"    {_short(report.generator, 24):<24}{report.version:>6}"
            f"{report.produced:>10}{len(refused):>9}{report.seconds:>10.3f}"
            f"{_opt_num(per, '.3f'):>10}{note}"
        )
    print(_under(header))
    print(
        f"    {'TOTAL':<24}{'':>6}{run.generated:>10}{total_refused:>9}"
        f"{sum(g.seconds for g in run.generators):>10.3f}"
    )
    for name, refused in refused_by_name.items():
        for entry in refused:
            print(f"      refused by {name}:")
            for line in _wrap(entry, 64, ""):
                print(f"        {line}")
    print()
    print("    'refused' counts payloads a generator built and did not emit — a tie in")
    print("    an extremal search, a shape the schema would reject.  They never entered")
    print("    the funnel, so they are in no rate below; a generator that dropped them")
    print("    silently would be flattering its own denominator.  This count is for THIS")
    print("    PASS ONLY: it reaches no run record and no ledger, so --report cannot show")
    print("    it (discovery/README.md §8.2, item 5).")
    if run.errors:
        print("    errors:")
        for err in run.errors:
            print(f"      - {_short(err, 70)}")
    print()


def section_generated_history(stats: Sequence[Any]) -> None:
    """The ledger's whole generation history, for ``--report``."""
    print("1)  WHAT HAS BEEN GENERATED  (whole ledger)")
    if not stats:
        print("    no generator invocation has ever been recorded.")
        print()
        return
    header = (f"    {'generator':<24}{'versions':>12}{'runs':>7}{'empty':>7}"
              f"{'raised':>8}{'produced':>10}{'seconds':>10}")
    print(header)
    print(_under(header))
    for stat in sorted(stats, key=lambda s: s.generator):
        print(
            f"    {_short(stat.generator, 24):<24}"
            f"{_short('/'.join(stat.versions), 12):>12}{stat.invocations:>7}"
            f"{stat.zero_yield:>7}{stat.errored:>8}{stat.produced:>10}"
            f"{stat.generation_seconds:>10.3f}"
        )
    print(_under(header))
    print(
        f"    {'TOTAL':<24}{'':>12}{sum(s.invocations for s in stats):>7}"
        f"{sum(s.zero_yield for s in stats):>7}"
        f"{sum(s.errored for s in stats):>8}"
        f"{sum(s.produced for s in stats):>10}"
        f"{sum(s.generation_seconds for s in stats):>10.3f}"
    )
    print()
    print("    'raised' counts invocations that ended in an exception.  It sits beside")
    print("    'empty' rather than inside it: 'found nothing' and 'broke' are different")
    print("    problems and one must not hide in the other.  A generator that raised")
    print("    part-way through keeps the candidates it had already yielded, so it can")
    print("    be counted in 'raised' and still show a non-zero 'produced'.")
    print("    'empty' counts invocations that produced no candidate at all.  They are")
    print("    logged as runs precisely because a candidate record needs a candidate:")
    print("    without the run stream every conversion rate would have a wrong")
    print("    denominator (discovery/README.md §7.1, §8.1).  There is no 'refused'")
    print("    column here and there cannot be: individual payloads a generator built")
    print("    and declined to emit reach no ledger, so the cumulative view loses them")
    print("    (§8.2, item 5).  Only a live pass can show that count.")
    print()


# ---------------------------------------------------------------------------
# section 2: the waterfall
# ---------------------------------------------------------------------------


def section_waterfall(
    stages: Sequence[Any], dispositions: Mapping[str, int], generated: int
) -> int:
    """Print entered -> deduped -> known -> screened -> surviving.

    ``stages`` is any sequence of stage tallies carrying ``stage``, ``entered``,
    ``left`` and ``seconds``: both :class:`ontology.funnel.StageTally` (one
    run) and :class:`ontology.metrics.StageStat` (the whole ledger) qualify,
    which is why one renderer serves both modes.  Returns the number that came
    out of the far end.
    """
    by_stage = {s.stage: s for s in stages}
    # Survivors leave at the terminal stage too — the funnel records a departure
    # for every candidate, promoted or not — so the terminal row must not count
    # them as removed, or the waterfall would report every run as barren.
    survived = int(dispositions.get("survives", 0))
    print("2)  THE FUNNEL WATERFALL")
    header = (f"    {'stage':<40}{'entered':>8}{'removed':>9}{'remaining':>11}"
              f"{'seconds':>10}")
    print(header)
    print(_under(header))
    remaining = generated
    for key, label in STAGE_LABELS:
        stat = by_stage.get(key)
        if stat is None:
            continue
        removed = stat.left - survived if key == "terminal" else stat.left
        remaining = stat.entered - removed
        print(
            f"    {label:<40}{stat.entered:>8}{removed:>9}{remaining:>11}"
            f"{stat.seconds:>10.3f}"
        )
    print(_under(header))
    print(
        f"    {'SURVIVING — leads, not results':<40}{'':>8}{'':>9}{survived:>11}"
    )
    print()
    counts = {k: int(dispositions.get(k, 0)) for k in DISPOSITIONS}
    extra = {k: int(v) for k, v in dispositions.items() if k not in counts}
    counts.update(extra)
    total = sum(counts.values())
    meaning = {
        "duplicate": "the ledger already had this observation",
        "invalid": "the schema refused it (a generator defect)",
        "known": "the catalogue recognised it",
        "trivial": "one line from something already recorded",
        "refuted": "checked, and false",
        "survives": "nothing killed it — a LEAD",
        "inconclusive": "no verdict, plus the ceiling that was hit",
    }
    header = f"    {'disposition':<20}{'count':>8}{'share':>9}   {'what it means':<42}"
    print(header.rstrip())
    print(_under(header))
    for name, count in counts.items():
        print(
            f"    {name:<20}{count:>8}{_pct(count, total):>9}   "
            f"{meaning.get(name, 'outside this version of the vocabulary')}"
        )
    print(_under(header))
    print(f"    {'TOTAL':<20}{total:>8}{'100.0%' if total else '—':>9}")
    print()
    print("    Count in equals count out: every candidate that entered left with exactly")
    print("    one disposition.  Duplicate counts are a LOWER bound — two records of one")
    print("    observation at different resolutions do not collide (README §4).")
    print()
    return survived


# ---------------------------------------------------------------------------
# section 3: the survivors
# ---------------------------------------------------------------------------


def _irreproducibility(prov: Mapping[str, Any]) -> str:
    """Why :meth:`Provenance.is_reproducible` said no, in words."""
    why: list[str] = []
    if prov["code_revision"] is None:
        why.append("the code revision is unavailable")
    elif prov["code_dirty"]:
        why.append("the working tree was dirty")
    elif prov["code_dirty"] is None:
        why.append("it is not known whether the tree was dirty")
    if prov["stochastic"] and prov["seed"] is None:
        why.append("randomness was used with no seed")
    return "; ".join(why) or "unknown"


def section_survivors(survivors: Sequence[Candidate], *, dry_run: bool, shown: int) -> None:
    print(f"3)  SURVIVORS  ({len(survivors)})   — LEADS, NOT RESULTS")
    print()
    if not survivors:
        print("    Nothing survived.  That is the expected outcome and it is not a")
        print("    failure of the run: the catalogue and the screens exist to produce")
        print("    exactly this, and the conversion table below is the measurement.")
        print()
        return
    for index, candidate in enumerate(survivors[:shown], start=1):
        prov = candidate.provenance.to_dict()
        precision = prov["precision"]
        prec_text = f"{precision['kind']}"
        if precision.get("value") is not None:
            prec_text += f"={precision['value']}"
        if precision.get("backend"):
            prec_text += f" ({precision['backend']})"
        effort = candidate.provenance.precision.effort_digits()
        evidence = dict(candidate.verdict.evidence)
        decided = candidate.verdict.status.value == "survives"
        label = candidate.label or "(no label)"
        print(f"    [{index}] {candidate.id}   kind={candidate.kind.value}")
        print(f"         label        : {_short(label, 60)}")
        for key, value in sorted(dict(candidate.claim).items()):
            print(f"         claim.{key:<7}: {_short(value, 60)}")
        print(f"         generator    : {prov['generator']} v{prov['generator_version']}")
        print(f"         lab object   : {prov['lab_object']}")
        print(f"         parameters   : {_short(prov['parameters'], 60)}")
        print(f"         precision    : {prec_text}  = {effort:g} effort digits")
        print(
            f"         seed         : {prov['seed']}   "
            f"stochastic={'yes' if prov['stochastic'] else 'no'}"
        )
        print(
            f"         code revision: {(prov['code_revision'] or 'unavailable')[:12]}"
            f"{' (dirty)' if prov['code_dirty'] else ''}"
            f"  via {prov['code_revision_source']}"
        )
        print(
            f"         captured     : {prov['captured_at']}   "
            f"generated in {_opt_num(prov['duration_s'], '.3f')} s"
        )
        reproducible = candidate.provenance.is_reproducible()
        why = "" if reproducible else f"  ({_irreproducibility(prov)})"
        print(f"         reproducible : {'yes' if reproducible else 'NO'}{why}")
        if decided:
            screens = ", ".join(evidence.get("screens_passed", ())) or "none"
            print(
                f"         verified at  : "
                f"{_opt_num(evidence.get('verified_effort'), '.4g')} effort digits, "
                f"above the {_opt_num(evidence.get('effort'), '.4g')} it was found at"
            )
            wrapped = _wrap(f"{screens}   (all passed)", 56, "")
            print(f"         screens      : {wrapped[0] if wrapped else 'none'}")
            for line in wrapped[1:]:
                print(f"                        {line}")
            print(
                f"         checks run   : "
                f"{', '.join(evidence.get('checks_run', ())) or 'none recorded'}"
            )
            gap = evidence.get("proof_gap", "")
            if gap:
                print("         proof gap    :")
                for line in _wrap(gap, 62, ""):
                    print(f"           {line}")
        else:
            print(
                "         verdict      : not written (dry run).  The promotion is in"
            )
            print(
                "                        the run record above; the evidence that earns"
            )
            print(
                "                        it — checks run, verified effort, proof gap —"
            )
            print(
                "                        is only produced when the ledger is written."
            )
        print()
    if len(survivors) > shown:
        print(f"    … and {len(survivors) - shown} more (raise --show-survivors)")
        print()
    if dry_run:
        print("    Dry run: these were screened but NOT written.  They are shown from")
        print("    memory, and the ledger does not know they exist.")
        print()


# ---------------------------------------------------------------------------
# section 4: the scorecard
# ---------------------------------------------------------------------------


def section_scorecard(stats: Sequence[Any], *, scope: str) -> None:
    print(f"4)  GENERATOR SCORECARD  ({scope})")
    print("    is this lead source worth the compute?  every rate is a share of 'made'")
    print()
    if not stats:
        print("    no generator invocation has been recorded.")
        print()
        return
    header = (
        f"    {'#':>2} {'generator':<22}{'made':>6}{'dup':>7}{'known':>7}"
        f"{'triv':>7}{'refut':>7}{'incon':>7}{'undec':>7}{'surv':>7}"
        f"{'sec':>9}{'sec/surv':>10}"
    )
    print(header)
    print(_under(header))
    for stat in stats:
        print(
            f"    {stat.rank:>2} {_short(stat.generator, 22):<22}{stat.produced:>6}"
            f"{_opt_pct(stat.duplicate_rate):>7}{_opt_pct(stat.known_rate):>7}"
            f"{_opt_pct(stat.trivial_rate):>7}{_opt_pct(stat.refuted_rate):>7}"
            f"{_opt_pct(stat.inconclusive_rate):>7}{_opt_pct(stat.undecided_rate):>7}"
            f"{_opt_pct(stat.survival_rate):>7}"
            f"{stat.seconds:>9.2f}{_opt_num(stat.cost_per_survivor, '.1f'):>10}"
        )
    made = sum(s.produced for s in stats)
    seconds = sum(s.seconds for s in stats)
    survived = sum(s.survives for s in stats)
    print(_under(header))
    print(
        f"    {'':>2} {'ALL':<22}{made:>6}"
        f"{_pct(sum(s.duplicate for s in stats), made):>7}"
        f"{_pct(sum(s.known for s in stats), made):>7}"
        f"{_pct(sum(s.trivial for s in stats), made):>7}"
        f"{_pct(sum(s.refuted for s in stats), made):>7}"
        f"{_pct(sum(s.inconclusive for s in stats), made):>7}"
        f"{_pct(sum(s.undecided for s in stats), made):>7}"
        f"{_pct(survived, made):>7}{seconds:>9.2f}"
        f"{_opt_num(seconds / survived if survived else None, '.1f'):>10}"
    )
    print()
    print("    Ranked by survivors per second, then by the share no check settled.")
    print("    'sec/surv' is wall-clock seconds per surviving lead — an em dash means")
    print("    the source has produced none, which is not a defect, only a price that")
    print("    has not bought anything yet.")
    print()


# ---------------------------------------------------------------------------
# the closing statement — the point of the whole console
# ---------------------------------------------------------------------------


def closing(survivors: int) -> None:
    print(RULE)
    print("READ THIS BEFORE QUOTING ANY NUMBER ABOVE")
    print(RULE)
    if survivors:
        print(
            f"  *  THE {survivors} SURVIVOR(S) ABOVE ARE LEADS, NOT RESULTS.  A survivor is an"
        )
    else:
        print(
            "  *  NOTHING SURVIVED.  SURVIVORS ARE LEADS, NOT RESULTS.  A survivor is an"
        )
    print("     observation that this laboratory's own screens could not kill with the")
    print("     effort they were given.  It is not a theorem, not a discovery, and not")
    print("     evidence for the Riemann Hypothesis or for anything else; each record")
    print("     carries a proof_gap stating what is missing before it could be one.")
    print("  *  \"NOT RECOGNISED OFFLINE\" IS NOT NOVELTY.  There is no network here, so")
    print("     no OEIS, no arXiv and no Zentralblatt were consulted.  A candidate the")
    print("     small curated catalogue did not match is a candidate it did not match —")
    print("     the absence of a lookup, not the presence of a find.  That is why these")
    print("     tables report an 'unsettled' residue and never a novelty rate.")
    print("  *  The already-known column is the number this console exists to show.  If")
    print("     it is not the largest one, the catalogue is too small — that is the")
    print("     first hypothesis, ahead of the leads being good.")
    print(RULE)


# ---------------------------------------------------------------------------
# the two modes
# ---------------------------------------------------------------------------


def do_report(store: Ledger, *, shown: int, dashboard: bool) -> int:
    view = store.view()
    report = funnel_report(view)
    stats = generator_scorecard(view)
    section_generated_history(stats)
    if not report.runs and not report.generated:
        print("2)  THE FUNNEL WATERFALL")
        print("    no run has been recorded: nothing to report, and no rate is defined")
        print("    over an empty population.")
        print()
    else:
        section_waterfall(report.stages, report.dispositions, report.generated)
    survivors = store.query(status="survives")
    section_survivors(list(survivors), dry_run=False, shown=shown)
    section_scorecard(stats, scope="whole ledger")
    if dashboard:
        print(RULE)
        print("APPENDIX — ontology.metrics.render_text()")
        print(RULE)
        print(render_text(view))
        print()
    closing(len(survivors))
    return len(survivors)


def do_run(
    domain: Domain,
    store: Ledger,
    *,
    generator_spec: str,
    limit: int | None,
    dry_run: bool,
    seed: int,
    context: Mapping[str, Any],
    shown: int,
    dashboard: bool,
) -> FunnelRun:
    chosen = select_generators(domain, generator_spec)
    captured: dict[str, Candidate] = {}
    proxies = tuple(CapturingGenerator(gen, captured) for gen in chosen)
    scoped = dataclasses.replace(domain, generators=proxies)

    ctx = dict(context)
    ctx["seed"] = seed

    view = store.view()
    section_header(
        domain,
        store,
        view,
        mode="DRY RUN (nothing is written)" if dry_run else "LIVE (appends to the ledger)",
        generators=chosen,
        seed=seed,
        limit=limit,
        context=ctx,
    )

    try:
        run = run_funnel(scoped, limit=limit, ledger=store, dry_run=dry_run, context=ctx)
    except BaseException:
        # The exception is re-raised, deliberately: a screen that throws is a
        # defect, not a verdict, and a console that swallowed it would turn a
        # broken pipeline into a quiet zero. What is added here is the one thing
        # the traceback does not say — that the accounting survived.
        print()
        print(RULE)
        print("THE RUN DID NOT COMPLETE — a plug-in raised.  The exception follows.")
        print(RULE)
        if not dry_run:
            print("  The run record was already written with state='crashed' and the")
            print("  outcomes it had decided, so the work it did stays in the funnel's")
            print("  denominators.  The candidates queued behind the failure reached no")
            print("  disposition and are in no rate; --report prints that count on its")
            print("  own line.  Re-running decides them.")
        else:
            print("  Nothing was written: a dry run keeps no record, so this run is in")
            print("  no denominator at all.")
        print(RULE)
        raise

    section_generated(run, proxies)
    section_waterfall(run.stage_tallies, run.dispositions(), run.generated)
    # Prefer the written record: it carries the verdict the funnel decided, which
    # the object captured at generation time cannot (it was still ``open`` then).
    # A dry run wrote nothing, so it falls back to the captured object and says so.
    decided = {} if dry_run else store.latest()
    survivors = [
        decided.get(cid) or captured[cid]
        for cid in run.survivors()
        if cid in decided or cid in captured
    ]
    section_survivors(survivors, dry_run=dry_run, shown=shown)
    # The scorecard for *this run only*: the metrics layer is handed a view
    # holding one run record, so the arithmetic is the same code that computes
    # the cumulative table under --report, not a second implementation of it.
    section_scorecard(
        generator_scorecard(LedgerView(runs=(run.to_dict(),))),
        scope="this run",
    )
    if dry_run:
        print("    (--dry-run: this run is NOT in the ledger, so it is in no cumulative")
        print("     rate.  Run without --dry-run, then --report, for the whole history.)")
        print()
    if dashboard:
        print(RULE)
        print("APPENDIX — ontology.metrics.render_text() over the whole ledger")
        print(RULE)
        print(render_text(store.view()))
        print()
    closing(len(run.survivors()))
    return run


# ---------------------------------------------------------------------------
# entry point
# ---------------------------------------------------------------------------


class _HelpFormatter(argparse.ArgumentDefaultsHelpFormatter):
    """Show defaults, but leave the worked examples on the lines they were written."""

    def _fill_text(self, text: str, width: int, indent: str) -> str:
        if text.lstrip().startswith("examples:"):
            return "".join(indent + line for line in text.splitlines(keepends=True))
        return super()._fill_text(text, width, indent)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run one pass of the discovery funnel over a laboratory domain and "
            "print the whole conversion table.  Generators mine already-computed "
            "objects for candidate observations (constants that might have a "
            "closed form, growth rates, relations, records over a bounded "
            "search, universal claims about an enumerated family); the "
            "candidates are deduplicated against the ledger, offered to an "
            "already-known catalogue, then to cheap and expensive screens that "
            "try to refute them; whatever nothing killed is recorded as a "
            "SURVIVOR.  The output is, in order: what each generator produced, "
            "the funnel waterfall (generated -> deduped -> known -> screened -> "
            "surviving), the survivors with full provenance, and the generator "
            "scorecard (candidates made, already-known rate, refuted rate, "
            "survival rate, seconds per survivor).  The scorecard is the point: "
            "most numerical 'discoveries' are already known or trivial, and a "
            "funnel that does not measure its own hit rate is measuring its "
            "operator's enthusiasm.  A SURVIVOR IS A LEAD, NOT A RESULT -- "
            "nothing here is evidence for the Riemann Hypothesis, and because "
            "there is no network, 'not recognised offline' is the absence of a "
            "lookup and never a claim of novelty.  The ledger lives in "
            "conjectures/, which is gitignored: it is a private notebook of "
            "unreviewed leads."
        ),
        formatter_class=_HelpFormatter,
        epilog=(
            "examples:\n"
            "  13_discovery_run.py --dry-run\n"
            "        a full pass over every generator; nothing is written\n"
            "  13_discovery_run.py --generators constants,relations --limit 8\n"
            "        two lead sources, at most eight candidates\n"
            "  13_discovery_run.py --context xi_points=0,1,2\n"
            "        deliberately ask for observations the catalogue does not cover\n"
            "  13_discovery_run.py --report\n"
            "        no generation at all: the dashboard over the existing ledger\n"
        ),
    )
    parser.add_argument(
        "--generators",
        default="all",
        metavar="all|NAMES",
        help="comma- or space-separated generator names ('constants' and "
             "'zeta_constants' both work), or 'all'",
    )
    parser.add_argument(
        "--limit", type=int, default=None, metavar="N",
        help="stop drawing candidates after N of them (generators are consulted "
             "in order; the rest are recorded as skipped)",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="generate and screen exactly as normal, write nothing at all -- "
             "this is how to find out what a run would cost",
    )
    parser.add_argument(
        "--report", action="store_true",
        help="skip generation entirely; print the metrics dashboard over the "
             "existing ledger",
    )
    parser.add_argument(
        "--seed", type=int, default=None, metavar="S",
        help="seed recorded in every candidate's provenance and used by the "
             "stochastic generators (default: the domain's own)",
    )
    parser.add_argument(
        "--ledger", default=None, metavar="PATH",
        help="ledger file (default: the private, gitignored conjectures/ledger.jsonl)",
    )
    parser.add_argument(
        "--domain", default="zeta", metavar="NAME",
        help="which registered laboratory domain to run",
    )
    parser.add_argument(
        "--context", action="append", default=[], metavar="KEY=VALUE",
        help="generator knob, repeatable; e.g. xi_points=0,1,2 or n_lambda=5",
    )
    parser.add_argument(
        "--show-survivors", type=int, default=10, metavar="N",
        help="how many survivors to print in full",
    )
    parser.add_argument(
        "--dashboard", action="store_true",
        help="also print ontology.metrics.render_text(): stage costs, screen "
             "costs and the funnel over time",
    )
    parser.add_argument(
        "--list", action="store_true",
        help="list the domain's generators, screens and detectors, then exit",
    )
    args = parser.parse_args(argv)

    if args.report and args.dry_run:
        parser.error("--report writes nothing and runs nothing; --dry-run is redundant")

    t0 = time.time()

    # Importing the domain module registers it. It is imported here rather than
    # at module scope so that --help costs nothing (the zeta domain drags in
    # mpmath, numpy and the whole laboratory package).
    from ontology.domains import zeta_domain  # registers the laboratory domain
    from ontology.registry import DomainError, get_domain

    domain_module: Any = zeta_domain if args.domain == zeta_domain.DOMAIN_NAME else None

    try:
        domain = get_domain(args.domain)
    except DomainError as exc:  # the message already names the alternatives
        raise SystemExit(f"error: {exc}")

    if args.list:
        print(domain.describe())
        return 0

    # Ledger(None) is the default, private, gitignored location.
    store = Ledger(args.ledger)

    if args.report:
        section_header(
            domain, store, store.view(), mode="REPORT (read-only)",
            generators=(), seed=0, limit=None, context={},
        )
        do_report(store, shown=args.show_survivors, dashboard=args.dashboard)
        print(f"[{time.time() - t0:.1f} s]")
        return 0

    # A domain may publish its own default seed; the console prefers it so that
    # a run with no --seed reproduces the domain's documented behaviour rather
    # than a number invented here.
    seed = args.seed
    if seed is None:
        seed = int(getattr(domain_module, "DEFAULT_SEED", 0))
    do_run(
        domain,
        store,
        generator_spec=args.generators,
        limit=args.limit,
        dry_run=args.dry_run,
        seed=seed,
        context=parse_context(args.context),
        shown=args.show_survivors,
        dashboard=args.dashboard,
    )
    print(f"[{time.time() - t0:.1f} s]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
