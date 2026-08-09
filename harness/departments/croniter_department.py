"""Department #4: cron schedule semantics — the first foreign-domain subject.

The subject is a frozen implementation of union day-of-month/day-of-week
semantics for cron expressions carrying the ``#`` (nth weekday) and ``W``
(nearest weekday) special forms — a feature added to the ``croniter`` library
(vendored at ``croniter_fixtures/``, commit pinned there). Nothing in this
department knows anything the laboratory computes; it is here to measure
``ROADMAP.md`` known gap #1 from the other side: can the *unchanged*
protocol referee a subject born outside this repository?

Two things distinguish this department historically:

* the subject and its rivals come from a codebase this repository had never
  seen before 2026-08-08;
* the reference battery content was first authored *blind* by a party
  independent of the implementer, then calibrated against five planted
  mutants (5/5 caught). The instruments below are the in-repo re-expression
  of that calibration, with every mutant carried as an exact source patch.

Instrument honesty rules observed here (the sham-battery lessons):

* payloads expose **behavior only** — a claim gets a callable, never a
  labelled record it could read instead of measuring;
* the oracle is independent: plain ``calendar`` arithmetic, no call into the
  subject;
* lesion magnitudes are **measured at import** (share of probe outputs the
  patch changes), never asserted;
* the detector runs bounded probes only (fixed call counts, fixed windows),
  so a lesion that makes iteration non-monotonic is *caught*, not hung on.

The four instruments consume different payload shapes, which
``harness.protocol`` explicitly permits (see ``run_ablation``'s docstring):
claims get the schedule callable; ablation and nulls act on the probe case
list; lesions act on the implementation *source text*.
"""

from __future__ import annotations

import calendar
import datetime as dt
import types

from harness.protocol import (
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
    register_department,
)
from harness.provenance import Provenance

from harness.departments.croniter_fixtures import FROZEN_COMMIT, frozen_source

# ---------------------------------------------------------------------------
# Loading implementations: source text -> module object
# ---------------------------------------------------------------------------

_FROZEN = frozen_source()


def _load(source: str, name: str) -> types.ModuleType:
    mod = types.ModuleType(name)
    mod.__dict__["__name__"] = name
    exec(compile(source, name, "exec"), mod.__dict__)
    return mod


def _patched(source: str, old: str, new: str, label: str) -> str:
    n = source.count(old)
    if n != 1:
        raise AssertionError(f"{label}: patch anchor matched {n} times, expected 1")
    return source.replace(old, new)


# ---------------------------------------------------------------------------
# The five calibration mutants, as exact source patches (from the 2026-08-08
# calibration run; M2/M3 serve as rivals, M1/M4/M5 as lesions)
# ---------------------------------------------------------------------------

_M1 = (  # default #/W backward-compatibility regression
    "                clean_split = not nth_weekday_of_month and not self.nearest_weekday",
    "                clean_split = True",
)
_M2 = (  # inverted forward combiner: naive union, non-monotonic iteration
    "                if is_prev:\n"
    "                    return t1 if t1 > t2 else t2\n"
    "                return t1 if t1 < t2 else t2",
    "                if is_prev:\n"
    "                    return t1 if t1 > t2 else t2\n"
    "                return t1 if t1 > t2 else t2",
)
_M3 = (  # '#'/'W' side-contamination during the union split
    "                    dom_side_nth: dict[int, set[int]] = {}\n"
    "                    dow_side_nearest: set[int] = set()",
    "                    dom_side_nth = nth_weekday_of_month\n"
    "                    dow_side_nearest = self.nearest_weekday",
)
_M4 = (  # off-by-one nth acceptance: backward jumps, re-emission at overlaps
    "                        candidate = c[n - 1]\n"
    "                    if (is_prev and candidate <= d.day) or (not is_prev and d.day <= candidate):",
    "                        candidate = c[n - 1]\n"
    "                    if (is_prev and candidate <= d.day) or (not is_prev and d.day - 1 <= candidate):",
)
_M5 = (  # flag honored by the iterator, silently ignored by croniter_range
    "        expand_from_start_time=expand_from_start_time,\n"
    "        day_or_union=day_or_union,\n    )",
    "        expand_from_start_time=expand_from_start_time,\n"
    "        day_or_union=False,\n    )",
)


# ---------------------------------------------------------------------------
# The independent oracle: plain calendar arithmetic, no subject calls
# ---------------------------------------------------------------------------

_MON, _FRI = 0, 4  # datetime.weekday() numbering


def _nth_weekday(year: int, month: int, weekday: int, n: int) -> dt.date | None:
    days = [
        d
        for d in calendar.Calendar().itermonthdates(year, month)
        if d.month == month and d.weekday() == weekday
    ]
    return days[n - 1] if len(days) >= n else None


def _nearest_weekday(year: int, month: int, day: int) -> dt.date | None:
    last = calendar.monthrange(year, month)[1]
    if day > last:
        return None
    d = dt.date(year, month, day)
    if d.weekday() < 5:
        return d
    if d.weekday() == 5:  # Saturday -> preceding Friday, unless it leaves the month
        prev = d - dt.timedelta(days=1)
        return prev if prev.month == month else d + dt.timedelta(days=2)
    nxt = d + dt.timedelta(days=1)  # Sunday -> following Monday, unless it leaves
    return nxt if nxt.month == month else d - dt.timedelta(days=2)


def _collect(start: dt.datetime, n: int, member) -> tuple[dt.datetime, ...]:
    out, day = [], start.date() + dt.timedelta(days=1)
    while len(out) < n:
        if member(day):
            out.append(dt.datetime(day.year, day.month, day.day))
        day += dt.timedelta(days=1)
    return tuple(out)


_START = dt.datetime(2024, 1, 1)

#: Union-mode probe cases: (expr, start, n, expected-from-oracle)
PROBES: tuple[tuple[str, dt.datetime, int, tuple[dt.datetime, ...]], ...] = (
    (
        "0 0 10 * fri#2",
        _START,
        6,
        _collect(
            _START, 6,
            lambda d: d.day == 10 or d == _nth_weekday(d.year, d.month, _FRI, 2),
        ),
    ),
    (
        "0 0 15W * mon",
        _START,
        8,
        _collect(
            _START, 8,
            lambda d: d.weekday() == _MON or d == _nearest_weekday(d.year, d.month, 15),
        ),
    ),
    (
        "0 0 31 2 fri#2",
        _START,
        3,
        _collect(
            _START, 3,
            lambda d: d.month == 2 and d == _nth_weekday(d.year, d.month, _FRI, 2),
        ),
    ),
)

#: Default-mode probe: with day_or_union OFF this expression must raise
#: (unsatisfiable day-of-month with '#’ present) — pinned upstream behavior.
DEFAULT_RAISE_EXPR = "0 0 31 2 fri#2"

#: Bounded croniter_range probe (fixed window, hang-proof) and its oracle.
RANGE_EXPR, RANGE_STOP = "0 0 10 * fri#2", dt.datetime(2024, 1, 31)
RANGE_EXPECTED = tuple(
    d for d in PROBES[0][3] if d <= RANGE_STOP
)


# ---------------------------------------------------------------------------
# Subjects — target and rivals expose one thing: behavior
# ---------------------------------------------------------------------------


class _Implementation:
    """A candidate implementation. ``payload()`` returns a schedule callable
    and nothing else — no fields a claim could read instead of measuring."""

    def __init__(self, name: str, source: str, blurb: str) -> None:
        self.name = name
        self._source = source
        self._blurb = blurb
        self._mod: types.ModuleType | None = None

    def describe(self) -> str:
        return self._blurb

    def _module(self) -> types.ModuleType:
        if self._mod is None:
            self._mod = _load(self._source, f"croniter_dept_{self.name}")
        return self._mod

    def payload(self):
        mod = self._module()

        def schedule(expr: str, start: dt.datetime, n: int, union: bool = True):
            it = mod.croniter(expr, start, ret_type=dt.datetime, day_or_union=union)
            return tuple(it.get_next() for _ in range(n))

        return schedule


TARGET = _Implementation(
    "frozen-implementation",
    _FROZEN,
    f"the frozen day_or_union implementation, upstream commit {FROZEN_COMMIT[:8]}",
)
RIVALS = (
    _Implementation(
        "inverted-combiner",
        _patched(_FROZEN, *_M2, label="M2"),
        "same API and claim, but the forward union combiner takes the farther side",
    ),
    _Implementation(
        "side-contaminated-union",
        _patched(_FROZEN, *_M3, label="M3"),
        "same API and claim, but each union side stays constrained by the other's special form",
    ),
)


# ---------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------


def accepts_union_flag(schedule) -> bool:
    """Fires when the implementation accepts the day_or_union API at all.

    True of the target and of every rival — the calibration claim the battery
    must kill: presence of the API says nothing about its semantics."""
    try:
        schedule("0 0 10 * fri#2", _START, 1, union=True)
    except TypeError:
        return False
    except Exception:
        return True  # accepted the flag; later failure is a semantics question
    return True


def matches_independent_oracle(schedule) -> bool:
    """Fires when every union-mode probe equals the calendar oracle exactly."""
    try:
        return all(schedule(expr, start, n) == expected for expr, start, n, expected in PROBES)
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Decoys — substitute the probe set, keep its shape
# ---------------------------------------------------------------------------

_PROBE_EXPRS = tuple(p[0] for p in PROBES)


class _DegenerateExpressions:
    name = "degenerate-expressions"
    probe = list(_PROBE_EXPRS)

    def describe(self) -> str:
        return "replaces every probe expression with '0 0 * * *'; shape kept, semantics removed"

    def substitute(self, exprs):
        return ["0 0 * * *" for _ in exprs]


class _SpecialFormsStripped:
    name = "special-forms-stripped"
    probe = list(_PROBE_EXPRS)

    def describe(self) -> str:
        return "strips '#n' and 'W' from every probe expression — the substance under test"

    def substitute(self, exprs):
        out = []
        for e in exprs:
            e = e.replace("W", "")
            e = e.split("#")[0] if "#" in e else e
            out.append(e)
        return out


def probe_distinguishing_power(exprs) -> float:
    """How many of ``exprs`` separate the target from the sharpest rival.

    The ablation measure: a probe set whose expressions cannot distinguish a
    correct union from a contaminated one has no substantive content, and a
    measurement that does not collapse when the special forms are stripped
    was never reading them."""
    target, rival = TARGET.payload(), RIVALS[1].payload()
    count = 0
    for expr in exprs:
        try:
            if target(expr, _START, 6) != rival(expr, _START, 6):
                count += 1
        except Exception:
            count += 1  # an expression only one side can answer still separates
    return float(count)


# ---------------------------------------------------------------------------
# Surrogates — date sequences with no cron semantics at all
# ---------------------------------------------------------------------------


class _FixedStrideNull:
    name = "fixed-stride-null"

    def describe(self) -> str:
        return "every third day from the probe start — a scheduler with no cron logic"

    def sample(self):
        return tuple(_START + dt.timedelta(days=3 * k) for k in range(1, 7))


class _MonthStartNull:
    name = "month-start-null"

    def describe(self) -> str:
        return "the first of each month — calendar structure, no expression semantics"

    def sample(self):
        return tuple(dt.datetime(2024, m, 1) for m in range(1, 7))


def oracle_agreement(dates) -> float:
    """Share of the first union probe's oracle dates reproduced by ``dates``."""
    expected = PROBES[0][3]
    return sum(1 for d in expected if d in tuple(dates)) / len(expected)


# ---------------------------------------------------------------------------
# Lesions — the calibration mutants as source patches, magnitudes measured
# ---------------------------------------------------------------------------


def _behavior_fingerprint(source: str) -> tuple:
    """Bounded, hang-proof behavioral sample of an implementation.

    Fixed call counts only; monotonicity violations are recorded as values
    rather than looped on, so a lesion that makes iteration jump backward is
    measured, not waited for."""
    mod = _load(source, "croniter_dept_probe")
    points = []
    for expr, start, n, _ in PROBES:
        try:
            it = mod.croniter(expr, start, ret_type=dt.datetime, day_or_union=True)
            points.extend(it.get_next() for _ in range(n))
        except Exception as exc:
            points.append(type(exc).__name__)
    try:  # default mode must raise here (upstream-pinned behavior)
        it = mod.croniter(DEFAULT_RAISE_EXPR, _START, ret_type=dt.datetime)
        points.append(tuple(it.get_next() for _ in range(2)))
    except Exception as exc:
        points.append(type(exc).__name__)
    try:  # bounded range probe: fixed n, never iterate-until-stop
        it = mod.croniter(RANGE_EXPR, _START, ret_type=dt.datetime, day_or_union=True)
        got = tuple(it.get_next() for _ in range(len(RANGE_EXPECTED)))
        points.append(("range-oracle-ok", got == RANGE_EXPECTED))
        # croniter_range iterates until it passes ``stop`` — under a lesion
        # that jumps backward it would never get there, so pull from the
        # generator a bounded number of times instead of exhausting it.
        gen = mod.croniter_range(_START, RANGE_STOP, RANGE_EXPR, day_or_union=True)
        rng = []
        for _ in range(len(RANGE_EXPECTED) + 3):
            try:
                rng.append(next(gen))
            except StopIteration:
                break
        points.append(("croniter_range", tuple(rng)))
    except Exception as exc:
        points.append(type(exc).__name__)
    return tuple(points)


_FROZEN_FINGERPRINT = _behavior_fingerprint(_FROZEN)


def _measured_magnitude(patched_source: str) -> float:
    """Share of fingerprint points the patch changes — measured, not asserted."""
    lesioned = _behavior_fingerprint(patched_source)
    total = max(len(_FROZEN_FINGERPRINT), len(lesioned))
    same = sum(1 for a, b in zip(_FROZEN_FINGERPRINT, lesioned) if a == b)
    return round((total - same) / total, 4)


class _SourcePatchLesion:
    """A planted violation: an exact 1–2 line patch to the frozen source."""

    probe = _FROZEN

    def __init__(self, name: str, patch: tuple[str, str], blurb: str) -> None:
        self.name = name
        self._old, self._new = patch
        self._blurb = blurb
        self.magnitude = _measured_magnitude(
            _patched(_FROZEN, self._old, self._new, label=name)
        )

    def describe(self) -> str:
        return f"{self._blurb} (measured magnitude {self.magnitude})"

    def apply(self, source: str) -> str:
        return _patched(source, self._old, self._new, label=self.name)


LESIONS = (
    _SourcePatchLesion(
        "default-compat-regression", _M1,
        "makes the union split unconditionally clean, changing default #/W error semantics",
    ),
    _SourcePatchLesion(
        "nth-overlap-reemission", _M4,
        "off-by-one nth acceptance: backward jumps and re-emission near overlaps",
    ),
    _SourcePatchLesion(
        "range-ignores-flag", _M5,
        "day_or_union honored by the iterator but silently dropped by croniter_range",
    ),
)


def oracle_mismatch_detector(source: str) -> bool:
    """Fires when an implementation's bounded fingerprint deviates from frozen."""
    return _behavior_fingerprint(source) != _FROZEN_FINGERPRINT


DETECTORS = (
    NamedDetector(
        name="fingerprint_mismatch",
        fires=oracle_mismatch_detector,
        probe=_FROZEN,
        note=(
            "bounded behavioral fingerprint against the frozen implementation "
            "(fixed pulls, never iterate-until-done — the hang lesson); fires on "
            "all three source-patch lesions, quiet on the frozen source"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The department
# ---------------------------------------------------------------------------

REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="accepts_union_flag",
        claim=accepts_union_flag,
        distinguishes=False,
        note="true of the target and both rivals: an API's presence proves nothing "
        "about its semantics — the battery must kill this",
    ),
    ReferenceClaim(
        name="matches_independent_oracle",
        claim=matches_independent_oracle,
        distinguishes=True,
        note="exact agreement with a calendar-arithmetic oracle that never calls "
        "the subject; fires for the frozen implementation only",
    ),
)

BATTERY = Battery(
    name="croniter-battery",
    target=TARGET,
    rivals=RIVALS,
    decoys=(_DegenerateExpressions(), _SpecialFormsStripped()),
    surrogates=(_FixedStrideNull(), _MonthStartNull()),
    lesions=LESIONS,
    notes="battery content first authored blind by a party independent of the "
    "implementer, then calibrated against five planted mutants (5/5 caught, "
    "2026-08-08); rivals and lesions here are those exact mutants as source "
    "patches, with magnitudes measured at import",
)

DEPARTMENT = Department(
    name="croniter",
    summary="cron schedule union semantics under '#' and 'W' — the first "
    "foreign-domain subject, refereed by the unchanged protocol",
    battery=BATTERY,
    door="docs/doors/croniter.md",
    modules=("harness.departments.croniter_fixtures",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "exact agreement with a calendar-arithmetic oracle on the bounded probe "
        "set, for the byte-pinned commit only; says nothing about other "
        "expressions, other versions, or unbounded iteration"
    ),
    provenance=Provenance(
        authored_by=(
            "reference battery content first authored blind by a party independent "
            "of the implementer (2026-08-08); in-repo instruments are the "
            "implementing process's re-expression, admitted because they reproduce "
            "the independent calibration's verdicts"
        ),
        authored_on="2026-08-08",
        independent_of_subject_author=True,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        notes=(
            "the five planted mutants were caught 5/5 in the blind calibration; "
            "the oracle is plain calendar arithmetic with no call into the subject"
        ),
    ),
)

register_department(DEPARTMENT, replace=True)
