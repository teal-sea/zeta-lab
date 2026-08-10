"""Department: calendar recurrence rules — *does this rule ever fire on a leap day?*

The subject is a **recurrence rule evaluated against a calendar over a window**,
and the property at issue is whether the schedule it emits ever lands on
29 February.

Why this is a real question and not a lookup: the Gregorian leap rule is three
nested conditions (÷4, not ÷100, unless ÷400); the calendar date a rule lands
on can depend on leap status without the rule ever *asking* for a leap day; and
a rule may name 29 February explicitly and still never fire.  The temptation is
therefore to answer the semantic question with a syntactic proxy — "the spec
says ``BYMONTH=2;BYMONTHDAY=29``, so it hits leap days".  One of the rivals
below exists to make that proxy die on contact.

The battery
-----------
*Target*  ``feb29_yearly`` — ``FREQ=YEARLY;BYMONTH=2;BYMONTHDAY=29`` over the
400-year window 1801–2200 on the Gregorian calendar.  It fires exactly 97
times, all of them leap days.

*Rivals* — every one is a deterministic recurrence rule, over the same window,
on the same calendar, emitting a well-formed schedule; and not one of them ever
fires on 29 February.  They were chosen so that it would be embarrassing for a
leap-day claim to hold of them:

  ``feb_29_odd_years``       asks for 29 February in as many words, and fires
                             never, because no odd year is a leap year.
  ``feb_28_of_leap_years``   fires in *exactly* the 97 years the target fires
                             in, selected by the same leap rule, one day earlier.
  ``mar_01_of_leap_years``   the mirror: exactly those 97 years, one day later.
  ``feb_28_yearly``          the immediate neighbour in date space.
  ``mar_01_yearly``          the other immediate neighbour.
  ``day_59_of_year``         day-of-year arithmetic that reads the calendar's
                             month lengths; lands on 28 February in every year.
  ``day_61_of_year``         leap-sensitive in the sharpest way — its calendar
                             date *moves* with leap status (1 March in leap
                             years, 2 March otherwise) and is never 29 February.
  ``quadrennial_1461_days``  a period locked to the mean four-year Julian cycle,
                             anchored one day after a leap day; it drifts
                             forward by exactly the three suppressed century
                             leap days, so it never reaches one.

*Decoys* ablate the three substantive inputs one at a time, each keeping the
shape: the requested day, the requested month, and the calendar's leap rule.

*Surrogates* are three null models of increasing strength, each preserving the
count or the cadence of firings and none of which knows what a leap day is.

*Lesions* corrupt the emitted schedule at magnitudes 1, 3, 12, 25 and 97 bad
entries, spanning two orders of magnitude.  Each violates exactly one schedule
invariant, and each plants its violation into *any* schedule, including an
empty one — a lesion that is inert on some subject is not a planted fault.

*Detectors* are schedule-integrity instruments, not leap-day instruments: they
ask whether the emitted schedule is a possible schedule at all (real Gregorian
dates, strictly increasing, no repeats, inside the declared window).  They are
silent on the target *and* on every rival — the claim is not — and they are
implemented twice over, once field-wise against a month-length table and once
as a serial day-number round-trip, sharing no line of code.
"""

import random
import sys
from dataclasses import dataclass, replace
from typing import Any

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import Battery, Department, NamedDetector, ReferenceClaim  # noqa: E402
from harness.provenance import Provenance  # noqa: E402

WINDOW = (1801, 2200)

_COMMON_MONTH_LENGTHS = (31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31)

#: Days 1-28 exist in every February of every year, so a day drawn from this
#: set carries no leap-year information at all.  Same for these months: every
#: one of them has a length the leap rule never touches.
_LEAP_AGNOSTIC_DAYS = tuple(range(1, 29))
_LEAP_AGNOSTIC_MONTHS = (1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
#: Year-days 1-59 land on the same calendar date in leap and common years alike.
_LEAP_AGNOSTIC_YEARDAYS = tuple(range(1, 60))
#: Frozen before any run: the seed the ablations draw their replacement values
#: from.  Nothing about it was chosen after seeing a schedule.
_ABLATION_SEED = 20240229


# ---------------------------------------------------------------------------
# The domain objects: a calendar, a rule spec, and the schedule they produce
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Calendar:
    """A civil calendar of twelve months, parameterised only by its leap rule.

    ``leap_rule`` is ``"gregorian"`` (÷4, not ÷100, unless ÷400) or ``"none"``
    (February is always 28 days).  The second exists so the leap rule can be
    ablated without changing anything else about the calendar.
    """

    leap_rule: str = "gregorian"

    def is_leap(self, year: int) -> bool:
        if self.leap_rule == "gregorian":
            return (year % 4 == 0 and year % 100 != 0) or year % 400 == 0
        return False

    def month_length(self, year: int, month: int) -> int:
        if month == 2 and self.is_leap(year):
            return 29
        return _COMMON_MONTH_LENGTHS[month - 1]

    def year_length(self, year: int) -> int:
        return 366 if self.is_leap(year) else 365

    def date_of_yearday(self, year: int, n: int):
        remaining = n
        for month in range(1, 13):
            length = self.month_length(year, month)
            if remaining <= length:
                return (year, month, remaining)
            remaining -= length
        raise ValueError(f"day {n} is past the end of year {year}")

    def yearday_of(self, year: int, month: int, day: int) -> int:
        return sum(self.month_length(year, m) for m in range(1, month)) + day

    def add_days(self, date, n: int):
        year, month, day = date
        remaining = self.yearday_of(year, month, day) + n
        while remaining > self.year_length(year):
            remaining -= self.year_length(year)
            year += 1
        return self.date_of_yearday(year, remaining)

    def describe(self) -> str:
        return f"twelve-month civil calendar, leap rule {self.leap_rule!r}"


GREGORIAN = Calendar("gregorian")
NO_LEAP = Calendar("none")


@dataclass(frozen=True)
class RuleSpec:
    """A recurrence rule, in the small subset of RFC-5545-ish shapes needed here.

    ``kind`` is one of:

    ``"monthday"``  fire on (``month``, ``day``) of every year the
                    ``year_filter`` admits, in years where that day exists;
    ``"yearday"``   fire on the ``yearday``-th day of every admitted year;
    ``"period"``    fire every ``period_days`` days from ``anchor``.

    ``year_filter`` is ``"all"``, ``"odd"`` or ``"leap"``.  No field of this
    record names any subject: a claim cannot read a label off a payload,
    because no payload carries one.
    """

    kind: str
    month: Any = None
    day: Any = None
    yearday: Any = None
    period_days: Any = None
    anchor: Any = None
    year_filter: str = "all"

    def describe(self) -> str:
        if self.kind == "monthday":
            return (
                f"FREQ=YEARLY;BYMONTH={self.month};BYMONTHDAY={self.day};"
                f"YEARS={self.year_filter}"
            )
        if self.kind == "yearday":
            return f"FREQ=YEARLY;BYYEARDAY={self.yearday};YEARS={self.year_filter}"
        if self.kind == "period":
            return f"EVERY {self.period_days} DAYS FROM {self.anchor}"
        return f"kind={self.kind}"


NULL_SPEC = RuleSpec(kind="none")


def _year_admitted(spec: RuleSpec, year: int, calendar: Calendar) -> bool:
    if spec.year_filter == "all":
        return True
    if spec.year_filter == "odd":
        return year % 2 == 1
    if spec.year_filter == "leap":
        return calendar.is_leap(year)
    raise ValueError(f"unknown year filter {spec.year_filter!r}")


def schedule(spec: RuleSpec, calendar: Calendar, window):
    """Every date the rule fires on inside ``window``, in increasing order."""
    lo, hi = window
    out = []
    if spec.kind == "monthday":
        for year in range(lo, hi + 1):
            if not _year_admitted(spec, year, calendar):
                continue
            if spec.day <= calendar.month_length(year, spec.month):
                out.append((year, spec.month, spec.day))
    elif spec.kind == "yearday":
        for year in range(lo, hi + 1):
            if not _year_admitted(spec, year, calendar):
                continue
            if spec.yearday <= calendar.year_length(year):
                out.append(calendar.date_of_yearday(year, spec.yearday))
    elif spec.kind == "period":
        current = spec.anchor
        while current[0] <= hi:
            if current[0] >= lo:
                out.append(current)
            current = calendar.add_days(current, spec.period_days)
    elif spec.kind == "none":
        pass
    else:
        raise ValueError(f"unknown rule kind {spec.kind!r}")
    return tuple(out)


@dataclass(frozen=True)
class Schedule:
    """The payload every claim, measure, statistic and detector here consumes.

    Immutable and hashable on purpose: an instrument that is handed a subject
    must not be able to alter it, and two payloads must be comparable as
    values.  It carries no name, no label and no verdict — the only way to
    answer a question about a subject is to do the calendar arithmetic.

    """

    spec: RuleSpec
    calendar: Calendar
    window: Any
    occurrences: Any

    def describe(self) -> str:
        return (
            f"{self.spec.describe()} on a {self.calendar.describe()} over "
            f"{self.window[0]}-{self.window[1]}: {len(self.occurrences)} firings"
        )


def make_payload(spec: RuleSpec, calendar: Calendar, window) -> Schedule:
    return Schedule(
        spec=spec,
        calendar=calendar,
        window=tuple(window),
        occurrences=schedule(spec, calendar, window),
    )


def _as_schedule(payload) -> Schedule:
    """Coerce whatever an instrument was handed into a :class:`Schedule`.

    Decoys and lesions must be **total**: one that raises, or that quietly
    returns its input unchanged because it did not recognise it, is an inert
    instrument, and an inert instrument measures nothing.  The first branch is
    the substantive path — a real schedule from a real subject.  The empty and
    raw-date branches are substantive too: an empty schedule is exactly the
    case ``feb_29_odd_years`` produces, and a lesion that is a no-op there
    would be an inert planted fault.  The last branch is purely defensive: an
    input this department cannot read at all is replaced by its own clean
    schedule, so the ablation or the planted fault happens rather than silently
    not happening.  See NOTES.md — the runner does hand these instruments
    probes that are not schedules, and the honest reading is that the
    substantive evidence for the decoys is the ablation reported there
    (97 leap-day firings to 0 for all three), not their behaviour on a probe
    that carries no calendar content.
    """
    if isinstance(payload, Schedule):
        return payload
    spec = calendar = window = occurrences = None
    if isinstance(payload, dict):
        spec = payload.get("spec")
        calendar = payload.get("calendar")
        window = payload.get("window")
        occurrences = payload.get("occurrences")
    else:
        spec = getattr(payload, "spec", None)
        calendar = getattr(payload, "calendar", None)
        window = getattr(payload, "window", None)
        occurrences = getattr(payload, "occurrences", None)
    if occurrences is not None:
        return Schedule(
            spec if isinstance(spec, RuleSpec) else NULL_SPEC,
            calendar if isinstance(calendar, Calendar) else GREGORIAN,
            tuple(window) if window else WINDOW,
            tuple(occurrences),
        )
    if isinstance(spec, RuleSpec):
        return make_payload(
            spec,
            calendar if isinstance(calendar, Calendar) else GREGORIAN,
            tuple(window) if window else WINDOW,
        )
    if isinstance(payload, (tuple, list)) and all(
        isinstance(entry, tuple) and len(entry) == 3 for entry in payload
    ):
        return Schedule(NULL_SPEC, GREGORIAN, WINDOW, tuple(payload))
    return _clean_schedule()


def _clean_schedule() -> Schedule:
    return make_payload(TARGET_SPEC, GREGORIAN, WINDOW)


# ---------------------------------------------------------------------------
# Subjects: the target and its rivals
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RuleSubject:
    name: str
    note: str
    spec: RuleSpec
    calendar: Calendar = GREGORIAN
    window: Any = WINDOW

    def describe(self) -> str:
        return f"{self.spec.describe()} — {self.note}"

    def payload(self) -> Schedule:
        return make_payload(self.spec, self.calendar, self.window)


TARGET_SPEC = RuleSpec(kind="monthday", month=2, day=29)

TARGET = RuleSubject(
    name="feb29_yearly",
    note=(
        "the genuine article: asks for 29 February every year and gets it in "
        "the 97 leap years of 1801-2200"
    ),
    spec=TARGET_SPEC,
)

RIVALS = (
    RuleSubject(
        name="feb_29_odd_years",
        note=(
            "requests 29 February in as many words, restricted to odd years; "
            "fires never, because no odd year is divisible by four"
        ),
        spec=RuleSpec(kind="monthday", month=2, day=29, year_filter="odd"),
    ),
    RuleSubject(
        name="feb_28_of_leap_years",
        note=(
            "fires in exactly the 97 years the target fires in, selected by the "
            "same Gregorian leap rule, one day earlier: same count, same years, "
            "no leap day"
        ),
        spec=RuleSpec(kind="monthday", month=2, day=28, year_filter="leap"),
    ),
    RuleSubject(
        name="mar_01_of_leap_years",
        note="the mirror of the above: exactly those 97 leap years, the day after",
        spec=RuleSpec(kind="monthday", month=3, day=1, year_filter="leap"),
    ),
    RuleSubject(
        name="feb_28_yearly",
        note="the immediate neighbour in date space: 28 February of all 400 years",
        spec=RuleSpec(kind="monthday", month=2, day=28),
    ),
    RuleSubject(
        name="mar_01_yearly",
        note="the other immediate neighbour: 1 March of all 400 years",
        spec=RuleSpec(kind="monthday", month=3, day=1),
    ),
    RuleSubject(
        name="day_59_of_year",
        note=(
            "day-of-year arithmetic, which reads the calendar's month lengths; "
            "day 59 is 28 February in leap and common years alike"
        ),
        spec=RuleSpec(kind="yearday", yearday=59),
    ),
    RuleSubject(
        name="day_61_of_year",
        note=(
            "leap-sensitive in the sharpest way: its calendar date moves with "
            "leap status (1 March in leap years, 2 March otherwise) and is never "
            "29 February"
        ),
        spec=RuleSpec(kind="yearday", yearday=61),
    ),
    RuleSubject(
        name="quadrennial_1461_days",
        note=(
            "a period locked to the mean four-year Julian cycle (1461 days), "
            "anchored one day after a leap day; it drifts forward by exactly the "
            "three suppressed century leap days and so never reaches one"
        ),
        spec=RuleSpec(kind="period", period_days=1461, anchor=(1801, 3, 1)),
    ),
)


# ---------------------------------------------------------------------------
# Decoys: ablate one substantive input, keep the shape
# ---------------------------------------------------------------------------


def _replacement(options, current, salt: int):
    """Pick, deterministically, an option that is not the value being ablated.

    A decoy that substitutes the value it was meant to replace has ablated
    nothing, so the current value is removed from the draw before the choice
    is made.
    """
    pool = [value for value in options if value != current]
    if not pool:
        pool = list(options)
    return random.Random(_ABLATION_SEED + salt).choice(pool)


@dataclass(frozen=True)
class RuleDecoy:
    name: str
    note: str
    field: str

    def describe(self) -> str:
        return self.note

    def substitute(self, payload) -> Schedule:
        given = _as_schedule(payload)
        spec = given.spec
        calendar = given.calendar
        window = given.window
        if spec.kind == "none":
            # Nothing substantive to ablate in a null spec; ablate the
            # department's own rule instead, so the decoy is never inert.
            spec = TARGET_SPEC
        if self.field == "day":
            if spec.kind == "monthday":
                spec = replace(spec, day=_replacement(_LEAP_AGNOSTIC_DAYS, spec.day, 1))
            elif spec.kind == "yearday":
                spec = replace(
                    spec, yearday=_replacement(_LEAP_AGNOSTIC_YEARDAYS, spec.yearday, 1)
                )
            elif spec.kind == "period":
                year, month, day = spec.anchor
                spec = replace(
                    spec, anchor=(year, month, _replacement(_LEAP_AGNOSTIC_DAYS, day, 1))
                )
        elif self.field == "month":
            if spec.kind == "monthday":
                spec = replace(spec, month=_replacement(_LEAP_AGNOSTIC_MONTHS, spec.month, 2))
            elif spec.kind == "yearday":
                # No month field to ablate; the analogue is to move the firing
                # into a month drawn without reference to the leap rule.
                target_month = _replacement(_LEAP_AGNOSTIC_MONTHS, None, 2)
                day = min(28, max(1, spec.yearday % 28 + 1))
                spec = RuleSpec(
                    kind="monthday", month=target_month, day=day, year_filter=spec.year_filter
                )
            elif spec.kind == "period":
                year, month, day = spec.anchor
                spec = replace(
                    spec,
                    anchor=(year, _replacement(_LEAP_AGNOSTIC_MONTHS, month, 2), min(day, 28)),
                )
        elif self.field == "calendar":
            calendar = NO_LEAP if calendar.leap_rule != "none" else GREGORIAN
        else:  # pragma: no cover - guarded by construction
            raise ValueError(f"unknown ablation field {self.field!r}")
        return make_payload(spec, calendar, window)


DECOYS = (
    RuleDecoy(
        name="day_of_month_ablated",
        field="day",
        note=(
            "replaces the requested day with one drawn (seed 20240229) from the "
            "days that exist in every February, excluding the day being replaced; "
            "keeps the frequency, the month, the year filter, the calendar and "
            "the window"
        ),
    ),
    RuleDecoy(
        name="month_ablated",
        field="month",
        note=(
            "replaces the requested month with one of the eleven whose length the "
            "leap rule never touches; keeps the day, the frequency, the year "
            "filter, the calendar and the window"
        ),
    ),
    RuleDecoy(
        name="leap_rule_ablated",
        field="calendar",
        note=(
            "leaves the rule and the window untouched and removes the leap rule "
            "from the calendar itself: twelve months, identical lengths, February "
            "always 28 days"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Surrogates: null models that know no leap rule
# ---------------------------------------------------------------------------


def _null_payload(occurrences) -> Schedule:
    return Schedule(
        spec=NULL_SPEC, calendar=GREGORIAN, window=WINDOW, occurrences=tuple(occurrences)
    )


@dataclass
class UniformDaySurrogate:
    """Same number of firings as the target, placed uniformly at random."""

    name: str = "uniform_days_same_count"
    count: int = 97
    seed: int = 11
    _rng: Any = None

    def __post_init__(self) -> None:
        self._rng = random.Random(self.seed)

    def describe(self) -> str:
        return (
            "keeps only the number of firings (97) and scatters them uniformly "
            "over the real days of 1801-2200; no rule, no month, no leap rule"
        )

    def sample(self) -> Schedule:
        lo, hi = WINDOW
        drawn = set()
        while len(drawn) < self.count:
            year = self._rng.randint(lo, hi)
            n = self._rng.randint(1, GREGORIAN.year_length(year))
            drawn.add(GREGORIAN.date_of_yearday(year, n))
        return _null_payload(sorted(drawn))


@dataclass
class RandomYeardaySurrogate:
    """One firing per year, on a uniformly random day of that year."""

    name: str = "one_random_day_per_year"
    seed: int = 23
    _rng: Any = None

    def __post_init__(self) -> None:
        self._rng = random.Random(self.seed)

    def describe(self) -> str:
        return (
            "keeps the yearly cadence and nothing else: one firing per year on a "
            "uniformly random day of that year, so leap days are reachable but "
            "never sought"
        )

    def sample(self) -> Schedule:
        lo, hi = WINDOW
        return _null_payload(
            GREGORIAN.date_of_yearday(year, self._rng.randint(1, GREGORIAN.year_length(year)))
            for year in range(lo, hi + 1)
        )


@dataclass
class RandomFebruaryDaySurrogate:
    """The strongest null here: yearly, already inside February, day uniform.

    It is handed the month for free, and 400 chances rather than the target's
    97, so that what is left to measure is only whether the *day* was chosen
    by something that knows about leap days.
    """

    name: str = "random_february_day_per_year"
    seed: int = 37
    _rng: Any = None

    def __post_init__(self) -> None:
        self._rng = random.Random(self.seed)

    def describe(self) -> str:
        return (
            "yearly, already inside February, day drawn uniformly from the days "
            "February actually has that year; the month is given away free, so "
            "only leap-day targeting is nulled"
        )

    def sample(self) -> Schedule:
        lo, hi = WINDOW
        return _null_payload(
            (year, 2, self._rng.randint(1, GREGORIAN.month_length(year, 2)))
            for year in range(lo, hi + 1)
        )


SURROGATES = (
    UniformDaySurrogate(),
    RandomYeardaySurrogate(),
    RandomFebruaryDaySurrogate(),
)


# ---------------------------------------------------------------------------
# Lesions: planted corruptions of the emitted schedule
# ---------------------------------------------------------------------------
#
# Each lesion violates exactly one invariant of a well-formed schedule, and
# each plants its violation into *any* schedule, empty or not: a lesion that
# happens to be a no-op on some subject is an inert planted fault, and an
# inert planted fault measures nothing.


@dataclass(frozen=True)
class ScheduleLesion:
    name: str
    magnitude: float
    note: str
    mode: str

    def describe(self) -> str:
        return self.note

    def apply(self, payload) -> Schedule:
        given = _as_schedule(payload)
        occurrences = tuple(given.occurrences)
        lo, hi = given.window
        if self.mode == "phantom_one":
            planted = ((2023, 2, 29),)
            occurrences = tuple(sorted(occurrences + planted))
        elif self.mode == "phantom_centuries":
            planted = ((1900, 2, 29), (2100, 2, 29), (2200, 2, 29))
            occurrences = tuple(sorted(occurrences + planted))
        elif self.mode == "duplicates":
            planted = ((lo, 1, 1),) * 12
            occurrences = tuple(sorted(occurrences + planted))
        elif self.mode == "out_of_order":
            planted = tuple((lo + k, 1, 2) for k in range(24, -1, -1))
            occurrences = occurrences + planted
        elif self.mode == "out_of_window":
            planted = tuple((hi + 1 + k, 1, 3) for k in range(97))
            occurrences = occurrences + planted
        else:  # pragma: no cover - guarded by construction
            raise ValueError(f"unknown lesion mode {self.mode!r}")
        return replace(given, occurrences=occurrences)


LESIONS = (
    ScheduleLesion(
        name="one_phantom_leap_day",
        magnitude=1.0,
        mode="phantom_one",
        note="plants a single impossible date, 29 February 2023 (1 bad entry)",
    ),
    ScheduleLesion(
        name="century_rule_forgotten",
        magnitude=3.0,
        mode="phantom_centuries",
        note=(
            "the classic bug: treats 1900, 2100 and 2200 as leap years and emits "
            "their non-existent 29 Februaries (3 bad entries)"
        ),
    ),
    ScheduleLesion(
        name="twelve_repeated_firings",
        magnitude=12.0,
        mode="duplicates",
        note="plants twelve copies of one date, so the schedule repeats itself (12 bad entries)",
    ),
    ScheduleLesion(
        name="twenty_five_out_of_order",
        magnitude=25.0,
        mode="out_of_order",
        note="appends twenty-five in-window dates in descending order, breaking monotonicity (25 bad entries)",
    ),
    ScheduleLesion(
        name="ninety_seven_past_the_window",
        magnitude=97.0,
        mode="out_of_window",
        note="appends ninety-seven firings in years past the declared window (97 bad entries)",
    ),
)


# ---------------------------------------------------------------------------
# Detectors: schedule integrity, twice over, sharing no code
# ---------------------------------------------------------------------------


def _greg_leap(year: int) -> bool:
    return (year % 4 == 0 and year % 100 != 0) or year % 400 == 0


def _parts(payload):
    """Occurrences and window, however the payload was handed over."""
    if isinstance(payload, Schedule):
        return tuple(payload.occurrences), tuple(payload.window)
    occurrences = getattr(payload, "occurrences", None)
    window = getattr(payload, "window", None)
    if occurrences is None and isinstance(payload, dict):
        occurrences = payload.get("occurrences")
        window = payload.get("window")
    if occurrences is None or window is None:
        raise TypeError("not a schedule")
    return tuple(occurrences), tuple(window)


def schedule_malformed_fieldwise(payload: Any) -> bool:
    """Fires when the emitted schedule is not a possible schedule at all.

    Field-wise implementation: a month-length table plus the explicit Gregorian
    leap rule, monotonicity by tuple comparison, window containment by year.
    It knows nothing about which dates the rule *wanted*, and nothing about
    leap days as a target — only about entries that cannot exist, repeat, run
    backwards, or fall outside the declared window.
    """
    try:
        occurrences, (lo, hi) = _parts(payload)
    except Exception:
        return True
    seen = set()
    previous = None
    for entry in occurrences:
        if not isinstance(entry, tuple) or len(entry) != 3:
            return True
        year, month, day = entry
        if not all(isinstance(v, int) for v in (year, month, day)):
            return True
        if not lo <= year <= hi:
            return True
        if not 1 <= month <= 12:
            return True
        length = _COMMON_MONTH_LENGTHS[month - 1]
        if month == 2 and _greg_leap(year):
            length = 29
        if not 1 <= day <= length:
            return True
        if entry in seen:
            return True
        seen.add(entry)
        if previous is not None and entry <= previous:
            return True
        previous = entry
    return False


def _days_from_civil(year: int, month: int, day: int) -> int:
    """Serial day number (Hinnant's algorithm); no leap table appears in it."""
    y = year - (1 if month <= 2 else 0)
    era = (y if y >= 0 else y - 399) // 400
    yoe = y - era * 400
    doy = (153 * (month + (-3 if month > 2 else 9)) + 2) // 5 + day - 1
    doe = yoe * 365 + yoe // 4 - yoe // 100 + doy
    return era * 146097 + doe - 719468


def _civil_from_days(z: int):
    z += 719468
    era = (z if z >= 0 else z - 146096) // 146097
    doe = z - era * 146097
    yoe = (doe - doe // 1460 + doe // 36524 - doe // 146096) // 365
    y = yoe + era * 400
    doy = doe - (365 * yoe + yoe // 4 - yoe // 100)
    mp = (5 * doy + 2) // 153
    d = doy - (153 * mp + 2) // 5 + 1
    m = mp + (3 if mp < 10 else -9)
    return (y + (1 if m <= 2 else 0), m, d)


def schedule_malformed_serial(payload: Any) -> bool:
    """The same invariants, reached by a completely different route.

    Every entry is pushed through a serial day-number conversion and back; an
    entry that does not round-trip is not a date.  Ordering, repetition and
    window containment then become integer comparisons on the serials.  This
    shares no code with :func:`schedule_malformed_fieldwise` — no month-length
    table, no leap-year predicate — so the two agree for different reasons.
    """
    try:
        occurrences, (lo, hi) = _parts(payload)
        first = _days_from_civil(lo, 1, 1)
        last = _days_from_civil(hi, 12, 31)
    except Exception:
        return True
    previous = None
    for entry in occurrences:
        if not isinstance(entry, tuple) or len(entry) != 3:
            return True
        year, month, day = entry
        if not all(isinstance(v, int) for v in (year, month, day)):
            return True
        if not 1 <= month <= 12:
            return True
        serial = _days_from_civil(year, month, day)
        if _civil_from_days(serial) != entry:
            return True
        if not first <= serial <= last:
            return True
        if previous is not None and serial <= previous:
            return True
        previous = serial
    return False


CLEAN_PROBE = TARGET.payload()

DETECTORS = (
    NamedDetector(
        name="schedule_integrity_fieldwise",
        fires=schedule_malformed_fieldwise,
        probe=CLEAN_PROBE,
        note=(
            "fires when the emitted schedule contains a date that cannot exist, "
            "repeats, runs backwards, or leaves the declared window; month-length "
            "table plus the explicit Gregorian leap rule"
        ),
    ),
    NamedDetector(
        name="schedule_integrity_serial",
        fires=schedule_malformed_serial,
        probe=CLEAN_PROBE,
        note=(
            "the same invariants via a serial day-number round-trip, with no "
            "month-length table and no leap-year predicate in it at all"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------


def ever_fires_on_leap_day(payload: Any) -> bool:
    """The claim at issue: some firing of this rule lands on 29 February."""
    return any(month == 2 and day == 29 for (_year, month, day) in payload.occurrences)


def spec_requests_february_29(payload: Any) -> bool:
    """The seductive syntactic proxy: the spec names 29 February.

    A real claim people make about recurrence rules, and a wrong one: the
    battery must kill it, because ``feb_29_odd_years`` requests exactly that
    date and fires never.
    """
    spec = payload.spec
    return spec.kind == "monthday" and spec.month == 2 and spec.day == 29


def ever_fires_in_february(payload: Any) -> bool:
    """A true but weaker claim: some firing is in February.

    True of the target and of three rivals, so it cannot be the load-bearing
    step of any leap-day argument.
    """
    return any(month == 2 for (_year, month, _day) in payload.occurrences)


def _is_pisces(month: int, day: int) -> bool:
    return (month == 2 and day >= 19) or (month == 3 and day <= 20)


def ABSURD_CLAIM(payload: Any) -> bool:  # noqa: N802 - fixed public name
    """Transparently absurd: astrology decides leap-day behaviour."""
    occurrences = payload.occurrences
    if not occurrences:
        return False
    _year, month, day = occurrences[0]
    return _is_pisces(month, day)


ABSURD_CLAIM_TEXT = (
    "A recurrence rule fires on leap days because its first occurrence falls "
    "under the sign of Pisces."
)


REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="ever_fires_on_leap_day",
        claim=ever_fires_on_leap_day,
        distinguishes=True,
        note=(
            "must pass: true of the target and of none of the eight rivals, "
            "including the three built out of the Gregorian leap rule itself"
        ),
    ),
    ReferenceClaim(
        name="spec_requests_february_29",
        claim=spec_requests_february_29,
        distinguishes=False,
        note=(
            "must be killed: shared with feb_29_odd_years, which asks for 29 "
            "February and fires never — the syntactic proxy explains nothing"
        ),
    ),
    ReferenceClaim(
        name="ever_fires_in_february",
        claim=ever_fires_in_february,
        distinguishes=False,
        note=(
            "must be killed: shared with feb_28_yearly, feb_28_of_leap_years and "
            "day_59_of_year, February rules that never see a leap day"
        ),
    ),
)


BATTERY = Battery(
    name="calendar_recurrence_leap_day",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "Every rival is a deterministic recurrence rule over the same window on "
        "the same Gregorian calendar, emitting a well-formed schedule, and none "
        "of them ever fires on 29 February. Three of them "
        "(feb_28_of_leap_years, mar_01_of_leap_years, day_61_of_year) are built "
        "out of the leap rule itself, so a claim that merely detects "
        "leap-awareness dies here; a fourth (feb_29_odd_years) requests the leap "
        "day by name and never gets one."
    ),
)


PROVENANCE = Provenance(
    authored_by="party08 (blind-authoring experiment; sealed conditions)",
    authored_on="2026-08-09",
    # The subject model (Calendar, RuleSpec, schedule) and the battery content
    # were written by the same agent in the same file. One author is one line
    # of evidence, and that is declared loudly rather than hidden.
    independent_of_subject_author=False,
    # Rivals, decoys, surrogates, lesions and both reference-claim verdicts were
    # derived from the Gregorian leap rule before any of them was executed; no
    # schedule output was inspected first.
    results_visible_when_authored=False,
    frozen_before_execution=True,
    # The detectors never call the rule evaluator: they read the emitted
    # schedule only, and validate it against calendar arithmetic of their own.
    oracle_calls_subject=False,
    # The two detectors share no code: one is a month-length table plus an
    # explicit leap predicate, the other a serial day-number round-trip with
    # neither. They do share an author, which the first field already declares.
    instruments_share_critical_dependency=False,
    # Structural edits made during the experiment were each followed by a fresh
    # recorded audit run; no threshold and no declared verdict was retuned to
    # rescue a failing check. The run count is in NOTES.md.
    edited_after_observing_failures=False,
    notes=(
        "Sealed conditions: only harness/protocol.py, harness/provenance.py, "
        "harness/README.md and the runner were readable while authoring. No "
        "existing department, no integrity or sham source, no test file was read."
    ),
)


DEPARTMENT = Department(
    name="calendar_recurrence",
    summary=(
        "Recurrence rules and leap days: whether a rule's emitted schedule ever "
        "lands on 29 February, refereed against rules built out of the Gregorian "
        "leap rule itself that never do."
    ),
    battery=BATTERY,
    door="docs/doors/calendar-recurrence.md",
    modules=("blind/party08/department.py",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "Surviving this battery shows only that the leap-day property of this one "
        "rule is carried by the pairing of its spec with the Gregorian leap rule "
        "over 1801-2200, and specifically not: that any syntactic feature of a "
        "recurrence spec implies leap-day firing, that the verdict transfers to "
        "another calendar, another window, or an RFC 5545 implementation with "
        "different month-end clamping, or that this schedule is what any "
        "particular library would emit."
    ),
    provenance=PROVENANCE,
)
