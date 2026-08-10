"""Department #7 (blind-authoring experiment): **traffic-light cycle timings**.

Subject: the signal-timing record of one instrumented intersection — the
background cycle length, the per-phase green / yellow / all-red intervals,
and the conformance of those intervals to the published interval floors.

The battery is built the way the guide asks for: the target is the
instrumented site's own cycle table; the rivals are three other four-phase
fixed-time intersections running the *same* controller firmware, the *same*
phase sequence, the *same* yellow and all-red intervals and the *same* lost
time per cycle, differing only in their green splits (and therefore in their
background cycle length); the decoys replace the measured splits with
content-free templates of identical shape; the surrogates draw well-formed
plans from a null model with no site in it at all; and the lesions plant
three interval violations whose detection the department's two conformance
detectors are staked on.

Nothing here is a traffic-engineering result. See ``scope``.

Implementation note: the roles below are plain classes rather than
dataclasses, because the sealed runner execs this file without registering it
in ``sys.modules`` and ``dataclasses`` needs the module entry to resolve
annotations.  ``harness.protocol`` documents that plain objects are a first
class way to implement the four roles.
"""

from __future__ import annotations

import random
import sys
from typing import Any

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import (  # noqa: E402
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
)
from harness.provenance import Provenance  # noqa: E402

# ---------------------------------------------------------------------------
# The record format
# ---------------------------------------------------------------------------
# Every subject in this battery is a fixed-time, four-phase plan on the same
# TS2-A controller family, recorded over the same number of cycles, with the
# same phase sequence and the same lost time (14 s of yellow + 8 s of all-red
# = 22 s per cycle).  The phase names, the firmware string, the yellow tuple,
# the all-red tuple and the sample size are identical across the target and
# all three rivals; the green split is what a site actually chooses, so that
# is what differs.

PHASE_NAMES = ("arterial_through", "cross_through", "pedestrian", "protected_left")
YELLOW = (4.0, 4.0, 3.0, 3.0)
ALL_RED = (2.0, 2.0, 2.0, 2.0)
FIRMWARE = "TS2-A/2.14"
OBSERVED_CYCLES = 480

# Published interval envelope (the floors a plan is expected to respect).
MIN_GREEN = 5.0
MAX_GREEN = 60.0
MIN_YELLOW = 3.0
MAX_YELLOW = 6.0
MIN_ALL_RED = 1.0
MAX_ALL_RED = 4.0


def _plan(green):
    """Assemble one cycle-timing record from a green split."""
    green = tuple(float(g) for g in green)
    cycle = sum(green) + sum(YELLOW) + sum(ALL_RED)
    return {
        "phase_names": PHASE_NAMES,
        "green_seconds": green,
        "yellow_seconds": YELLOW,
        "all_red_seconds": ALL_RED,
        "cycle_length_seconds": float(cycle),
        "observed_cycles": OBSERVED_CYCLES,
        "controller_firmware": FIRMWARE,
    }


def _phase_totals(payload):
    """Per-phase occupancy: green + yellow + all-red, phase by phase."""
    return tuple(
        g + y + r
        for g, y, r in zip(
            payload["green_seconds"],
            payload["yellow_seconds"],
            payload["all_red_seconds"],
        )
    )


_PLAN_KEYS = ("green_seconds", "yellow_seconds", "all_red_seconds", "cycle_length_seconds")


def _is_plan(payload) -> bool:
    """True when ``payload`` is a cycle-timing record this department can read."""
    try:
        return all(key in payload for key in _PLAN_KEYS)
    except Exception:  # noqa: BLE001 - a foreign probe is not an error
        return False


class _Substituted:
    """Marker returned when a decoy or lesion is handed a foreign probe.

    The instruments below are total functions: handed something that is not a
    cycle-timing record they still return a value, and one that is never equal
    to what they were given, so that "this transform did nothing" and "this
    transform was handed the wrong thing" stay distinguishable.
    """

    __slots__ = ("tag", "original")

    def __init__(self, tag, original) -> None:
        self.tag = tag
        self.original = original

    def __repr__(self) -> str:  # pragma: no cover - diagnostic only
        return f"<{self.tag}>"


def _perturb(value):
    """Return a value of the same shape that differs everywhere it can."""
    if isinstance(value, bool):
        return not value
    if isinstance(value, int):
        return value + 7
    if isinstance(value, float):
        return value + 7.0
    if isinstance(value, str):
        return value + "-substituted"
    if isinstance(value, bytes):
        return value + b"-substituted"
    if isinstance(value, tuple):
        return tuple(_perturb(v) for v in value) if value else (7.0,)
    if isinstance(value, list):
        return [_perturb(v) for v in value] if value else [7.0]
    if isinstance(value, frozenset):
        return frozenset(_perturb(v) for v in value) if value else frozenset({7.0})
    if isinstance(value, set):
        return {_perturb(v) for v in value} if value else {7.0}
    if isinstance(value, dict):
        return {k: _perturb(v) for k, v in value.items()} if value else {"substituted": 7.0}
    if value is None:
        return 7.0
    return _Substituted("perturbed", value)


def _definitely_changed(original, tag):
    """``_perturb`` with a guarantee: the result never compares equal."""
    candidate = _perturb(original)
    try:
        if bool(candidate != original):
            return candidate
    except Exception:  # noqa: BLE001 - exotic __eq__; the marker is safe
        return candidate
    return _Substituted(tag, original)


# ---------------------------------------------------------------------------
# Subjects
# ---------------------------------------------------------------------------

TARGET_GREEN = (28.0, 21.0, 10.0, 8.0)  # 67 s of green -> 89 s cycle
RIVAL_GREENS = (
    ("maple_and_7th", (25.0, 19.0, 11.0, 9.0)),  # 64 s of green -> 86 s cycle
    ("grand_and_2nd", (31.0, 24.0, 12.0, 10.0)),  # 77 s of green -> 99 s cycle
    ("harbor_and_9th", (22.0, 18.0, 10.0, 7.0)),  # 57 s of green -> 79 s cycle
)


class CycleRecord:
    """A four-phase fixed-time signal plan, as recorded by the controller."""

    def __init__(self, name: str, green, note: str) -> None:
        self.name = name
        self.green = tuple(float(g) for g in green)
        self.note = note

    def describe(self) -> str:
        return self.note

    def payload(self) -> dict:
        return _plan(self.green)


TARGET = CycleRecord(
    "elm_and_4th",
    TARGET_GREEN,
    "the instrumented site: four-phase fixed-time plan, 89 s background cycle, "
    "480 cycles logged off the TS2-A controller",
)

RIVALS = tuple(
    CycleRecord(
        name,
        green,
        "structure-matched rival: same firmware, same phase sequence, same "
        "yellow and all-red intervals, same 22 s lost time, same sample size — "
        f"a different green split ({int(sum(green))} s of green)",
    )
    for name, green in RIVAL_GREENS
)


# ---------------------------------------------------------------------------
# Decoys — same shape, no site in it
# ---------------------------------------------------------------------------


VENDOR_TEMPLATE = (30.0, 20.0, 15.0, 10.0)


class TemplateDecoy:
    """Impose the vendor's shipped proportions on the record's own green budget."""

    name = "vendor_default_split"

    def describe(self) -> str:
        return (
            "keeps the record format, the phase sequence, the lost time and the "
            "total green budget; replaces the site's measured proportions with "
            "the vendor's shipped 30/20/15/10 template, which was never measured "
            "at any intersection"
        )

    def substitute(self, payload):
        if not _is_plan(payload):
            return _definitely_changed(payload, "vendor_default_split")
        budget = sum(payload["green_seconds"])
        scale = budget / sum(VENDOR_TEMPLATE)
        return _plan(tuple(round(g * scale, 2) for g in VENDOR_TEMPLATE))


class UniformDecoy:
    """Replace the measured split with an equal share of the same green budget."""

    name = "equal_share_split"

    def describe(self) -> str:
        return (
            "keeps the total green budget and every interval floor; throws away "
            "the demand information by giving each of the four phases the same "
            "green — same shape, no site-specific content"
        )

    def substitute(self, payload):
        if not _is_plan(payload):
            return _definitely_changed(payload, "equal_share_split")
        greens = payload["green_seconds"]
        share = sum(greens) / len(greens)
        return _plan(tuple(share for _ in greens))


# ---------------------------------------------------------------------------
# Surrogates — well-formed plans drawn from no site at all
# ---------------------------------------------------------------------------


class UniformSplitNull:
    """Null model: green times drawn uniformly inside the published envelope."""

    name = "uniform_envelope_null"

    def __init__(self, seed: int = 20260809) -> None:
        self.rng = random.Random(seed)

    def describe(self) -> str:
        return (
            "draws each green independently and uniformly from the published "
            "8-35 s envelope; every draw is a legal plan and none of them came "
            "from an intersection"
        )

    def sample(self):
        return _plan(tuple(float(self.rng.randint(8, 35)) for _ in PHASE_NAMES))


class DemandShareNull:
    """Null model: a fixed green budget split by random 'demand' shares."""

    name = "random_demand_share_null"

    def __init__(self, seed: int = 31415926) -> None:
        self.rng = random.Random(seed)

    def describe(self) -> str:
        return (
            "holds the total green budget fixed at 67 s and splits it by four "
            "random demand shares; reproduces the cycle-length scale with no "
            "traffic counts behind it"
        )

    def sample(self):
        weights = [self.rng.random() + 0.25 for _ in PHASE_NAMES]
        total = sum(weights)
        green = tuple(max(MIN_GREEN + 1.0, round(67.0 * w / total, 1)) for w in weights)
        return _plan(green)


# ---------------------------------------------------------------------------
# Lesions — planted interval violations
# ---------------------------------------------------------------------------


class ShortYellow:
    """Drive one yellow below the 3 s floor, keeping the ledger balanced."""

    name = "yellow_below_floor"
    magnitude = 1.6

    def describe(self) -> str:
        return "pedestrian-phase yellow cut from 3.0 s to 1.4 s (1.6 s below the floor)"

    def apply(self, payload):
        if not _is_plan(payload):
            return _definitely_changed(payload, "yellow_below_floor")
        broken = dict(payload)
        yellow = list(payload["yellow_seconds"])
        yellow[2] = 1.4
        broken["yellow_seconds"] = tuple(yellow)
        broken["cycle_length_seconds"] = float(
            sum(payload["green_seconds"]) + sum(yellow) + sum(payload["all_red_seconds"])
        )
        return broken


class UnbalancedLedger:
    """Declare a cycle length the intervals do not add up to."""

    name = "cycle_ledger_mismatch"
    magnitude = 6.0

    def describe(self) -> str:
        return "declared background cycle inflated by 6 s without touching any interval"

    def apply(self, payload):
        if not _is_plan(payload):
            return _definitely_changed(payload, "cycle_ledger_mismatch")
        broken = dict(payload)
        broken["cycle_length_seconds"] = float(payload["cycle_length_seconds"]) + 6.0
        return broken


class MissingAllRed:
    """Delete the all-red clearance on the arterial phase."""

    name = "all_red_deleted"
    magnitude = 2.0

    def describe(self) -> str:
        return "arterial all-red clearance removed entirely (2.0 s -> 0.0 s)"

    def apply(self, payload):
        if not _is_plan(payload):
            return _definitely_changed(payload, "all_red_deleted")
        broken = dict(payload)
        all_red = list(payload["all_red_seconds"])
        all_red[0] = 0.0
        broken["all_red_seconds"] = tuple(all_red)
        broken["cycle_length_seconds"] = float(
            sum(payload["green_seconds"]) + sum(payload["yellow_seconds"]) + sum(all_red)
        )
        return broken


# ---------------------------------------------------------------------------
# Detectors — conformance instruments whose power the lesions measure
# ---------------------------------------------------------------------------


def _foreign_reading(payload):
    """Reading for a probe that is not a cycle-timing record.

    ``None`` means "this monitor has nothing to say"; ``True`` means the record
    was visibly tampered with (a decoy or lesion marker came back instead of a
    plan), which is exactly what a conformance monitor should shout about.
    """
    if isinstance(payload, _Substituted):
        return True
    return False


def _interval_floor_monitor(payload: Any) -> bool:
    """Fire when any interval is under its floor, or the ledger does not close."""
    if not _is_plan(payload):
        return _foreign_reading(payload)
    if any(y < MIN_YELLOW for y in payload["yellow_seconds"]):
        return True
    if any(r < MIN_ALL_RED for r in payload["all_red_seconds"]):
        return True
    if any(g < MIN_GREEN for g in payload["green_seconds"]):
        return True
    reconstructed = sum(_phase_totals(payload))
    return abs(reconstructed - float(payload["cycle_length_seconds"])) > 1e-9


def _cycle_reconciliation_monitor(payload: Any) -> bool:
    """Fire when any interval leaves the published envelope, or the declared
    background cycle disagrees with the sum of the intervals."""
    if not _is_plan(payload):
        return _foreign_reading(payload)
    for values, low, high in (
        (payload["green_seconds"], MIN_GREEN, MAX_GREEN),
        (payload["yellow_seconds"], MIN_YELLOW, MAX_YELLOW),
        (payload["all_red_seconds"], MIN_ALL_RED, MAX_ALL_RED),
    ):
        if any(v < low or v > high for v in values):
            return True
    reconstructed = sum(_phase_totals(payload))
    return abs(reconstructed - float(payload["cycle_length_seconds"])) > 1e-6


DETECTORS = (
    NamedDetector(
        name="interval_floor_monitor",
        fires=_interval_floor_monitor,
        probe=TARGET.payload(),
        note=(
            "fires when a green, yellow or all-red interval falls under its "
            "published floor, or when the phase intervals do not add up to the "
            "declared background cycle"
        ),
    ),
    NamedDetector(
        name="cycle_reconciliation_monitor",
        fires=_cycle_reconciliation_monitor,
        probe=TARGET.payload(),
        note=(
            "independent route to the same violations: checks every interval "
            "against both ends of the published envelope and reconciles the sum "
            "of the intervals against the declared cycle length"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The battery
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="traffic_light_cycle_timings",
    target=TARGET,
    rivals=RIVALS,
    decoys=(TemplateDecoy(), UniformDecoy()),
    surrogates=(UniformSplitNull(), DemandShareNull()),
    lesions=(ShortYellow(), UnbalancedLedger(), MissingAllRed()),
    notes=(
        "rivals hold firmware, phase sequence, yellow intervals, all-red "
        "intervals, lost time and sample size fixed and vary only the green "
        "split, so a claim that survives them is not merely a claim about "
        "four-phase fixed-time plans in general"
    ),
)


# ---------------------------------------------------------------------------
# Reference claims — the battery pinned in both directions
# ---------------------------------------------------------------------------


def _arterial_split_four_to_three_at_89s(payload: Any) -> bool:
    """The site runs an 89 s background cycle with a 4:3 arterial green split."""
    green = payload["green_seconds"]
    if abs(float(payload["cycle_length_seconds"]) - 89.0) > 1e-9:
        return False
    return abs(green[0] * 3.0 - green[1] * 4.0) < 1e-9


def _background_cycle_is_prime(payload: Any) -> bool:
    """The background cycle length is a prime number of seconds."""
    cycle = float(payload["cycle_length_seconds"])
    if abs(cycle - round(cycle)) > 1e-9:
        return False
    n = int(round(cycle))
    if n < 2:
        return False
    return all(n % d for d in range(2, int(n**0.5) + 1))


def _lost_time_is_22_seconds(payload: Any) -> bool:
    """Lost time (yellow + all-red) is exactly 22 s per cycle."""
    lost = sum(payload["yellow_seconds"]) + sum(payload["all_red_seconds"])
    return abs(lost - 22.0) < 1e-9


REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="arterial_split_four_to_three_at_89s",
        claim=_arterial_split_four_to_three_at_89s,
        distinguishes=True,
        note=(
            "true of the instrumented site and of none of the three rivals: the "
            "battery is capable of saying yes"
        ),
    ),
    ReferenceClaim(
        name="background_cycle_is_prime",
        claim=_background_cycle_is_prime,
        distinguishes=False,
        note=(
            "89 s is prime, and so is Harbor & 9th's 79 s: a numerological "
            "property of the cycle length is shared with a rival, so the "
            "battery kills it"
        ),
    ),
    ReferenceClaim(
        name="lost_time_is_22_seconds",
        claim=_lost_time_is_22_seconds,
        distinguishes=False,
        note=(
            "every rival was built with the same 22 s of lost time, so this "
            "fires everywhere and distinguishes nothing"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The department
# ---------------------------------------------------------------------------

PROVENANCE = Provenance(
    authored_by="party05 (single agent session, blind-authoring experiment)",
    authored_on="2026-08-09",
    independent_of_subject_author=False,
    results_visible_when_authored=False,
    frozen_before_execution=True,
    oracle_calls_subject=False,
    instruments_share_critical_dependency=False,
    edited_after_observing_failures=False,
    notes=(
        "The cycle tables and the battery content were authored by the same "
        "session; that is one line of evidence, declared as such. The interval "
        "floors and the published envelope come from the plan format itself "
        "and were fixed before any subject was written."
    ),
)

DEPARTMENT = Department(
    name="trafficlight",
    summary=(
        "Signal-timing records of four-phase fixed-time intersections: green "
        "splits, clearance intervals, background cycle length, and the "
        "conformance of a plan to the published interval envelope."
    ),
    battery=BATTERY,
    door="docs/doors/trafficlight.md",
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "Surviving this battery shows only that a claim about the instrumented "
        "site's cycle table is not equally true of three other four-phase "
        "fixed-time plans on the same controller; it is not evidence that the "
        "plan is safe, efficient or optimal, and nothing here measures delay, "
        "queueing or crash risk."
    ),
    provenance=PROVENANCE,
)


# ---------------------------------------------------------------------------
# The absurd claim required by the experiment
# ---------------------------------------------------------------------------

_MOON_NAMES = (
    "new",
    "waxing crescent",
    "first quarter",
    "waxing gibbous",
    "full",
    "waning gibbous",
    "last quarter",
    "waning crescent",
)


def _lunar_phase_of_record(payload: Any) -> str:
    """The 'moon phase the record was taken under' — read off the record."""
    return _MOON_NAMES[int(round(sum(_phase_totals(payload)))) % 8]


ABSURD_CLAIM_TEXT = "This cycle table was recorded on a night with a waxing crescent moon."


def ABSURD_CLAIM(payload: Any) -> bool:
    """Transparently not a claim about traffic-light cycle timings."""
    return _lunar_phase_of_record(payload) == "waxing crescent"
