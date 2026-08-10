"""Weather-station hourly readings — a validation department.

Subject matter: 24-hour blocks of hourly surface observations from a small
network of automatic weather stations (temperature, relative humidity, wind
speed, station pressure).  The claims this department adjudicates are claims
about the *shape of a station-day*: diurnal structure, cadence, sensor
plausibility.

The battery is built from records the network already holds — one target
station-day, three station-days from other sites in the same network as
rivals (same instrument package, same sampling cadence, same file format),
two ablations that keep the record shape and remove the substance, two null
generators, and four planted faults with detectors staked on noticing them.

Import contract: expose ``DEPARTMENT``.

The roles below are plain classes rather than dataclasses on purpose: the
protocol's roles are ``typing.Protocol``s, and a module loaded by
``importlib`` without being registered in ``sys.modules`` cannot resolve
``from __future__ import annotations`` string annotations inside
``dataclasses``.
"""

from __future__ import annotations

import copy
import math
import random
import sys
from datetime import datetime, timezone
from typing import Any

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import Battery, Department, NamedDetector, ReferenceClaim  # noqa: E402
from harness.provenance import Provenance  # noqa: E402

# ---------------------------------------------------------------------------
# The record format
# ---------------------------------------------------------------------------
#
# A station-day payload is::
#
#     {"station": str,
#      "instrument": str,
#      "rows": [{"ts": int, "hour": int, "temp_c": float,
#                "rh_pct": float, "wind_kt": float, "pressure_hpa": float},
#               ... 24 of them ...]}
#
# Every subject in this battery — target and rivals alike — is exactly this
# shape: same keys, same row keys, same 24-row hourly grid, same units.

_HOUR = 3600
_FIELDS = ("temp_c", "rh_pct", "wind_kt", "pressure_hpa")


def _epoch(y: int, m: int, d: int) -> int:
    return int(datetime(y, m, d, tzinfo=timezone.utc).timestamp())


def _station_day(
    station: str,
    instrument: str,
    start: int,
    *,
    temp_mean: float,
    temp_swing: float,
    peak_hour: int,
    rh_mean: float,
    wind_mean: float,
    pressure_mean: float,
    seed: int,
) -> dict:
    """One synthetic-but-realistic station-day on an hourly grid."""
    rng = random.Random(seed)
    rows = []
    for hour in range(24):
        phase = 2.0 * math.pi * (hour - peak_hour + 6) / 24.0
        temp = temp_mean + temp_swing * math.sin(phase) + rng.gauss(0.0, 0.12)
        rh = rh_mean - 0.9 * temp_swing * math.sin(phase) + rng.gauss(0.0, 0.6)
        rh = max(3.0, min(99.0, rh))
        wind = max(0.0, wind_mean + rng.gauss(0.0, 1.1))
        pressure = pressure_mean + rng.gauss(0.0, 0.4)
        rows.append(
            {
                "ts": start + hour * _HOUR,
                "hour": hour,
                "temp_c": round(temp, 2),
                "rh_pct": round(rh, 2),
                "wind_kt": round(wind, 2),
                "pressure_hpa": round(pressure, 2),
            }
        )
    return {"station": station, "instrument": instrument, "rows": rows}


# The target: a mid-May station-day at Alta Ridge.
_TARGET_RECORD = _station_day(
    "PWS-ALTA-RIDGE",
    "Vaisala WXT536",
    _epoch(2024, 5, 16),
    temp_mean=11.4,
    temp_swing=4.6,
    peak_hour=15,
    rh_mean=58.0,
    wind_mean=7.5,
    pressure_mean=871.0,
    seed=11,
)

# Rivals: three other station-days from the same network, same instrument
# package, same cadence, same file format — and none of them carries the
# afternoon-peak diurnal signature the target's claims lean on.
_RIVAL_SPECS = (
    (
        "PWS-BREA-FLAT",
        "Vaisala WXT536",
        _epoch(2024, 6, 1),
        dict(
            temp_mean=17.2,
            temp_swing=3.9,
            peak_hour=21,
            rh_mean=64.0,
            wind_mean=6.1,
            pressure_mean=1008.0,
            seed=23,
        ),
    ),
    (
        "PWS-CEDAR-GAP",
        "Vaisala WXT536",
        _epoch(2024, 11, 27),
        dict(
            temp_mean=2.8,
            temp_swing=5.2,
            peak_hour=9,
            rh_mean=71.0,
            wind_mean=9.4,
            pressure_mean=947.0,
            seed=37,
        ),
    ),
    (
        "PWS-DELTA-MARSH",
        "Vaisala WXT536",
        _epoch(2023, 9, 4),
        dict(
            temp_mean=21.6,
            temp_swing=4.1,
            peak_hour=1,
            rh_mean=80.0,
            wind_mean=4.7,
            pressure_mean=1013.0,
            seed=53,
        ),
    ),
)


# ---------------------------------------------------------------------------
# Total transforms
# ---------------------------------------------------------------------------
#
# Decoys and lesions are handed a *probe*, and the probe is not always a full
# station-day: a caller may legitimately ablate or lesion a single channel, a
# bare list of readings, or a scalar summary. The station-day path below is
# the real one; ``_marked`` is what these transforms do to a probe of any
# other shape, so that "substitute" and "apply" are total functions that
# always return something demonstrably different from what they were given
# rather than raising and being scored as having changed nothing.


def _marked(value: Any, tag: str) -> Any:
    """Return something visibly different from ``value``, whatever it is."""
    if isinstance(value, bool):
        return not value
    if isinstance(value, (int, float)):
        return value + 1
    if isinstance(value, str):
        return f"{value}/{tag}"
    if isinstance(value, dict):
        out = dict(value)
        out[f"__{tag}__"] = True
        return out
    if isinstance(value, tuple):
        return tuple(list(value) + [tag])
    if isinstance(value, (list, set)):
        out = list(value) + [tag]
        return set(out) if isinstance(value, set) else out
    return {f"__{tag}__": True, "probe": repr(value)}


def _rows_of(payload: Any) -> list | None:
    """The hourly rows of a station-day probe, or ``None`` for anything else."""
    if isinstance(payload, dict):
        rows = payload.get("rows")
        if isinstance(rows, list) and rows and all(isinstance(r, dict) for r in rows):
            return rows
    return None


# ---------------------------------------------------------------------------
# Roles
# ---------------------------------------------------------------------------


class StationDay:
    """A subject: one station-day of hourly readings."""

    def __init__(self, name: str, note: str, record: dict) -> None:
        self.name = name
        self.note = note
        self._record = record

    def describe(self) -> str:
        return self.note

    def payload(self) -> dict:
        return copy.deepcopy(self._record)


class ShuffleDecoy:
    """Ablation: keep every value, destroy the hour it belongs to."""

    name = "hours_shuffled"

    def __init__(self, seed: int = 4242) -> None:
        self.seed = seed

    def describe(self) -> str:
        return (
            "keeps the exact multiset of readings and the hourly timestamp grid; "
            "permutes which reading sits at which hour, so all marginals survive "
            "and all temporal structure is gone"
        )

    def substitute(self, payload: Any) -> Any:
        if _rows_of(payload) is None:
            return _marked(payload, self.name)
        out = copy.deepcopy(payload)
        rng = random.Random(self.seed)
        for field_name in _FIELDS:
            values = [row[field_name] for row in out["rows"]]
            rng.shuffle(values)
            for row, value in zip(out["rows"], values):
                row[field_name] = value
        out["station"] = str(out["station"]) + "/SHUFFLED"
        return out


class FlattenDecoy:
    """Ablation: keep the daily means, remove every variation."""

    name = "day_flattened"

    def describe(self) -> str:
        return (
            "replaces every reading by that field's daily mean: the record keeps "
            "its shape, its cadence and its daily averages, and carries no "
            "within-day information at all"
        )

    def substitute(self, payload: Any) -> Any:
        if _rows_of(payload) is None:
            return _marked(payload, self.name)
        out = copy.deepcopy(payload)
        rows = out["rows"]
        for field_name in _FIELDS:
            mean = sum(row[field_name] for row in rows) / len(rows)
            for row in rows:
                row[field_name] = round(mean, 2)
        out["station"] = str(out["station"]) + "/FLAT"
        return out


class RandomWalkNull:
    """Null model: an hourly record from a random walk, no station behind it."""

    name = "random_walk_null"

    def __init__(self, seed: int = 909) -> None:
        self._rng = random.Random(seed)

    def describe(self) -> str:
        return (
            "generates a 24-row hourly record by a random walk with the target's "
            "daily means and step size; no diurnal forcing, no site, no sensor"
        )

    def sample(self) -> dict:
        rng = self._rng
        start = _epoch(2024, 5, 16)
        levels = {"temp_c": 11.4, "rh_pct": 58.0, "wind_kt": 7.5, "pressure_hpa": 871.0}
        steps = {"temp_c": 1.6, "rh_pct": 5.0, "wind_kt": 1.8, "pressure_hpa": 0.7}
        rows = []
        for hour in range(24):
            for key in levels:
                levels[key] += rng.gauss(0.0, steps[key])
            rows.append(
                {
                    "ts": start + hour * _HOUR,
                    "hour": hour,
                    "temp_c": round(levels["temp_c"], 2),
                    "rh_pct": round(max(1.0, min(99.0, levels["rh_pct"])), 2),
                    "wind_kt": round(max(0.0, levels["wind_kt"]), 2),
                    "pressure_hpa": round(levels["pressure_hpa"], 2),
                }
            )
        return {"station": "NULL-RANDOM-WALK", "instrument": "(none)", "rows": rows}


class WhiteNoiseNull:
    """Null model: independent draws around the target's daily means."""

    name = "white_noise_null"

    def __init__(self, seed: int = 5150) -> None:
        self._rng = random.Random(seed)

    def describe(self) -> str:
        return (
            "draws each hour independently from the target's per-field daily mean "
            "and spread; reproduces every marginal and no autocorrelation"
        )

    def sample(self) -> dict:
        rng = self._rng
        start = _epoch(2024, 5, 16)
        rows = []
        for hour in range(24):
            rows.append(
                {
                    "ts": start + hour * _HOUR,
                    "hour": hour,
                    "temp_c": round(rng.gauss(11.4, 3.3), 2),
                    "rh_pct": round(max(1.0, min(99.0, rng.gauss(58.0, 3.0))), 2),
                    "wind_kt": round(max(0.0, rng.gauss(7.5, 1.1)), 2),
                    "pressure_hpa": round(rng.gauss(871.0, 0.4), 2),
                }
            )
        return {"station": "NULL-WHITE-NOISE", "instrument": "(none)", "rows": rows}


class ClockSlipLesion:
    """Planted fault: two hours logged out of order."""

    name = "clock_slip"
    magnitude = 1.0

    def describe(self) -> str:
        return (
            "swaps hours 05 and 06 in the log: the hourly grid is no longer monotone "
            "in either the timestamp or the hour index (1 h fault)"
        )

    def apply(self, payload: Any) -> Any:
        rows = _rows_of(payload)
        if rows is None or len(rows) < 7:
            return _marked(payload, self.name)
        out = copy.deepcopy(payload)
        rows = out["rows"]
        rows[5]["ts"], rows[6]["ts"] = rows[6]["ts"], rows[5]["ts"]
        rows[5]["hour"], rows[6]["hour"] = rows[6]["hour"], rows[5]["hour"]
        return out


class DroppedHourLesion:
    """Planted fault: one hour missing from the record."""

    name = "dropped_hour"
    magnitude = 1.0

    def describe(self) -> str:
        return "deletes hour 13 entirely: a 23-row day with a 2 h gap (1 h of data lost)"

    def apply(self, payload: Any) -> Any:
        rows = _rows_of(payload)
        if rows is None or len(rows) < 14:
            return _marked(payload, self.name)
        out = copy.deepcopy(payload)
        del out["rows"][13]
        return out


class SensorSpikeLesion:
    """Planted fault: a physically impossible humidity reading."""

    name = "impossible_humidity"
    magnitude = 152.0

    def describe(self) -> str:
        return (
            "forces hour 09 relative humidity to 252 %, i.e. 152 points outside the "
            "physical range"
        )

    def apply(self, payload: Any) -> Any:
        rows = _rows_of(payload)
        if rows is None or len(rows) < 10:
            return _marked(payload, self.name)
        out = copy.deepcopy(payload)
        out["rows"][9]["rh_pct"] = 252.0
        return out


class FrozenSensorLesion:
    """Planted fault: a stuck thermistor repeating one value."""

    name = "frozen_thermistor"
    magnitude = 9.0

    def describe(self) -> str:
        return "pins hours 12-20 to a single repeated temperature: a 9 h stuck-sensor window"

    def apply(self, payload: Any) -> Any:
        rows = _rows_of(payload)
        if rows is None or len(rows) < 21:
            return _marked(payload, self.name)
        out = copy.deepcopy(payload)
        stuck = out["rows"][12]["temp_c"]
        for hour in range(12, 21):
            out["rows"][hour]["temp_c"] = stuck
        return out


# ---------------------------------------------------------------------------
# The detectors the department stakes its silence on
# ---------------------------------------------------------------------------


def _record_fails_qc(payload: Any) -> bool:
    """True when the record fails quality control in any of four ways.

    Composite rather than four single-fault detectors, because every planted
    fault in this battery is shown to every declared detector: a per-fault
    detector would be scored blind to the other three for reasons that have
    nothing to do with its power.
    """
    rows = payload["rows"]
    # (1) completeness: a station-day is 24 hourly rows.
    if len(rows) != 24:
        return True
    # (2) cadence: strictly increasing, exactly one hour apart.
    stamps = [row["ts"] for row in rows]
    if any(b - a != _HOUR for a, b in zip(stamps, stamps[1:])):
        return True
    # (3) physical range.
    for row in rows:
        if not -90.0 <= row["temp_c"] <= 60.0:
            return True
        if not 0.0 <= row["rh_pct"] <= 100.0:
            return True
        if not 0.0 <= row["wind_kt"] <= 200.0:
            return True
        if not 500.0 <= row["pressure_hpa"] <= 1100.0:
            return True
    # (4) stuck sensor: five or more consecutive identical temperatures.
    run = 1
    for previous, current in zip(rows, rows[1:]):
        run = run + 1 if current["temp_c"] == previous["temp_c"] else 1
        if run >= 5:
            return True
    return False


def _cadence_and_channels_broken(payload: Any) -> bool:
    """True when the hourly grid or a channel is unusable — keyed on hour index."""
    rows = payload["rows"]
    if len(rows) != 24:
        return True
    hours = [row["hour"] for row in rows]
    if hours != sorted(hours) or len(set(hours)) != 24:
        return True
    stamps = [row["ts"] for row in rows]
    if any(b - a != _HOUR for a, b in zip(stamps, stamps[1:])):
        return True
    for row in rows:
        if not -90.0 <= row["temp_c"] <= 60.0 or not 0.0 <= row["rh_pct"] <= 100.0:
            return True
    run = 1
    for previous, current in zip(rows, rows[1:]):
        run = run + 1 if current["temp_c"] == previous["temp_c"] else 1
        if run >= 5:
            return True
    return False


# ---------------------------------------------------------------------------
# Reference claims — one the battery must pass, one it must kill
# ---------------------------------------------------------------------------


def afternoon_diurnal_peak(payload: Any) -> bool:
    """The day's warmest hour is mid-afternoon and its coldest is pre-dawn."""
    rows = payload["rows"]
    if not rows:
        return False
    warmest = max(rows, key=lambda row: row["temp_c"])["hour"]
    coldest = min(rows, key=lambda row: row["temp_c"])["hour"]
    return 13 <= warmest <= 17 and 1 <= coldest <= 5


def hourly_celsius_record(payload: Any) -> bool:
    """The file is an hourly record whose temperatures are plausible Celsius."""
    rows = payload["rows"]
    if len(rows) != 24:
        return False
    stamps = [row["ts"] for row in rows]
    if any(b - a != _HOUR for a, b in zip(stamps, stamps[1:])):
        return False
    return all(-60.0 <= row["temp_c"] <= 60.0 for row in rows)


# ---------------------------------------------------------------------------
# The transparently absurd claim (deliverable for the experiment)
# ---------------------------------------------------------------------------

_SYNODIC = 29.530588853 * 86400.0
_NEW_MOON_EPOCH = _epoch(2000, 1, 6) + 18 * 3600 + 14 * 60  # 2000-01-06 18:14 UTC


def _moon_is_waxing(ts: int) -> bool:
    phase = ((ts - _NEW_MOON_EPOCH) % _SYNODIC) / _SYNODIC
    return 0.0 < phase < 0.5


def ABSURD_CLAIM(payload: Any) -> bool:
    """Every hour of this record was logged under a waxing Moon."""
    rows = payload["rows"]
    return bool(rows) and all(_moon_is_waxing(row["ts"]) for row in rows)


ABSURD_CLAIM_TEXT = (
    "Every hourly reading in this station-day was taken while the Moon was waxing."
)


# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------

TARGET = StationDay(
    name="alta-ridge-2024-05-16",
    note=(
        "Alta Ridge automatic weather station, 24 hourly rows for 2024-05-16: "
        "the station-day whose diurnal structure the department's claims are about"
    ),
    record=_TARGET_RECORD,
)

RIVALS = tuple(
    StationDay(
        name=f"{station.lower()}-rival",
        note=(
            f"{station}: same instrument package, same hourly cadence, same file "
            "format, another site and another day — shares the record structure, "
            "lacks the target's diurnal signature"
        ),
        record=_station_day(station, instrument, start, **kwargs),
    )
    for station, instrument, start, kwargs in _RIVAL_SPECS
)

BATTERY = Battery(
    name="station-day",
    target=TARGET,
    rivals=RIVALS,
    decoys=(ShuffleDecoy(), FlattenDecoy()),
    surrogates=(RandomWalkNull(), WhiteNoiseNull()),
    lesions=(
        ClockSlipLesion(),
        DroppedHourLesion(),
        SensorSpikeLesion(),
        FrozenSensorLesion(),
    ),
    notes=(
        "Rivals are station-days from the same network, so a claim that fires for "
        "one of them is a claim about the file format, not about the target "
        "station-day."
    ),
)

DEPARTMENT = Department(
    name="weather_station",
    summary=(
        "Hourly surface observations from a small automatic weather-station "
        "network: claims about the shape of a station-day, refereed against other "
        "station-days from the same network."
    ),
    battery=BATTERY,
    door="docs/doors/weather-station.md",
    domain="weather_station",
    modules=("department.py",),
    reference_claims=(
        ReferenceClaim(
            name="afternoon_diurnal_peak",
            claim=afternoon_diurnal_peak,
            distinguishes=True,
            note=(
                "The target's warmest hour is mid-afternoon and its coldest is "
                "pre-dawn. None of the rival station-days has that phase, so the "
                "battery is expected to pass this one."
            ),
        ),
        ReferenceClaim(
            name="hourly_celsius_record",
            claim=hourly_celsius_record,
            distinguishes=False,
            note=(
                "Being a 24-row hourly file in plausible Celsius is a property of "
                "the network's file format, which every rival has too. The battery "
                "is expected to kill this one."
            ),
        ),
    ),
    detectors=(
        NamedDetector(
            name="record_quality_control",
            fires=_record_fails_qc,
            probe=None,
            note=(
                "fires when a station-day fails QC: wrong row count, non-hourly or "
                "non-monotone timestamps, a channel outside its physical range, or "
                "a temperature stuck for five hours or more"
            ),
        ),
        NamedDetector(
            name="cadence_and_channel_audit",
            fires=_cadence_and_channels_broken,
            probe=None,
            note=(
                "a second pass over the same failure modes keyed on the hour index "
                "rather than the timestamp"
            ),
        ),
    ),
    scope=(
        "Surviving this battery means only that a claim about this station-day is "
        "not equally true of the other station-days from the same network listed "
        "here, is not reproduced by these two ablations or these two null "
        "generators, and is stated against detectors whose power on four planted "
        "faults has been measured. It says nothing about whether the claim is "
        "meteorologically correct, whether it generalises beyond these four "
        "station-days, or whether the sensors were calibrated."
    ),
    provenance=Provenance(
        authored_by="party01, blind-authoring experiment",
        authored_on="2026-08-09",
        independent_of_subject_author=False,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        instruments_share_critical_dependency=False,
        edited_after_observing_failures=False,
        notes=(
            "Battery content and subject records were authored by the same process; "
            "that is one line of evidence, not two."
        ),
    ),
)
