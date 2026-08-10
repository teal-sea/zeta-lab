"""Harness department: **musical chord progressions** (toy domain).

Subject: recorded chord progressions represented as a session record — a key,
a mode, a sequence of roman-numeral chord symbols, their durations, and the
provenance of the take that produced them.  The department's question is the
usual one: *does a claim about harmonic structure hold for this progression
and fail for progressions that share its shape but lack the property?*

The battery is built out of material the domain already has: real cadential
alternatives as rivals (a modal vamp with no dominant, a chromatic-mediant
cycle, a plagal hymn close), two ablations that keep the rhythm and delete the
harmony, two null models that generate progressions from no musical intent,
and three planted harmonic faults whose detection is staked on two declared
alarms.
"""

from __future__ import annotations

import random
import sys

sys.path.insert(0, "/Users/thomas/Zeta")

from harness.protocol import (  # noqa: E402
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
)
from harness.provenance import Provenance  # noqa: E402

# ---------------------------------------------------------------------------
# The record type the whole department speaks
# ---------------------------------------------------------------------------

DIATONIC_MAJOR = ("I", "ii", "iii", "IV", "V", "vi", "vii")
DIATONIC_DORIAN = ("i", "II", "III", "IV", "v", "vi", "VII")


def _record(
    ident: str,
    key: str,
    mode: str,
    chords: tuple[str, ...],
    durations: tuple[int, ...],
    session: dict,
) -> dict:
    """One take of one progression, with the session provenance attached."""
    return {
        "id": ident,
        "key": key,
        "mode": mode,
        "chords": tuple(chords),
        "durations": tuple(durations),
        "session": dict(session),
    }


def _copy(payload: dict) -> dict:
    out = dict(payload)
    out["chords"] = tuple(payload["chords"])
    out["durations"] = tuple(payload["durations"])
    out["session"] = dict(payload["session"])
    return out


def _root(symbol: str) -> str:
    """Strip chord quality/extension, leaving the roman-numeral scale degree."""
    keep = []
    for ch in symbol:
        if ch.isdigit():
            break
        keep.append(ch)
    root = "".join(keep)
    for suffix in ("maj", "dim", "aug", "sus", "add", "m"):
        if root.endswith(suffix) and len(root) > len(suffix):
            root = root[: -len(suffix)]
    return root


def _scale(payload: dict) -> tuple[str, ...]:
    return DIATONIC_DORIAN if payload["mode"] == "dorian" else DIATONIC_MAJOR


def _is_take(payload) -> bool:
    """Is this one of this department's session records?"""
    return isinstance(payload, dict) and "chords" in payload and "mode" in payload


# -- Totality --------------------------------------------------------------
# The instruments below are also handed payloads that are not session records
# (a bare sequence, an empty container, a number).  A decoy that raises on an
# unfamiliar shape has emptied nothing and a lesion that raises has planted
# nothing, so both fall back to a shape-preserving generic form rather than
# to an exception.


def _emptied(value):
    """The same shape with its content replaced by a neutral element."""
    if isinstance(value, bool):
        return False
    if isinstance(value, (int, float)):
        return type(value)(0)
    if isinstance(value, str):
        return ""
    if isinstance(value, (list, tuple, set)):
        return type(value)(_emptied(v) for v in value)
    if isinstance(value, dict):
        return {k: _emptied(v) for k, v in value.items()}
    return None


def _generic_substitute(payload, tag: str):
    try:
        blank = _emptied(payload)
        if blank != payload:
            return blank
    except Exception:  # noqa: BLE001 - fall through to the wrapper
        pass
    return {"substituted_by": tag, "shape_of": repr(type(payload).__name__), "was": payload}


def _generic_lesion(payload, tag: str, magnitude: float):
    """Plant a visible foreign element in a payload of unknown shape."""
    if isinstance(payload, list):
        return [*payload, tag]
    if isinstance(payload, tuple):
        return (*payload, tag)
    if isinstance(payload, dict):
        out = dict(payload)
        out["planted_fault"] = tag
        return out
    if isinstance(payload, str):
        return payload + "|" + tag
    if isinstance(payload, bool):
        return not payload
    if isinstance(payload, (int, float)):
        return type(payload)(payload + magnitude)
    return {"planted_fault": tag, "host": payload}


# ---------------------------------------------------------------------------
# Subjects: the target and the rivals
# ---------------------------------------------------------------------------


class Progression:
    """A recorded progression. Target and rivals share this interface."""

    def __init__(self, name: str, note: str, record: dict) -> None:
        self.name = name
        self._note = note
        self._record = record

    def describe(self) -> str:
        return self._note

    def payload(self) -> dict:
        return _copy(self._record)


TARGET = Progression(
    "standard_ii_V_I_turnaround",
    "seven-bar jazz turnaround in C major; closes V7 -> Imaj7, the authentic "
    "cadence whose leading-tone resolution the department's claims are about",
    _record(
        "take-C-1947",
        "C",
        "major",
        ("ii7", "V7", "Imaj7", "vi7", "ii7", "V7", "Imaj7"),
        (4, 4, 4, 4, 4, 4, 8),
        {
            "venue": "Studio A, 12th Street",
            "engineer": "R. Vandelay",
            "date": "2019-03-21",
            "lunar_phase": "waxing gibbous",
            "reference_pitch_hz": 440.0,
            "take": 3,
            "tape_speed_ips": 15,
        },
    ),
)

RIVALS = (
    Progression(
        "modal_vamp_dorian",
        "two-chord D-dorian vamp: same record shape, same bar count, but the "
        "mode supplies no dominant, so no authentic cadence is available",
        _record(
            "take-D-2203",
            "D",
            "dorian",
            ("i7", "IV7", "i7", "IV7", "i7", "IV7", "i7"),
            (4, 4, 4, 4, 4, 4, 8),
            {
                "venue": "St. Ambrose Church Hall",
                "engineer": "P. Okonkwo",
                "date": "2021-11-04",
                "lunar_phase": "new moon",
                "reference_pitch_hz": 432.0,
                "take": 1,
                "tape_speed_ips": 7,
            },
        ),
    ),
    Progression(
        "chromatic_mediant_cycle",
        "E-flat major chromatic-mediant cycle: same shape and same closing "
        "tonic, reached by root motion of a third rather than by a dominant",
        _record(
            "take-Eb-0518",
            "Eb",
            "major",
            ("I", "bIII", "bVI", "I", "bIII", "bVI", "I"),
            (4, 4, 4, 4, 4, 4, 8),
            {
                "venue": "Hall of Mirrors",
                "engineer": "L. Brandt",
                "date": "2017-06-30",
                "lunar_phase": "waning crescent",
                "reference_pitch_hz": 415.0,
                "take": 12,
                "tape_speed_ips": 30,
            },
        ),
    ),
    Progression(
        "plagal_hymn_close",
        "G major hymn setting: same shape, closes IV -> I, the plagal 'amen' "
        "cadence — a close without the leading-tone resolution",
        _record(
            "take-G-3310",
            "G",
            "major",
            ("I", "IV", "I", "vi", "IV", "IV", "I"),
            (4, 4, 4, 4, 4, 4, 8),
            {
                "venue": "Rehearsal Room 2",
                "engineer": "M. Tsuji",
                "date": "2023-01-09",
                "lunar_phase": "full",
                "reference_pitch_hz": 442.0,
                "take": 5,
                "tape_speed_ips": 15,
            },
        ),
    ),
    Progression(
        "deceptive_close_ballad",
        "A minor ballad of the same shape whose dominant resolves to vi "
        "instead of I — the deceptive cadence, the nearest miss available",
        _record(
            "take-A-7781",
            "A",
            "major",
            ("ii7", "V7", "vi7", "IV", "ii7", "V7", "vi7"),
            (4, 4, 4, 4, 4, 4, 8),
            {
                "venue": "Bell Sound, Room 4",
                "engineer": "D. Ferreira",
                "date": "2015-08-17",
                "lunar_phase": "waning gibbous",
                "reference_pitch_hz": 439.0,
                "take": 9,
                "tape_speed_ips": 15,
            },
        ),
    ),
)


# ---------------------------------------------------------------------------
# Decoys: keep the rhythm, delete the harmony
# ---------------------------------------------------------------------------


class ChordsScrubbed:
    name = "chord_symbols_scrubbed"

    def describe(self) -> str:
        return (
            "every chord symbol replaced by 'N.C.' (no chord); bar count, "
            "durations, key, mode and session metadata preserved exactly"
        )

    def substitute(self, payload):
        if not _is_take(payload):
            return _generic_substitute(payload, self.name)
        out = _copy(payload)
        out["chords"] = tuple("N.C." for _ in payload["chords"])
        return out


class SlashNotationOnly:
    name = "harmony_reduced_to_slash_marks"

    def describe(self) -> str:
        return (
            "every bar replaced by the rhythm-slash mark 'x' — play the "
            "groove, no pitch content; metre, length, key and session "
            "metadata preserved, harmonic identity gone"
        )

    def substitute(self, payload):
        if not _is_take(payload):
            return _generic_substitute(payload, self.name)
        out = _copy(payload)
        out["chords"] = tuple("x" for _ in payload["chords"])
        return out


# ---------------------------------------------------------------------------
# Surrogates: progressions from no musical intent
# ---------------------------------------------------------------------------


class UniformDiatonicWalk:
    name = "uniform_random_diatonic"

    def __init__(self, seed: int = 20240719) -> None:
        self._rng = random.Random(seed)

    def describe(self) -> str:
        return (
            "each bar drawn independently and uniformly from the seven "
            "diatonic degrees: same alphabet, same length, no voice leading"
        )

    def sample(self) -> dict:
        chords = tuple(self._rng.choice(DIATONIC_MAJOR) for _ in range(7))
        return _record(
            f"surrogate-uniform-{self._rng.randrange(10**6)}",
            "C",
            "major",
            chords,
            (4, 4, 4, 4, 4, 4, 8),
            {
                "venue": "(synthetic)",
                "engineer": "(none)",
                "date": "(none)",
                "lunar_phase": "(none)",
                "reference_pitch_hz": 440.0,
                "take": 0,
                "tape_speed_ips": 0,
            },
        )


class ChordBagShuffle:
    name = "chord_bag_shuffle"

    def __init__(self, seed: int = 991) -> None:
        self._rng = random.Random(seed)

    def describe(self) -> str:
        return (
            "the target's own chord multiset, re-ordered at random: the "
            "harmonic vocabulary is preserved and the syntax is destroyed"
        )

    def sample(self) -> dict:
        bag = list(TARGET.payload()["chords"])
        self._rng.shuffle(bag)
        out = TARGET.payload()
        out["id"] = f"surrogate-shuffle-{self._rng.randrange(10**6)}"
        out["chords"] = tuple(bag)
        out["session"] = {
            "venue": "(synthetic)",
            "engineer": "(none)",
            "date": "(none)",
            "lunar_phase": "(none)",
            "reference_pitch_hz": 440.0,
            "take": 0,
            "tape_speed_ips": 0,
        }
        return out


# ---------------------------------------------------------------------------
# Lesions: planted harmonic faults
# ---------------------------------------------------------------------------


class Lesion:
    def __init__(self, name: str, note: str, magnitude: float, tail: tuple[str, ...]) -> None:
        self.name = name
        self.magnitude = magnitude
        self._note = note
        self._tail = tail

    def describe(self) -> str:
        return self._note

    def apply(self, payload):
        if not _is_take(payload):
            return _generic_lesion(payload, self.name, self.magnitude)
        out = _copy(payload)
        chords = list(payload["chords"])
        n = len(self._tail)
        chords[-n:] = list(self._tail)
        out["chords"] = tuple(chords)
        return out


LESIONS = (
    Lesion(
        "tritone_substituted_close",
        "the closing tonic is replaced by bII7, a chromatic chord: one bar "
        "altered, the authentic cadence destroyed",
        1.0,
        ("bII7",),
    ),
    Lesion(
        "borrowed_parallel_minor_tail",
        "the final two bars are replaced by bVII -> bIII, both borrowed from "
        "the parallel minor: two bars altered",
        2.0,
        ("bVII", "bIII"),
    ),
    Lesion(
        "chromatic_planing_tail",
        "the final three bars are planed chromatically (#IV7 -> bVI -> bII): "
        "three bars altered, key centre abandoned",
        3.0,
        ("#IV7", "bVI", "bII"),
    ),
)


# ---------------------------------------------------------------------------
# Detectors: the alarms this department stakes its silence on
# ---------------------------------------------------------------------------


_LESION_TAGS = frozenset(
    ("tritone_substituted_close", "borrowed_parallel_minor_tail", "chromatic_planing_tail")
)


def _foreign_element(payload) -> bool:
    """A planted fault in a payload that is not one of our session records."""
    if isinstance(payload, dict):
        return "planted_fault" in payload
    if isinstance(payload, (list, tuple, set)):
        return any(isinstance(v, str) and v in _LESION_TAGS for v in payload)
    if isinstance(payload, str):
        return any(tag in payload for tag in _LESION_TAGS)
    return False


def _has_nondiatonic(payload) -> bool:
    if not _is_take(payload):
        return _foreign_element(payload)
    scale = _scale(payload)
    return any(_root(c) not in scale for c in payload["chords"])


def _cadence_broken(payload) -> bool:
    if not _is_take(payload):
        return _foreign_element(payload)
    chords = payload["chords"]
    if len(chords) < 2:
        return True
    return not (_root(chords[-2]) == "V" and _root(chords[-1]) == "I")


CLEAN_PROBE = TARGET.payload()

DETECTORS = (
    NamedDetector(
        name="nondiatonic_chord_alarm",
        fires=_has_nondiatonic,
        probe=TARGET.payload(),
        note=(
            "fires when any bar carries a chord whose root lies outside the "
            "declared key's scale; quiet on the clean take"
        ),
    ),
    NamedDetector(
        name="broken_cadence_alarm",
        fires=_cadence_broken,
        probe=TARGET.payload(),
        note=(
            "fires when the final two bars are not dominant -> tonic; quiet "
            "on the clean take, which closes V7 -> Imaj7"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Reference claims: one the battery must pass, one it must kill
# ---------------------------------------------------------------------------


def closes_with_authentic_cadence(payload) -> bool:
    """The progression ends dominant -> tonic in its own declared key."""
    if not _is_take(payload):
        return False
    chords = payload["chords"]
    return (
        len(chords) >= 2
        and _root(chords[-2]) == "V"
        and _root(chords[-1]) == "I"
        and payload["mode"] == "major"
    )


def contains_a_tonic_chord(payload) -> bool:
    """The progression touches its tonic somewhere — true of nearly anything."""
    if not _is_take(payload):
        return False
    return any(_root(c).lower() == "i" for c in payload["chords"])


REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="closes_with_authentic_cadence",
        claim=closes_with_authentic_cadence,
        distinguishes=True,
        note=(
            "holds for the turnaround and for none of the four rivals: the "
            "modal vamp has no dominant, the mediant cycle arrives by third, "
            "the hymn closes plagally, the ballad's dominant deceives"
        ),
    ),
    ReferenceClaim(
        name="contains_a_tonic_chord",
        claim=contains_a_tonic_chord,
        distinguishes=False,
        note=(
            "true of the target and of every rival: a claim about tonality "
            "so weak that it separates nothing, and the battery must say so"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="chord_progression_battery",
    target=TARGET,
    rivals=RIVALS,
    decoys=(ChordsScrubbed(), SlashNotationOnly()),
    surrogates=(UniformDiatonicWalk(), ChordBagShuffle()),
    lesions=LESIONS,
    notes=(
        "rivals are four real cadential alternatives of the same record "
        "shape; decoys keep metre and delete harmony; surrogates generate "
        "progressions with no musical intent; lesions plant chromatic faults "
        "of one, two and three bars"
    ),
)

DEPARTMENT = Department(
    name="chords",
    summary=(
        "harmonic claims about recorded chord progressions, refereed against "
        "cadential alternatives of the same record shape"
    ),
    battery=BATTERY,
    door="docs/doors/chords.md",
    domain="chords",
    modules=("blind_candidate",),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "surviving this battery means a claim about the closing harmony of "
        "one seven-bar take is not shared with four cadential alternatives "
        "of the same shape; it says nothing about any other progression, any "
        "other corpus, or whether the claim is musically interesting"
    ),
    provenance=Provenance(
        authored_by="party02 (blind department-authoring exercise)",
        authored_on="2026-08-09",
        independent_of_subject_author=True,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        instruments_share_critical_dependency=False,
        edited_after_observing_failures=False,
        notes=(
            "battery content (rivals, decoys, surrogates, lesions, reference "
            "claims) written from the public protocol contract alone"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The absurd claim, for the hollowness test
# ---------------------------------------------------------------------------

ABSURD_CLAIM_TEXT = "This progression was recorded under a waxing moon."


def ABSURD_CLAIM(payload) -> bool:  # noqa: N802 - name fixed by the task
    if not isinstance(payload, dict):
        return False
    return str(payload.get("session", {}).get("lunar_phase", "")).startswith("waxing")
