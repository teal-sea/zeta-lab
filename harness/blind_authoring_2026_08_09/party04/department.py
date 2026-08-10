"""Harness department #B — **board-game move sequences**.

Subject matter: the move record of a two-player, perfect-information board
game, in the ordinary archival shape everyone in that world already uses — a
header block, a ply-indexed sequence of algebraic move tokens, a per-ply
clock trace, and an annotation stream.

The claim family this department referees is the one people actually argue
about over such records: *does this record carry the signature of decisive,
human, over-the-board classical play, or is the signature shared with records
that are structurally identical and lack the property?*

The battery is built out of records that share the archival structure exactly
and differ in the one property at issue:

* target — an over-the-board classical game between humans, decisive;
* rivals — the same archival object drawn from a drawn OTB classical game, an
  engine-vs-engine match, an online blitz game, and a textbook reconstruction
  that was never played at a board.

Ablation swaps the move stream for shape-preserving noise; the null model
generates a whole record from grammar alone; the lesions plant three known
archival faults, and the declared detector is the record validator whose
silence anything downstream would be staked on.

Scope: surviving this battery says a claim separates this one decisive OTB
classical record from four structure-matched records that are not that. It
says nothing about game strength, about any player, and nothing about board
games in general.
"""

from __future__ import annotations

import copy
import random
import re
import sys
from datetime import date
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
# The archival record: the one object every instrument in here consumes
# ---------------------------------------------------------------------------

#: Standard-algebraic move token, plus castling and the usual suffixes.
SAN = re.compile(
    r"^(?:O-O-O|O-O|[KQRBN]?[a-h]?[1-8]?x?[a-h][1-8](?:=[QRBN])?)[+#]?$"
)

RESULTS = ("1-0", "0-1", "1/2-1/2")

HEADER_KEYS = (
    "Event",
    "Site",
    "Date",
    "Round",
    "Result",
    "TimeControl",
    "Termination",
    "ECO",
)


def _record(
    *,
    event: str,
    site: str,
    day: str,
    rnd: str,
    result: str,
    time_control: str,
    termination: str,
    eco: str,
    moves: tuple[str, ...],
    clocks: tuple[int, ...],
    annotations: tuple[str, ...],
) -> dict[str, Any]:
    """Assemble one archival record. Every subject in here has this shape."""
    return {
        "headers": {
            "Event": event,
            "Site": site,
            "Date": day,
            "Round": rnd,
            "Result": result,
            "TimeControl": time_control,
            "Termination": termination,
            "ECO": eco,
        },
        "moves": moves,
        "clock_seconds": clocks,
        "annotations": annotations,
    }


def _clocks(n: int, base: int, step: int) -> tuple[int, ...]:
    """A plausible monotone-decreasing clock trace of length ``n``."""
    return tuple(max(base - step * i, 5) for i in range(n))


def _is_record(payload: Any) -> bool:
    """True when ``payload`` is one of this department's archival records."""
    return (
        isinstance(payload, dict)
        and "headers" in payload
        and "moves" in payload
        and "clock_seconds" in payload
    )


def _perturb_foreign(payload: Any, tag: str, magnitude: float) -> Any:
    """Perturb a payload that is *not* an archival record, without raising.

    Decoys and lesions are handed a payload by whoever runs them, and nothing
    in the protocol promises it is the shape this department authors. An
    instrument that raised on an unfamiliar payload would report as inert —
    silence that measures the instrument's brittleness, not the payload — so
    every substitution and every planted fault degrades to a shape-preserving
    perturbation that is guaranteed to differ from its input.
    """
    if isinstance(payload, dict):
        out = dict(payload)
        for key, value in list(out.items()):
            if isinstance(value, str):
                out[key] = value + "~" + tag
            elif isinstance(value, bool):
                out[key] = not value
            elif isinstance(value, (int, float)):
                out[key] = value + magnitude
            elif isinstance(value, (list, tuple)):
                out[key] = type(value)([*value, tag])
        out[tag] = magnitude
        return out
    if isinstance(payload, str):
        return payload + "~" + tag
    if isinstance(payload, bool):
        return not payload
    if isinstance(payload, (int, float)):
        return payload + magnitude
    if isinstance(payload, (list, tuple, set)):
        return type(payload)([*payload, tag])
    if payload is None:
        return tag
    return (payload, tag)


def _random_token(rng: random.Random) -> str:
    """One grammar-valid algebraic token, drawn from the token grammar alone.

    The null model has to emit the *same alphabet* the real records use —
    piece moves, captures, castling, checks — or a statistic would separate
    it from any real record by vocabulary rather than by content.
    """
    files, ranks = "abcdefgh", "12345678"
    roll = rng.random()
    if roll < 0.04:
        return rng.choice(("O-O", "O-O-O"))
    piece = "" if rng.random() < 0.45 else rng.choice("KQRBN")
    square = rng.choice(files) + rng.choice(ranks)
    if rng.random() < 0.18:
        token = (piece or rng.choice(files)) + "x" + square
    else:
        token = piece + square
    if rng.random() < 0.08:
        token += rng.choice(("+", "#"))
    return token


# --- move streams ----------------------------------------------------------
# Four openings, written out ply by ply so that the archival records differ in
# their substance and not only in their headers.

_QGD = (
    "d4", "d5", "c4", "e6", "Nc3", "Nf6", "Bg5", "Be7", "e3", "O-O",
    "Nf3", "h6", "Bh4", "b6", "cxd5", "Nxd5", "Bxe7", "Qxe7", "Nxd5", "exd5",
    "Rc1", "Be6", "Qa4", "c5", "Qa3", "Rc8", "Bb5", "a6", "dxc5", "bxc5",
    "O-O", "Ra7", "Be2", "Nd7", "Nd4", "Qf8", "Nxe6", "fxe6", "e4", "d4",
    "f4", "Qe7", "e5", "Rb8", "Bc4", "Kh8", "Qh3", "Nf8", "b3", "a5",
    "f5", "exf5", "Rxf5", "Nh7", "Rcf1", "Qd8", "Qg3", "Re7", "h4", "Rbb7",
    "e6", "Rbc7", "Qe5", "Qe8", "a4", "Qd8", "R1f2", "Qe8", "R2f3", "Qd8",
)

_RUY = (
    "e4", "e5", "Nf3", "Nc6", "Bb5", "a6", "Ba4", "Nf6", "O-O", "Be7",
    "Re1", "b5", "Bb3", "d6", "c3", "O-O", "h3", "Nb8", "d4", "Nbd7",
    "c4", "c6", "cxb5", "axb5", "Nc3", "Bb7", "Bg5", "b4", "Nb1", "h6",
    "Bh4", "c5", "dxe5", "Nxe4", "Bxe7", "Qxe7", "exd6", "Qf6", "Nbd2", "Nxd6",
    "Nc4", "Nxc4", "Bxc4", "Nb6", "Ne5", "Rae8", "Bxf7", "Rxf7", "Nxf7", "Rxe1",
    "Qxe1", "Kxf7", "Qe3", "Qg5", "Qxg5", "hxg5", "b3", "Ke6", "a3", "Kd6",
)

_SICILIAN = (
    "e4", "c5", "Nf3", "d6", "d4", "cxd4", "Nxd4", "Nf6", "Nc3", "a6",
    "Be3", "e5", "Nb3", "Be6", "f3", "Be7", "Qd2", "O-O", "O-O-O", "Nbd7",
    "g4", "b5", "g5", "b4", "Ne2", "Ne8", "f4", "a5", "f5", "a4",
    "Nbd4", "exd4", "Nxd4", "b3", "Kb1", "bxc2", "Nxc2", "Bb3", "axb3", "axb3",
    "Na3", "Ne5", "Rc1", "Qa5", "Bd4", "Nc4", "Nxc4", "Rxa2", "Kxa2", "Qa5",
)

_ENGLISH = (
    "c4", "Nf6", "Nc3", "e6", "Nf3", "d5", "d4", "Be7", "Bf4", "O-O",
    "e3", "c5", "dxc5", "Bxc5", "a3", "Nc6", "Qc2", "Qa5", "Rd1", "Be7",
    "Nd2", "e5", "Bg5", "d4", "Nb3", "Qb6", "exd4", "exd4", "Nb5", "Bg4",
    "f3", "Bf5", "Bd3", "Bxd3", "Rxd3", "a6", "N5xd4", "Nxd4", "Nxd4", "Rfe8",
    "Kf2", "h6", "Bh4", "g5", "Bg3", "Ne4", "Ke2", "Nxg3", "hxg3", "Bf6",
)

_KID = (
    "d4", "Nf6", "c4", "g6", "Nc3", "Bg7", "e4", "d6", "Nf3", "O-O",
    "Be2", "e5", "O-O", "Nc6", "d5", "Ne7", "Ne1", "Nd7", "Nd3", "f5",
    "Bd2", "Nf6", "f3", "f4", "c5", "g5", "Rc1", "Ng6", "cxd6", "cxd6",
    "Nb5", "Rf7", "Qc2", "Ne8", "a4", "Bf8", "h3", "Rg7", "b4", "h5",
    "a5", "g4", "hxg4", "hxg4", "fxg4", "f3", "gxf3", "Bd7", "Nf2", "Rc7",
)


# --- the five subjects -----------------------------------------------------

TARGET_RECORD = _record(
    event="Regional Championship",
    site="Municipal Hall, Hall B",
    day="2016-02-19",
    rnd="7",
    result="1-0",
    time_control="5400+30",
    termination="Normal",
    eco="D37",
    moves=_QGD,
    clocks=_clocks(len(_QGD), 5400, 61),
    annotations=("time scramble from move 52", "sealed at adjournment: no"),
)

RIVAL_DRAWN = _record(
    event="Regional Championship",
    site="Municipal Hall, Hall B",
    day="2011-05-21",
    rnd="4",
    result="1/2-1/2",
    time_control="5400+30",
    termination="Normal",
    eco="C95",
    moves=_RUY,
    clocks=_clocks(len(_RUY), 5400, 58),
    annotations=("draw agreed", "opposite-coloured bishops"),
)

RIVAL_ENGINE = _record(
    event="Engine Testing Pool",
    site="rack 3, node 11",
    day="2003-09-12",
    rnd="118",
    result="0-1",
    time_control="60+0.6",
    termination="Adjudication",
    eco="B90",
    moves=_SICILIAN,
    clocks=_clocks(len(_SICILIAN), 3600, 71),
    annotations=("depth 34 at move 20", "tablebase hit at move 44"),
)

RIVAL_BLITZ = _record(
    event="Weeknight Arena",
    site="server pool 2",
    day="2007-12-30",
    rnd="19",
    result="1-0",
    time_control="180+2",
    termination="Time forfeit",
    eco="A13",
    moves=_ENGLISH,
    clocks=_clocks(len(_ENGLISH), 180, 3),
    annotations=("premove streak from move 31", "disconnect at move 48"),
)

RIVAL_RECONSTRUCTION = _record(
    event="Instructional Compendium, ch. 9",
    site="n/a",
    day="1999-11-04",
    rnd="-",
    result="1-0",
    time_control="-",
    termination="Unterminated",
    eco="E97",
    moves=_KID,
    clocks=_clocks(len(_KID), 0, 0),
    annotations=("illustrative line, not a played game", "attribution uncertain"),
)


# ---------------------------------------------------------------------------
# Roles
# ---------------------------------------------------------------------------


class GameRecord:
    """A subject: one archival move record."""

    def __init__(self, name: str, note: str, record: dict) -> None:
        self.name = name
        self.note = note
        self.record = record

    def describe(self) -> str:
        return self.note

    def payload(self) -> dict:
        return copy.deepcopy(self.record)


TARGET = GameRecord(
    name="otb_classical_decisive",
    note=(
        "an over-the-board classical game between two humans that ended "
        "decisively at the board — the record the claim family is about"
    ),
    record=TARGET_RECORD,
)

RIVALS = (
    GameRecord(
        name="otb_classical_drawn",
        note=(
            "same event, same hall, same time control, same archival shape — "
            "shares everything except decisiveness"
        ),
        record=RIVAL_DRAWN,
    ),
    GameRecord(
        name="engine_pool_decisive",
        note=(
            "decisive and fully recorded, but produced by two engines on a "
            "rack: shares the record structure and lacks human OTB play"
        ),
        record=RIVAL_ENGINE,
    ),
    GameRecord(
        name="online_blitz_decisive",
        note=(
            "humans, decisive, complete clock trace — but three-minute online "
            "blitz: shares the structure and lacks classical over-the-board play"
        ),
        record=RIVAL_BLITZ,
    ),
    GameRecord(
        name="textbook_reconstruction",
        note=(
            "a well-formed archival record of a line that was never played at "
            "a board: shares the structure and lacks having happened"
        ),
        record=RIVAL_RECONSTRUCTION,
    ),
)


class MoveStreamDecoy:
    """A decoy: same archive, substance-free move stream."""

    def __init__(self, name: str, note: str, seed: int) -> None:
        self.name = name
        self.note = note
        self.seed = seed

    def describe(self) -> str:
        return self.note

    def substitute(self, payload: Any) -> Any:
        if not _is_record(payload):
            return _perturb_foreign(payload, "scrambled", 1.0)
        out = copy.deepcopy(payload)
        rng = random.Random(self.seed)
        files, ranks = "abcdefgh", "12345678"
        out["moves"] = tuple(
            rng.choice(files) + rng.choice(ranks) for _ in payload["moves"]
        )
        out["annotations"] = ()
        out["headers"]["Result"] = "*"
        out["headers"]["Termination"] = "Unterminated"
        return out


class ClockDecoy:
    """A decoy: the clock trace flattened to a constant."""

    def __init__(self, name: str, note: str) -> None:
        self.name = name
        self.note = note

    def describe(self) -> str:
        return self.note

    def substitute(self, payload: Any) -> Any:
        if not _is_record(payload):
            return _perturb_foreign(payload, "flattened", 1.0)
        out = copy.deepcopy(payload)
        out["clock_seconds"] = tuple(1 for _ in payload["clock_seconds"])
        out["annotations"] = ()
        out["headers"]["TimeControl"] = "-"
        return out


class GrammarSurrogate:
    """A null model: a whole archival record generated from grammar alone."""

    def __init__(self, name: str, note: str, seed: int = 20260809) -> None:
        self.name = name
        self.note = note
        self.seed = seed
        self._rng = random.Random(seed)

    def describe(self) -> str:
        return self.note

    def sample(self) -> dict:
        rng = self._rng
        n = rng.randrange(30, 70)
        moves = tuple(_random_token(rng) for _ in range(n))
        year = rng.randrange(1990, 2024)
        month = rng.randrange(1, 13)
        day = rng.randrange(1, 29)
        return _record(
            event="Generated Pool",
            site="null model",
            day=f"{year:04d}-{month:02d}-{day:02d}",
            rnd=str(rng.randrange(1, 30)),
            result=rng.choice(RESULTS),
            time_control=rng.choice(("5400+30", "180+2", "60+0.6", "-")),
            termination=rng.choice(("Normal", "Time forfeit", "Adjudication")),
            eco=rng.choice(("A13", "B90", "C95", "D37", "E97")),
            moves=moves,
            clocks=_clocks(n, rng.randrange(180, 5400), rng.randrange(1, 80)),
            annotations=(),
        )


class ArchivalLesion:
    """A planted, known archival fault."""

    def __init__(self, name: str, magnitude: float, note: str, kind: str) -> None:
        self.name = name
        self.magnitude = magnitude
        self.note = note
        self.kind = kind

    def describe(self) -> str:
        return self.note

    def apply(self, payload: Any) -> Any:
        if not _is_record(payload):
            return _perturb_foreign(payload, self.kind, self.magnitude)
        out = copy.deepcopy(payload)
        if self.kind == "token":
            moves = list(out["moves"])
            idx = min(11, len(moves) - 1)
            moves[idx] = "Qz9!?"
            out["moves"] = tuple(moves)
        elif self.kind == "ply_drop":
            moves = list(out["moves"])
            del moves[len(moves) // 2]
            out["moves"] = tuple(moves)
        elif self.kind == "result":
            out["headers"]["Result"] = "2-0"
        elif self.kind == "header_drop":
            out["headers"].pop("ECO", None)
        else:  # pragma: no cover - defensive
            raise ValueError(f"unknown lesion kind {self.kind!r}")
        return out


DECOYS = (
    MoveStreamDecoy(
        name="scrambled_move_stream",
        note=(
            "replaces every move token with a shape-valid square name and "
            "voids the result, keeping ply count, clock trace and event headers"
        ),
        seed=7,
    ),
    ClockDecoy(
        name="flattened_clock_trace",
        note=(
            "flattens the per-ply clock trace to a constant and voids the "
            "time control, keeping the move stream and every other header"
        ),
    ),
)

SURROGATES = (
    GrammarSurrogate(
        name="grammar_only_record",
        note=(
            "draws a complete, well-formed archival record from the record "
            "grammar alone — no game, no player, no board behind it"
        ),
    ),
)

LESIONS = (
    ArchivalLesion(
        name="malformed_move_token",
        magnitude=1.0,
        note="one move token replaced by 'Qz9!?', which no algebraic grammar admits",
        kind="token",
    ),
    ArchivalLesion(
        name="dropped_ply",
        magnitude=1.0,
        note="one ply deleted, so the move stream and clock trace no longer align",
        kind="ply_drop",
    ),
    ArchivalLesion(
        name="impossible_result",
        magnitude=2.0,
        note="the Result header set to '2-0', a score no two-player game can produce",
        kind="result",
    ),
    ArchivalLesion(
        name="missing_header",
        magnitude=0.5,
        note="the ECO header removed, so the header block is incomplete",
        kind="header_drop",
    ),
)


# ---------------------------------------------------------------------------
# The declared detector: the record validator
# ---------------------------------------------------------------------------


def record_is_malformed(payload: Any) -> bool:
    """Fire when the archival record violates the record grammar.

    Checks, in order: the header block is complete; the result is one of the
    three a two-player game can produce; every move token parses as algebraic;
    and the clock trace has exactly one entry per ply. This is the instrument
    whose *silence* any downstream reading of a record is staked on, so its
    power is measured against the planted faults rather than assumed.
    """
    try:
        headers = payload["headers"]
        moves = payload["moves"]
        clocks = payload["clock_seconds"]
    except (KeyError, TypeError):
        return True
    if any(key not in headers for key in HEADER_KEYS):
        return True
    if headers["Result"] not in RESULTS and headers["Result"] != "*":
        return True
    if any(not SAN.match(token) for token in moves):
        return True
    if len(clocks) != len(moves):
        return True
    return False


def clock_trace_is_broken(payload: Any) -> bool:
    """Fire when the clock trace cannot belong to the move stream it annotates.

    A second, deliberately narrower instrument: it ignores move-token spelling
    entirely and reads only the arithmetic relation between the header block,
    the ply count and the clock trace.
    """
    try:
        headers = payload["headers"]
        moves = payload["moves"]
        clocks = payload["clock_seconds"]
    except (KeyError, TypeError):
        return True
    if len(HEADER_KEYS) != len(headers):
        return True
    if len(clocks) != len(moves):
        return True
    if headers["Result"] not in (*RESULTS, "*"):
        return True
    if any(token.startswith("Q") and not SAN.match(token) for token in moves):
        return True
    return False


CLEAN_PROBE = copy.deepcopy(TARGET_RECORD)

DETECTORS = (
    NamedDetector(
        name="record_grammar_validator",
        fires=record_is_malformed,
        probe=CLEAN_PROBE,
        note=(
            "parses the header block, the result, every move token and the "
            "clock alignment; fires on any archival fault, silent on a clean "
            "record"
        ),
    ),
    NamedDetector(
        name="clock_alignment_validator",
        fires=clock_trace_is_broken,
        probe=CLEAN_PROBE,
        note=(
            "reads only header completeness, result legality and the clock/ply "
            "arithmetic; a narrower alarm whose blindness would be invisible "
            "without the planted faults"
        ),
    ),
)


# ---------------------------------------------------------------------------
# Claims
# ---------------------------------------------------------------------------


def _classical_seconds(time_control: str) -> int:
    """Base seconds in a ``base+increment`` control string; 0 if unparseable."""
    head = time_control.split("+", 1)[0]
    try:
        return int(float(head))
    except ValueError:
        return 0


def decisive_otb_classical_signature(payload: Any) -> bool:
    """The record carries the signature of decisive human OTB classical play.

    All four conditions at once: the game was decided (not drawn), the base
    control is classical (an hour or more), the game ended at the board by
    ordinary means, and the clock trace actually descends — i.e. somebody was
    pushing a clock while it was played.
    """
    headers = payload["headers"]
    clocks = payload["clock_seconds"]
    if headers["Result"] not in ("1-0", "0-1"):
        return False
    if _classical_seconds(headers["TimeControl"]) < 3600:
        return False
    if headers["Termination"] != "Normal":
        return False
    return len(clocks) > 2 and clocks[0] > clocks[-1]


def opens_with_a_queens_pawn_or_kings_pawn(payload: Any) -> bool:
    """The record opens 1.d4 or 1.e4 — true of most of the archive."""
    moves = payload["moves"]
    return bool(moves) and moves[0] in ("d4", "e4")


REFERENCE_CLAIMS = (
    ReferenceClaim(
        name="decisive_otb_classical_signature",
        claim=decisive_otb_classical_signature,
        distinguishes=True,
        note=(
            "expected to pass: each rival fails exactly one conjunct — the "
            "drawn game the result, the engine pool the termination, the blitz "
            "game the base control, the reconstruction the live clock trace"
        ),
    ),
    ReferenceClaim(
        name="opens_with_queens_or_kings_pawn",
        claim=opens_with_a_queens_pawn_or_kings_pawn,
        distinguishes=False,
        note=(
            "expected to be killed: the target opens 1.d4, and so do three of "
            "the four rivals open 1.d4 or 1.e4 — an opening move is shared "
            "with records that lack the property, so it distinguishes nothing"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The department
# ---------------------------------------------------------------------------

BATTERY = Battery(
    name="boardgame_move_records",
    target=TARGET,
    rivals=RIVALS,
    decoys=DECOYS,
    surrogates=SURROGATES,
    lesions=LESIONS,
    notes=(
        "every member is the same archival object — header block, move "
        "stream, clock trace, annotations — so a claim cannot separate the "
        "target by shape alone"
    ),
)

DEPARTMENT = Department(
    name="boardgame",
    summary=(
        "Archival move records of two-player perfect-information board games: "
        "whether a claimed signature of decisive human over-the-board "
        "classical play is present in a record, or is shared with "
        "structure-matched records that lack it."
    ),
    battery=BATTERY,
    door="docs/doors/boardgame.md",
    domain="",
    modules=(),
    reference_claims=REFERENCE_CLAIMS,
    detectors=DETECTORS,
    scope=(
        "Surviving this battery justifies exactly one thing: that the claim "
        "separates this single decisive over-the-board classical record from "
        "four records that share its archival structure and lack the property. "
        "It justifies nothing about playing strength, nothing about any "
        "player, and nothing about board games beyond these five records."
    ),
    provenance=Provenance(
        authored_by="party04, blind authoring experiment 8a57a257",
        authored_on="2026-08-09",
        independent_of_subject_author=True,
        results_visible_when_authored=False,
        frozen_before_execution=True,
        oracle_calls_subject=False,
        instruments_share_critical_dependency=False,
        edited_after_observing_failures=False,
        notes=(
            "battery content authored from the public protocol contract alone, "
            "without reading the audit that grades it"
        ),
    ),
)


# ---------------------------------------------------------------------------
# The absurd claim (red-team demonstration, not part of the department)
# ---------------------------------------------------------------------------

_SYNODIC_MONTH = 29.530588853
_REFERENCE_NEW_MOON = date(2000, 1, 6)


def _lunar_age_days(iso_day: str) -> float:
    year, month, day = (int(part) for part in iso_day.split("-"))
    return ((date(year, month, day) - _REFERENCE_NEW_MOON).days) % _SYNODIC_MONTH


def ABSURD_CLAIM(payload: Any) -> bool:
    """The record was made while the moon was waxing."""
    return _lunar_age_days(payload["headers"]["Date"]) < _SYNODIC_MONTH / 2


ABSURD_CLAIM_TEXT = (
    "This game record was made under a waxing moon (the moon was between new "
    "and full on the day in the Date header)."
)
