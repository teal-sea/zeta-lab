"""Tests for ``THREADS.md`` — the loose-thread ledger.

The mechanism is a flat file because a mechanism agents will not write to is
worth nothing, and every heavier option this lab has tried (a registry page, a
declared ledger, a framework) either rotted or went unused. These tests check
the shape and nothing else: ids unique and monotonic, five required fields per
block, status from a closed vocabulary.

They deliberately do **not** check the prose. A test that grades whether a
thread is *interesting* would be the same mistake as the one recorded in
``harness/VERDICT.md``.

Stdlib + pytest only: this must pass in a checkout with none of the numerical
dependencies installed.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

THREADS = Path(__file__).resolve().parents[1] / "THREADS.md"

REQUIRED_FIELDS = ("Noticed", "Matters", "From", "Resume", "Status")
STATUSES = ("parked", "pulling", "dead")

HEADING = re.compile(r"^### (T-\d{3})\s+(.+)$", re.M)


def _blocks() -> list[tuple[str, str, str]]:
    """(id, name, body) for each thread block, body running to the next heading."""
    text = THREADS.read_text(encoding="utf-8")
    matches = list(HEADING.finditer(text))
    out = []
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        out.append((m.group(1), m.group(2).strip(), text[m.end():end]))
    return out


def test_the_ledger_exists_and_holds_threads() -> None:
    assert THREADS.is_file(), "THREADS.md is the whole mechanism; it must exist"
    assert _blocks(), "an empty ledger means nobody is recording; seed it with a real thread"


def test_ids_are_unique() -> None:
    ids = [tid for tid, _, _ in _blocks()]
    duplicated = {i for i in ids if ids.count(i) > 1}
    assert not duplicated, f"thread ids must never be reused: {sorted(duplicated)}"


def test_ids_are_monotonic() -> None:
    """Ids only ever go up, so a reader can tell recency from the number."""
    numbers = [int(tid.split("-")[1]) for tid, _, _ in _blocks()]
    assert numbers == sorted(numbers), f"ids must ascend in file order: {numbers}"


@pytest.mark.parametrize("field", REQUIRED_FIELDS)
def test_every_thread_carries_every_field(field: str) -> None:
    """A thread missing 'Resume' cannot be resumed, which is the whole point."""
    for tid, name, body in _blocks():
        assert f"**{field}**" in body, f"{tid} ({name}) is missing **{field}**"


def test_every_status_is_from_the_closed_vocabulary() -> None:
    for tid, name, body in _blocks():
        line = next(ln for ln in body.splitlines() if ln.startswith("**Status**"))
        said = line.split("**Status**", 1)[1].strip()
        assert any(said.startswith(s) for s in STATUSES), (
            f"{tid} ({name}) status must begin with one of {STATUSES}, got {said!r}"
        )


def test_the_documented_format_matches_what_the_tests_enforce() -> None:
    """The template at the top of the file is the contract; keep them in step."""
    text = THREADS.read_text(encoding="utf-8")
    header = text.split("---", 1)[0]
    for field in REQUIRED_FIELDS:
        assert f"**{field}**" in header, f"the template must document **{field}**"
    for status in STATUSES:
        assert status in header, f"the template must document the {status!r} status"
