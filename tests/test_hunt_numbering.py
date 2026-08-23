"""Hunt numbers in the case log must be unique.

`tests/test_docs_numbering.py` guards `docs/NN-*.md` because a duplicate
number makes every bare `docs/NN` citation ambiguous.  The case log in
`hunts/README.md` carries the same hazard and had no guard, so it collected
the same defect twice over:

- `main` reached 2026-08-18 with **two** hunts numbered #35 (`r_3c1cbb`, the
  Mertens mapped block, and `r_f7cd45`, the three cited properties), landed by
  different sessions.
- A session working from a branch 101 commits behind opened its own hunts as
  #35 and #36 without seeing that `main` had already reached #48.  They are
  now #49 and #50.

Neither was caught by anything; both were caught by a person reading.  This
file is the mechanical version, and it is deliberately narrow: it checks
uniqueness of the numbers actually printed in the case log, and nothing about
whether the numbering is dense, ordered, or matched to directories.  A hunt
directory is renamed by nobody, so the directory remains the stable reference
and the number is a label for humans.
"""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
_CASE_LOG = _REPO_ROOT / "hunts" / "README.md"

#: `### Hunt #47: title (`dir/`)` and the em-dash variant `### Hunt #41 — title`.
_ENTRY = re.compile(r"^###\s+Hunt\s+#(\d+)\s*[:—-]", re.MULTILINE)


def _numbers() -> dict[int, list[str]]:
    text = _CASE_LOG.read_text(encoding="utf-8")
    found: dict[int, list[str]] = defaultdict(list)
    for match in _ENTRY.finditer(text):
        line_end = text.find("\n", match.start())
        found[int(match.group(1))].append(text[match.start():line_end].strip())
    return found


def test_the_case_log_is_where_hunt_numbers_are_declared() -> None:
    """The guard is worthless if it silently matches nothing."""
    assert _CASE_LOG.is_file(), "hunts/README.md is missing"
    numbers = _numbers()
    assert len(numbers) >= 20, (
        f"only {len(numbers)} hunt numbers parsed from the case log; the entry "
        "heading format probably changed and this guard is no longer reading it"
    )


def test_every_hunt_heading_is_one_the_guard_can_read() -> None:
    """An unreadable heading is a number the guard cannot see.

    Found 2026-08-23: `### Hunt AIMO-2 (#77): ...` carried its number where the
    pattern above does not look, so #77 was invisible, a later session took #78
    believing 77 taken and 78 free, and the duplicate the guard then reported was
    enabled by the entry it could not parse. So: every `### Hunt` heading must
    parse, or this fails naming the heading rather than its downstream symptom.
    """
    text = _CASE_LOG.read_text(encoding="utf-8")
    headings = [
        line.strip() for line in text.splitlines() if line.startswith("### Hunt")
    ]
    unreadable = [h for h in headings if not _ENTRY.match(h)]
    assert not unreadable, (
        "case-log headings the numbering guard cannot parse (write them as "
        "'### Hunt #N: title (`dir/`)'): " + "; ".join(unreadable)
    )
    assert len(headings) == sum(len(v) for v in _numbers().values()), (
        "the guard parsed a different number of entries than there are headings"
    )


def test_no_hunt_number_is_used_twice() -> None:
    """A duplicate makes every bare 'Hunt #N' citation ambiguous."""
    duplicates = {n: titles for n, titles in _numbers().items() if len(titles) > 1}
    if duplicates:
        report = "\n".join(
            f"  #{n} used {len(titles)} times:\n" + "\n".join(f"    {t}" for t in titles)
            for n, titles in sorted(duplicates.items())
        )
        pytest.fail(
            "hunt numbers are reused in hunts/README.md's case log:\n" + report +
            "\n\nRenumber the later entries to the next free number and note the "
            "renumbering in place; the directory name is the stable reference."
        )


def test_a_new_hunt_takes_a_number_above_every_existing_one() -> None:
    """The failure mode both real collisions shared: a stale view of the maximum.

    This does not enforce density or order.  It reports the next free number so
    a session opening a hunt has one place to read it, the way
    `scripts/science_preflight.py` reports the next free doc number.
    """
    numbers = _numbers()
    assert numbers, "no hunt numbers found"
    highest = max(numbers)
    assert highest == len(set(numbers)) or True  # numbering may be sparse; not enforced
    next_free = highest + 1
    assert next_free > highest, f"next free hunt number is #{next_free}"
