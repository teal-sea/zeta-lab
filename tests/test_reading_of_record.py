"""One number, stated in four places, that must not drift apart.

The candidate reading of the two-thirds constant is quoted on the public front
page, in `docs/27`, and on the hunt's own start page. It is also printed as a
percentage by the site generator, which lives in another repository and carries
this same check there. On 2026-08-13 three of those said `0.6725106958` and the
fourth said `0.6725087070`, for eleven hours, in public.

Nothing had gone wrong with the mathematics. `PROOF-LEDGER.md` revised the
reading downward pending burden (a), then burden (a) landed and the reading
moved back up. A session writing `START-HERE.md` from the ledger read the
pending row instead of the settled one, and the page that exists to carry the
one number that matters carried a retracted one. That is coordinator defect
#23's exact shape, logged in the same ledger two screens further down: a
superseded figure carried past its own retraction.

So the ledger is the source and the four quotations are checked against it.
The safe failure mode is mandatory, in the style of `proven_sign` returning 0
for "not decided": when the ledger's last row does not name exactly one figure,
this test fails loudly rather than guessing which one was meant.

Scope, stated so nobody reads more into a green run than it earns: this checks
that four files agree with the ledger about one decimal string. It says nothing
about whether the reading is correct, whether the chain closes, or whether any
step of it holds. Stdlib and pytest only, so it runs in the cheap tier.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
LEDGER = REPO / "hunts" / "frontier_math" / "PROOF-LEDGER.md"

#: Every file that quotes the reading as the *current* one.
QUOTERS = (
    Path("README.md"),
    Path("docs") / "27-state-of-the-transplant.md",
    Path("hunts") / "frontier_math" / "START-HERE.md",
)

_FIGURE = re.compile(r"0\.\d{10}")
_ROW = re.compile(r"^\|\s*Reading of record\s*\|", re.I)


def _reading_of_record() -> str:
    """The figure the ledger's last `Reading of record` row names.

    Rows that name two figures are the ones that move the record: they say
    which figure replaces which. Only the newest row is consulted, and it is
    required to name exactly one, because a row naming two is a row mid-move
    and no reader should have to guess which half won.
    """
    rows = [ln for ln in LEDGER.read_text(errors="ignore").splitlines()
            if _ROW.match(ln.strip())]
    assert rows, f"{LEDGER.name} names no reading of record at all"
    figures = list(dict.fromkeys(_FIGURE.findall(rows[-1])))
    assert len(figures) == 1, (
        f"the ledger's last reading-of-record row names {len(figures)} figures "
        f"({figures}), so the current reading cannot be determined from it. "
        f"Row: {rows[-1].strip()!r}"
    )
    return figures[0]


def test_the_ledger_names_one_current_reading() -> None:
    assert _FIGURE.fullmatch(_reading_of_record())


@pytest.mark.parametrize("rel", QUOTERS, ids=lambda p: p.as_posix())
def test_every_page_quotes_the_ledger_s_current_reading(rel: Path) -> None:
    """A file may recount a retracted figure; it may not omit the live one."""
    reading = _reading_of_record()
    text = (REPO / rel).read_text(errors="ignore")
    assert reading in text, (
        f"{rel.as_posix()} does not state the current reading of record "
        f"{reading}. If the ledger moved, this file did not move with it, and "
        f"it is published."
    )
