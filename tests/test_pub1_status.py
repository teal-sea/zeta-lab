"""One status, stated in two places, that must not drift apart.

`lean/ZetaLean/Pub1/OBLIGATIONS.md` records whether the Pub 1 strong closure
still carries analytic obligations. `docs/27` §2 quotes that status in the
kernel-checked table, which is the page a reader consults to learn what grade
each piece of the transplant holds.

On 2026-08-17 they disagreed. The obligations had closed over 2026-08-14/16 —
`strongClosureData_final` holds with no analytic or membership hypothesis, so
`pub1_strong_closure` assumes only `IsProfile w` and `pub1_strong_closure_exists`
assumes nothing at all — and `OBLIGATIONS.md` said `status: CLOSED`, while the
`docs/27` row still said **Conditional** and named four hypotheses that no
longer existed.

Nothing had gone wrong with the mathematics, and this instance pointed the
harmless way: the stale row *under*claimed. That is exactly why it is worth a
guard. The same drift pointing the other direction — a row saying
*unconditional* after an obligation reopened — is a false claim about what a
proof assumes, which is the one kind of error this tree treats as critical.
A guard that only fires in the expensive direction would have to know which
direction it was in; this one just requires the two files to agree.

The safe failure mode is mandatory, in the style of `proven_sign` returning 0
for "not decided": a status string the guard does not recognise fails loudly
rather than being mapped to whichever grade seems likelier.

Scope, stated so nobody reads more into a green run than it earns: this checks
that two files agree about one word. It says nothing about whether the closure
is correct, whether the Lean proof is sound, or whether the axioms are clean —
`#print axioms` and the kernel say that, not this. Stdlib and pytest only, so
it runs in the cheap tier.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
OBLIGATIONS = REPO / "lean" / "ZetaLean" / "Pub1" / "OBLIGATIONS.md"
DOC27 = REPO / "docs" / "27-state-of-the-transplant.md"

#: The statuses this guard knows how to read, mapped to the grade token
#: `docs/27` must use. Anything else is an error, not a default.
#:
#: The token is matched **bolded**, not as a bare word, and that detail is
#: load-bearing twice over. First, `Conditional` is a substring of
#: `Unconditional`, so a naive containment test reports a correct row as
#: carrying both grades — the guard's own first draft did exactly that.
#: Second, the row's prose legitimately mentions the grade it used to carry;
#: only the bolded token is the row's *claim*, so only it is checked.
_KNOWN_STATUSES = {
    "CLOSED": "Unconditional",
    "OPEN": "Conditional",
}

#: Any bolded grade token in the row, however it is spelled.
_GRADE_TOKEN = re.compile(r"\*\*(Un)?[Cc]onditional\*\*")

_STATUS_LINE = re.compile(
    r"^#\s*Pub 1 strong closure\s*—\s*status:\s*(?P<status>[A-Z]+)\s*$"
)

#: The `docs/27` table row that quotes the status.
_ROW = re.compile(r"^\|\s*3\s*\|\s*The Pub 1 source-admissible strong closure")


def _declared_status() -> str:
    """The status `OBLIGATIONS.md` declares in its own heading."""
    assert OBLIGATIONS.is_file(), f"{OBLIGATIONS} is missing"
    for line in OBLIGATIONS.read_text(errors="ignore").splitlines():
        match = _STATUS_LINE.match(line.strip())
        if match:
            return match.group("status")
    raise AssertionError(
        f"{OBLIGATIONS.name} declares no status heading. The guard reads the "
        "line '# Pub 1 strong closure — status: <STATUS>'; if that heading was "
        "reworded, reword this guard with it rather than deleting it."
    )


def _doc27_row() -> str:
    """The `docs/27` §2 table row for item 3."""
    for line in DOC27.read_text(errors="ignore").splitlines():
        if _ROW.match(line.strip()):
            return line
    raise AssertionError(
        f"{DOC27.name} has no item-3 row for the Pub 1 strong closure. It is "
        "the row this guard exists to keep honest; if item 3 was renumbered, "
        "update the pattern here."
    )


def test_the_declared_status_is_one_this_guard_understands() -> None:
    """An unrecognised status is undecided, and undecided fails loudly."""
    status = _declared_status()
    assert status in _KNOWN_STATUSES, (
        f"{OBLIGATIONS.name} declares status {status!r}, which this guard does "
        f"not know how to check against docs/27. Known: "
        f"{sorted(_KNOWN_STATUSES)}. Add it here deliberately — do not let an "
        "unknown status pass as though it had been verified."
    )


def test_docs_27_states_the_grade_the_obligations_file_declares() -> None:
    """The two files must agree about whether the closure is conditional."""
    status = _declared_status()
    if status not in _KNOWN_STATUSES:
        pytest.skip("unrecognised status; the check above owns that failure")

    expected = _KNOWN_STATUSES[status]
    row = _doc27_row()
    claimed = [m.group(0) for m in _GRADE_TOKEN.finditer(row)]

    assert claimed, (
        f"The docs/27 item-3 row states no bolded grade at all, so it makes no "
        f"claim this guard can check against {OBLIGATIONS.name}'s "
        f"{status!r}. State the grade as **{expected}**.\n\nRow:\n{row}"
    )
    assert len(set(claimed)) == 1, (
        f"The docs/27 item-3 row bolds more than one grade ({sorted(set(claimed))}), "
        "leaving a reader to guess which is current. That ambiguity is the "
        f"defect this guard exists to prevent.\n\nRow:\n{row}"
    )
    assert claimed[0] == f"**{expected}**", (
        f"{OBLIGATIONS.name} declares status {status!r}, so the docs/27 item-3 "
        f"row must claim **{expected}**; it claims {claimed[0]}. The row is "
        "what a reader consults for this piece's grade, and it currently "
        f"disagrees with the file that owns the answer.\n\nRow:\n{row}"
    )


def test_the_unconditional_theorems_still_carry_the_names_the_doc_cites() -> None:
    """`docs/27` names Lean theorems; a rename must not leave the doc pointing at nothing.

    This is deliberately a *name* check and not a proof check. It cannot tell
    whether `pub1_strong_closure` proves what the row says it proves — only
    the kernel does that. It catches the cheaper and commoner failure: the doc
    citing an identifier that no longer exists.
    """
    source = REPO / "lean" / "ZetaLean" / "Pub1" / "Unconditional.lean"
    assert source.is_file(), f"{source} is missing"
    text = source.read_text(errors="ignore")
    for name in ("pub1_strong_closure", "pub1_strong_closure_exists",
                 "strongClosureData_final"):
        assert re.search(rf"^theorem {re.escape(name)}\b", text, re.M), (
            f"{source.name} declares no theorem {name!r}, but docs/27 cites it "
            "by name. Either the theorem was renamed and the doc was not, or "
            "the doc names something that never existed."
        )
