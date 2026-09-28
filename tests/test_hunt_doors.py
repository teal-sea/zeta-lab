"""The door analysis, enforced.

``CLAUDE.md`` section "Door analysis: what every ceiling hunt owes" was added on
2026-08-24, after the field walked through doors this lab had derived and left
shut.  It requires a hunt that measures a ceiling to end its ``RESULTS.md`` with
a section named "The doors" carrying three things: the active constraints at the
optimum, the frozen-constant inventory, and the information class of each door.

**Nothing checked it.**  ``tests/test_doors.py`` is a different rule with the
same word in it: that file is about ``docs/doors/``, the entry-point guides for
readers.  The hunt rule had no test at all, so on 2026-09-10 a measurement found
that three of the fifteen doors sections in the tree were already missing parts
the rule requires, and one of those was seventy-five words long.  A rule with no
check does not decay loudly; it decays quietly and then gets cited as if it had
been enforced all along.

What this file enforces, and what it deliberately does not:

* **Shape, on every doors section that exists.**  If a hunt wrote one, it carries
  all three parts and is long enough to have said something.  This is the half
  that can be checked mechanically for every hunt in the tree, and it stops the
  rule rotting backwards.
* **Not coverage.**  The rule says *every ceiling hunt*, and nothing in a hunt's
  files declares mechanically whether it measured a ceiling.  ``HUNTSPEC.md`` has
  a ``frontier`` field but no ``ceiling`` field, so a test that tried to guess
  from prose would go red for reasons that have nothing to do with doors, which
  is worse than no test.  Sixty of the seventy-five hunts with a ``RESULTS.md``
  have no doors section, and this file does not claim to know how many of those
  owe one.  Closing that half means adding a declaration to the hunt contract,
  which is a change to ``hunts/HUNTSPEC.md`` and is the operator's to make.
"""

from __future__ import annotations

import os
import re

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HUNTS = os.path.join(REPO_ROOT, "hunts")

HEADING = re.compile(r"^#+[ \t]*the doors\b", re.IGNORECASE | re.MULTILINE)

# The three parts the rule names, and the token that shows one was attempted.
REQUIRED = {
    "active constraints at the optimum": "constraint",
    "the frozen-constant inventory": "frozen",
    "the information class of each door": "information class",
}

# A section shorter than this cannot carry three ranked inventories. The shortest
# section that passes on 2026-09-10 is 300 words; the one that fails is 75.
MIN_WORDS = 150

# Measured 2026-09-10: doors sections already in the tree that do not meet the
# rule they were written under. These are real defects, not exemptions. Each
# names what is missing so whoever did that hunt can finish it, and the test
# below fails if this list GROWS, and fails again if an entry here starts
# passing and is not deleted. It is a debt that can only shrink.
KNOWN_INCOMPLETE = {
    "r_0dfb8d": "75 words, and no information class",
    "r_4166b0": "no frozen-constant inventory, no information class",
    "support_eccd5f5e": "no active constraints, no frozen-constant inventory",
}


def _doors_section(results_md: str) -> str | None:
    m = HEADING.search(results_md)
    return results_md[m.start():] if m else None


def _hunts_with_doors() -> list[tuple[str, str]]:
    out = []
    for name in sorted(os.listdir(HUNTS)):
        path = os.path.join(HUNTS, name, "RESULTS.md")
        if not os.path.isfile(path):
            continue
        with open(path, encoding="utf-8") as fh:
            sec = _doors_section(fh.read())
        if sec is not None:
            out.append((name, sec))
    return out


def _faults(section: str) -> list[str]:
    faults = []
    if len(section.split()) < MIN_WORDS:
        faults.append(f"{len(section.split())} words, under the {MIN_WORDS} a three-part section needs")
    low = section.lower()
    for part, token in REQUIRED.items():
        if token not in low:
            faults.append(f"no {part}")
    return faults


def test_the_tree_still_has_doors_sections_to_check():
    """A rename or a moved directory must not turn this file into a no-op."""
    found = _hunts_with_doors()
    assert len(found) >= 15, f"only {len(found)} doors sections found; did hunts/ move?"


@pytest.mark.parametrize("name", sorted(n for n, _ in _hunts_with_doors()))
def test_a_doors_section_carries_all_three_parts(name):
    section = dict(_hunts_with_doors())[name]
    faults = _faults(section)
    if name in KNOWN_INCOMPLETE:
        assert faults, (
            f"hunts/{name} is listed in KNOWN_INCOMPLETE as {KNOWN_INCOMPLETE[name]!r} "
            "but its doors section now passes. Delete the entry: the debt list only shrinks."
        )
        pytest.xfail(f"known incomplete since 2026-09-10: {KNOWN_INCOMPLETE[name]}")
    assert not faults, (
        f"hunts/{name}/RESULTS.md has a doors section that does not meet the rule in CLAUDE.md: "
        + "; ".join(faults)
        + ". The three parts are the active constraints at the optimum, the frozen-constant "
        "inventory, and the information class of each door."
    )


def test_the_incomplete_list_names_only_hunts_that_exist():
    """A debt list that outlives its hunts stops being a debt and becomes decoration."""
    have = {n for n, _ in _hunts_with_doors()}
    stale = sorted(set(KNOWN_INCOMPLETE) - have)
    assert not stale, f"KNOWN_INCOMPLETE names hunts with no doors section any more: {stale}"
