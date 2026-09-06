"""``python -m harness.new_department <name>``, scaffold a department honestly.

Generates three files, a department module, its test file, and its door,
every one of which **fails loudly until real content replaces the
placeholders**. That is the point of the scaffold: the sham battery this
repository once caught (commit ``431cc74``) was placeholders written to the
checks' shapes, so a scaffold that generated runnable placeholder
instruments would be a sham-battery generator. This one generates questions
with ``raise`` statements under them.

The generated module cannot register: ``NotImplementedError`` at import
until every instrument answers its question. The generated door has the
sections a reader needs and refuses to pretend they are written. Listing
the new department in ``KNOWN_DEPARTMENTS`` before the work is done makes
the conformance suite fail, which is the correct order of events.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[1]

_MODULE_TEMPLATE = '''"""Department: {name}, one line on the subject, or delete this file.

Before writing any instrument, answer these in prose here, because every
battery this scaffold has ever prevented started by skipping one of them:

* What exactly is the claim, in one sentence a rival could falsify?
* What would kill it? If nothing in the tree can, this is a probe, not a
  department, see hunts/README.md, and stop here.
* What is a credible rival: shares the structure, lacks the property,
  *by construction*, the way finitefield's counterfeits satisfy a² > 4p?
* What substantive input does a decoy remove, and what does it preserve?
* What is the null world, and is it a value or a distribution? (If a
  distribution: run_null_band, and surrogates that vary per call.)
* What relevant defect can be planted, at more than one magnitude?
* How do you know the detector can see it, and stay quiet when nothing
  is planted? Where does its power measurably stop?
* What is known-good, what is known-bad, and do both re-derive?
* Who authored the battery content, and had they seen the results?
* What is the scope of a PASS, and what does it deliberately not say?
"""

from __future__ import annotations

from harness.protocol import (
    Battery,
    Department,
    NamedDetector,
    ReferenceClaim,
    register_department,
)
from harness.provenance import Provenance

DEPARTMENT_NAME = "{name}"

raise NotImplementedError(
    "the {name} department is a scaffold: every instrument below is a "
    "question, not an implementation, see the module docstring"
)

# --- subjects: the genuine article, and rivals that lack the property -----
# TARGET = ...   # payload() must expose behavior, never a label a claim
#                # could read instead of measuring (the 431cc74 lesson)
# RIVALS = (...,)  # each shares the claimed structure and lacks the
#                  # property BY CONSTRUCTION, a rival that might have the
#                  # property refutes nothing (see stateval's false start)

# --- decoys / surrogates / lesions ----------------------------------------
# DECOYS = (...,)      # substitute(probe) must change the substance;
#                      # declare a `probe` of the shape you consume
# SURROGATES = (...,)  # if your null is a distribution, sample() must vary
#                      # per call (seeded state), for run_null_band
# LESIONS = (...,)     # magnitudes measured or derived, never asserted;
#                      # more than one scale, and say where detection stops

# --- detectors: what your silence is staked on ----------------------------
# DETECTORS = (
#     NamedDetector(name=..., fires=..., probe=<clean payload>,
#                   note="where its power measurably stops"),
# )

# --- calibration: one claim killed, one passing, both re-derived ----------
# REFERENCE_CLAIMS = (
#     ReferenceClaim(name=..., claim=..., distinguishes=False,
#                    note="true of the target AND every rival"),
#     ReferenceClaim(name=..., claim=..., distinguishes=True,
#                    note="the property the rivals lack"),
# )

# BATTERY = Battery(name=DEPARTMENT_NAME, target=TARGET, rivals=RIVALS,
#                   decoys=DECOYS, surrogates=SURROGATES, lesions=LESIONS)

# DEPARTMENT = Department(
#     name=DEPARTMENT_NAME,
#     summary=...,
#     battery=BATTERY,
#     door="docs/doors/{name}.md",
#     reference_claims=REFERENCE_CLAIMS,
#     detectors=DETECTORS,
#     scope="exactly what a pass licenses, and what it does not",
#     provenance=Provenance(
#         authored_by=...,
#         independent_of_subject_author=...,   # declare, or leave None
#         results_visible_when_authored=...,
#         frozen_before_execution=...,
#     ),
# )
#
# register_department(DEPARTMENT, replace=True)
'''

_TEST_TEMPLATE = '''"""Department ({name}), audits beyond structural conformance.

The conformance suite runs automatically once the department is listed in
KNOWN_DEPARTMENTS. What belongs HERE is the anatomy the generic audit
cannot know: pinned measured numbers, each detector's measured floor, and
any preserved false start.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


@pytest.mark.skip(reason="scaffold: write the department first, then pin its anatomy")
def test_pin_the_measured_anatomy() -> None:
    """Replace with: reference-claim re-derivations with pinned numbers,
    detector floors (what magnitude each goes blind at), null-band
    measurements, and the department's own audit grade."""
    raise NotImplementedError
'''

_DOOR_TEMPLATE = '''# Department: {name}, NOT YET ADMITTED

> This door is a scaffold. A department whose door pretends to be written
> is lying to the one reader who needed it. Fill every section or delete
> the directory.

**Subject.** (what is under referee, in two sentences)

**Why this department exists.** (what assumption in the shared architecture
does it stress that existing departments do not? If the answer is nothing,
question the admission, departments are not added for breadth.)

**The battery.** (the four roles as a table: rivals, decoys, surrogates,
lesions, and for each, why it is not a placeholder)

**Detectors.** (what the silence is staked on, and where power measurably
stops)

**First command:** (one line a newcomer can run)

**Honest scope.** (what a pass licenses; what it deliberately does not;
which of the audit's declared blind spots bite hardest here)
'''


def _valid_name(name: str) -> bool:
    return bool(re.fullmatch(r"[a-z][a-z0-9_]{1,30}", name))


def scaffold(name: str, *, root: Path = _REPO_ROOT) -> list[Path]:
    """Write the three files; refuse to overwrite anything that exists."""
    if not _valid_name(name):
        raise SystemExit(f"department name {name!r} must match [a-z][a-z0-9_]+")
    targets = {
        root / "harness" / "departments" / f"{name}_department.py": _MODULE_TEMPLATE,
        root / "tests" / f"test_harness_{name}_department.py": _TEST_TEMPLATE,
        root / "docs" / "doors" / f"{name}.md": _DOOR_TEMPLATE,
    }
    existing = [path for path in targets if path.exists()]
    if existing:
        raise SystemExit(
            "refusing to overwrite: " + ", ".join(str(p.relative_to(root)) for p in existing)
        )
    written = []
    for path, template in targets.items():
        path.write_text(template.format(name=name), encoding="utf-8")
        written.append(path)
    return written


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("name", help="department name, [a-z][a-z0-9_]+")
    args = parser.parse_args(argv)
    written = scaffold(args.name)
    for path in written:
        print(f"wrote {path.relative_to(_REPO_ROOT)}")
    print(
        "\nnext:\n"
        "  1. answer the questions in the module docstring, in prose, first\n"
        "  2. build the instruments; the module raises until you remove the scaffold guard\n"
        "  3. pin the measured anatomy in the test file\n"
        "  4. write the door honestly\n"
        f"  5. list {args.name!r} in harness/departments/__init__.py: LAST;\n"
        "     that line is what turns the conformance audit on"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
