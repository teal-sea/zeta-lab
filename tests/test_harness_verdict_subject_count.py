"""One number, stated in six places, that had already drifted from its evidence.

`harness/VERDICT.md` and five pages that quote it said the gate was "four
preregistered experiments, three subjects, 74 agent runs". The gate ran on two.
v1, v2 and v3 all name `harness/departments/croniter_fixtures/frozen_croniter.py`
as the subject, and only v4 moves to the compiler package; v3 says so in as many
words, that `frozen_croniter` "cannot host this comparison" and a fourth attempt
needs a different domain. The third subject people were counting is the
mathematics venue in `VERDICT.md` §7, which that same file introduces as a
**fifth**, in-flight experiment. It is not one of the four, and adding it to the
four while leaving the count of experiments at four counts one experiment twice.

This is the same shape as the reading-of-record defect and as coordinator defect
#23: a figure quoted from a summary sentence instead of re-derived from the
record underneath it. So the record is the source here too, and the count is
derived rather than restated.

**The derivation.** Each gate's own frozen Python artifacts say what that
experiment was built against, which is stronger evidence than the prose above
them: `gate/build_claims.py` and `gate2/build_claims.py` import
`frozen_croniter`, `gate3/mutants.py` reads it by path, and `gate4/score.py`
imports `compiler.semantics`. The number of subjects is the number of distinct
answers, and it is two. Each protocol document is then required to mention the
subject its own artifacts used, so prose and evidence cannot describe different
experiments.

The safe failure mode is mandatory, in the style of `proven_sign` returning 0 for
"not decided". Every step that could guess instead raises: a gate whose artifacts
match no subject fingerprint, or more than one, fails rather than picking; a
missing protocol or evidence directory fails; and a quoting page that states no
subject count at all fails rather than passing vacuously, because a sentence
reworded around the number would otherwise silently retire this guard.

Scope, stated so nobody reads more into a green run than it earns: this checks
that six files agree with the gate evidence about how many subjects the four
experiments used. It says nothing about the verdict, about the other figures in
those sentences, or about whether the harness deserved its demotion. Stdlib and
pytest only, so it runs in the cheap tier.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
EVIDENCE = REPO / "harness" / "gate-evidence"

#: Each gate protocol document, paired with the evidence directory it froze.
PROTOCOLS = {
    "HARNESS-GATE-2026-08-13.md": "gate",
    "HARNESS-GATE-V2-2026-08-13.md": "gate2",
    "HARNESS-GATE-V3-2026-08-13.md": "gate3",
    "HARNESS-GATE-V4-2026-08-13.md": "gate4",
}

#: How to recognise a subject, not how many there are. A gate is attributed to a
#: subject when its frozen artifacts name that subject's module.
SUBJECT_FINGERPRINTS = {
    "croniter fixtures": re.compile(r"frozen_croniter"),
    "compiler": re.compile(r"\bcompiler\b"),
}

#: Every file that quotes the gate's subject count as a current figure.
QUOTERS = (
    Path("harness") / "VERDICT.md",
    Path("harness") / "gate-evidence" / "HARNESS-GATE-V4-2026-08-13.md",
    Path("README.md"),
    Path("CLAUDE.md"),
    Path("ROADMAP.md"),
    Path("docs") / "doors" / "adopt.md",
)

_WORDS = {
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10,
}

#: Anchored on the gate claim rather than on the bare word, because these files
#: count other things in subjects too: `ROADMAP.md` has a department that "works
#: on three of four subjects" and `VERDICT.md` has "six subject packs", and
#: neither is this figure. The count must follow "experiments" inside the same
#: sentence, which is the shape every quotation of the gate result takes:
#: "four preregistered experiments, two subjects, 74 agent runs" and "four
#: experiments in two subjects". Whitespace is normalised first so the match
#: survives a reflow.
_CLAIM = re.compile(
    r"\bexperiments\b[^.]{0,20}?\b(" + "|".join(_WORDS) + r"|\d+) subjects\b",
    re.I,
)


def _stated_counts(text: str) -> list[int]:
    """Every subject count the text states as part of the gate claim."""
    flat = " ".join(text.split())
    return [
        _WORDS.get(m.group(1).lower()) or int(m.group(1))
        for m in _CLAIM.finditer(flat)
    ]


def _subject_of(gate_dir: str) -> str:
    """The one subject the gate's frozen artifacts were built against.

    Zero matches means a subject this test does not know how to recognise, and
    more than one means the artifacts name two. Neither is a number, so both
    raise instead of contributing a guess to the count.
    """
    root = EVIDENCE / gate_dir
    assert root.is_dir(), f"{gate_dir}/ is missing from {EVIDENCE}"

    sources = sorted(root.rglob("*.py"))
    assert sources, f"{gate_dir}/ froze no Python artifact to derive a subject from"

    blob = "\n".join(p.read_text(errors="ignore") for p in sources)
    hits = sorted(n for n, pat in SUBJECT_FINGERPRINTS.items() if pat.search(blob))
    assert len(hits) == 1, (
        f"{gate_dir}/ names {len(hits)} known subjects ({hits}) across "
        f"{len(sources)} frozen artifacts, so its subject cannot be determined. "
        f"If a gate ran against a new subject, add its fingerprint here rather "
        f"than letting the count guess."
    )
    return hits[0]


def _subject_count() -> int:
    """How many distinct subjects the four gate experiments used."""
    subjects = {}
    for protocol, gate_dir in PROTOCOLS.items():
        path = EVIDENCE / protocol
        assert path.is_file(), f"gate protocol {protocol} is missing"
        subject = _subject_of(gate_dir)
        assert SUBJECT_FINGERPRINTS[subject].search(path.read_text(errors="ignore")), (
            f"{protocol} never mentions {subject}, the subject its own frozen "
            f"artifacts in {gate_dir}/ were built against. The prose and the "
            f"evidence are describing different experiments."
        )
        subjects[protocol] = subject
    return len(set(subjects.values()))


def test_the_gate_evidence_names_a_determinable_number_of_subjects() -> None:
    count = _subject_count()
    assert 1 <= count <= len(PROTOCOLS), (
        f"derived {count} subjects from {len(PROTOCOLS)} experiments, which is "
        f"not a possible answer"
    )


@pytest.mark.parametrize("protocol", sorted(PROTOCOLS), ids=lambda s: s)
def test_each_gate_ran_against_exactly_one_identifiable_subject(protocol: str) -> None:
    assert _subject_of(PROTOCOLS[protocol]) in SUBJECT_FINGERPRINTS


@pytest.mark.parametrize("rel", QUOTERS, ids=lambda p: p.as_posix())
def test_every_page_states_the_derived_subject_count(rel: Path) -> None:
    """A page may not quote a subject count the gate evidence does not support."""
    count = _subject_count()
    text = (REPO / rel).read_text(errors="ignore")

    stated = _stated_counts(text)
    assert stated, (
        f"{rel.as_posix()} states no subject count at all. It quoted one when "
        f"this guard was written, so either the figure was reworded away and "
        f"this file should leave QUOTERS, or the sentence lost its number."
    )
    wrong = [n for n in stated if n != count]
    assert not wrong, (
        f"{rel.as_posix()} says {wrong} subjects; the gate evidence derives "
        f"{count}. v1, v2 and v3 all ran on frozen_croniter and only v4 moved "
        f"to the compiler package. The mathematics venue in VERDICT.md is a "
        f"fifth experiment, not a third subject of these four."
    )
