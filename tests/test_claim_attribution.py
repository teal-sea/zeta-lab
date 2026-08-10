"""A superseded bound may not be stated as the current record.

Written because of a defect the suite missed, and then narrowed twice because the
first two attempts were hollow. Both the defect and the two failed attempts are
recorded, because the failures are the more useful half.

## The defect

On 2026-08-10 an outside reader found two problems with how this tree's prose
restates the de Bruijn–Newman bounds, both contradicting
`zeta.heatflow.lambda_facts()`, which held the right answer all along:

1. `docs/08` §6 — the "what is tractable" summary a newcomer starts from — stated
   `Lambda <= 0.22` as the upper bound, with no mention anywhere nearby of the
   `0.2` that superseded it.
2. `docs/12` credited `Λ ≤ 0.2` to "the Polymath15 machinery". It is Platt and
   Trudgian's own published result.

2135 tests walked past both. The general class is worth closing: **prose here
restates facts a module already holds in structured form, and nothing checks the
restatement.**

## What this file enforces, and why it is only half

> If a document states a Λ upper bound that `lambda_facts()` records as superseded,
> the bound that superseded it must appear nearby.

Derived from the module, not duplicated here: "superseded" means a decimal upper
bound strictly larger than `lambda_facts()['upper_bound']`. It catches defect 1
verbatim, and it does not fire on the many correct bare statements of the current
interval (`Λ ∈ [0, 0.2]`) that appear in indexes and summaries.

## Two failed attempts, recorded rather than deleted

**Attempt 1 — "a stated bound must name its author."** Rejected: it fires on
`docs/00`, `docs/05` and `README.md`, all of which correctly state `Λ ∈ [0, 0.2]`
in a table-of-contents row or a summary sentence. Demanding a citation in an index
row is not a defect check, it is noise. A checker that rejects correct prose fails
this repository's own admission rule.

**Attempt 2 — the same rule, "proved" by a planted fault.** Worse, and the reason
this docstring is long. The historical `docs/12` sentence was:

> Feeding Platt–Trudgian's `3·10^12` into the Polymath15 machinery is what gives
> `Λ ≤ 0.2` (`docs/05` §3)

It **names the correct authors** and it **cites the authoritative section**. Every
lexical rule that would flag it also flags the corrected wording, which names
Polymath15 nearer to `0.2` than Platt–Trudgian for a legitimate reason. The
misattribution lives in the sentence's assignment of credit, not in its tokens.

The fault originally planted in this file to demonstrate detection had
`Platt–Trudgian's` silently removed — a fault shaped to fit the detector rather
than the fault that occurred. That is the hollow-battery failure mode this
repository measures in its own audit (`docs/23`: six of six blind-authored
batteries measured nothing), reproduced here at n=1 by the agent writing the
detector. It was caught only by diffing the planted text against `git show`.

**Recorded conclusion: defect 2 is not reachable by a lexical check.** Its real
remedy is the editorial one already applied — cite `docs/05` §3 rather than
paraphrase it — and that is a convention, not a test. Claiming otherwise would be
the overclaim this file exists to prevent.
"""

from __future__ import annotations

import pathlib
import re
import sys

import pytest

_REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

#: Characters either side of a bound statement in which the successor must sit.
WINDOW = 500


def _prose_files() -> list[pathlib.Path]:
    """This repository's own claims. ``docs/reviews/`` is external material."""
    files = sorted((_REPO_ROOT / "docs").glob("*.md"))
    files += [_REPO_ROOT / "ROADMAP.md", _REPO_ROOT / "README.md"]
    return [f for f in files if f.exists()]


def _current_and_superseded() -> tuple[str, list[str]]:
    """``('0.2', ['0.22'])`` — read off ``lambda_facts()``, not written here."""
    from zeta.heatflow import lambda_facts

    facts = lambda_facts()
    current = facts["upper_bound"]
    superseded = []
    for entry in facts["history"]:
        m = re.search(r"<=\s*(\d+\.\d+)", entry["bound"])
        if m and float(m.group(1)) > float(current):
            superseded.append(m.group(1))
    return f"{current}", sorted(set(superseded))


def _bound_positions(text: str, value: str) -> list[int]:
    """Offsets where ``value`` is stated as a Λ bound rather than mentioned."""
    hits = []
    for m in re.finditer(rf"{re.escape(value)}(?!\d)", text):
        before = text[max(0, m.start() - 120) : m.start()]
        if re.search(r"Λ|Lambda", before):
            hits.append(m.start())
    return hits


def _violations(text: str) -> list[str]:
    """Superseded bounds stated with no sight of the bound that replaced them.

    The Λ-proximity test identifies that a *superseded* value is being stated as a
    bound rather than merely appearing. The **successor** needs no such test:
    plain presence of its numeral in the window is enough, and requiring
    Λ-proximity for it produced a false positive on `docs/07`, whose correct
    sentence names the successor 60 characters later but puts `Lambda_dBN` a line
    and a half before it.
    """
    current, superseded = _current_and_superseded()
    successor = re.compile(rf"{re.escape(current)}(?!\d)")
    out = []
    for old in superseded:
        for at in _bound_positions(text, old):
            window = text[max(0, at - WINDOW) : at + WINDOW]
            if not successor.search(window):
                out.append(text[max(0, at - 90) : at + 40].replace("\n", " ").strip())
    return out


def test_the_ground_truth_is_machine_readable() -> None:
    """The premise: this test reads the bounds, it does not restate them."""
    current, superseded = _current_and_superseded()
    assert current == "0.2", current
    assert superseded == ["0.22"], superseded


@pytest.mark.parametrize("path", _prose_files(), ids=lambda p: p.name)
def test_no_document_states_a_superseded_bound_as_the_record(path) -> None:
    bad = _violations(path.read_text(encoding="utf-8"))
    assert not bad, (
        f"{path.name} states the superseded Λ bound without the bound that "
        f"replaced it nearby: {bad}. lambda_facts() records 0.22 as superseded by "
        f"0.2 (Platt–Trudgian, 2021). This is the defect an outside reader found "
        f"in docs/08 on 2026-08-10."
    )


def test_it_catches_the_real_historical_text_verbatim() -> None:
    """Detector power against the fault that actually shipped, from ``git show``.

    Copied verbatim from ``docs/08`` at ``3810615~1``. Not paraphrased and not
    shaped to fit the detector — the earlier version of this file did exactly
    that, and the docstring above records why.
    """
    historical = (
        "3. **The de Bruijn–Newman constant.** `Lambda <= 1/2` (de Bruijn, 1950); "
        "`Lambda >= 0` is a\n"
        "   **THEOREM** (Rodgers–Tao; announced 2018, published 2020), so RH is now "
        "exactly `Lambda = 0`.\n"
        "   **Polymath15** (2018) drove the upper bound to `Lambda <= 0.22` — a "
        "real, open, collaborative\n"
        "   project in which a competent programmer could and did contribute "
        "compute and code. See\n"
        "   `docs/05-de-bruijn-newman.md` and `zeta/heatflow.py`.\n"
    )
    assert _violations(historical), (
        "the check does not fire on the text that actually shipped, so it would "
        "not have prevented the defect"
    )


def test_it_accepts_the_corrected_text_verbatim() -> None:
    """Specificity. A checker that only ever rejects distinguishes nothing."""
    corrected = (
        "   **Polymath15** (2018) drove the upper bound to `Lambda <= 0.22`, "
        "sharpened to `Lambda <= 0.2` by\n"
        "   Platt–Trudgian (2021) — see `docs/05` §3 for both, and note neither is "
        "strict.\n"
    )
    assert _violations(corrected) == []


def test_it_does_not_fire_on_bare_statements_of_the_current_interval() -> None:
    """Why attempt 1 was rejected: index rows are not defects.

    These three are real strings from `docs/00`, `docs/05` and `README.md`, all
    correct, and all rejected by the first version of this check.
    """
    for correct in (
        "Heat flow *on* `Ξ`; zero collisions; `Λ ∈ [0, 0.2]` and RH ⟺ `Λ = 0`.",
        "- **What is proved:** `0 <= Lambda <= 0.2`, and RH `<=>` `Lambda = 0`.",
        "a real   number `Lambda` known to lie in `[0, 0.2]`, pinned at one end by "
        "a theorem",
    ):
        assert _violations(correct) == [], correct


def test_the_misattribution_half_is_documented_as_out_of_reach() -> None:
    """The negative result, pinned so a later session cannot quietly claim it.

    The historical `docs/12` sentence satisfies every lexical rule available: the
    correct authors are named and the authoritative section is cited. If someone
    later believes this file covers misattribution, this test is where the belief
    should break.
    """
    historical = (
        "valuable as an *input*. Feeding Platt–Trudgian's `3·10^12` into the "
        "Polymath15 machinery is what\ngives `Λ ≤ 0.2` (`docs/05` §3), and Platt's "
        "certified L-function zeros are an ingredient in\n"
    )
    assert "Platt" in historical and "docs/05" in historical
    assert _violations(historical) == [], (
        "this file does not detect misattribution, and must not appear to: the "
        "real sentence names the right authors and cites the right section"
    )
