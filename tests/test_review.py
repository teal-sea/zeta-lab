"""The standing adversarial review: blindness structural, outcomes costed.

Pins: the blind brief cannot carry the author's reasoning (it is absent from
the materials dict, not promised absent); a withdrawal costs artifacts; an
author attacking their own claim is named as a missing line of evidence; and
the ledger's exemplar (the 0.672529 clean kill) cites artifacts that exist,
while its open case (URMS2 0.51) surfaces exactly the two missing attacks.
The September and October candidates entered on 2026-10-10 each surface both
missing attacks, state their grade in their own text, and keep the
half-plane hypothesis they are conditional on.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from harness.departments.review_ledger import CLAIMS, OUTCOMES  # noqa: E402
from harness.review import (  # noqa: E402
    AttackOutcome,
    ClaimUnderReview,
    ReviewError,
    generate_briefs,
    standing_reasons,
)


def _claim(**overrides) -> ClaimUnderReview:
    base = dict(
        name="c",
        claim="X holds",
        author="author-1",
        assumptions=("a1",),
        code_paths=("path.py",),
        controls_run=("control-1",),
        author_reasoning="because of a hunch about symmetry",
    )
    base.update(overrides)
    return ClaimUnderReview(**base)


# ---------------------------------------------------------------------------
# 1. briefs: blindness is structural
# ---------------------------------------------------------------------------


def test_the_blind_brief_physically_lacks_the_reasoning() -> None:
    blind, whitebox = generate_briefs(_claim())
    assert "author_reasoning" not in blind.materials
    assert "hunch" not in repr(blind.materials)
    assert whitebox.materials["author_reasoning"] == "because of a hunch about symmetry"


def test_both_briefs_share_the_attack_surface_and_the_question() -> None:
    blind, whitebox = generate_briefs(_claim())
    for brief in (blind, whitebox):
        assert brief.materials["claim"] == "X holds"
        assert brief.materials["controls_run"] == ("control-1",)
        assert "appearance of this result" in brief.question
    assert blind.checklist == ()
    assert any("shared preprocessing" in item for item in whitebox.checklist)


# ---------------------------------------------------------------------------
# 2. outcomes: kills cost artifacts, recording is not resolving
# ---------------------------------------------------------------------------


def test_a_withdrawal_without_artifacts_is_refused() -> None:
    with pytest.raises(ReviewError, match="rumor"):
        AttackOutcome(
            claim_name="c", role="blind", attacker="a", claim_withdrawn=True
        )


def test_an_attack_that_found_nothing_is_still_an_outcome() -> None:
    outcome = AttackOutcome(claim_name="c", role="blind", attacker="a")
    assert outcome.findings == ()
    assert outcome.claim_withdrawn is False


def test_an_unnamed_attacker_is_refused() -> None:
    with pytest.raises(ReviewError, match="named attacker"):
        AttackOutcome(claim_name="c", role="blind", attacker="  ")


# ---------------------------------------------------------------------------
# 3. standing: both roles, neither by the author
# ---------------------------------------------------------------------------


def test_no_outcomes_means_two_missing_attacks() -> None:
    reasons = standing_reasons(_claim(), ())
    assert len(reasons) == 2
    assert any("blind" in r for r in reasons)
    assert any("white-box" in r for r in reasons)


def test_an_author_run_attack_is_named_as_missing_evidence() -> None:
    claim = _claim()
    outcomes = (
        AttackOutcome(claim_name="c", role="blind", attacker="author-1"),
        AttackOutcome(claim_name="c", role="white-box", attacker="someone-else"),
    )
    reasons = standing_reasons(claim, outcomes)
    assert len(reasons) == 1
    assert "run by its author" in reasons[0]


def test_a_complete_review_has_no_missing_reasons() -> None:
    claim = _claim()
    outcomes = (
        AttackOutcome(claim_name="c", role="blind", attacker="attacker-a"),
        AttackOutcome(claim_name="c", role="white-box", attacker="attacker-b"),
    )
    assert standing_reasons(claim, outcomes) == ()


# ---------------------------------------------------------------------------
# 4. the ledger: the exemplar is checkable, the open case is visible
# ---------------------------------------------------------------------------


def test_the_exemplars_artifacts_exist() -> None:
    exemplar = next(o for o in OUTCOMES if o.claim_name == "blockpos-0.672529")
    assert exemplar.claim_withdrawn is True
    for artifact in exemplar.artifacts:
        assert (_REPO_ROOT / artifact).exists(), (
            f"the review ledger cites {artifact}, which does not exist: a "
            "kill nobody can rerun is a rumor"
        )


def test_the_open_case_is_now_standing() -> None:
    """Both attacks on urms2-0.51 have now run, from attackers who are not the author.

    The history of this test is the ledger working. It first asserted both
    attacks were missing, true until 2026-08-15; then that the blind attack
    had run and the white-box one had not, true until 2026-08-16, when
    Fulcrum R-065F29 recorded the white-box outcome. Standing does not mean
    the claim is true: it means both required attacks have recorded outcomes
    and the record says what each found. R-065F29 did not withdraw the claim,
    and its findings are in the ledger for the operator to resolve.
    """
    urms2 = next(c for c in CLAIMS if c.name == "urms2-0.51")
    assert standing_reasons(urms2, OUTCOMES) == ()

    roles = {o.role for o in OUTCOMES if o.claim_name == "urms2-0.51"}
    assert roles == {"blind", "white-box"}


def test_every_recorded_outcome_cites_artifacts_that_exist() -> None:
    """An attack nobody can rerun is a rumor, withdrawal or not."""

    for outcome in OUTCOMES:
        assert outcome.artifacts, (
            f"the {outcome.role} attack on {outcome.claim_name!r} names no "
            "artifact: nothing about it is rerunnable"
        )
        for artifact in outcome.artifacts:
            assert (_REPO_ROOT / artifact).exists(), (
                f"the review ledger cites {artifact}, which does not exist"
            )


def test_the_exemplars_review_is_now_standing() -> None:
    blockpos = next(c for c in CLAIMS if c.name == "blockpos-0.672529")
    reasons = standing_reasons(blockpos, OUTCOMES)
    # Both a blind and white-box attack have now been run. The review is standing.
    assert len(reasons) == 0


# ---------------------------------------------------------------------------
# 5. the September and October candidates: queued, unattacked, graded
# ---------------------------------------------------------------------------

#: Landed candidates entered on 2026-10-10 with no outcome, because no attack
#: had run on any of them. When one lands, its AttackOutcome goes in OUTCOMES
#: and its name leaves this set in the same commit, the way the history of
#: ``test_the_open_case_is_now_standing`` records urms2-0.51's.
UNATTACKED = frozenset(
    {
        "qrh-linnik-7/3",
        "qrh-class-number-1500",
        "qrh-nonresidue-log8",
        "qrh-ninth-powers",
        "qrh-seventh-powers",
        "oob-envelope-L1.19",
        "four-point-0.6728604",
    }
)


def test_the_unattacked_candidates_each_ask_for_both_attacks() -> None:
    names = {c.name for c in CLAIMS}
    assert UNATTACKED <= names, f"missing from the ledger: {UNATTACKED - names}"
    for claim in CLAIMS:
        if claim.name not in UNATTACKED:
            continue
        assert not [o for o in OUTCOMES if o.claim_name == claim.name], (
            f"{claim.name!r} now has a recorded attack: take it out of "
            "UNATTACKED and say what the attack found"
        )
        reasons = standing_reasons(claim, OUTCOMES)
        assert len(reasons) == 2
        assert all(claim.name in r for r in reasons)


def test_every_claim_names_paths_that_exist() -> None:
    """A brief that points an attacker at a missing file is a brief for nothing."""
    for claim in CLAIMS:
        assert claim.code_paths, f"{claim.name!r} names no code or artifact"
        for path in claim.code_paths:
            assert (_REPO_ROOT / path).exists(), (
                f"{claim.name!r} cites {path}, which does not exist"
            )


def test_the_new_entries_state_their_grade_and_keep_their_hypothesis() -> None:
    """The record has no grade field, so the grade lives in the claim's text.

    And "proved given X" keeps X: every claim built on OpenAI's half-plane
    names it in the claim and carries it as an assumption an attacker can
    target, rather than leaving it in the author's reasoning, which the blind
    attacker never sees.
    """
    for claim in CLAIMS:
        if claim.name not in UNATTACKED:
            continue
        assert "Grade:" in claim.claim, f"{claim.name!r} states no grade"
        # The reserved word belongs to zeta/rigor.py and the Lean arm.
        assert not re.search(r"\bcertif(y|ied)\b", claim.claim, re.I)
        if claim.name.startswith("qrh-"):
            assert "OpenAI's Theorem 1.1" in claim.claim
            assert "7/8" in claim.claim
            assert any("Theorem 1.1" in a for a in claim.assumptions)
            assert "no person has reviewed" in claim.claim or (
                "reviewed by no person" in claim.claim
            )
