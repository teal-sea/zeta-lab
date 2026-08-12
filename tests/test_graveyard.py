"""The graveyard: kills carry mechanisms, guards, and checkable citations."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from harness.departments.graveyard_ledger import GRAVES  # noqa: E402
from harness.graveyard import GraveyardError, KilledResult, unguarded  # noqa: E402


# ---------------------------------------------------------------------------
# 1. what a grave must carry
# ---------------------------------------------------------------------------


def test_a_kill_without_a_mechanism_is_refused() -> None:
    with pytest.raises(GraveyardError, match="gossip"):
        KilledResult(name="g", status="withdrawn", why="  ", caught_by="a control")


def test_a_grave_for_something_alive_is_refused() -> None:
    with pytest.raises(GraveyardError, match="only the dead"):
        KilledResult(name="g", status="promising", why="w", caught_by="c")


def test_an_unguarded_grave_is_storable_but_loud() -> None:
    grave = KilledResult(name="g", status="withdrawn", why="w", caught_by="c")
    assert grave.guarded is False
    reasons = unguarded((grave,))
    assert len(reasons) == 1 and "recur silently" in reasons[0]


def test_the_card_renders_the_memos_fields() -> None:
    grave = KilledResult(
        name="x-candidate",
        status="withdrawn",
        why="algebraic mismatch",
        caught_by="explicit counterexample",
        regression_test="tests/test_x.py",
        formal_obstruction="lean/X.lean",
        recurrence_guard="guard installed",
    )
    card = grave.card()
    for fragment in (
        "STATUS               WITHDRAWN",
        "WHY                  algebraic mismatch",
        "CAUGHT BY            explicit counterexample",
        "REGRESSION TEST      tests/test_x.py",
        "FORMAL OBSTRUCTION   lean/X.lean",
        "guard installed",
    ):
        assert fragment in card


# ---------------------------------------------------------------------------
# 2. the ledger: transcribed, cited, guarded
# ---------------------------------------------------------------------------


def test_the_ledger_is_non_empty_and_every_grave_is_guarded() -> None:
    assert GRAVES
    assert unguarded(GRAVES) == (), (
        "an opening grave has no guard: either add the guard or record "
        "loudly why none exists"
    )


def test_every_cited_repository_path_exists() -> None:
    for grave in GRAVES:
        for citation in (grave.regression_test, grave.formal_obstruction):
            if not citation.strip():
                continue
            assert (_REPO_ROOT / citation).exists(), (
                f"grave {grave.name!r} cites {citation}, which does not exist"
            )


def test_the_transpose_kill_is_the_exemplar_card() -> None:
    exemplar = next(g for g in GRAVES if "0.672529" in g.name)
    assert exemplar.status == "withdrawn"
    assert "u u^T" in exemplar.why
    assert exemplar.regression_test == "tests/test_frontier_math_clean_kill.py"
    assert exemplar.formal_obstruction == "lean/ZetaLean/FrontierMathObstruction.lean"
    assert exemplar.guarded
