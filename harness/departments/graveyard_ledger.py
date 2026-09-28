"""The repository's graveyard, the opening graves, entered from the records.

Machinery in :mod:`harness.graveyard`; this file names the dead. Every entry
below is transcribed from a landed record (HANDOFF's withdrawal records,
docs/24, the CLEAN-KILL report), never from memory, and the conformance test
pins that every cited repository path exists. Live threads' withdrawals
(e.g. anything from the Level 7 branch) enter when their branch lands.
"""

from __future__ import annotations

from harness.graveyard import KilledResult

GRAVES: tuple[KilledResult, ...] = (
    KilledResult(
        name="blockpos 0.672529 (and siblings 0.6725124, 0.6725318)",
        status="withdrawn",
        why=(
            "the construction used u u* where the pinned upstream zero side "
            "uses u u^T; an off-line pair is the hyperbolic block "
            "2m(xx^T - yy^T), whose interaction with the on-line part can be "
            "negative, and the proposed final additive inequality reads 9 >= 13"
        ),
        caught_by=(
            "an exact Gaussian-integer counterexample: u_x=1, u_z=i, "
            "u_conj(z)=-i gives tr(P1 Q') = -2"
        ),
        regression_test="tests/test_frontier_math_clean_kill.py",
        formal_obstruction="lean/ZetaLean/FrontierMathObstruction.lean",
        recurrence_guard=(
            "the squared-modulus block scan that had zero power against this "
            "bug is retained as an instrument-defect control, and the "
            "standing-review checklist names transpose-for-adjoint swaps"
        ),
        record="hunts/frontier_math/CLEAN-KILL-REPORT.md",
    ),
    KilledResult(
        name="conditional 0.6728294 (the bin artifact)",
        status="withdrawn",
        why=(
            "midpoint bin-to-cell assignment inflated chain counts, briefly "
            "producing a conditional bound past CG 1993"
        ),
        caught_by=(
            "the bin-width ladder: the floor fell under refinement, and the "
            "claim was withdrawn before shipping"
        ),
        recurrence_guard=(
            "cell edges now snap to the bin grid in the instrument; CG's "
            "conditional 0.6727534 stands unbeaten at current search depth"
        ),
        record="HANDOFF.md (frontier math record, 2026-08-11)",
    ),
    KilledResult(
        name="naive prime-by-prime (placewise) positivity",
        status="closed",
        why=(
            "individual place contributions can sometimes be represented as "
            "norms, but the local pieces do not consistently carry the sign "
            "naive global assembly needs"
        ),
        caught_by=(
            "the local-positivity hunt's own instruments; zeta.criteria face "
            "1 is the in-tree counterexample to the coefficient-blindness "
            "universal (ROADMAP known gap #0)"
        ),
        recurrence_guard=(
            "the do-not-fund list (ROADMAP, the outside memos triaged) names "
            "the route closed; the surviving question is the local-to-global "
            "successor, which is a different mechanism"
        ),
        record="docs/24-the-local-positivity-attempt.md",
    ),
)
