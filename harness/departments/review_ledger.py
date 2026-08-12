"""The repository's standing-review ledger — real claims, real attacks.

Machinery in :mod:`harness.review`; this file names actual claims. Two
entries open the ledger:

* **The exemplar, completed**: the 0.672529 positivity construction and its
  clean kill. This is the attack the whole standing-review specification is
  modeled on, entered retrospectively with its artifacts — the exact
  Gaussian-integer witness (``tr(P₁Q′) = −2``, the ``9 ≥ 13`` contradiction),
  the regression test, and the kernel-checked obstruction. The conformance
  test pins that every cited artifact still exists.
* **The open case**: the URMS2 0.51 theorem (main, 2026-08-11). Its briefs
  are generatable from this record today; ``standing_reasons`` lists what is
  missing — recorded outcomes from attackers who are not the author — and
  that list is the reviewer's worklist, not a formality. The Level 7
  frontier-math result is deliberately NOT entered: its thread is live, and
  a review enters the ledger when its subject lands, not while it moves.
"""

from __future__ import annotations

from harness.review import AttackOutcome, ClaimUnderReview

CLAIMS: tuple[ClaimUnderReview, ...] = (
    ClaimUnderReview(
        name="blockpos-0.672529",
        claim=(
            "the constructive block-positivity residue transplants to the "
            "pinned upstream zero side, giving 0.672529 unconditionally"
        ),
        author="frontier_math blockpos session (2026-08)",
        assumptions=(
            "the upstream zero side uses u u* (it uses u u^T)",
            "off-line pair blocks interact non-negatively with on-line part",
        ),
        code_paths=("hunts/frontier_math/blockpos.py",),
        controls_run=(
            "squared-modulus block scan (zero power against the transpose "
            "bug by construction — retained as an instrument-defect control)",
        ),
        author_reasoning=(
            "positivity of each block was checked numerically; the "
            "construction was believed basis-independent"
        ),
    ),
    ClaimUnderReview(
        name="urms2-0.51",
        claim=(
            "the URMS2 bandwidth extends past the half band to 0.51, with "
            "the algebraic frontier formalized (main, 503158a and ancestors)"
        ),
        author="urms2 bridge sessions (2026-08-11)",
        assumptions=(
            "the true logarithmic frequency separation is preserved rather "
            "than collapsed into a cutoff estimate",
        ),
        code_paths=("hunts/higher_xi/",),
        controls_run=("the audit pass recorded in commit 4e5aeaa",),
        author_reasoning=(
            "several apparent bandwidth barriers were artifacts of lossy "
            "estimates; this one fell to preserving frequency separation"
        ),
    ),
)

OUTCOMES: tuple[AttackOutcome, ...] = (
    AttackOutcome(
        claim_name="blockpos-0.672529",
        role="white-box",
        attacker="frontier_math clean-kill session (2026-08-11)",
        findings=(
            "the pinned upstream zero side uses u u^T, not u u*: an off-line "
            "pair is the hyperbolic block 2m(xx^T − yy^T), whose interaction "
            "with the on-line part can be negative",
            "exact witness u_x=1, u_z=i, u_conj(z)=-i gives tr(P1 Q') = -2; "
            "with five unit on-line labels the final inequality reads 9 >= 13",
        ),
        artifacts=(
            "hunts/frontier_math/clean_kill.py",
            "hunts/frontier_math/CLEAN-KILL-REPORT.md",
            "lean/ZetaLean/FrontierMathObstruction.lean",
        ),
        claim_withdrawn=True,
    ),
)
