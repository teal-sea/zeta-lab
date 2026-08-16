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
        role="blind",
        attacker="Antigravity Zeta Lab Researcher",
        findings=(
            "If an instrument evaluates u u^* instead of u u^T, it constructs a Gram matrix that is PSD by definition. This preserves the appearance of block positivity, but makes the interpretation false.",
            "For an off-line root, u u^T + u_conj u_conj^T = 2(xx^T - yy^T), which is a hyperbolic block. A dedicated scan confirms cross-block interaction evaluates to approximately -0.000435.",
        ),
        artifacts=(
            "hunts/frontier_math/blind_attack.py",
            "hunts/frontier_math/BLIND-ATTACK-REPORT.md",
        ),
        claim_withdrawn=True,
    ),
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
    AttackOutcome(
        claim_name="urms2-0.51",
        role="blind",
        attacker="Fulcrum hunt R-FB9C81 (run 36a6a319, Antigravity, 2026-08-15)",
        findings=(
            "no structural failure found in the RC2 off-diagonal error "
            "bounds: the claim survives this attack",
            "the arithmetic conditions the Montgomery-Vaughan mean-value "
            "theorem requires hold past the half-band, because coefficient "
            "decay absorbs the increased polynomial length",
        ),
        artifacts=(
            "hunts/r_fb9c81/RESULTS.md",
            "hunts/r_fb9c81/probe.py",
            "hunts/r_fb9c81/HANDBACK.json",
        ),
    ),
    AttackOutcome(
        claim_name="urms2-0.51",
        role="white-box",
        attacker="Fulcrum hunt R-065F29 (run 726a6b3f, Claude Opus 5, 2026-08-16)",
        findings=(
            "the mathematics of the half-band crossing survives: the exact "
            "block second moment saturates to four significant figures "
            "(17.2964 to 17.3642) while W/U grows from 1.3 to 9.9, which is "
            "the W-independence the claim asserts, measured in the regime the "
            "old proof's W/U = o(1) forbade",
            "section 4's partial summation is correct under its hypothesis: a "
            "surrogate family satisfying A(y) << y log y makes the upper-range "
            "sum saturate over a 67-fold W sweep",
            "but the record's own falsification control does not satisfy that "
            "hypothesis. On the frozen level-two family that section 9's "
            "ell = 6, 8, 10 table runs on, A(y)/(y log y) climbs by a factor of "
            "88 from its trough, and the upper-range sum grows like W^0.825 at "
            "fixed x instead of saturating. The ladder cannot see this because "
            "it moves x and W together at effective gamma = 1 and never varies "
            "W at fixed x, which is the quantity section 4 claims",
            "URMS2-051-AUDIT.md gate 6's 'independent route' is a second "
            "arithmetic assembly of the same numbers: C2_EXTENDED.json "
            "reproduces corrected_coefficients(40) exactly, both routes import "
            "the same tail majorant, and a one-part-in-1e6 mutation of "
            "fock_upper_coefficient(41) moves both denominators by the "
            "identical 4.426081703885579e-27",
            "the four recorded margins of urms2_051_witness() do not select "
            "51/100: they stay feasible to alpha = 257/500 at the published "
            "(delta, gamma, epsilon) and admit alpha = 0.9 with (delta, gamma, "
            "epsilon) free, so something binds that is not written down",
            "four of the six obligations URMS2-051.md section 7 lists have no "
            "audit gate and are carried by 'retain their earlier bounds' -- "
            "bounds established under gamma < delta < 1, inherited across the "
            "gamma = 21/20 > 1 regime change that is this proof's whole novelty",
        ),
        artifacts=(
            "hunts/r_065f29/RESULTS.md",
            "hunts/r_065f29/probe.py",
            "hunts/r_065f29/results.json",
            "hunts/r_065f29/HANDBACK.json",
        ),
    ),
)
