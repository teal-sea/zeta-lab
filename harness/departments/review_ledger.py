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
    ClaimUnderReview(
        name="rf-c003-window",
        claim=(
            "the quartic window v*(s) = 1 - (1467/1000)s^2 + (1159/1000)s^4 "
            "improves the source paper's cos(8s/5) window, giving "
            "F(v*) = 2245228120295149280/3276332462159207451 and the "
            "RH-conditional constant 50176758585216887915/58973984318865734118 "
            "(hunts/rogue_frontier/window_opt/, landed 2026-08-21)"
        ),
        author="rogue_frontier campaign (2026-08-17/18)",
        assumptions=(
            "the source paper's SS7.1 and SS7.5(g) functional is transcribed "
            "correctly, so the optimisation is over the right F",
            "the claim is RH-conditional and is not stated otherwise",
            "the rounded rational window is within 8.9e-9 of the true optimum, "
            "which is asserted by the arm rather than enclosed",
        ),
        code_paths=("hunts/rogue_frontier/window_opt/",),
        controls_run=(
            "v = 1 reproduces the published sine-Gram moments (4/3, 2) on "
            "three independent routes (quadrature, piecewise-linear exact, "
            "Fraction exact)",
            "the paper's own cos(8s/5) window reproduces its printed 30-digit "
            "m2, m3 and F on both the float and the sympy routes",
            "the Fraction route and the sympy route agree exactly on the "
            "optimised quartic",
        ),
        author_reasoning=(
            "an even quartic has enough freedom to beat the paper's single "
            "cosine, and the whole functional is exactly rational on that "
            "class, so the improvement can be stated without any float"
        ),
    ),
    ClaimUnderReview(
        name="k2-far-constant-depth1",
        claim=(
            "the far-field constant 637/1000 does not survive at depth 1: "
            "sup Dam*(s^2-2)/y^2 measures 0.6636 > 0.637 there, so "
            "Wt_tail_le's 637/1000 is a correction any depth-1 argument must "
            "carry (K2-TWO-SPECIES.md section 2, 2026-08-15)"
        ),
        author="frontier_math two-species session (2026-08-15)",
        assumptions=(
            "the scanned range [8, 400] is the range on which 637/1000 is "
            "asserted (it is not: Wt_tail_le is stated for w = s^2-2 >= 1368, "
            "i.e. s >= 37.0135)",
            "the failing constant belongs to Wt_tail_le (it does not: that "
            "lemma has no depth variable in its statement)",
        ),
        code_paths=("hunts/frontier_math/two_species.py",),
        controls_run=(
            "the depth-1/2 row of the same table reproduces the k=1 "
            "landscape, so the scan itself was cross-checked against known "
            "values (it has zero power against a range mismatch, since both "
            "rows are scanned over the same wrong range)",
        ),
        author_reasoning=(
            "the depth-1/2 scan gives 0.6220 < 0.637 and the depth-1 scan "
            "gives 0.6636 > 0.637, so the constant looked like it was being "
            "crossed as depth rose"
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
    AttackOutcome(
        claim_name="urms2-0.51",
        role="white-box",
        attacker="Fulcrum hunt R-2AC05F (run 55786d8e, Claude Opus 5, 2026-08-20)",
        findings=(
            "the xi-double-prime form-factor row that hunts/higher_xi/ "
            "C2_EXACT.json and C2_EXTENDED.json rest on survives an "
            "independent fourth derivation: a formal Dirichlet word algebra "
            "written for this adjudication, importing neither hunt, "
            "reproduces C_2,i = 1, -8, 24, -32, 64/3, -64/3, 1216/45, "
            "-256/15, 1088/63, -11776/945, 42496/4725 exactly at all eleven "
            "indices",
            "its external control passes: the same code at kappa = 1 "
            "reproduces the Farmer-Gonek closed form (arXiv:0803.0425) "
            "exactly at all eleven indices, including the four forced zeros",
            "the conflicting table in hunts/rogue_frontier/fkappa/ (commit "
            "360c545, corrected mode, rows['2'] = 1, -4, 4, -16, 52/3, ...) "
            "is wrong from i = 2, and the mechanism is inheritance rather "
            "than arithmetic: its RESULTS.md section 1 carries Bian's "
            "Lemma 12 constant C_kappa,2 = -4 as an axiom while auditing the "
            "code around it",
            "general form of the defect, derived here and recorded nowhere "
            "else: the x^1 coefficient of Qhat_kappa = Q_kappa / L^kappa is "
            "kappa*g for every kappa, so C_kappa,2 = -4*kappa (-4, -8, -12, "
            "-16, -20 for kappa = 1..5). Lemma 12's universal -4 is the "
            "dropped M(v_l)M(w_k) weight that C2_PROVENANCE.md names on "
            "thesis page 71, confirming higher_xi's causal diagnosis",
            "measured control power rather than asserted: planting exactly "
            "that defect in this probe leaves the Farmer-Gonek kappa = 1 "
            "control passing and moves C_2,2 to the published -4, while a "
            "one-factorial corruption of the pairing turns the same control "
            "red. The only externally anchored control either hunt ran has "
            "zero power against the defect that decided the dispute; the "
            "control that would have caught it is to compute C_kappa,2 for "
            "kappa = 1, 2, 3 and assert the values differ",
            "no attack was mounted on the URMS2 bandwidth argument itself; "
            "this outcome bears only on the coefficient table beneath it, "
            "which it leaves standing",
        ),
        artifacts=(
            "hunts/r_2ac05f/RESULTS.md",
            "hunts/r_2ac05f/probe.py",
            "hunts/r_2ac05f/fault_check.py",
            "hunts/r_2ac05f/results.json",
            "hunts/r_2ac05f/HANDBACK.json",
        ),
    ),
    AttackOutcome(
        claim_name="rf-c003-window",
        role="white-box",
        attacker="Fulcrum hunt R-F00E48 (run 8b5765ae, Claude Opus 5, 2026-08-21)",
        findings=(
            "this is a landing check, not a mathematical attack, and it is "
            "recorded as one so nobody later mistakes it for review: the "
            "hunt salvaged window_opt/ onto main and re-ran the arm's own "
            "code, so it shares every assumption the claim makes",
            "what it does establish: moments_polyeven_exact(OPT_Q) recomputes "
            "F = 2245228120295149280/3276332462159207451 exactly from the "
            "landed source, and the landed RESULTS.md quotes that same "
            "rational, so the document and the code agree in this tree",
            "the arm's REPRODUCE.md headline command did not run at all. It "
            "named functional.exact_F_quartic(1467, 1159), a symbol that has "
            "never existed under either that name or that signature; the "
            "function is moments_polyeven_exact(OPT_Q) and it returns "
            "(m2, m3, F). A reader following the published recipe would have "
            "got an ImportError, which is a reproducibility defect in a "
            "promoted claim and is now fixed and pinned",
            "nothing was attacked in the transcription of the source paper's "
            "SS7.1/SS7.5(g) functional, in the optimality of the rounded "
            "quartic, or in the enclosure arm. The claim therefore stands "
            "with no blind attack and no independent white-box derivation, "
            "which standing_reasons() will keep saying until someone runs one",
        ),
        artifacts=(
            "hunts/r_f00e48/probe.py",
            "hunts/r_f00e48/results.json",
            "hunts/r_f00e48/RESULTS.md",
            "hunts/r_f00e48/HANDBACK.json",
            "hunts/rogue_frontier/LANDING.md",
        ),
    ),
    AttackOutcome(
        claim_name="k2-far-constant-depth1",
        role="white-box",
        attacker="Fulcrum hunt R-A7C12F (run e09a7f8a, Claude Opus 5, 2026-08-23)",
        findings=(
            "the claim is withdrawn: 637/1000 DOES survive at depth 1 on the "
            "range it is asserted on. An Arb pass at 96 bits over "
            "s in [37.0135, 400] with the depth as a thin ball gives "
            "sup Dam(1,s)*(s^2-2) <= 0.6317736, against 637/1000, margin "
            "+0.0052 (0.82%). The enclosure costs a factor 1.00005 over the "
            "float scan, so the bound is not an artifact of interval width",
            "the 0.6636 is a range mismatch, not a crossed constant. "
            "two_species.far_constant scans s in [8, 400], but Wt_tail_le is "
            "stated for w = s^2 - 2 >= 1368, i.e. s >= 37.0135. Both starred "
            "sups are attained at s = 12.715 (depth 1/2) and s = 12.625 "
            "(depth 1), i.e. w = 159.7 and w = 157.4, roughly 8.7x below the "
            "threshold. At those two arguments the proved envelope Wt(w)*w is "
            "0.7042 and 0.7054, so BOTH rows of the table, 0.6220 and 0.6636, "
            "sit under the constant that actually applies there",
            "Wt_tail_le is misattributed and cannot fail at any depth. Its "
            "statement (Counting.lean:93) is Wt w <= (637/1000)/w for "
            "1368 <= w, an inequality between two explicit rational functions "
            "of one variable; no y occurs in it. The depth-carrying lemma is "
            "Qim_far_sq / Qim_far_sq_abs (FarField.lean:227,232), whose "
            "hypothesis is hy : y <= 1/2",
            "and that hypothesis is load-bearing, which is the real finding "
            "under the false one. Qim^2 <= y^2 Wt(s^2-2) fails at depth 1: "
            "max ratio 1.00438 at s = 395.8, rising with s. Its asymptotic "
            "content holds iff 4 sinh(y/2)^2 cos(1/sqrt2)^2/y^2 <= 5/8, which "
            "breaks at y = 0.97266. So a k >= 3 pass that raises depth "
            "inherits a broken DERIVATION ROUTE, not a broken constant",
            "the constant's own headroom is measured rather than assumed: on "
            "the asserted range it first exceeds 637/1000 at depth 1.0494 "
            "(float scan), with asymptotic break depth 1.0855. Depth 1 sits "
            "inside that, depth 2y for y <= 1/2 sits exactly on its edge",
            "not attacked, and named so nobody reads this as more than it is: "
            "s > 400 has no enclosure here. The k=2 far rows close that tail "
            "by composing Wt_tail_le with Qim_far_sq, and Qim_far_sq is "
            "precisely the step that fails at depth 1, so the depth-1 tail is "
            "float-grade only (sup 0.62781 on [400, 4000], against the closed "
            "form 0.62777). Re-deriving Wt's coefficients for y <= 1 is the "
            "named obligation and was not attempted",
            "the other starred entry of the same table, no_damage's 28/5 "
            "shrinking to 5.3984 at depth 1, was NOT examined. It is a "
            "different lemma with a different quantifier structure and this "
            "outcome says nothing about it",
        ),
        artifacts=(
            "hunts/r_a7c12f/probe.py",
            "hunts/r_a7c12f/results.json",
            "hunts/r_a7c12f/RESULTS.md",
            "hunts/r_a7c12f/HANDBACK.json",
            "hunts/r_a97060/ball_field.py",
        ),
    ),
)
