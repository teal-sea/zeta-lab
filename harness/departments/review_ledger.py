"""The repository's standing-review ledger, real claims, real attacks.

Machinery in :mod:`harness.review`; this file names actual claims. Two
entries open the ledger:

* **The exemplar, completed**: the 0.672529 positivity construction and its
  clean kill. This is the attack the whole standing-review specification is
  modeled on, entered retrospectively with its artifacts, the exact
  Gaussian-integer witness (``tr(P₁Q′) = −2``, the ``9 ≥ 13`` contradiction),
  the regression test, and the kernel-checked obstruction. The conformance
  test pins that every cited artifact still exists.
* **The open case**: the URMS2 0.51 theorem (main, 2026-08-11). Its briefs
  are generatable from this record today; ``standing_reasons`` lists what is
  missing, recorded outcomes from attackers who are not the author, and
  that list is the reviewer's worklist, not a formality. The Level 7
  frontier-math result is deliberately NOT entered: its thread is live, and
  a review enters the ledger when its subject lands, not while it moves.
* **The landed September and October candidates** (entered 2026-10-10):
  hunts #123 to #126 and the seventh-power extension, all built on OpenAI's
  7/8 half-plane, the L = 1.19 out-of-band window bound and the
  c = 2330/10^6 four-point build. ``ClaimUnderReview`` has no grade field,
  so each claim states its grade in its own text. None has a recorded
  outcome below, because no attack has run on any of them. An audit or a
  referee lane that the producing hunt ran is listed under
  ``controls_run``, not entered as an attack: it was not run from these
  briefs, and it is not the outside review that "pending external review"
  is waiting for.
"""

from __future__ import annotations

from harness.review import AttackOutcome, ClaimUnderReview

#: The input every half-plane claim below is conditional on, worded once so
#: the five entries cannot drift apart on what was and was not checked.
_QRH_INPUT = (
    "OpenAI, 'The Quasi-Riemann Hypothesis' (preprint dated 2026-09-30), "
    "Theorem 1.1: zeta and every Dirichlet L-function have no zero with "
    "Re s > 7/8. Its Lean statements were rebuilt here and accepted by Lean's "
    "kernel and the independent NanoDa kernel (docs/38 section 7); its "
    "195-page argument has been reviewed by no person"
)

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
            "bug by construction, retained as an instrument-defect control)",
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
    ClaimUnderReview(
        name="qrh-linnik-7/3",
        claim=(
            "given OpenAI's Theorem 1.1 (no Dirichlet L-function vanishes in "
            "Re s > 7/8) and Chen-Gupta-Li's single-modulus zero-density "
            "estimate (arXiv:2507.08296v2, a preprint), the least prime "
            "p = a (mod q) with (a, q) = 1 satisfies "
            "p(q, a) <= C(eps) q^(7/3 + eps) for every modulus q and every "
            "class a, with C(eps) effective; on refereed density inputs alone "
            "the exponent is 12/5 (hunt #123, hunts/qrh_linnik/, PR #277, "
            "landed 2026-10-08). Grade: candidate, pending external review: "
            "an ordinary written proof that no person has reviewed, on an "
            "input whose argument no person has reviewed"
        ),
        author="hunt #123 session (qrh_linnik, branch hunt/qrh-linnik, 2026-10-08)",
        assumptions=(
            _QRH_INPUT,
            "Chen-Gupta-Li Theorem 1.2 (arXiv:2507.08296v2, unrefereed) holds "
            "as stated for a single modulus, including its q1^(1/3) "
            "gcd-twist term, which sets 7/3",
            "Montgomery's Ingham-type mean value bound and Huxley (1975), the "
            "refereed inputs behind 12/5",
        ),
        code_paths=(
            "hunts/qrh_linnik/RESULTS.md",
            "hunts/qrh_linnik/exponents.py",
            "hunts/qrh_linnik/explicit_check.py",
            "hunts/qrh_linnik/test_qrh_linnik.py",
        ),
        controls_run=(
            "exact exponent algebra checked against a float grid, with "
            "planted lesions (a wrong CGL term, Huxley removed), pinned by "
            "test_qrh_linnik.py",
            "the explicit formula's sign and normalisation calibrated "
            "numerically for zeta (explicit_check.py; one route, measured)",
            "least primes for q <= 5000 tabulated as a descriptive picture "
            "(least_primes.json); a finite table cannot test a bound with an "
            "unspecified C(eps)",
        ),
        author_reasoning=(
            "a smoothed explicit formula with height cutoff a small power of "
            "x; the half-plane removes every zero above 7/8, so the Siegel "
            "zero, Deuring-Heilbronn repulsion and log-free density estimates "
            "drop out of the argument, and L is set by the single-modulus "
            "density exponent on [1/2, 7/8], which binds at sigma = 5/7 where "
            "Ingham's mean value bound meets CGL's q1^(1/3) term; CGL already "
            "state the conditional implication (Corollary 1.4), so nothing is "
            "claimed novel"
        ),
    ),
    ClaimUnderReview(
        name="qrh-class-number-1500",
        claim=(
            "given OpenAI's Theorem 1.1 (no Dirichlet L-function has a zero "
            "with Re s > 7/8), h(D) >= sqrt|D| / (10 pi log log |D|) for every "
            "negative fundamental discriminant D, and "
            "L(1, chi_D) >= 1/(10 log log |D|) for every such D other than -3; "
            "hence the imaginary quadratic fields of class number h are "
            "exactly those the hunt's exact search finds, for every h <= 1500: "
            "9 245 562 fields, the largest with |D| = 562 394 347 (hunt #124, "
            "hunts/qrh_class_number/, PR #279, landed 2026-10-08). Grade: "
            "candidate, pending external review: an ordinary written proof "
            "that no person has reviewed, every constant evaluated in Arb "
            "(enclosure-carrying), the lists by exact integer computation, on "
            "an input whose argument no person has reviewed"
        ),
        author="hunt #124 session (qrh_class_number, branch hunt/qrh-class-number, 2026-10-08)",
        assumptions=(
            _QRH_INPUT,
            "the verified interval cover that turns the bound into the table "
            "D(h) (dtable.json) has no gap, so h(D) <= h forces |D| <= D(h)",
            "the reduced-form sieve visits every fundamental discriminant "
            "below D(1500) and counts each class number exactly; the lists' "
            "counts and sha256 are committed, the full list is not, and "
            "streamed counts were recomputed independently in four windows, "
            "not throughout (oct08_extensions/MISSION.md records the same "
            "limit)",
        ),
        code_paths=(
            "hunts/qrh_class_number/RESULTS.md",
            "hunts/qrh_class_number/lbound.py",
            "hunts/qrh_class_number/explicit.py",
            "hunts/qrh_class_number/run_bounds.py",
            "hunts/qrh_class_number/run_search.py",
            "hunts/qrh_class_number/cn.c",
            "hunts/qrh_class_number/dtable.json",
            "hunts/qrh_class_number/search_H1500.json",
            "hunts/qrh_class_number/test_qrh_class_number.py",
        ),
        controls_run=(
            "the bound against exact L(1, chi_D) for every fundamental D with "
            "100 <= |D| <= 3 * 10^6: no violation, a planted inflation is "
            "caught (RESULTS.md section 6)",
            "Watkins' h <= 100 classification reproduced exactly; the odd "
            "h <= 1500 agree with Holmin and Kurlberg's GRH-conditional "
            "counts, computed by a different method",
            "1900 entries of the H = 1500 output, including the largest |D| "
            "for every h, against PARI qfbclassno, no disagreement "
            "(controls_pari_H1500.json)",
            "weakening the abscissa to 11/12 and 15/16 weakens the bound in "
            "the predicted way; the GRH specialisation is compared with "
            "Lamzouri, Li and Soundararajan",
        ),
        author_reasoning=(
            "Littlewood's short Euler product with two Cesaro cutoffs, and "
            "Hadamard positivity for the zero sum with every zero charged at "
            "beta = 7/8, make L(1, chi_D) explicitly large; a verified interval "
            "cover gives D(h), and an exact reduced-form sieve without GRH "
            "then enumerates every fundamental discriminant below D(1500)"
        ),
    ),
    ClaimUnderReview(
        name="qrh-nonresidue-log8",
        claim=(
            "given OpenAI's Theorem 1.1 (no Dirichlet L-function vanishes in "
            "Re s > 7/8), for every q >= 3 and every nonprincipal Dirichlet "
            "character chi mod q the least n with chi(n) not in {0, 1} is at "
            "most (log q)^8, and at most (0.7 log q)^8 for q >= 5; hence the "
            "least quadratic nonresidue mod every odd prime p is at most "
            "(log p)^8, and every odd composite n has a Miller-Rabin (strong) "
            "witness at most (0.7 log n)^8 (hunt #125, hunts/qrh_nonresidue/, "
            "PR #278, landed 2026-10-08). Grade: candidate, pending external "
            "review: an ordinary written proof that no person has reviewed, "
            "enclosure-carrying numerics, on an input whose argument no "
            "person has reviewed"
        ),
        author="hunt #125 session (qrh_nonresidue, branch hunt/qrh-nonresidue, 2026-10-08)",
        assumptions=(
            _QRH_INPUT,
            "the functional equation and the Hadamard identity at "
            "sigma0 = 2 theta + c price the sum over zeros with no zero "
            "counting; no zero location beyond the half-plane is used",
        ),
        code_paths=(
            "hunts/qrh_nonresidue/RESULTS.md",
            "hunts/qrh_nonresidue/explicit.py",
            "hunts/qrh_nonresidue/verify.py",
            "hunts/qrh_nonresidue/verification.json",
            "hunts/qrh_nonresidue/test_qrh_nonresidue.py",
        ),
        controls_run=(
            "every Arb constant against an independent mpmath evaluation",
            "exact subgroup generation for 3 <= q <= 10^4 and exhaustive "
            "least-nonresidue, primitive-root and strong-witness tables to "
            "10^7, plus OEIS record values re-derived by direct computation",
            "a weakened abscissa moves the measured exponent to 12 and 16 as "
            "predicted; a planted fault (the zero sum dropped) is refuted by "
            "n(48473881) = 67",
        ),
        author_reasoning=(
            "a smoothed explicit formula with weight (n/x)^(1/4) log(x/n), the "
            "zero sum bounded through the Hadamard identity, so the exponent "
            "1/(1 - 7/8) = 8 comes with constant 1 for every q >= 3; the "
            "exponent itself is classical (Rodosskii; Montgomery-Vaughan "
            "13.12), the explicit constant and the all-moduli statement were "
            "not found in the search"
        ),
    ),
    ClaimUnderReview(
        name="qrh-ninth-powers",
        claim=(
            "given OpenAI's Theorem 1.1 for zeta (zeta has no zero with "
            "Re s > 7/8), for every integer n >= 1 there is a prime p with "
            "n^9 < p < (n+1)^9; with it, a prime in (x, x + (1/2) x^(7/8) log x] "
            "for every real x >= e^8, and |psi(x) - x| < x^(7/8) (log x)^2 / "
            "(128 pi) for x >= e^10 (hunt #126, hunts/qrh_prime_powers/, "
            "PR #276, landed 2026-10-08). Grade: candidate, pending external "
            "review: ordinary written proofs that no person has reviewed, "
            "every numerical inequality decided in Arb (enclosure-carrying), "
            "small cases by Pratt certificates, on an input whose argument no "
            "person has reviewed"
        ),
        author="hunt #126 session (qrh_prime_powers, branch hunt/qrh-prime-powers, 2026-10-08)",
        assumptions=(
            _QRH_INPUT,
            "the explicit zero-counting bounds cited in RESULTS.md section 1; "
            "the verified RH height only widens margins (k = 9 also closes "
            "with none)",
            "the steps the hunt itself names for a reviewer to check first "
            "hold: the use of (I4) in Lemma 3.1, Lemma 5.1's Stieltjes "
            "boundary terms, the monotonicity Lemma 6.2, and the tail lemmas "
            "6.4, 8.2 and 9.3, of which 9.3 is written as a sketch",
        ),
        code_paths=(
            "hunts/qrh_prime_powers/RESULTS.md",
            "hunts/qrh_prime_powers/bound.py",
            "hunts/qrh_prime_powers/verify.py",
            "hunts/qrh_prime_powers/pratt.py",
            "hunts/qrh_prime_powers/verification.json",
            "hunts/qrh_prime_powers/test_qrh.py",
        ),
        controls_run=(
            "two routes for each load-bearing identity: the explicit-formula "
            "normalisation against a direct prime sum, the closed-form "
            "zero-sum integrals against quadrature",
            "threshold control (Proposition T): the same chain at abscissa "
            "11/12 and 15/16 closes at k = 13 and k = 17 as predicted, and "
            "fails at k - 1 in each case",
        ),
        author_reasoning=(
            "the exact explicit formula for a quadratic B-spline weight, sums "
            "over zeros bounded in closed form through explicit N(T), an Arb "
            "cover of 10 <= n <= e^100, an analytic tail and Pratt "
            "certificates for n <= 9; the gap (n+1)^k - n^k, about "
            "k x^(1 - 1/k), beats an error of size x^(7/8) (log x)^2 exactly "
            "when k >= 9, and without further input the chain fails at k = 8; "
            "qrh-seventh-powers inherits this weight, formula and base "
            "routine, so a defect found here bears on both"
        ),
    ),
    ClaimUnderReview(
        name="qrh-seventh-powers",
        claim=(
            "given QRH(7/8) for zeta (no nontrivial zero of zeta has real part "
            "above 7/8, the zeta part of OpenAI's Theorem 1.1) and Kadiri, "
            "Lumley and Ng's explicit zero-density rows (arXiv:2101.12263v1, "
            "Lemma 4.14 and Table 1), every integer n >= 1 has a prime "
            "strictly between n^7 and (n+1)^7; an eighth-power version on the "
            "same route is its audited predecessor (hunts/oct08_extensions/, "
            "PR #282, landed 2026-10-08). Grade: written conditional "
            "candidate: a written proof with every numerical step "
            "enclosure-carrying; an independent written audit by a separate "
            "agent context, of the author's model family, passed; reviewed by "
            "no person; not formalized in Lean; no worldwide priority claimed"
        ),
        author="oct08_extensions producer (Codex root; route prime_gap_density, 2026-10-08)",
        assumptions=(
            _QRH_INPUT,
            "KLN's rows at sigma = 0.75, 0.8, 0.85, 0.86 and 0.87 hold as "
            "printed (rounded upward in layers.py); their constant "
            "calculations are accepted, not recomputed, and their critical-line "
            "input rests on Hiary, Patel and Yang plus a new Acb low-height "
            "check (audits/kln-restoration/)",
            "hunt #126's explicit formula, weight, zero counting and verified "
            "RH height, inherited unchanged (claim qrh-ninth-powers); "
            "base_bound.py is byte-for-byte from that branch and the audit "
            "reuses it, so computational independence stops there",
        ),
        code_paths=(
            "hunts/oct08_extensions/RESULTS.md",
            "hunts/oct08_extensions/REVIEW-STATUS.md",
            "hunts/oct08_extensions/routes/prime-gap-multistrip/RESULTS.md",
            "hunts/oct08_extensions/routes/prime-gap-multistrip/layers.py",
            "hunts/oct08_extensions/routes/prime-gap-multistrip/verification.txt",
            "hunts/oct08_extensions/routes/prime-gap/RESULTS.md",
            "hunts/oct08_extensions/routes/prime-gap/density.py",
            "hunts/oct08_extensions/routes/prime-gap/base_bound.py",
            "hunts/oct08_extensions/audits/prime-gap-multistrip/AUDIT.md",
            "hunts/oct08_extensions/audits/prime-gap-multistrip/check.py",
            "hunts/oct08_extensions/audits/prime-gap/AUDIT.md",
            "hunts/oct08_extensions/audits/prime-gap/SOURCE-CHECK.md",
            "hunts/oct08_extensions/audits/kln-restoration/SOURCE-CHECK.md",
            "tests/test_seventh_power_replay.py",
        ),
        controls_run=(
            "764 Arb cells at 256 bits cover 2.25 <= log n <= 50 with every "
            "margin above 0.13045, an analytic tail below 0.012961 covers "
            "log n >= 50, and nine trial-division witnesses cover n <= 9 "
            "(verification.txt, replayed by tests/test_seventh_power_replay.py)",
            "the independent written audit run inside the producing hunt: its "
            "own 384-bit density integrator, exact rational synthetic zero "
            "atoms at every strip boundary, missing-first-layer and "
            "missing-last-layer mutants rejected (audits/prime-gap-multistrip/)",
            "the same bound fails at k = 6 near log n = 29 while k = 7 passes: "
            "a failure of the bound, not a statement about primes",
            "source checks: KLN's Lemma 4.14 rather than its introductory "
            "theorem, the explicit-formula source (audits/prime-gap/), and "
            "the critical-line correction (audits/kln-restoration/)",
        ),
        author_reasoning=(
            "bound x^(beta - 1) pointwise by x^(s0 - 1) plus positive "
            "increments times the indicators beta > s_j over the strips "
            "3/4 < 0.8 < 0.85 < 0.86 < 0.87 < 7/8, so cumulative density upper "
            "bounds substitute without subtracting independently bounded "
            "counts; for log x >= 8 each increment decreases in x, so a cell "
            "takes the increments at its left end and the zero sums at its "
            "right; a single split at 0.85 already closes k = 8, and "
            "resolving the strips closes k = 7"
        ),
    ),
    ClaimUnderReview(
        name="oob-envelope-L1.19",
        claim=(
            "for every real even f with supp f in [-1.19, 1.19] (support "
            "2.38), Weil's form on the window satisfies "
            "Q(f) >= 5.7178e-48 ||f||^2; the route is the out-of-band envelope "
            "lemma: a correction to the Weil symbol at frequencies of size at "
            "least 2L leaves the form unchanged on the window, so the envelope "
            "constant in arXiv:2608.24827's one-stroke reduction can drop from "
            "sup P_L to sup (P_L - H) (hunts/oob_envelope/, PR #258, landed "
            "2026-09-28). Grade: candidate, hardened by two independent "
            "implementations (sharing python-flint), resting on an ordinary "
            "derivation that passed the hunt's referee lane; even sector "
            "only; not kernel-checked; pending external verification"
        ),
        author="oob_envelope numerics and theory lanes (2026-09-27/28)",
        assumptions=(
            "Q >= R_H, the modified reduction (theory lane): an ordinary "
            "derivation, referee PASS with stated scope, reviewed at L = 4/5 "
            "and independent of L",
            "Zhu's two-block bound (13) and the reduction of arXiv:2608.24827 "
            "as transcribed, with the tail terms eps_D and eps_B enclosed",
            "the numerics lane's Gauss-Legendre quadrature radii, which the "
            "referee did not audit; the referee's own Clenshaw-Curtis route "
            "is the independent check",
        ),
        code_paths=(
            "hunts/oob_envelope/numerics/RESULTS.md",
            "hunts/oob_envelope/numerics/RUNS.md",
            "hunts/oob_envelope/numerics/stage_b_modal.py",
            "hunts/oob_envelope/numerics/stage_b_result.json",
            "hunts/oob_envelope/theory/RESULTS.md",
            "hunts/oob_envelope/referee/REVIEW.md",
            "hunts/oob_envelope/referee/l119.py",
        ),
        controls_run=(
            "the hunt's referee lane, reading none of the author's code, "
            "proves lambda_min(R_H) > 5.7179e-48 on the same 500-mode subspace "
            "with its own Clenshaw-Curtis-192/Arb implementation and "
            "recomputes the tail terms (referee/REVIEW.md, 'L = 1.19', PASS)",
            "negative controls: at L = 4/5, T# = 60, where the form is "
            "indefinite, the step returns no bound; a planted in-band constant "
            "fires; dropping or flipping H does not discriminate at L = 4/5",
            "on Davenport-Heilbronn, where the form is negative, the valid "
            "pipeline returns no bound",
            "one-sided consistency with Zhu's Table 3 ceiling at L = 1.1",
        ),
        author_reasoning=(
            "|F|^2 is the Fourier transform of f * f~, supported in [-2L, 2L], "
            "so a bounded almost-periodic H whose frequencies all have size at "
            "least 2L integrates to zero against it; per prime the best "
            "out-of-band correction is a Caratheodory-Toeplitz problem, "
            "realised within a Fejer loss by a nonnegative kernel sum; with "
            "H = sine:16 the envelope constant at L = 1.19 falls from "
            "A_L = 7.0750 to 3.8634773 (envelope.json), which brings the "
            "matrix to N = 500 even Legendre modes"
        ),
    ),
    ClaimUnderReview(
        name="four-point-0.6728604",
        claim=(
            "for every eps > 0 and all sufficiently large T, the number of "
            "simple zeros of zeta on the critical line with ordinate in "
            "(T, 2T] is at least ((14400000 H - 17240)/14366681 - eps) times "
            "the number of nontrivial zeros there, counted with multiplicity, "
            "where H = 3/2 - cot(1/sqrt 2)/sqrt 2; the coefficient is about "
            "0.6728603588, from four-point pressure parameters "
            "(n, c, m, p) = (4, 2330/10^6, 432, 2500) "
            "(hunts/four_point_pressure/, PR #259, landed 2026-09-28). Grade: "
            "kernel-checked at the pinned revision 5522b963 by the "
            "laboratory's own build, pending external verification, not "
            "registered with Palomar"
        ),
        author="four_point_pressure sessions (candidate d28df5f9, 2026-09-05; Hermes repair and lab build at 5522b963, 2026-09-28)",
        assumptions=(
            "the Lean statements say what the claim says: Mathlib's "
            "riemannZeta, multiplicity as analytic order, ordinates in "
            "(T, 2T] (hunts/ainta_seven_point/lean-four-point/StrongerChallenge.lean)",
            "the build record at 5522b963 is what it reports: one build on the "
            "laboratory's own Modal compute at Lean 4.33.0-rc2, not an outside "
            "rebuild",
            "the later Lean 4.35 port changes module headers, visibility and "
            "dependency pins; the 2026-09-28 bundle is not evidence that those "
            "changes compile, and the port's comparison is a separate record",
        ),
        code_paths=(
            "hunts/four_point_pressure/RUNS.md",
            "hunts/four_point_pressure/evidence/README.md",
            "hunts/four_point_pressure/evidence/main-axioms-print-output.txt",
            "hunts/four_point_pressure/PALOMAR-READINESS.md",
            "hunts/ainta_seven_point/lean-four-point/",
            "tests/test_four_point_build_evidence.py",
        ),
        controls_run=(
            "49 build receipts, zero sorry warnings, and only propext, "
            "Classical.choice and Quot.sound for the six advertised "
            "declarations (evidence/README.md)",
            "source hashes recomputed from Git objects at 5522b963 during "
            "integration; tests/test_four_point_build_evidence.py pins the "
            "saved record, its source binding and the coefficient",
            "the emitted-source preflight of 2026-09-05 (1516 cell lemmas, "
            "11863 leaves, zero problems): an arithmetic and coverage check, "
            "not a kernel check",
            "after the Lean 4.35 port, Lean, NanoDa and con-ron accepted the "
            "exported solution in the laboratory's own comparison "
            "(PALOMAR-READINESS.md); not a registry verdict",
        ),
        author_reasoning=(
            "substituting c = 2330/10^6, m = 432, p = 2500 into the existing "
            "n-point bridge gives the coefficient "
            "(14400000 H - 17240)/14366681 exactly; the finite certificate is "
            "a generated tree of interval cell lemmas proved inside Lean, so "
            "the theorem carries no certificate hypothesis; the parameter "
            "floor was already tabulated in hunts/ainta_seven_point/FOUR-POINT.md, "
            "so the parameters are not a discovery"
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
