# Author response to THEOREM_B_FORMULA_REVIEW.md

- Artifact: `THEOREM_B_FORMULA_REPAIR.md`, with `formula_repair_checks.py` and
  `results_formula_repair_checks.json`.
- Reviewed form: `95ae36b9c09c0cf28844e40e50f7fceac2f95cfb`. This response describes the
  revision committed after it.
- The review file and the reviewer's own checks (`formula_review_checks.py`,
  `results_formula_review_checks.json`) were not edited, not re-run and not committed by the
  author.
- **The revised proofs have not been reviewed.** Nothing below claims otherwise.

## Summary

| finding | disposition | artifact changed |
|---|---|---|
| R1 inclusive zero sum | accepted | yes |
| R2 two-sided count for divergence | accepted | yes |
| R3 transfer margin in (MISSING) | accepted; remedy validated and tightened, not copied | yes |
| R4 "explicit sequence" overclaim | accepted | yes |
| R5 clarity bundle | accepted in part: (a) to (e) accepted, (f) declined | yes, except (f) |
| open item: M&V primary source not inspected | closed | yes (section 8) |

**Load-bearing formula: unchanged.** The coefficient `c(rho') = (rho'-1)/(2 rho'(rho'+1))`,
the remainder shape `C_1 x^2 T^{-1} log^2(xT) + 2 C_1 x log x + C_2`, and every numerical
check value are as in `95ae36b`. What changed is the index set, multiplicity notation,
thresholds, provenance and the scope of several claims.

## Source verification for (F1)

The reviewer could not reach Montgomery and Vaughan and marked (F1) as resting on the
RESULTS.md section 17 paraphrase. For this revision the primary statement was read: *MNT I*
Theorem 12.10 (chapter 12, "Explicit formulae", pp. 397 to 418, author-hosted copy at Penn
State, read 2026-09-20). Checked against what Proposition 3 needs:

1. *Hypotheses.* `c > 1` constant, `x >= c`, `T >= 2`, `chi` primitive mod `q > 1`. No
   restriction `T <= x` and no admissible-height condition. The implied constant depends on
   `c` only, so the bound is uniform in `x` and `T`.
2. *Normalization.* The theorem is for the midpoint form `psi_0(x, chi)`; the half-jump at
   prime powers is absorbed as the file already said.
3. *Index set and multiplicity.* The sum runs over nontrivial zeros with `|gamma| <= T`,
   inclusive of any real zero, each counted with multiplicity.
4. *Trivial zeros.* For odd `chi` (`kappa = 1`) the trivial-zero terms are as used in
   section 5.
5. *Error term.* The printed error carries `min(1, x/(T<x>))` and `log^2(3xT)`. Using
   `min(1, .) <= 1`, `log^2(3xT) <= 4 log^2(xT)` for `xT >= 3`, and the odd-character
   collapse of the `log` term gives exactly the shape Proposition 3 uses.

Consequence: **Proposition 3 does not need to be made conditional on (F1)**, and neither its
coefficient nor its remainder shape changes. No numerical value of `C_1` is claimed, so the
remainder is shape-explicit and not effective.

(F2-low) was checked in the same way against chapter 14 (Theorem 14.5, Corollary 14.6). One
gap remains and is stated in the artifact: the bound `S(T, chi) << log(q(T+2))` was not
located in the extracted chapter text and is cited from the standard literature.

## R1. Proposition 3 drops a possible real zero

**Accepted.** The reviewer is right that the proof carried `|gamma'| <= T` and the statement
narrowed to `0 < |gamma'| <= T` without justification; a real zero would contribute a term of
order up to `x^2` that `E` does not absorb.

**Change: yes.** Both remedies were applied, with the inclusive statement as the load-bearing
one:

- Proposition 3, section 6 Steps 1 to 3 and `C_2` now use `sum_{|gamma'| <= T} m(rho') ...`,
  inclusive, multiplicity explicit, matching (F1) as verified above.
- New Lemma 1 (section 1): `L(s, chi_3) > 0` for real `s > 0`, proved by grouping the series
  as `sum_k [(3k+1)^{-s} - (3k+2)^{-s}]`, each bracket positive, giving
  `L(s) >= 1 - 2^{-s} > 0`, with the grouping justified by Dirichlet's test and analytic
  continuation. For `chi_3` the inclusive and exclusive index sets therefore coincide, but
  Proposition 3 does not depend on Lemma 1.
- `rho' = 0` and `rho' = -1` are excluded from `C_2` as the reviewer noted (`L(0) = 1/3`,
  `-1` is trivial).
- Check C7 illustrates Lemma 1 numerically against a tail bound proved on the spot. It is
  labelled NOT PROOF.

**Surviving claim.** Proposition 3 as stated, with an inclusive, multiplicity-weighted zero
sum, derived from the verified (F1); and, for `chi_3`, no real zero in `(0, 1)`.

## R2. Divergence cited from an upper-bound-only fact

**Accepted.** An upper bound on zero density is consistent with convergence and cannot give
`sum |c(rho')| = infinity`.

**Change: yes.** Defect 1 (section 2) now uses (F2-low), the two-sided count from *MNT I*
Theorem 14.5 and Corollary 14.6, to get `N(2T, chi) - N(T, chi) >> T log T`; with the
per-zero bound `|c(rho')| >= 1/(7 |gamma'|)` for `|gamma'| >= 1` (re-derived by the reviewer
and unchanged) a dyadic sum gives `sum_{|gamma'| <= T} |c| >> log^2 T`, hence divergence.
Wherever only an upper bound is used (convergence of `C_2`, the competitor bound in section
7(b)) the text now cites (F2-up) and says an upper bound suffices. "Asymptotically" survives
only where both bounds are cited (section 10, point 1: bounded above and below by constant
multiples of `log^2 T`).

**Surviving claim.** `sum |c(rho')|` diverges, so the expansion `(*)` of
THEOREM_B_SEQUENCE.md is refuted as stated. The refutation rests on Corollary 14.6 (read in
the primary source) plus the classical `S(T, chi)` bound (cited, page not inspected).

## R3. (MISSING) not sufficient as stated

**Accepted, and the reviewer's remedy was checked rather than adopted wholesale.**

The margin actually needed in step (e) is not `1 - Theta > 0`. Step (e) must absorb the
Theorem A error `O(N^{Theta + Theta_chi} log^4 N)` against the signal `N^{1 + beta_0}`, so
the exact condition is

    1 + beta_0 > Theta + Theta_chi.

Under (H-ISO), `beta_0 = Theta_chi` and this reduces to `Theta < 1`, which is where the
original `1 - Theta > 0` came from. Under (MISSING) the witness is only nonextremal,
`beta_0 >= Theta_chi - eta`, and then:

- (H-TRANSFER) (`Theta < Theta_chi`) gives only `Theta < 1` in effect and **does not** imply
  the margin for arbitrary `eta`: with `beta_0 = Theta_chi - eta` the margin is
  `1 - Theta - eta`, which is negative once `eta > 1 - Theta`. Adding (H-TRANSFER) to
  (MISSING), as the review suggested first, is therefore not sufficient on its own.
- A sufficient restriction is `eta <= 1 - Theta`, since then
  `1 + beta_0 >= 1 + Theta_chi - eta >= Theta + Theta_chi`. The reviewer's `Theta <= 1 - 2 eta`
  also suffices but is stronger than needed.
- Alternatively the exact margin can be carried as an explicit hypothesis.

Separately, `epsilon_1 = g/2` in step (a) is defined from (H-ISO)'s gap and is meaningless
under (MISSING); the `epsilon_1` supplied by (MISSING) is used instead, and the truncation
error is rebalanced with it.

**Change: yes.** Section 10 replaces "go through verbatim" with Adaptation 1 (`epsilon_1`
from (MISSING); surviving main term `(3 delta / 4) . 2 m_0 |c_0| x_n^{1 + beta_0} (1 + o(1))`)
and Adaptation 2 (exact margin, sufficient restriction `eta <= 1 - Theta`, and an explicit
sentence that (H-TRANSFER) does not supply the margin for arbitrary `eta`).

**Surviving claim.** Under (MISSING) plus either the stated margin or `eta <= 1 - Theta`,
`E(N_n) >> N_n^{1 + 2 Theta_chi - 2 eta}` along an infinite sequence. (MISSING) itself is
unproved, so this is a statement of what would suffice, not a result.

## R4. "Explicit sequence" overclaims

**Accepted.**

**Change: yes.** Theorem 4 is retitled from "conditional constructive oscillation" to
"conditional oscillation along a closed-form sequence", and now says the sequence is explicit only as a function of the
hypothetical witness zero `rho_0` supplied by (H-ISO), and that since no zero is exhibited no
sequence of real numbers is exhibited. Section 10 now states that (MISSING) is an existence
statement, that everything derived from it is existential, and that no constructive or
effective claim is made. The two remaining sentences in section 10 that spoke of a
"constructive statement" or "recovering constructiveness" were reworded to match.

**Surviving claim.** Theorem 4 removes the epsilon of Theorem B and gives a closed-form
sequence in terms of `gamma_0, phi_0`, conditionally on (H-ISO) and (H-TRANSFER). Nothing
constructive or effective is claimed, conditionally or otherwise.

## R5. Clarity bundle

Per instruction only items bearing on truth or hypotheses were acted on.

- **(a) Accepted, changed.** "Explicit two-parameter remainder" is now "shape-explicit in `x`
  and `T` up to one absolute constant", with a sentence that no value of `C_1` is claimed and
  nothing is effective.
- **(b) Accepted, changed.** Multiplicity `m(rho')` is now explicit in (F1), (F2) and the
  proof of Proposition 3, and (F1)'s multiplicity convention was confirmed in the primary
  source.
- **(c) Accepted, changed.** Theorem 4 now reads "for all sufficiently large `n`", with the
  threshold stated: `x_n >= 4` and `T(x_n) >= max(4, |gamma_0|)`, which hold for
  `n >= n_0(beta_0, gamma_0, g)`. A matching threshold paragraph was added to section 7.
- **(d) Accepted, changed.** The `+ N log N` in the step (e) transfer bound is now attributed
  to (E3) of RESULTS.md section 15, not to Theorem A.
- **(e) Accepted, changed.** Section 9 no longer calls C5 "the direct numerical statement of
  Defect 1"; it now says C5 illustrates the size estimate at 21 critical-line ordinates and
  that divergence is the analytic argument resting on (F2-low). The same paragraph now says
  C6 compares an error *bound* with the signal, so it shows the estimate cannot establish
  resonance and says nothing about the actual error.
- **(f) Declined, no change.** The source's `c_0 = (rho'-1)/(rho'(rho'+1))` and the repair's
  `c = (rho'-1)/(2 rho'(rho'+1))` differ by the factor 2 that a conjugate pair supplies:
  `2 |c| = |c_0|`, so both documents give the same pair sum
  `|c_0| x^{1+beta_0} cos(...)`. The reviewer confirms the repair is self-consistent. This is
  a normalization difference with no truth or hypothesis at stake, so under the brief it is
  left alone.

## Additional change not raised by the review

Check C8 was added to answer the review's remaining uncertainty about the 21 inherited
ordinates: it confirms `|L(1/2 + i gamma)| <= 1.57e-14` at every listed ordinate and compares
the count (21) with the Riemann and von Mangoldt prediction to height 60 (22.61). It records
that completeness is **not** proved. Nothing load-bearing depends on the list.

## Revised disposition

- Lemma 0, Lemma 1, the section 5 polar structure and Proposition 3: *derived*, with exact
  hypotheses (primitive odd `chi_3` mod 3; `x >= 4`, `T >= 4`; one absolute constant `C_1`
  from (F1)). Proposition 3 is a **useful intermediate lemma with exact hypotheses**.
- Theorem 4: *derived, conditional* on (H-ISO) and (H-TRANSFER).
- The unconditional variant in section 10: an **unresolved attempt with a missing analytic
  input**, (MISSING), plus the stated margin or `eta <= 1 - Theta`.
- Section 9 checks: *measured*, NOT PROOF.
- Nothing here is enclosure-carrying or kernel-checked, and nothing is numerically effective.

## Checks run for this revision

`formula_repair_checks.py` (main venv, about 3 s): C1 to C8 all pass; results in
`results_formula_repair_checks.json`. The reviewer's scripts were not run.
