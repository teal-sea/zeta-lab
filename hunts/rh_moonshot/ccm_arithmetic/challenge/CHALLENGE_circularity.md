# CHALLENGE (circularity): ccm_arithmetic

Hunt #150, mechanism 1. Circularity challenger, 2026-10-26, branch
`hunt/rh-moonshot-challenge-circularity`. This session did not build the construction and
edited none of its files. It read `NOTES.md` (commit `77e245890` on `hunt/rh-moonshot`,
merged here at `c220f1310`, and its m = 4 update `bc1b23cbd`, merged at `3fbe180af`), `ccm_common.py`, `measure.py` and `rigidity.py`, and scored
them against the rubric pre-registered in `MISSION.md` (section "Challenge-phase scoring
rubric", 2026-10-26).

Files here: `circ_ccm.py` (reads the builder's committed `data/measure_*.json`, recomputes
no matrix), `test_ccm_arithmetic_challenge_circularity.py` (3 tests), this page.

Grades as in `MISSION.md`. Nothing written here is kernel-checked.

## Verdict

**Unresolved, agreeing with the builder.** No hidden use of RH, GRH or the zeros was found
in the form. One grade is above its evidence, and it is the one that would matter most if
the chain were pushed:

- **C1 (positivity of zeta's form is band-level and float grade).** NOTES section 3
  ("lambda_1 > 0 (Rayleigh ball of the computed vector)"), the section 4 table ("lambda_1
  > 0 on all 30 cells, c <= 60" under "form at the windows measured") and section 8 ("a
  positive Rayleigh ball") present positivity as carried by a ball. It is not, for two
  reasons the NOTES half-state (lines 15-18):
  1. A Rayleigh quotient of any vector is >= lambda_1, so a positive ball bounds the
     lowest eigenvalue from **above** only. It carries a negative value of the form when
     negative (the rivals' failures are sound), and carries nothing when positive.
  2. The basis e_0, e_k (k <= N) of NOTES section 2 is nested in N, so the band-N matrix
     is a principal submatrix of every larger band, and by Cauchy interlacing
     lambda_1(N) is an **upper** bound on the infimum of the window form. Checked on the
     builder's data: lambda_1 is nonincreasing in N on every window of zeta (10),
     Dedekind (13) and DH (14), with no exception. For zeta it is still falling steeply
     at the largest band: from N = 32 to N = 128 it drops by 9.8 orders at c = 13 and by
     112.25 orders at c = 60 (`circ_ccm.py`). No limit in N is measured.

  So "lambda_1 > 0" is: the band-N lowest eigenvalue, located by a float eigensolver at
  400 to 1600 bits, is positive (measured). Positivity of zeta's Weil form on the window
  log c is not established for any c here, and for c >= 13 it would exceed the windows on
  which the `MISSION.md` frontier records positivity at all. Simplicity (lambda_2 /
  lambda_1 >= 1.6e6) is band-level and measured for the same reason. The rivals'
  negative values are unaffected: a negative value at a stated vector of the band is a
  negative value of the window form.
- **C2 (RH-equivalence risk, unresolved).** The builder's own reading (NOTES section 5,
  first bullet) is that capture tracks positivity to within an exponentially small gap
  scale, so a proof of link (2) for every c may have to deliver all-window positivity,
  which is Weil's criterion. That would make the target a reformulation (kill condition
  3). This session confirms the co-location in the data the NOTES report (DH loses
  capture between c = 31 and 33, its form sign change is at [30.617, 30.818]; Epstein at
  59/2; W_{1/4} between 2 and 3) and adds nothing that decides it.

## Scorecard

1. **Disposition.** Unresolved: no step refuted for zeta on the grid; links (1) and (2)
   are unproved for any infinite family of c (NOTES section 7).
2. **Grade per step.**
   - Link (1), simplicity and evenness: measured at band level (C1); no Temple bound
     (NOTES section 5).
   - Prop. 4.1 of Connes and van Suijlekom (real zeros of F_v for any real distribution
     under link (1)): cited, not re-read here.
   - Link (2), capture and F_v -> Xi on compacts: measured on c <= 60, N <= 128; the
     relative error on Im z = 0.45 is at best 7.3e-2 and its decay is not established
     (NOTES section 5). The perturbative capture bound is vacuous on every cell at
     m = 2, and at m = 4 on c = 43, 50, 60 (NOTES section 3 as updated in `bc1b23cbd`,
     read after merging it; its numbers were not recomputed here).
   - Link (3), Hurwitz: classical, but needs link (2) on a neighbourhood of
     |Im z| < 1/2, which is not measured to converge.
   - Rival failures: DH and Epstein negative values ball-carried for stated vectors
     (hardened for "the form takes a negative value"), W_{1/4}'s sign change hardened by
     Arb LDL^T. Agreed.
   - zeta's lambda_1 > 0: **should read measured, band-level** (C1), not ball-carried.
   - Composite: measured, as the NOTES say (section 8).
3. **The Euler-product step.** Named: link (2), capture surviving every window (NOTES
   section 4). Tested against DH, Epstein (1,1,6) and W_{1/4}, each of which loses capture
   at a located window; Dedekind (Euler product) keeps it to c = 60. Note on the control:
   reading Dedekind's success as "Euler product implies capture" treats GRH for
   L(s, chi_-23) as true at the heights these windows resolve; that is an expectation,
   not an input of the form, and this session did not check those zeros.
4. **Finite stand-ins.** Three finite ranges, all stated as measured by the builder and
   none offered as uniform: windows c <= 60, bands N <= 128, zeros below height 100. The
   band range is the one that bites (C1): band-N positivity stands in, in the section 4
   table's wording, for window positivity. The kappa law ("approach at rate O(t^2/c)") is
   a fit on finitely many cells and the NOTES call it measured.
5. **Novelty search.** None recorded by the builder (NOTES section 8: "No novelty search
   was made"). This session's query, 2026-10-26, web search: "Connes Consani Moscovici
   zeta spectral triples truncated Weil quadratic form lowest eigenvector prolate zeros
   converge Riemann zeros arXiv 2511.22755": arXiv 2511.22755 itself was not returned;
   found the precursors Connes-Consani arXiv 2106.01715 (small eigenvalues of the Weil
   form on a bounded interval, eigenvectors via prolate functions, low spectrum tracking
   the first 31 zeros), Connes-Consani-Moscovici arXiv 2310.18423 (semilocal prolate
   operator), and an EMS chapter "Zeta spectral triples" stating that a rigorous proof of
   the observed convergence would establish RH. No published refutation of step 2 was
   found. The phenomenon measured here (ground-state zeros matching zeta's) is CCM's own,
   as the NOTES say. zbMATH, MathSciNet and Lean Zulip were not searched.
6. **Rivals on complete hypotheses.** The chain has no complete proof, so no rival can
   refute an implication; the entries concern the distinguishing link.
   - DH: fails link (2) between c = 31 and 33 (measured). Lacks the Euler product. Not a
     counterexample.
   - Epstein (1,1,6): fails link (2) at c = 59/2 (measured). Not a counterexample.
   - W_{1/4}: fails link (2) between c = 2 and 3, form negative at c = 2.39 (hardened).
     Lacks unitarity of local roots. Not a counterexample.
   - zeta(s - delta): not run by the builder or by this session; excludes nothing. It
     would lack the s -> 1 - s functional equation about Re s = 1/2 on which the
     even-sector construction and the reality of Xi rest (derived from the definitions
     in NOTES section 2, not computed).
7. **Circularity.** None in the form. Requirement A provenance, by hand: `matrix()`
   (`ccm_common.py` lines 213-229) assembles archimedean, pole and prime blocks through
   `weil_trunc`'s `BallTruncation` and `weil_propagation`'s `wp_common`; `wa_matrix`
   (lines 171-204) reads Lambda(n)(n^a + n^-a) on prime powers <= c and digamma values;
   none calls `xi_kind`, a zero table or a xi-phase. Xi and the zeros enter only the
   diagnostics: `radical_vector` and `xi_kind` (lines 243-288, 380-401), the zero list
   `data/zeta_zeros_T200.json` and `mp.zetazero` in `measure.py` lines 181-193 and
   `rigidity.py` line 118. The target statement itself names Xi (convergence to Xi),
   which is legitimate: a proof must show closeness to Xi without reading its zeros, and
   nothing in the construction yet does that.

## Run manifest

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-26-challenge-circularity
hunt: rh_moonshot
started: 2026-10-26T13:35+00:00
finished: 2026-10-26T14:30+00:00
ran:
  - .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/challenge/circ_ccm.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot
outcome: no hidden RH or zero import in the form; zeta's lambda_1 > 0 is band-level and float grade, since a positive Rayleigh ball and a band-N eigenvalue both bound the window infimum from above and lambda_1 falls by up to 112 orders from N = 32 to 128; unresolved
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/challenge/circ_ccm.py
  - hunts/rh_moonshot/ccm_arithmetic/challenge/test_ccm_arithmetic_challenge_circularity.py
  - hunts/rh_moonshot/ccm_arithmetic/challenge/CHALLENGE_circularity.md
```

Compute: under a second; no estimate block needed. The builder's tests pass in this
checkout: `.venv/bin/python -m pytest -q -n0 hunts/rh_moonshot` gave 142 passed in 97 s,
the whole hunt with the four challenge directories in one process. The full grid at
c = 60, N = 128 was not rebuilt here.

## Amendment 2026-10-26 (follow-up): field 5, prior art and published refutations

Added after the scorecard above was accepted; the original text is kept unchanged. All
queries were web searches on 2026-10-26; hits are as the result pages and arXiv abstract
pages returned them, and no paper was read beyond its abstract or excerpts.

| # | query (abridged) | hits that bear on the mechanism |
| --- | --- | --- |
| 1 | Connes Consani Moscovici "zeta spectral triples" arXiv 2511.22755, truncated Weil form, ground state | A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv 2511.22755 (27 Nov 2025): rank-one perturbations of a spectral triple built from Euler products over p <= x, numerical agreement with the low zeros, and "A rigorous proof of this convergence would establish the Riemann Hypothesis" (abstract); no mention of DH or of functions without an Euler product on the abstract page. A. Groskin, *High-Precision Approximation of Riemann Zeros via the Truncated Weil Form*, arXiv 2605.20224 (2026, v4): an implementation of the Connes-van Suijlekom Galerkin matrix at sixteen cutoffs, no proof claimed, convergence called open; no rivals tested on the abstract page. A Zenodo record (https://zenodo.org/records/23441946) claiming evenness from simplicity, unreviewed and not assessed here |
| 2 | Connes van Suijlekom arXiv 2511.23257, lowest eigenvalue simple, even eigenfunction, real zeros | A. Connes and W. D. van Suijlekom, *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*, arXiv 2511.23257, Commun. Math. Phys. 406 (2025) 312: the cited Prop. 4.1 (real zeros of the ground state's transform for any real distribution, under simplicity, isolation and evenness), proved through a Caratheodory-Fejer corollary and Hurwitz; the authors flag verifying that the minimal eigenvalue is simple as the key difficulty |
| 3 | Davenport-Heilbronn, Weil quadratic form, small eigenvalue, prolate approximation, off-line zeros | A. Connes, C. Consani, H. Moscovici, *Zeta zeros and prolate wave operators*, arXiv 2310.18423 (2024); A. Connes and C. Consani, *Spectral triples and zeta-cycles*, arXiv 2106.01715; *A finite Guinand-Weil dictionary and archimedean tail order for the truncated Weil quadratic form*, arXiv 2607.02828; X. Zhu, *Weil positivity in compact windows: a finite reduction, [one word elided under the lexical rule] two-sided bounds, and a Landau-Widom decay law*, arXiv 2608.24827 (2026): lower bounds at window L = 0.8, variational upper bounds beyond, and the empirical law -ln lambda_min(L) ~ 2 pi^2 N(T*)/ln N(T*) with T* = 2 pi e^(2L); under RH lambda_min(L) <= exp(-L e^L) for large L. No published test of the CCM steps on DH or another function without an Euler product was found |
| 4 | (from the positivity_geometry searches) Connes-Consani, *Weil positivity and trace formula, the archimedean place*, arXiv 2006.13771 | positivity of the Weil form at the archimedean place via Hermitian Toeplitz matrices and prolate functions |
| 5 | Lean Zulip, CCM, truncated Weil form | no thread returned by the searches above; the Zulip archive was not browsed |

**What changes.**

- **C1 is consistent with the published picture.** Zhu (hit 3) finds that the window
  infimum lambda_min(L) is positive but plunges doubly exponentially in the window, and
  establishes a lower bound only at L = 0.8. The ground-state eigenvalues reported here
  (1e-192 at c = 60, N = 128) are of that kind. They are band-level upper bounds on a
  quantity whose positivity is open at these windows. C1 stands, now with a citation.
- **The cited Prop. 4.1 is published** (hit 2, Commun. Math. Phys.); its proof's own
  flagged difficulty is link (1), simplicity, which this mechanism measures only at band
  level.
- **CCM's own statement** that convergence would establish RH (hit 1) is the mechanism's
  target; no published proof or refutation of step 2 was found, and no published rival
  test of it. The rival table of NOTES section 4 is, as far as these searches reach, not
  in the literature (novelty not established; this is a search result, not a claim).
- **Disposition: unchanged** (unresolved).

**Correction to the run manifest above.** Its `finished` time, 14:30, was written before
the work finished and is later than the clock at the time; it is not a measured time, and its `started` time is an estimate as well. The follow-up's
`finished` time below is read from the clock and its `started` time is approximate (to
about 10 minutes).

```runmanifest
id: rh_moonshot-ccm_arithmetic-2026-10-26-challenge-circularity-field5
hunt: rh_moonshot
started: 2026-10-26T13:30+00:00
finished: 2026-10-26T13:38+00:00
ran:
  - web searches 1-5 of the table above and the arXiv abstract pages of 2511.22755, 2608.24827 and 2605.20224
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/ccm_arithmetic/challenge
outcome: no published proof, refutation or rival test of CCM step 2 found; Zhu's Landau-Widom law is consistent with C1; disposition unchanged
artifacts:
  - hunts/rh_moonshot/ccm_arithmetic/challenge/CHALLENGE_circularity.md
```
