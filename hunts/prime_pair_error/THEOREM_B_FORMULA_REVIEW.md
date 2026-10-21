# Independent review: repair of the sharp-cutoff character-weighted explicit formula

- Artifact: `hunts/prime_pair_error/THEOREM_B_FORMULA_REPAIR.md` (+ `formula_repair_checks.py`, `results_formula_repair_checks.json`)
- Reviewed SHA: `95ae36b9c09c0cf28844e40e50f7fceac2f95cfb`, branch `teal-sea/theorem-b-formula-repair` (worktree as named; `git status --short` clean at open, no checkout performed)
- Reviewer posture: independent; no constructor running; background docs (THEOREM_B_SEQUENCE.md, FAREY_BASELINE_REPAIR.md App. B, RESULTS.md ss.17/18, REFEREE.md s.4) used as context, not authority
- Review outputs owned here: this file plus `formula_review_checks.py` / `results_formula_review_checks.json`. Author files, old evidence, and all other paths untouched (verified via `git status --short`). No commit, no push/PR/merge, no CI/lake/heavy numerics.

## Verdict

**Not clean: four real findings (R1-R4), none fatal to the core repair.** Proposition 3 is proved as stated *except* for a statement/proof mismatch that drops possible real zeros (R1, one-line fix; the proof in s.6 actually proves the inclusive-sum version). Theorem 4's derivations (a)-(e) check out conditionally, modulo R1. The s.5 polar derivations are all correct, confirmed by an independent method. The s.10 (MISSING) sufficiency claim is not established as stated: it lacks the transfer margin (R3) and mislabels an existential sequence explicit (R4). The load-bearing divergence refutation (Defect 1) cites an upper-bound-only fact for a lower-bound conclusion (R2, standard fix). Required fixes are small and named below; no re-architecture is asked for.

## Objections (each: PENDING until author response)

### R1. Proposition 3 drops a possible real zero: `0 < |gamma'|` vs F1's `|gamma'| <= T` [proof gap; fix: one line]

- Exact claim: s.3 Prop. 3 (lines 142-164), `I(x) = sum_{0 < |gamma'| <= T} ...`.
- Support: inherited (F1) as restated at s.6 (lines 293-298) sums over `|gamma'| <= T`, which includes a real zero (`gamma' = 0`) if one exists. The s.6 proof itself carries `sum_{|gamma'| <= T}` through Steps 1-3 and only narrows to `0 <` in the statement. So the proof proves the inclusive version; the statement silently discards any real-zero term.
- Consequence: a real zero `beta' in (0,1)` contributes `m c x^{1+beta'}` of order up to `x^2`, which is not absorbed by `E` (`2C_1 x log x + C_2` cannot cover it at large `T`). The file never states `L(s,chi_3)` has no real zero. (F2) does not exclude one; s.6's `delta_0` argument covers small *nonzero* `|rho'|`, not `gamma' = 0`. My coarse scan finds `L > 0` on (0,1) at 399 points (min ~0.36), which is suggestive but not proof.
- Remedy (minimal): state the sum as `|gamma'| <= T`. Nothing else changes: real-zero terms are individually real (reality claim intact), `beta' <= beta_c` keeps them inside the s.7(b) competitor bound, and `C_2` gains only finite terms (`rho' = 0, -1` already excluded since `L(0) = 1/3 != 0` and `-1` is trivial). Alternatively add a proved no-real-zero lemma; the inclusive sum is cheaper.

### R2. Divergence of `sum |c(rho')|` cites an upper-bound-only fact [missing hypothesis; fix: one citation]

- Exact claim: s.2 Defect 1 (lines 89-92), "by ... (F2) ... the zeros in `[T,2T]` number asymptotically `T log T`", hence `sum |c| = infinity`; reused at s.7(b) and s.10 point 1 ("asymptotically `log^2 T`").
- Support: (F2) as stated at s.8 (lines 428-432) and RESULTS.md s.17 is an *upper* bound (`O(log)` per unit interval, hence `sum << log^2 T`). An upper bound is consistent with convergence and cannot yield divergence or any `asymptotic`/lower claim. The per-zero lower bound `|c(rho')| >= 1/(7|gamma'|)` for `|gamma'| >= 1` is correct (re-derived: `|rho'-1| >= |gamma'|`, `|rho'| <= sqrt(2)|gamma'|`, `|rho'+1| <= sqrt(5)|gamma'|`, `2 sqrt(10) < 7`), but divergence needs a *lower* dyadic count.
- Consequence: the load-bearing negative result (refutation of `(*)`) is not established by the cited fact. Negative claims are held to the same standard as positive ones.
- Remedy: add (F2-low), the two-sided Riemann-von Mangoldt count for `L(s,chi)` (e.g. Davenport ch.15/16 or M&V ch.10), or at minimum a lower bound `>> T log T` per dyadic block. Standard textbook fact; the conclusion (`sum |c| = infinity`) is true, only the citation is wrong. After the fix, weaken "asymptotically" to the one-sided claim actually used wherever only an upper bound is needed (competitor mass, `C_2`).

### R3. (MISSING) is not sufficient as stated: transfer margin absent, "verbatim" inaccurate [proof gap / missing hypothesis]

- Exact claim: s.10 (lines 487-488), "Given (MISSING), sections 7(a), 7(d) and 7(e) go through verbatim and yield `E(N_n) >> N_n^{1+2Theta_chi-2eta}`".
- Support: s.7(e) uses (H-TRANSFER) (`Theta < Theta_chi`) to get `Theta + Theta_chi < 1 + beta_0` with margin `1 - Theta > 0`, absorbing `O(N^{Theta+Theta_chi} log^4 N)`. (MISSING) states no hypothesis on `Theta`. If `Theta = 1` (a priori possible), the margin is `beta_0 - Theta_chi >= -eta`, and the transfer fails. RESULTS.md s.18 avoids exactly this via a case split (CHHL Theorem 2 when `Theta_chi <= Theta`); s.10 has no split. Separately, s.7(a) sets `eps_1 = g/2` from (H-ISO)'s gap `g`, which is undefined under (MISSING); (MISSING)'s own `eps_1` must be used instead, so "verbatim" is inaccurate.
- Consequence: the "exact remaining gap" is missing a hypothesis; as written it does not imply its conclusion.
- Remedy: add (H-TRANSFER) to (MISSING) (or the s.18-style case split, or `Theta <= 1 - 2eta`), and replace "go through verbatim" with the two-line adaptation (`eps_1` from (MISSING); transfer via the added margin).

### R4. "Explicit sequence" overstates what s.10 delivers (and needs qualification in Thm 4) [nonblocking clarity]

- Exact claims: s.3 line 183 ("the sequence is explicit") for Theorem 4; s.10 line 488 ("along an explicit sequence, unconditionally") for the (MISSING) consequence.
- Support: Theorem 4's `x_n = exp((2 pi n - phi_0)/gamma_0)` is an explicit formula *in terms of unlocated (H-ISO) data* (`gamma_0`, `phi_0`, `beta_0`); that is stronger than Theorem B's pure-existence sequence but not numerically explicit, and should say so. Worse, (MISSING) only posits "an unbounded sequence `x_n` with `cos(...) >= 1-delta/4`" satisfying an inequality "for infinitely many `n`": that is an existential subsequence of exactly the Theorem B kind. Calling it "explicit" re-imports the non-constructivity s.10 otherwise honestly diagnoses.
- Remedy: qualify Thm 4's "explicit" as "explicit modulo the hypothesized witness zero"; reword s.10's conclusion to "along an infinite sequence satisfying an explicit phase condition".

### R5. Clarity bundle (all nonblocking, no validity at stake)

- (a) "Explicit two-parameter remainder" (s.0/s.11): `C_1` (M&V's unevaluated implied constant) and `C_2` (unevaluated infinite sum) are never numerically determined, so Prop. 3 yields no drawable error bar; s.9 C6 silently drops `C_1`. The bound is shape-explicit only. Say so.
- (b) Multiplicity: (F1) as restated never says zeros are counted with multiplicity, but Prop. 3's `m(rho')` and the `<< log^2 T` mass bounds need it. Add "counted with multiplicity" to the (F1)/(F2) restatements.
- (c) Theorem 4 needs "for all sufficiently large `n`" (requires `T(x_n) >= max(4, |gamma_0|)` so Prop. 3 applies and the witness pair is inside the truncation).
- (d) Attribution: the `+ N log N` in the s.7(e) transfer bound comes from (E3)/(E5) + s.15, not from Theorem A (s.17) alone. Harmless (it only weakens the bound); cite both.
- (e) s.9 "C5 is the direct numerical statement of Defect 1" overstates: 21 ordinates illustrate `|c| ~ 1/(2 gamma)` (test points assume `beta' = 1/2`); divergence is analytic (see R2). The check script's own docstring already hedges ("an illustration of the ratio, nothing more"); align the MD text with it.
- (f) Cross-reference note: the source's s.4 `c_0 = (rho'-1)/(rho'(rho'+1))` differs by a factor 2 from the repair's `c`; the repair is self-consistent (conjugate pair sums to `2 m_0 |c_0| x^{1+beta_0} cos`, verified), but a reader cross-checking against SEQUENCE.md will trip. One-line normalization note suffices.

## Checked and cleared (no objection)

- **Lemma 0** (`I = psi_1 - (x/2) psi`, exact for all real `x`, endpoint convention respected): re-derived by hand; identity holds.
- **s.6 error algebra**: `E_1` integration via monotone majorant, `E_2 = -(x/2)E_0`, total `C_1 x^2 T^{-1} log^2(xT) + 2C_1 x log x + C_2`, and the `C_2` convergence (dyadic `4/gamma'^2` + finitely many low zeros with `|rho'| >= delta_0 > 0`): all verified by hand. The derivation is self-contained from (F1), so s.5 polar terms are automatically inside `E`; no double-counting.
- **s.5 residues** (the brief's required independent derivation): `s = 1` analytic (kernel zero, `L(1,chi) != 0`); `s = 0` simple pole with residue `mu_1 x`, `mu_1 = -(L'/L)(0)/2`; `s = -1` double pole with `A = 1`, residue `log x + 1/2 + h(-1)` (kernel expansion `(-1-u/2+O(u^2))/u` confirmed); closed forms `h(-1) = euler + log(2pi/3) - 1 - (L'/L)(2,chi_3)`, `nu = 1/2 + h(-1)` re-derived through the odd-character functional equation (`Lambda(s) = Lambda(1-s)`, root number 1); trivial-zero tail `-(k+1)x^{-2k}/(2k(2k+1))`, `O(x^{-2})`; nontrivial coefficient identity and `c = 0` only at `s = 1` (not a zero). The source's `mu_1 x + mu_0` constant-at-`s=-1` is indeed wrong (should be `log x + nu`); harmless to resonance, worth correcting wherever inherited. Independently confirmed numerically by a *different* method (Cauchy contour integrals, not the author's finite differences): `|A-1| ~ 1e-48`, `|B-nu| ~ 1e-41`, `mu_1` limits agree to `~1e-30`. All pass.
- **Theorem 4 (a)-(e) derivations**: truncation exponent `x^{1+beta_0-g/2}` with `T <= x` (uses `g <= beta_0`, holds since remaining-zero `Re > 0`); competitor `|c| <= 1/|gamma'|` for `|gamma'| >= 1` (verified) with finite low-height remainder; witness phase alignment exact at `x_n`; `c_0 != 0`; ratio `x_{n+1}/x_n = exp(2pi/gamma_0)`; integer transfer `I(x)-I(N) = (x-N)psi(N,chi)/2` exact with Chebyshev `O(N)` negligible; `E(N) >= 2T(N)^2/N` transfer with margin `1-Theta > 0` under (H-TRANSFER); "no epsilon loss" and the stated (conditional) strengthening over Theorem B are legitimate as written, modulo R4's qualification.
- **Defect 3 framing** (upper bound vs actual error): C6 compares the *error bound* against the witness scale; it establishes the `T = x^delta` *regime* is too weak, not that actual error cancels signal. The file's wording ("refuted as stated", i.e. the claim *with its justification via `(*)`*) stays within what a bound comparison proves. No overclaim found.
- **Attribution spot-checks**: (R7) Mellin transform matches REFEREE.md s.4 line 282 and RESULTS.md s.18 line 818 verbatim; (F1) quote matches RESULTS.md s.17 lines 693-700 verbatim, including the arbitrary-`T` gloss and the `Lambda(x)chi(x)/2` midpoint correction (direction consistent with the repo's own `docs/04` midpoint account); Theorem B comparison statements match s.18.
- **Author checks**: read as-is (not re-run, to avoid rewriting author files); values agree with my independent numbers (`nu = 0.643831644563`, `mu_1 = -0.474099413336`, `A = 1`); every check is labeled NOT PROOF in file, script header, and results JSON.

## What survives

Lemma 0; all of s.5 (polar structure + the `mu_0 -> log x + nu` correction); Prop. 3's proof (which establishes the inclusive-sum version; statement needs R1); the per-zero `|c| ~ 1/(2|gamma'|)` estimate and Defect 3's regime arithmetic; Theorem 4 conditionally (needs R1, R4-qualification); the s.10 diagnosis of *why* the unconditional case is hard (growing competitor mass, Kronecker non-uniformity, Landau non-constructivity), though its (MISSING) needs R3/R4. The s.11 disposition ("useful intermediate lemma, not a complete sequence repair") remains accurate and is, if anything, reinforced: R1-R3 are small, but they sit on the load-bearing joints.

## Reviewer checks actually run

`formula_review_checks.py` (dps=30, ~20 s, main-venv, no network): Cauchy `A=1`/`B=nu`, `mu_1` shrinking-`h` limits, 399-point real-line scan (no sign change, min ~0.36), coefficient identity at the 21 read-only located ordinates. All pass; results in `results_formula_review_checks.json`. The author's `formula_repair_checks.py` was deliberately not executed. Scratch work in `/tmp/reviewer_scratch.py` (dps=40 pilot) is not part of the deliverable.

## Remaining uncertainties (not objections)

- The M&V primary text is not in this repo and a fetch of an online copy timed out, so uniformity-in-`T`, the midpoint correction, and multiplicity rest on RESULTS.md s.17's gloss plus the repo's own `docs/04` account, not on direct inspection. A one-look confirmation against the book would close R5(b) and the "no admissible-height" premise; I did not pursue further per the no-broad-literature instruction.
- Whether `L(s,chi_3)` has a real zero is left open by the artifact; R1's remedy (inclusive sum) is deliberately chosen to not need the answer.
- The 21 located ordinates in `results_landau_zero_probe.json` were used read-only for illustrations; their provenance was not audited (not needed: nothing load-bearing depends on them).

---

# Follow-up review of the revision (appended, original above preserved verbatim)

- Reviewed SHA: `3006ef28e5b7d5a6161220256d0456339561e3dd` (prior review covered `95ae36b9c09c0cf28844e40e50f7fceac2f95cfb`). Read: this file, `AUTHOR_RESPONSE.md`, and the `95ae36b..3006ef2` diff of `THEOREM_B_FORMULA_REPAIR.md` plus the `formula_repair_checks.py` diff. Author files untouched; reviewer owns only this file, `formula_review_checks.py`, `results_formula_review_checks.json`.
- Primary check: fetched the single author-hosted chapter PDF named in the brief (MNT I ch.12, pp. 397-418), extracted text, read Theorem 12.10, Lemma 12.7, and the surrounding proof. Narrow ch.14 lookup attempted for R2: the directory URL returns unrelated boilerplate, so no ch.14 text was retrieved and none was guessed at; the R2 sub-verdict below is an explicit unresolved-source verdict on that sliver, not an inherited gloss.
- Residue/numerical checks from the original review were not reopened (nothing in the revision touches them; coefficient and remainder shape are byte-identical in effect). One new reviewer check was added for the new analysis (Lemma 1 grouped series); all pass.

## Per-finding status

| finding | status | artifact changed |
|---|---|---|
| R1 inclusive zero sum | resolved | yes (inclusive `\|gamma'\| <= T` with `m(rho')` throughout Prop. 3, s.6, `C_2`; plus new Lemma 1 as backup) |
| R2 two-sided count for divergence | resolved, with one openly-stated source sliver (below) | yes ((F2-low) via Thm 14.5/Cor. 14.6; (F2-up) where only upper bounds are used; "asymptotically" kept only for the two-sided s.10 claim) |
| R3 transfer margin in (MISSING) | resolved as analysis (exact margin stated; "verbatim" withdrawn; H-TRANSFER correctly shown insufficient for arbitrary `eta`) | yes |
| R4 "explicit sequence" | resolved for Theorem 4; NOT resolved for the s.10 sequence (see new F3) | yes (retitle, witness-modulo qualification, thresholds, "sufficiently large n") |
| R5(a)-(e) clarity bundle | resolved | yes |
| R5(f) normalization note | declined by author, acceptable (no truth at stake; repair self-consistent as verified in original review) | no |

## Verified in this round

- **Lemma 1 (new).** Proof re-derived by hand and correct: Dirichlet test gives convergence for real `s > 0` (bounded `chi_3` partial sums, `n^{-s}` monotone to 0), locally uniform on `Re s > 0`, hence the entire `L(s,chi_3)`; the `S_{3k}` subsequence yields the grouped brackets, each positive, first bracket `1 - 2^{-s} > 0`. So no real zero exists and the inclusive/exclusive index sets coincide for `chi_3`. Corroborated by the new reviewer check `F_grouped_series_lemma1` (pass) alongside the original 399-point scan. Proposition 3 does not depend on it, as the artifact states.
- **R3 margin.** The exact condition `1 + beta_0 > Theta + Theta_chi` is the correct strict threshold of step (e) (Theorem A error vs `N^{1+beta_0}` signal), and `eta <= 1 - Theta` is sufficient given `beta_0 > Theta_chi - eta`. The author's remark that the reviewer's `Theta <= 1 - 2eta` also suffices but is stronger is accurate. On coordinator point (4): MISSING's strict `>` propagates to a strict margin (`1 + beta_0 > 1 + Theta_chi - eta >= Theta + Theta_chi`); the response's `>=` sits on the lower-bound link only. Rationale aligns; no edit needed. Remark: without (H-TRANSFER), `Theta = 1` is a priori possible and then `eta <= 1 - Theta` admits no `eta > 0`, so of the two offered branches the explicit-margin hypothesis is the operative one; the artifact's non-vacuity sentence leans on `Theta < 1` from (H-TRANSFER).
- **Primary (F1) reduction.** Confirmed against the actual Theorem 12.10 text: hypotheses `x >= c > 1`, `T >= 2`, primitive `chi` mod `q > 1`; no `T <= x`, no admissible-height condition (Lemma 12.7 supplies an internal `T_1 in [T,T+1]`, so uniformity in `T` is as claimed); midpoint `psi_0`; inclusive `|gamma| <= T` sum arising as residues (hence multiplicity-counting by construction); odd-`chi` trivial zeros at odd negative integers (confirms s.5 independently); error `(log x) min(1, x/(T<x>)) + (x/T)(log qxT)^2`. The artifact's crude reduction holds: `min <= 1` even at prime powers, `log(3xT) <= 2log(xT)` for `x,T >= 2`, odd-character log collapse `<= (1/2)log 3`, half-jump `<= (log x)/2` inside the shape. R5(b) closed.
- **R2 chain from stated premises.** `N(2T,chi) - N(T,chi) >> T log T` follows from the quoted Corollary 14.6 main term by elementary differencing, and with the verified per-zero `|c| >= 1/(7|gamma'|)` the dyadic `>> log^2 T` divergence is correct. Unresolved-source sliver: Corollary 14.6 and the `S(T,chi) << log(q(T+2))` bound were not directly inspected by this reviewer (ch.14 not retrievable, directory page dead); the artifact openly states exactly this gap. Standard classical estimate; recorded, not waved.
- **Theorem 4.** Threshold paragraph and "sufficiently large `n`" (`T(x_n) >= max(4,|gamma_0|)`) present; transfer margin under (H-ISO)+(H-TRANSFER) exact (`beta_0 = Theta_chi`, margin `1 - Theta > 0` via `Theta < Theta_chi <= 1`); s.7(a) factor 4 intact (`g < beta_0` gives `T <= x`). R5(c)(d) fixes confirmed.

## New findings (all in s.10, none touching core Prop. 3 or Theorem 4)

### F1. Adaptation 1 displays a false inequality for unrestricted `epsilon_1` [wrong constant; conclusion survives]

- Exact claim: s.10 Adaptation 1, `C_1 x_n^2 T_n^{-1} log^2(x_n T_n) <= 4 C_1 x_n^{1+beta_0-epsilon_1} log^2 x_n` "for any `epsilon_1 > 0`".
- With `T_n = x_n^{1-beta_0+epsilon_1}`, `log(x_n T_n) = (2 - beta_0 + epsilon_1) log x_n`, so the true factor is `(2 - beta_0 + epsilon_1)^2`, which exceeds 4 whenever `epsilon_1 > beta_0` (e.g. `beta_0 = 0.6`, `epsilon_1 = 1` gives 5.76). The s.7 original earned its 4 from `T <= x` via the (H-ISO) gap; (MISSING) supplies no gap, so the constant cannot be inherited. The `o(x_n^{1+beta_0})` conclusion still holds for any fixed `epsilon_1 > 0`, but the displayed inequality is false as stated and is not harmless without correction.
- Minimal correction: write the exact `C_1 (2 - beta_0 + epsilon_1)^2 x_n^{1+beta_0-epsilon_1} log^2 x_n`, or add the hypothesis `0 < epsilon_1 <= beta_0` and keep the 4.

### F2. (MISSING) quantifiers do not force the good subsequence to escape to infinity [proof gap]

- Exact claim: (MISSING) posits "an unbounded sequence `x_n` with `cos(...) >= 1 - delta/4`" satisfying the competitor bound "for infinitely many `n`", and s.10 concludes `E(N_n) >> ...` "along the sequence it names".
- An unbounded sequence with a property holding for infinitely many indices need not have an unbounded subsequence of good indices (unboundedness may come entirely from bad indices). The transfer conclusion needs `x_n -> infinity` along the good indices (`o(1)` terms, large `T_n`, integer transfer). As stated the implication is not established.
- Minimal correction: require the competitor bound "for infinitely many `n` with `x_n -> infinity`" (equivalently, a subsequence `x_{n_k} -> infinity` satisfying both the phase and competitor bounds), and state the conclusion along the corresponding `N_{n_k}`.

### F3. s.10 closing paragraph still credits (MISSING)'s sequence with closed-form explicitness [mislabel; R4 remainder]

- Exact claim: s.10 "(MISSING) is an existence statement" paragraph, "the sequence `x_n` is explicit as a formula in `gamma_0` and `phi_0`".
- (MISSING) supplies a phase inequality and an arbitrary existential sequence, not the closed form `exp((2pi n - phi_0)/gamma_0)`; that formula is Theorem 4's (H-ISO) construction. The paragraph as written re-imports exactly the non-constructivity R4 removed everywhere else.
- Minimal correction: "the phase condition is explicit in `gamma_0, phi_0`, but the sequence satisfying it is purely existential; no closed form is available under (MISSING)."

## Verdicts, separately

- **Core formula (Lemma 0, Lemma 1, s.5 polar structure, Proposition 3): verified as a useful intermediate lemma with exact hypotheses.** The one load-bearing external input (F1) now rests on the inspected primary statement, not a gloss. No further edits required here.
- **Conditional Theorem 4: verified, conditional on (H-ISO)+(H-TRANSFER).** R1/R4/R5-corrections all landed; derivations were already cleared. No further edits required here.
- **Section 10 unconditional extension: not established; remains an unresolved attempt with honest diagnosis.** Requires exactly the three minimal corrections above (F1 constant, F2 quantifiers, F3 explicitness wording). With them it becomes a correct statement of what would suffice (conditional on unproved (MISSING) plus the stated margin), still existential, still non-effective. Nothing here upgrades without (MISSING) itself.

## Reviewer checks run this round

`formula_review_checks.py` (main venv, dps=30): all five pass, including new `F_grouped_series_lemma1` (grouped partials vs Hurwitz within tail scale, bracket positivity, `L >= 1 - 2^{-s}` at `s = 0.5, 0.9, 1.5`). Results in `results_formula_review_checks.json`. Author checks read as-is, not re-run. Scratch PDF/text in `/tmp` (`MNTI_ch12.pdf/.txt`, `mnti_dir.html`) are not part of the deliverable. Lexical guard re-checked by scan: no reserved word in the three owned files.
