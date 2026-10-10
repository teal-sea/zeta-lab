# REVIEW: referee/, the ΔT error bound (internal review, not external)

**Verdict.** The two derivations that carry the follow-up's outcome survive
review: bound_trunc/'s Lemma 1 (both truncation tails are infinite traces)
and Lemma 3 with its Corollary 3.1 (the mode-free floor). bound_quad/'s
Proposition 3 is correct, and its status (unresolved; a restricted-class
obstruction for the Gram-pencil route) is the right one. assembler/'s
composition, decision rule and floor count are sound; its outcome 4 on every
cell follows from the two null bounds. No derivation failed. Two interface
defects and one limitation of wording are recorded below, none of which
changes an outcome. This is **internal review by another worker of the same
laboratory, not external review**: every statement it passes becomes
"ordinary argument, reviewed internally, unreviewed externally", and
nothing more.

Every number below is pinned by `test_referee_bounds.py` in this folder
(the phase 2 section, written after routing, is labelled as such in the
file).

## 0. Order of work and two disclosures

- Phase 1 (falsification tests and plants) was committed at 4875122 before
  anything in bound_trunc/, bound_quad/ or assembler/ was read (BRIEF.md,
  Independence). The coordinator then routed the three folders.
- While checking the branch, `git log --oneline` showed the subject lines of
  bound_trunc/'s and bound_quad/'s milestone 1 commits (4a0818f, ab0f8fa).
  No file of theirs was opened; the test design and the plant list were
  fixed before those lines appeared, and nothing changed after them was
  prompted by them (later edits follow this folder's own plant numbers only).
- The first full run of `test_referee_bounds.py`, just before the phase 1
  commit, found `bound_quad/eps_quad.py` and both JSON files already on disk
  (uncommitted work in progress) and so executed them. What reached this
  folder was pytest's summary only: a `ValueError` raised in `eps_quad.py`,
  the trunc JSON without an entry at the 280-mode build's S_exact (fixed in
  the committed JSON, which now passes), and every entry of both files null.
  No source line was read. Phase 1 was verified before the commit on the
  subset that needs no bound, plus `tests/test_hunt_probe_discipline.py` and
  `tests/test_docs_numbering.py`.

## 1. Per derivation

### bound_trunc/ DERIVATION s2

| statement | verdict | reason |
|---|---|---|
| Identity A (item 1: ran Π^(n) = Θ(ran S^(n))) | **pass** | (Θ*^{−1}V)^⊥ = Θ(V^⊥), and Θ*^{−1} maps ran P onto itself; items 2 to 4 follow |
| **Lemma 1** (τ_f(R_n) = τ_f(Π'_n) = +∞) | **pass** | τ_f(1 − P) is the Hilbert-Schmidt norm of convolution by f cut to a half-line, ∫_0^∞‖f‖² = ∞; 1 − P splits into mutually orthogonal projections in both ways; positive traces add. Uses A1, CC Thm 4.7, and T_S finite, which Lemma 3 supplies without circularity |
| Claim (i), convergence of ΔT^(n) proven nowhere in the record | **pass** (a statement about the record) | my own search of two_adic/ RESULTS, kernel/ INTERFACE and the two modules finds "converged" only for measured responses; kernel/'s convergence statement is about the z-sum on u ≤ X |
| Claim (ii), the Sonin-overlap route does not close | **pass** as stated | it is a blocked route, not a proof that no bound exists, and the text says so |
| **Lemma 3** (κT_∞ ≤ T_S ≤ KT_∞, κ = (√2 − 1)⁴) | **pass** | the Riesz Gram of Θ on ran S_∞ lies in [(1 − a)², (1 + a)²]; ‖ΘX‖_HS lies within [1 − a, 1 + a] times ‖X‖_HS since Θ commutes with ϑ(f); Tr(G^{−1}M) ≥ Tr(M)/‖G‖. Pointwise in f, hence as Galerkin forms; direction right |
| **Corollary 3.1** (the floor) | **pass** | needs T_∞ ≥ 0 and a t covering Q's and T_∞'s errors and any float64 rounding of A, as stated; nothing beyond A1 to A4 |
| Corollary 3.2, Lemma 2, 2', Proposition 4 | pass on reading | not load-bearing for any outcome; Proposition 4 is a size, not a bound, and says so |
| Lemma 1's measured companion (s2.9) | **pass, now on two routes** | see s3 |

**What Lemma 1 does and does not do.** It does not show that ΔT^(n) fails
to converge to ΔT_exact. It shows that no positivity or strong-convergence
argument can show that it does, so the identification lim ΔT^(n) = ΔT_exact
is an assumption wherever a statement about the exact R_S rests on a stored
ΔT. It makes no statement about the stored matrices false: checker/ s7.9's
exact inertia of the stored R stands. What it removes is any reading of the
nvec response as an error estimate. Claims about R_S already graded
"measured, weakest step ΔT" should name that identification as an unproven
assumption.

### bound_quad/ DERIVATION s2

| statement | verdict | reason |
|---|---|---|
| Prop 1 (decomposition E1 to E7) | pass | triangle inequality; A9 for the real part (A9 now proven, s2 finding 7) |
| Prop 2 (E1 ≤ κ(S)·nvec) | pass | (1/2π)∫ρ_Q = Tr Q = nvec, Cauchy-Schwarz on Σ\|V̂_n\|², valid only for S > 2πN/L (see finding 5) |
| **Prop 3** (‖X‖ ≥ (1 − d)/λ_min(G_S) − 1) | **pass** | G_S^{−1/2}G_ex G_S^{−1/2} ≥ λ_min(G_ex) G_S^{−1}; provenance of the per-build numbers as stated (measured λ_min at two builds, cond(F) enclosures elsewhere) |
| status of E2: unresolved, restricted-class obstruction of the pencil route, route (ii) closes | **pass** | the right ALIGNMENT s5 status: Prop 3 is about one route. Note: the pencil ignores that the bad direction's leverage sits near \|s\| ≈ S, where the window weight is at most κ(S); a frequency-weighted argument may close E2 more cheaply than route (ii) (a thread, not a claim) |
| Prop 5 (E6), Prop 6 (E7) | pass on reading, consistent with the plants | the SVD route and the fsum assembly move ΔT by less than the noise floor (below 2e−14) at (80, 1200), against E6 and E7 of 2.8e−4 and 3.3e−8 there (bound_quad/'s values) |
| A9 (ΔT_exact real symmetric) | **closed by a proof here** | finding 7 |

### assembler/ PREREG 81f0b47, Addendum A e174d19, floor count 90b73e0

| statement | verdict | reason |
|---|---|---|
| composition (a) | pass | every term an exact rational or a stated hardened size |
| A1 (no gap between the two bounds) | **pass** | bound_trunc/'s ΔT^(n) = τ_f(Q_∞^(n) − Q_S^(n)) and bound_quad/'s ΔT_nvec,exact are the same object |
| A2 (the discarded imaginary part) | **closed** | finding 7 |
| count (b): Weyl, interlacing, V_4 nesting | pass | L ≤ n_−(R_ex) ≤ U; nested compressions give the monotone max and min |
| rule (c), outcome 2's chain | pass | U_32 ≤ L_16 ≤ n(16) ≤ n(32) ≤ U_32 |
| outcome 1's test L*_32 > L*_16 | **pass for what it claims, limitation of wording** | finding 8 |
| floor F_N = n_−(Q − κ_lo T_∞ + ηI) | pass | valid lower bound given Lemma 3, T_∞ ≥ 0 and η covering the stated input sizes |
| the floor counts (0, 1, 2 at c = 2.2, 2.5, 2.9; the same at N = 8, 16, 32) | **pass, reproduced** | float64 eigenvalues of Q − κT_∞ with T_∞ by kernel/'s moments route (not the assembler's `sonin.T_inf_matrix`) give the same counts on all nine cells, the two at c = 2.9 near −1.0e−4 and −1.7e−5 (`test_the_floor_count_by_a_float64_route`; measured, a second route beside the assembler's exact one) |
| outcome 4 on every cell | **pass** | both folders' eps_upper are null on all 33 builds; the rule's first branch |

## 2. Findings, in the order they were sent to the coordinator

1. **Lemma 1 holds** (s1). Its consequence is the scope statement above, not
   a refutation of any stored-matrix statement.
2. **Lemma 3 and Corollary 3.1 hold**, direction right (s1).
3. **Lemma 1's companion is hardened.** `run_companion_check.py` recomputes
   c_j (f = U_0, c = 2.9, |s| ≤ 60, j < 160) from two_adic/'s float64
   w-quadrature instead of kernel/'s Tate closed form. The two agree to
   1.1e−10 absolute; the slope of P(n) per unit of log n is 0.98996 on
   [40, 80] and 0.99098 on [80, 160].
4. **bound_quad/ Prop 3 and its status are right** (s1).
5. **`eps_quad` raises `ValueError` where S ≤ 2πN/L** (Prop 2's range),
   e.g. at this folder's (80, 150) and (80, 200) plants at N = 32. That is
   fail-closed: no finite number escapes, and a test pins it. It is also off
   the interface: the brief fixed the return type as `flint.arb`, and the
   JSON's "no bound" is null, whose function analogue is a non-finite ball
   (which `eps_quad` already returns through `arb.pos_inf()` when a part is
   missing). Raising conflates "this route gives no bound" with "invalid
   input" and breaks any caller that maps ε over configurations. Suggested
   fix: `e1` returns `arb.pos_inf()` there. This folder's tests read a raise
   as "no bound" and record it (`Eps.raised`).
6. **assembler/ PREREG and Addendum A pass** (s1).
7. **A2 = A9 closed.** `ta_mellin.window_hat` computes
   V̂_n(s) = e^{isL/2}(e^{ikL} − 1)/(ik√L) with k = 2πn/L − s, and
   e^{ikL} = e^{−isL}, so V̂_n(s) = −2 sin(sL/2)/(k√L), a real function (the
   same as bound_trunc/ Proposition 4's formula). ρ is real and nonnegative,
   so M = (1/2π)∫ρ V̂V̂^T is real symmetric, and so is ΔT_exact in the Mellin
   form. The stored imaginary part is rounding (`test_window_hat_is_real`).
8. **The outcome-1 test shows that the lower bound rises, not that the
   count grows.** L*_32 > L*_16 can fire on 0, 0, 1. Growth of n_− itself
   needs L*_32 > U*_16. The brief's outcome-1 wording claims only lower
   bounds, so the rule is valid for what it claims; a future line 2 should
   say "the lower bound rises" unless L*_32 > U*_16. Moot here: outcome 4.

Also measured (`test_lemma3_sandwich_holds_on_every_stored_T_S`): every
stored T_S, all 33 matrices, lies strictly inside Lemma 3's sandwich. The
smallest eigenvalue of T_S − κT_∞ is at least 1.09e−3, and that of
KT_∞ − T_S at least 2.78e−3 (tightest at c = 2.9, 364 modes). A consistency
check of the lemma with the data, measured grade, not a proof.

## 3. The interface finding (phase 1, sent with 4875122)

The interface takes (c, N, nvec, S, Kmax) only. The w Gauss nodes per panel,
the s panel width and nodes, the term counts of the 1/w tail series and the
derivative orders of φ̃_n at 1 are fixed inside two_adic/ and are not
arguments. So a coarsening of any of them cannot be tested against the
bound, only a refinement (assumption R). The s7b runs were built at s panel
width 2, not the stored builds' width 1, so their dominance test needs
assumption W2. At (80, 1200), c = 2.2, N = 8 the two widths differ by
4.8e−13 in spectral norm, so W2 is harmless there.

## 4. Per test (`test_referee_bounds.py`)

The inequality every bound test uses: a valid bound implies
‖ΔT_a − ΔT_b‖₂ ≤ ε_a + ε_b (I), and nothing stronger. The named assumptions
are M (the refined reference makes ε_a alone dominate), R (a refinement
outside the interface stays inside the bound), D (eps_quad alone covers a
change that keeps the modes) and W2 (s7b's width).

| test | result | reason |
|---|---|---|
| replica reproduces the stored (80, 1200), N = 8 row | pass | agreement below 1e−13 on every c |
| plants JSON complete; exact enclosures lower ≤ spec ≤ Frobenius upper | pass | 30 units, 30 pairs |
| a plant reproduces from its JSON row | pass | S 800 against 1200, N = 8 |
| the noise floor | pass | eight refinements at (80, 1200) below 2e−14 |
| interface and defect plants move ΔT above ten times the floor | pass | smallest: Kmax 10 against 12 at (40, 1200), 3.31e−13 |
| defects against the truncation response | pass | a dropped mode exceeds the 60 → 80 response only at N = 8. At N = 16 and 32, 80 modes do not resolve the window: the response (9.92e−2 to 0.146) exceeds the dropped mode's (4.55e−2 to 7.82e−2). This was my phase 1 hypothesis for every N, and the numbers refuted it; the test states what holds |
| (I) on interface plants; (I) under M; under R; under R and D | **skip** | no finite bound: eps_trunc is +∞ everywhere, eps_quad is +∞ or raises |
| defects not covered | **skip** | no finite bound |
| stored responses (N = 16, 32, all pairs) under (I) | **skip** | no finite bound on any build |
| s7b responses under (I) and W2 | **skip** | no finite bound |
| s7b width 2 against stored width 1 | pass | 4.8e−13 |
| JSON entries cover every stored build (both folders) | **pass** | 33 entries each, keyed by S_exact, Kmax = kmax_for(nvec), nulls with reasons |
| eps_upper ≥ the ball's upper end (both) | **skip** | every entry is null |
| eps_quad fails closed below the window band | pass | finding 5 (no finite ball; the raise is recorded, not required) |
| the floor count by a float64 route | pass | s1, assembler/ |
| null entries match the functions (both) | **pass** | every null entry has a non-finite ball or a raise |
| closing pieces E6, E7 against the plants | pass | s1 |
| window_hat is real | pass | finding 7 |
| Lemma 1's companion by a second route | pass | finding 3 |
| Lemma 3's sandwich on every stored T_S | pass | s2 |
| REVIEW's plant numbers | pass | s5 |

The falsification tests of items 1 and 2 of the brief could not falsify
anything, because no finite bound exists. They skip with that reason and
do not pass. They will run unchanged against any future finite ε.

## 5. What the plants measured (a record for whoever builds a bound)

Spectral norms of ΔT differences on c ∈ {2.2, 2.5, 2.9}, N ∈ {8, 16, 32}
(`referee_plants.json`, float64, one route, with exact lower and upper
enclosures of each norm):

- **Gram step and sample data in the ill-conditioned regime.** A relative
  perturbation of 1e−13 on the ζ_n(w) samples (the measured sample-error
  size) moves ΔT by up to 5.19e−5 at cond(F_z) = 6.7e11 (80 modes, S = 200)
  and up to 2.41e−2 at cond(F_z) = 3.84e14 (S = 150). A 2^−53 perturbation
  of the Gram factor's rows moves it by 2.74e−6 and 7.36e−4. The stored
  280, 319 and 364-mode builds sit between those two conditions. So a bound
  on the Gram step there has to be at least of the order of the band, which
  agrees with bound_quad/'s s2.7.
- **Tail series.** Raising the 1/w tail from 25 to 40 terms (and the dilates
  from 8 to 16 terms, orders 4 to 8) moves ΔT by 4.59e−9 to 5.26e−9 at
  (80, 1200): above float64 noise, far below the band.
- **Kmax.** 8 against 12 at (40, 1200): 2.40e−8; 10 against 12: 3.31e−13.
- **S.** 1200 against 2400 at 80 modes: up to 2.84e−3; 150 against 2400:
  up to 0.239.
- **Defects.** The explicit inverse at cond(G_z) of about 4.5e23 (80, 200)
  moves ΔT by up to 0.365; a dropped mode by 4.55e−2 to 7.82e−2.

## 6. Grades after this review

Lemmas 1 and 3, Corollary 3.1, bound_quad/'s Propositions 1 to 3, and the
assembler's composition and rule move from "ordinary argument, unreviewed"
to **"ordinary argument, reviewed internally (referee/), unreviewed
externally"**. The floor n_−(R_S) ≥ 2 at c = 2.9 on the full space
(assembler/) is then conditional on a reviewed-internally Lemma 3 and on
kernel/'s T_∞ derivation, which this review did not cover and which stays
unreviewed. The count 4, 10, 20 keeps its grade: measured as a statement
about R_S, weakest step ΔT, now with the identification lim ΔT^(n) = ΔT_exact
named as an unproven assumption (Lemma 1).

## 7. Threads (observed, not pursued)

- A frequency-weighted perturbation bound for E2, using κ(S) at the
  bad direction's frequencies instead of the Gram pencil (s1, bound_quad/).
- Whether ΔT^(n) converges to ΔT_exact or to ΔT_exact plus a bias: the
  companion shows each tail growing like 0.99 log n and the stored ΔT's U_0
  entry moving by far less, which is consistent with cancellation and
  settles nothing.

## 8. Reproduction

    PYTHONPATH=<worktree root> <venv python> run_referee_plants.py --only <units>   # phase 1 plants (units in batches under 10 minutes)
    PYTHONPATH=<worktree root> <venv python> run_referee_plants.py --pairs          # pair norms into referee_plants.json
    PYTHONPATH=<worktree root> <venv python> run_companion_check.py                 # referee_companion.json (about 20 s)
    PYTHONPATH=<worktree root> <venv python> -m pytest -q -n0 test_referee_bounds.py
