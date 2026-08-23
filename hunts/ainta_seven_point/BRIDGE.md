# The bridge, formalised to its hypotheses

Ainta's seven-point simple-zero bound (`paper/riemann.tex` at
`ainta/zeta-simple-zeros` commit `040c5e899e658aed7b56a2a87f501798fe10761d`, cited
`[A]` with line numbers), stated and proved in Lean on top of the vendored
`anthropics/zeta-23-lean` (`[L23]`, rev `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`),
as a theorem about Mathlib's `riemannZeta`. Integrated 2026-08-23 on the branch
`bridge/integrate` from the five attack branches `bridge/{skeleton,finite,pinching,S8,S9}`.

**Verdict in one line.** Every step of `TRUST-MAP.md`'s S2 to S16 is proved, with
exactly one exception: S10, the finite inequality `F6 >= c` that the Arb verifier
accepts, which enters the theorem as a named hypothesis. The theorem is sorry-free,
uses only `propext`, `Classical.choice` and `Quot.sound`, and is conditional on S10
and on the rational side condition `c(m - 6) <= 1`. Aristotle was not used: 0 of 15
permitted submissions.

## 1. The theorem, verbatim

`lean/bridge/Zeta23Ext/Bridge/Main.lean`, namespace `Zeta23Ext.Bridge` (the files moved out
of `hunts/frontier_math/zeta23ext` on 2026-08-23 for packaging; see section 8):

```lean
theorem seven_point_bound (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)
```

with, in `Bridge/Defs.lean`,

```lean
def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)
```

where `HD 1 = 3/2 - (1/√2) cot(1/√2) = 0.6725007036794116…` is `[L23]`'s Theorem D
constant (`Zeta23/ThmD/Mult.lean`, `HD_one`), `Ncount T (2T)` counts the nontrivial
zeros of `riemannZeta` with ordinate in `(T, 2T]` with multiplicity and
`N0simple T (2T)` the simple ones on the critical line (`Zeta23/Statement.lean`),
and `F6 p g` is Ainta's seven-point functional at pressure denominator `p`
([A] eq:F6, with `1/3000` replaced by `1/p`).

At the published parameters, with the side conditions discharged by `norm_num`:

```lean
theorem seven_point_bound_paper
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * HD 1 - 2680) / 1340003 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)
```

via `Phi_paper : Phi (19 / 5000) 269 3000 = (1345000 * HD 1 - 2680) / 1340003`. The
constant is `[A]` Theorem 1.1's `0.6730085279277797613…`, against Theorem D's
`0.6725007036794116457…`.

At this laboratory's own parameters, added 2026-08-23 for the registry surface, via
`Phi_lab : Phi (34697 / 10000000) 294 3400 = (520625000 * HD 1 - 915625) / 518855453`:

```lean
theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * HD 1 - 915625) / 518855453 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T)

theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * HD 1 - 915625) / 518855453 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ)
```

`0.6730295534796928…`, the `p = 3400` figure of `RESULTS.md`. The ratio form needs no
positivity guard because `Ncount T (2T) → ∞` (`eventually_Ncount_pos`, from `[L23]`'s
Riemann-von Mangoldt consequence). **What is better here is the assumed certificate, not
the proved mathematics:** the same parametric theorem is instantiated at a different `(c,
m, p)`, and `hCert` at `(34697/10^7, 3400)` is exactly as unproved in Lean as `hCert` at
`(19/5000, 3000)`.

The conclusion's shape is `[L23]`'s `thmD₀_simple_mult` with `HD 1` replaced by
`Phi c m p`; the unconditional base theorem is the special case one recovers by
dropping the defect.

### The `n`-point theorem, and the eight-point instance (2026-08-23)

Every step of the bridge was then made parametric in the point count, and the statement
above became a three-line corollary of a general theorem. Nothing in the seven-point
statement moved: `F6 p` is `F 7 p` by `rfl` and `Phi` is `Phi_n 7` by `norm_num`, so the
registry surface that advertises it is unaffected down to the byte.

```lean
theorem n_point_bound (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_n n c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)
```

with, in `Bridge/Defs.lean`,

```lean
def Phi_n (n : ℕ) (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)
```

**The two numerals were the whole content of the generalisation.** The paper's `6` in the
numerator is the number of times a single gap is charged when the pressure term is summed
over the windows of a block ([A]:348, *"each single gap occurs at most six times"*), which
is `n−1`; its `m−6` is the number of windows of `n` consecutive points in a block of `m`,
which is `m−(n−1)`. The block cap `A₀ = c(m−(n−1)) ≤ 1` caps `m` at `(n−1) + ⌊1/c⌋`.

At eight points, at the certificate this hunt's own run accepts (`RESULTS.md` §3;
`c = 41763/10⁷` at `p = 3200`, cap `c(m−7) ≤ 1` giving `m ≤ 7 + ⌊10⁷/41763⌋ = 246`), via
`Phi_lab8 : Phi_n 8 (41763 / 10000000) 246 3200 = (2460000000 * HD 1 - 5359375) / 2450018643`:

```lean
theorem eight_point_bound
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * HD 1 - 5359375) / 2450018643 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T)

theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * HD 1 - 5359375) / 2450018643 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ)
```

`(2 460 000 000 H − 5 359 375)/2 450 018 643 = 0.67305298298962888…`, recomputed at 50
digits and agreeing with the `0.673052983` of `RESULTS.md` §3. Against the seven-point
laboratory figure `0.67302955347969271…` that is a gain of `2.34 × 10⁻⁵`. **The same
caveat applies with the same force:** `hCert` at `(8, 41763/10⁷, 3200)` is exactly as
unproved in Lean as `hCert` at `(7, 19/5000, 3000)`. What changed is that the *bridge*
from an eight-point certificate to a proportion is no longer a reading of the paper: it is
a theorem, and `RESULTS.md` §3's earlier *"stated, not proved"* is superseded.

One genuine mathematical change was needed, in `Main.pre_solve`: the paper's tolerance
`η = min(ε/10, A₀)` is sound at `n = 7` only because the accumulated coefficient
`m + 3 + (n−1)(m−1)` is then at most `10m`. It is now scaled by that coefficient itself,
`η = min(εm/(m + 3 + (n−1)(m−1)), A₀)`, which is sound at every `n`. Everything else in the
assembly turned out to be independent of the point count given the two derived reals; S6,
S7, S8, S9, S12, S14, S15 and the S8/S9/pinching helpers needed no edit at all, because
none of them ever sees a point count.

## 2. Build record

**Whole-package build at the root**, since 2026-08-23:

```
cd lean/bridge && lake build
Build completed successfully (8864 jobs).    62 s wall against the prebuilt store
```

*(8860 jobs before the `n`-point generalisation and the eight-point surface of 2026-08-23;
the four new jobs are `EightChallenge` and `EightSolution` and their targets.)*

Equivalently `bash lean/bridge/assemble.sh`, which symlinks the prebuilt Mathlib and
`Zeta23` stores in and then runs exactly that. The default targets are the development
(`Zeta23Ext`), `BridgeChallenge`, `BridgeSolution`, `EightChallenge` and
`EightSolution`, so this one command builds the theorem, both sets of advertised
statements and their proofs.

*(Before the move this was a standalone module build,
`cd hunts/frontier_math/zeta23ext && lake build Zeta23Ext.Bridge.Main`, 8854 jobs in 44 s,
because that package does not assemble at its root, issue #101. That is why the files
moved; #101 is still open for what remains there and no longer touches this theorem.)*

Toolchain `leanprover/lean4:v4.33.0-rc2`, mathlib `51e6992efd06126df61a496bebf8f49482a4e129`,
`Zeta23` at the pinned rev above. Exactly seven `sorry` warnings in the whole build, four in
`BridgeChallenge.lean` and three in `EightChallenge.lean`, and all seven are the deliberate
ones the Palomar format requires of a statement-only module; every other warning in the log
is a deprecation notice from `Zeta23` itself. Every `#print axioms` line in the package (93
of them across `Defs`, `Helpers_*`, `S6` to `S16`, `Main`, `BridgeSolution` and
`EightSolution`, the four advertised `Zeta23Ext.Palomar` and three advertised
`Zeta23Ext.PalomarEight` declarations included) reports
`[propext, Classical.choice, Quot.sound]`. Static scan of
every `.lean` file in the package: no `axiom`, `opaque`, `unsafe`, `admit`, `native_decide`,
`implemented_by` or `extern`.

`hunts/frontier_math/zeta23ext/Zeta23Ext.lean` no longer imports either moved module, and
the orphan guard in `tests/test_zeta23ext_imports.py` passes (10 of 10 in that file and
`test_hunt_probe_discipline.py`, two slow tests deselected).

## 3. The step table

Status is PROVED (a Lean theorem in this tree, standard axioms), L23 (a theorem of
the vendored upstream consumed by import), or HYPOTHESIS (a named hypothesis of
`seven_point_bound`). Grades are the trust map's, for contrast.

| step | statement | where | status | trust map grade |
| --- | --- | --- | --- | --- |
| S0 | analytic inputs (explicit formula, RvM, Chebyshev-Mertens, Montgomery-Vaughan, Stirling) | `[L23]` `Zeta23/Hypotheses.lean` `PaperInputs`, discharged by `paperInputs_zeta` | L23 | done |
| S1 | `H = 3/2 - (1/√2) cot(1/√2)` | `[L23]` `Zeta23/ThmD/Mult.lean` `HD_one`, `thmD₀_simple_mult` | L23 | done |
| S2 | stability rank-trace `‖P+Q‖² ≥ 4 tr(P+Q) - 3r - 4b + tr Ψ(M)` | `Zeta23Ext/StableRankTrace.lean` `stable_rank_trace` (and the sharp form with no hypothesis on `V`) | PROVED | SMALL |
| S3 | von Neumann trace inequality | `[L23]` `Zeta23/LinAlg/VonNeumann.lean` | L23 | done |
| S4 | positive-part splitting, `rank Q₊ = n₊(Q)` | `[L23]` `Zeta23/LinAlg/HermitianPosPart.lean` | L23 | done |
| S5 | `tr Ψ(M)` well defined | `[L23]` `specMap` | L23 | done |
| S6 | `Â = P₁ + Q'` with `n₊(Q') ≤ s₂ + p` | `Bridge/S6.lean` `regroup_posIndex` | PROVED | SMALL-MEDIUM |
| S7 | `s₁ ≥ 4 tr Â - ‖Â‖² - 2N(I') + D(M)` | `Bridge/S7.lean` `count_defect` | PROVED | SMALL |
| S8 | tail passage `N₀ˢ ≥ H N + D(M°) - o(N)` | `Bridge/S8.lean` `tail_passage`, `Helpers_S8.lean` | PROVED | LARGE |
| S9 | uniform kernel limit `⟨v_ρ, v_ρ'⟩ = k(x_ρ - x_ρ') + o(1)`; deleted strips hold `o(N)` zeros | `Bridge/S9.lean` `kernel_limit`, `deleted_strips`, `Helpers_S9.lean` | PROVED | LARGE |
| S10 | `F6(g) ≥ c` for all `g ≥ 0` | hypothesis `hCert` of `seven_point_bound` | HYPOTHESIS | LARGE (as Lean) |
| S11 | block energy `E_m + (6/p) span ≥ c(m - 6)` | `Bridge/S11.lean` `block_energy` | PROVED | SMALL |
| S12 | block defect `tr Ψ(G) ≥ min{1, 2 Σ_{i<j} |G_ij|²}` | `Bridge/S12.lean` `block_defect` (and `block_defect_of_isHermitian`, no positivity needed) | PROVED | SMALL |
| S13 | block bound `D(G_B) + (6/p) span(B) ≥ A₀ - o(1)` | `Bridge/S13.lean` `block_bound`; the cap `A₀ = c(m - 6) ≤ 1` is the hypothesis `hA0` | PROVED, with `hA0` a HYPOTHESIS | MEDIUM |
| S14 | block pinching `D(M°) ≥ Σ_B D(G_B)`, and `D(M) ≥ D(M°)` | `Bridge/S14.lean` `pinching_partition`, `pinching_submatrix`, `Helpers_pinching.lean` | PROVED | MEDIUM, "MISSING from Mathlib" |
| S15 | average over offsets; `x_{S°} - x₁ ≤ N + o(N)` | `Bridge/S15.lean` `offset_average`, `span_retained_le` | PROVED | SMALL-MEDIUM |
| S16 | solve for `N₀ˢ`, `Phi(c, m, p)` | `Bridge/S16.lean` `solve_linear`, `Phi_paper` | PROVED | TRIVIAL |

Assembly (`Bridge/Main.lean`): `eventually_h7` (S7 at the Montgomery-Taylor window
with S14's `D(M) ≥ D(M°)`), `block_bound_eventually` (S9 + S13, uniform in `T`),
`pre_solve` (S8 + S9 + S13 + S14 + S15 with every `o(N)` an explicit `η N`), then
S16. All PROVED.

## 4. The hypotheses, in words, and why each is believed

**`hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g`** (S10). For every six
nonnegative gaps, Ainta's seven-point functional, the pressure term `(1/p) Σ gᵢ` plus
the 21 pairwise overlap weights `w = k²` with coefficient `2/(7 - r)` for a pair
spanning `r` gaps, is at least `c`. This is [A] Proposition 4.1, lines 294 to 299
(eq:F6bound), at `c = 19/5000`, `p = 3000`. Believed because the Arb
interval-arithmetic verifier at `github.com/ainta/zeta-simple-zeros` accepts it
([A] lines 301 to 328: grid `1/4000`, 128 bits, 707 901 nodes, depth 37) and this
hunt reproduced that run field for field, one secondary table hash differing with
no effect on any count, and re-ran it with the pressure cutoff made sound
(`RESULTS.md`, `RUNS.md` entries of 2026-08-22 and 23). The
infimum is bracketed `0.003826 ≤ inf F6 ≤ 0.0038262312115073`, so `19/5000 = 0.0038`
has margin `2.6e-5`. It is not a Lean fact: Arb enclosures are trusted by the
verifier, and re-enclosing a 45 600-cell sinc table inside Lean is the scale
problem `TRUST-MAP.md` section 2 describes. It enters the theorem the way `[L23]`
takes `EnclOK` for its own external numerics. Non-vacuity: `F6 p 0 = 12` and
`F6 ≥ (1/p) Σ g`, so the class of `(c, p)` satisfying `hCert` is nonempty for small
`c`; what the certificate adds is the specific value.

**`hA0 : c * (m - 6) ≤ 1`** (S13's cap, [A] eq:mA, lines 372 to 375). The block
constant `A₀ = c(m - 6)` may not exceed 1, because S12 only ever yields `min{1, ·}`.
At the published values `A₀ = 4997/5000`; discharged by `norm_num` in
`seven_point_bound_paper`. `TRUST-MAP.md` section 1.2 is the account of why this
makes `m` a derived quantity, `m ≤ 6 + ⌊1/c⌋`, not a free parameter.

**`7 ≤ m`, `0 < p`, `0 < c`.** Blocks need seven points, the pressure denominator
must be positive, and a certificate constant `c ≤ 0` is vacuous since `F6 ≥ 0`.
All three hold at `(19/5000, 269, 3000)` and are discharged by `norm_num`.

Nothing else is assumed. In particular the analytic inputs S0 are not hypotheses:
`paperInputs_zeta` discharges `PaperInputs` for `riemannZeta` inside `[L23]`.

## 5. Aristotle submissions

None. Five agents, cap 3 each, **0 of 15 used**. Per-group ledgers are in
`bridge/ARISTOTLE-{skeleton,finite,pinching,S8,S9}.md`; merged into
`lean/ARISTOTLE-RUNS.md` as Batch 12. Every obligation closed by direct proof under
the pinned toolchain before a residual existed, and the standing rule
(`ARISTOTLE-PROBE.md` section 7) is that a closed target is not sent.

| group | obligations | used |
| --- | --- | --- |
| skeleton | bridge typechecks end to end, 11 named `sorry` lemmas; S7, S16 proved | 0 of 3 |
| finite | S6, S7, S11, S12, S13, S15 (seven lemmas) | 0 of 3 |
| pinching | S14 (two lemmas) | 0 of 3 |
| S8 | `tail_passage` | 0 of 3 |
| S9 | `kernel_limit`, `deleted_strips` | 0 of 3 |

## 6. What the formal state showed that the paper hides

**Skeleton.** The whole deduction of [A] sections 2 and 5 is filter arithmetic once
the step lemmas are stated at the Montgomery-Taylor window `mtParams T = (paramsOf
stdProfile 1).atD T`. The only `[L23]` objects that had to be re-exposed were
`blockData`'s `S₁, s₁, s₂, Ncount, blockP, blockQ` and the `Params.atD` window; the
paper's `D(M)` is `rtrace (specMap hM Psi)` with `Psi = gc 2 + 1` from the S2 probe.

**Finite group (S6, S7, S11, S12, S13, S15).** (1) Lemma 4.3 (S12) does not need
`G ⪰ 0`; it holds for every Hermitian matrix, so the paper's hypothesis is
decoration. (2) Lemma 4.2 (S11) hides two mechanisms under one sentence: "a pair
spanning `r` gaps occurs at most `7 - r` times" is a fibre count over triples
`(window, a, b) ↦ (window + a, window + b)`, while "`6/3000` times the sum of gaps
equals `span/500`" is not a counting bound but an exact telescoping identity
`Σ_{i<m-6} (y_{i+6} - y_i) = Σ_{i<6} (y_{m-6+i} - y_i)`; both need `w` even, which
the paper never says. (3) eq:269block (S13) silently uses `|k| ≤ 1`, never stated
in [A]; it is true because `cos(√2 t) ≥ 0` on `[-1/2, 1/2]` (that is, `√2/2 < π/2`),
and the error term is `2 m² δ`, not the paper's `o(1)` with no constant. (4) The
"average over the `m` offsets" of section 5 (S15) is cleaner as a sum over all
`n - m + 1` block starts with one pinching partition per residue class mod `m`; the
full-block count becomes exact and the floor-function bookkeeping disappears; the
S14 input is consumed once per residue, `m` times total, matching the paper's
`m · D(M°)`. (5) `x_{S°} - x₁ ≤ LT/2π = N + o(N)` needs `L ≤ ℓ₁`, that is
`2 log 2 - 1 ≥ 0` at `λ = 1` and `λ ≤ 1` in general, plus `log T = o(T)` to absorb
the RvM error into `ε N`; all three are absent from [A] section 5.

**Pinching (S14).** The paper justifies eq:pinching in one sentence: pinching is an
average of unitary conjugations and `X ↦ tr Ψ(X)` is convex and unitarily invariant.
Both halves are missing from Mathlib and both Lean trees, and each is heavier than
the fact invoked: convexity of a matrix trace functional on Hermitian matrices is a
Peierls/majorization theorem, and unitary invariance needs eigenvalue transfer under
conjugation. Neither is needed. For Hermitian `M = U diag(λ) Uᴴ` and injective `g`,
the matrix `Y = Vᴴ (U restricted to rows g)` has orthonormal rows and
`diag(μ) = Y diag(λ) Yᴴ`, so the spectrum of a principal submatrix is a
row-stochastic mixture of the spectrum of `M`, and scalar Jensen finishes
(`eigenvalues_submatrix_eq_mix`). Two asymmetries the sentence flattens: the
partition form `Σ_B D(G_B) ≤ D(M)` needs no positivity of `Ψ` at all (block weights
sum to exactly 1 per eigen-direction), whereas Corollary 2.2's `D(M) ≥ D(M°)` is
where `Ψ ≥ 0` enters, so the two S14 lemmas consume different properties of `Ψ`.
Unitary invariance is a red herring: `tr f(·)` is invariant automatically. And
upstream's own `sum_gc_diag_le_sum_gc_eigenvalues` (`RankTraceMult.lean:119`) is
the 1x1-blocks fibre of this theorem at `f = gc c`, so "MISSING from Mathlib" was
one abstraction step away from a lemma already kernel-checked in the vendored tree,
the same pattern `ARISTOTLE-PROBE.md` documented for S2.

**S8.** The trust map graded S8 LARGE and the skeleton's residual note located the
difficulty in `[L23]`'s `λ → 1⁻` passage (`eps_form_HD`): Theorem D exported at each
fixed `λ < 1`, `HD 1` reached by a limit over different windows, through which a
defect living at the `λ = 1` window cannot ride; the note also asserted that
`[L23]`'s `calE` does not tend to 0 at `λ = 1`. Neither holds in the tree.
`Zeta23.Assembly.calE_tendsto_zero` is stated for `0 < λ ≤ 1`; every other analytic
input of the endgame takes `P.Valid`, which is `0 < λ ≤ 1`, and `paramsOf
stdProfile 1` is Valid; and `thmD_mult2_abstract`'s `hlam : P.lam < 1` is consumed
exactly once, as `hlam.le`. So the `λ → 1⁻` passage is a presentation choice, not a
mathematical necessity, and the defect goes through the endgame at `λ = 1` by
transcription: `seamA_mult2` and `thmD_mult2_abstract` re-stated with the zero-side
core as a hypothesis carrying `+ D`, `D` entering the fixed-`T` inequality once and
the `o(N)` bookkeeping verbatim. The step graded LARGE is a 20-line instantiation
plus a 260-line transcription with four marked edits. What the paper hides is the
opposite of what was feared: its "Theorem D gives `tr Ĝ = N(1 + o(1))`,
`‖Ĝ‖² = (1/c₁* + o(1)) N`" is already formalised at `λ = 1` by `[L23]`, two layers
below the theorem it chose to export.

**S9.** (1) `R₀` is not a hypothesis of eq:kernel-limit. The paper states the limit
"uniformly for retained simple zeros with `|x_ρ - x_ρ'| ≤ R₀`"; the formal bound at
height `T` is `10 (c_DT/w)²/L⁴ + 12 w/L` for every pair of retained zeros at every
separation: the tail goes through `|K_∞ - K| ≤ (ρ(γ) + ρ(γ'))/2` (`[L23]`
`PrimeSide.abs_Kinf_sub_Kfun_le`), a sum of two one-point quantities, and the limit
`Φ_D(hx)/(aL) → k(x)` is an `L¹` statement about the window in which `x` enters
only through `|e^{ihxu}| = 1`. Nothing is uniform-on-compacts; everything is
uniform. `kernel_limit` keeps `R₀` and `H : PaperInputs Z` in its signature, unused,
because `Main` consumes it positionally. (2) `[L23]` already has the uniform-in-`T`
Poisson identity for the Montgomery-Taylor window: not `Poisson.lean`'s
`hasSum_phiHatR_mul` (which needs a `TaperProfile` and does not apply to `P.atD T`)
but `AdmWindow.hasSum_vHatR_mul` in `ThmD/WindowCore.lean`, with the `T`-independent
decay constant `cDT ϱ λ`, which is the whole uniformity. (3) The `r⁻²` decay of
[C26] section 5.3 is already `PrimeSide.rho_le_majorant`; the strips of normalised
width `L²` put all three of its arguments at `≥ 2πL`, and the normalised tail is
`O(L⁻⁴)`, not the paper's (correct, weaker) `O(L⁻²)`. (4) The limit needs no new
analysis: `ThmD.integral_abs_phiDsq_sub_sharp` and `ThmD.aD_close` plus one
substitution for the cosine transform of the sharp window. (5) `deleted_strips` is
the only S9 fact that touches the zeros (through `H.RvM`'s local count and main
term); window additivity and monotonicity of the abstract `Z.N` had to be written,
since `[L23]` has them only for the concrete `Ncount`.

## 7. Corrections owed to earlier documents

- `TRUST-MAP.md` S8 row and section 2, "S8 and S9 are the bridge": both steps are
  now proved; the LARGE grade measured the distance from the exported theorem, not
  from the tree. The `calE` claim in the skeleton's original S8 docstring was wrong
  and is gone. Recorded in `TRUST-MAP.md` under a dated correction rather than by
  rewriting the rows.
- `TRUST-MAP.md` S14, "general pinching MISSING from Mathlib and both Lean trees":
  still true of Mathlib at the pinned rev; no longer true of this tree.
- `ARISTOTLE-PROBE.md` section 12 recommended against a third Palomar entry for S2
  alone. That recommendation stands for S2 alone; section 8 below is the answer
  for the assembled theorem.
- `hunts/README.md` Hunt #79: "what is missing is carrying the new spectral defect
  through the tail passage and the uniform kernel limit" is superseded.

## 8. Is this Palomar material as it stands?

In substance, yes, and it does not need S8 or S9 first: both are proved. The formal
content is not "S2, S16 and whatever else"; it is the whole of Ainta's argument from
the finite inequality to the zero count, including the two steps the trust map
called the bridge, the pinching theorem it called missing, and the seven finite
lemmas, all kernel-checked against `[L23]` and Mathlib. The theorem is conditional
on exactly one non-Lean input, S10, a numerical inequality in six real variables
that an interval-arithmetic program accepts, and it says so in its statement: the
certificate is a named hypothesis, not an axiom, and the published constant is
recovered by `norm_num` from it. That is the same shape as `[L23]`'s own treatment
of its numerical tables, and a registry that accepts "conditional on a stated
hypothesis" can take it honestly with the hypothesis in `status.scope`.

### The three packaging blockers are resolved (2026-08-23)

This section listed three obstacles. None of them was the mathematics, and all three
are now closed. **Nothing has been submitted**, and the editorial question below is
untouched.

1. **The selected project assembles at its root.** Palomar replays the selected
   project, and `hunts/frontier_math/zeta23ext` does not assemble on `main`
   (issue #101, three modules the Bridge never imports). `StableRankTrace.lean` and
   the sixteen `Bridge/` modules therefore moved, by `git mv`, into a Lake package of
   their own at **`lean/bridge/`** (package `Zeta23Bridge`, library `Zeta23Ext`),
   which requires `anthropics/zeta-23-lean` at the same pinned commit, uses the same
   toolchain and the same Mathlib revision as `lean/` so the prebuilt store is
   shared, and whose root module imports both. `lake build` there completes, 8860
   jobs. Module names and namespaces are unchanged, so every declaration named in
   this document still has the name it had. The extension package keeps everything
   else and no longer imports the two; #101 stays open for what remains there and no
   longer touches this theorem.
2. **The Challenge and Solution modules are authored.** `lean/bridge/BridgeChallenge.lean`
   states four theorems over Mathlib alone in the namespace `Zeta23Ext.Palomar` —
   `seven_point_bound`, `seven_point_bound_paper`, and two at this laboratory's own
   parameters `(34697/10^7, 294, 3400)`, `seven_point_bound_lab` and
   `seven_point_bound_lab_ratio`, the second of which states the conclusion as a bound
   on `N₀ˢ/N` — with the format's four deliberate `sorry`s, one per statement.
   `lean/bridge/BridgeSolution.lean` proves the same four from
   `Zeta23Ext.Bridge.Main`; every bridge is `rfl` except `H_eq`, which is `[L23]`'s
   `HD_one`. ~~The eight-point statement of `RESULTS.md` is **not** advertised: its
   bridge from certificate to proportion is stated, not proved, and an unproved
   bridge has no business on a registry surface.~~ **Superseded 2026-08-23:** that
   bridge is now proved (section 1, `n_point_bound` and `eight_point_bound`), so the
   reason not to advertise it is gone. It is advertised, on its own surface — see
   below — and not by editing this one, which is in flight.
3. **The licence headers are correct.** All seventeen moved files carried Apache-2.0
   headers copied from the dependency's house style while this repository is MIT;
   they now carry the MIT header the rest of `lean/` uses. The one file that adapts
   `[L23]`'s code rather than importing it, `Bridge/Helpers_S8.lean`, keeps its
   attribution to Anthropic, PBC and the Apache-2.0 licence of the transcribed proof
   bodies, as a notice in its own header and in `lean/bridge/NOTICE`.

`scripts/palomar_precheck.py . lean/bridge lean/comparator-bridge.json
lean/palomar-bridge/formalization.yaml` now reports **66 pass, 1 warn, 0 FAIL**; the
warn is the standing one that the pinned toolchain is a release candidate, which the
two registered surfaces carry too. *(The comparator and metadata later moved to
`lean/bridge/comparator.json` and `lean/bridge/formalization.yaml`; at that layout, and
with the current script, both surfaces read 63 pass, 1 warn, 0 FAIL.)*

### The eight-point surface, added 2026-08-23

A **second** surface over the same Lake package, in the disjoint namespace
`Zeta23Ext.PalomarEight`, advertising three declarations: `n_point_bound`,
`eight_point_bound` and `eight_point_bound_ratio`.

| file | what it is |
|---|---|
| `lean/bridge/EightChallenge.lean` | statement-only over Mathlib alone, three deliberate `sorry` |
| `lean/bridge/EightSolution.lean` | proves the three from `Zeta23Ext.Bridge.Main`; every bridge `rfl` except `H_eq` (`HD_one`) and `Phi_n_eq`, which carries `H_eq` into the constant |
| `lean/bridge/comparator-eight.json` | the three theorem names, the same three permitted axioms |
| `lean/bridge/formalization-eight.yaml` | origin source-based, `adapts` Ainta, review self-assessed |

`scripts/palomar_precheck.py . lean/bridge lean/bridge/comparator-eight.json
lean/bridge/formalization-eight.yaml` reports **63 pass, 1 warn, 0 FAIL**, the warn being
the standing release-candidate one; re-running the seven-point surface reports the same,
unchanged.

**The seven-point surface was not touched.** A submission of it is in flight, so
`comparator.json`, `formalization.yaml`, `BridgeChallenge.lean` and `BridgeSolution.lean`
are byte-identical to what was submitted. One consequence is worth stating plainly: that
entry's `status.scope` says the eight-point generalisation *"this laboratory has stated but
not proved and which is therefore not offered here at all"*, which is now stale, and it
cannot be corrected without editing a document under review. The correction lives in the
eight-point entry's `review.notes` instead, which says so in as many words. **Nothing has
been submitted for the eight-point surface.**

### What is still the registry's call

Editorially, the entry advertises a refinement of a theorem already registered from
the upstream repository, conditional on a third party's unformalised numerics, and
whether that clears the notability floor is the registry's call, not a claim this
document can make for it. Recommendation unchanged: submit the conditional theorem as
it stands, with S10 named. Do not wait for S10 in Lean; that is a separate, large
project and the theorem's value does not depend on it.

## 9. Defects found during integration

- `bridge/ARISTOTLE-finite.md` quoted the reserved word inside a grep command, which
  `tests/test_hunt_probe_discipline.py` flags; reworded.
- `Bridge/Main.lean`'s docstrings (skeleton) still described the step lemmas as
  named `sorry`s and predicted `sorryAx` in the axiom audit; corrected to the
  proved state and the hypotheses listed by name.
- `Zeta23Ext.lean` did not import the Bridge, so the orphan guard failed on every
  attack branch (documented by the skeleton as the integrator's one-line fix); added.
- No group changed the statement of any step lemma relative to the skeleton
  (checked by diffing every `theorem` signature in S6, S8, S9, S11 to S15 against
  `origin/bridge/skeleton`); S12 added a strictly stronger companion.

## 10. What this does not claim

Nothing here bears on the Riemann Hypothesis (`docs/08`). `lean/bridge` assembles at
its root; `hunts/frontier_math/zeta23ext` still does not (#101), and that is now a
separate matter about modules this theorem never imported. Nothing has been submitted
to any registry from the eight-point surface, and the general theorem does not make any
certificate a Lean fact: `n_point_bound` is conditional at every `n`, and the eight-point
inequality is evidence from an interval-arithmetic verifier and nothing more. S10 is not a Lean fact and no claim is made that the Arb run is a
proof in the sense this laboratory's Lean arm uses the word; that applies equally to
this laboratory's own `(34697/10^7, 3400)` run, which is the same kind of evidence as
the published one and is assumed the same way. The
constants inside the proofs (`1600 A₀ L²` for the strips, `12 w/L` for the limit,
`2 m² δ` for the block error) are not sharp and were not tuned; every consumer
takes them as `∀ᶠ T`. Aristotle's calibration question from Batch 11 remains
open and is the owner's to spend on.
