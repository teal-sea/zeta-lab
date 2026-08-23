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

`hunts/frontier_math/zeta23ext/Zeta23Ext/Bridge/Main.lean`, namespace `Zeta23Ext.Bridge`:

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

The conclusion's shape is `[L23]`'s `thmD₀_simple_mult` with `HD 1` replaced by
`Phi c m p`; the unconditional base theorem is the special case one recovers by
dropping the defect.

## 2. Build record

Standalone module build, the way `ARISTOTLE-PROBE.md` section 1b built
`StableRankTrace` (the package root does not assemble on `main`, issue #101, for
reasons in three modules none of which the Bridge imports):

```
cd hunts/frontier_math/zeta23ext && lake build Zeta23Ext.Bridge.Main
Build completed successfully (8854 jobs).    44 s wall from deleted Bridge oleans
```

Toolchain `leanprover/lean4:v4.33.0-rc2`, mathlib `51e6992efd06126df61a496bebf8f49482a4e129`,
`Zeta23` at the pinned rev above. All sixteen Bridge modules plus `StableRankTrace`
recompiled; zero `sorry` warnings; the only warnings in the log are deprecation
notices from `Zeta23` itself. Every `#print axioms` line in the tree (72 of them
across `Defs`, `Helpers_*`, `S6` to `S16` and `Main`) reports
`[propext, Classical.choice, Quot.sound]`. Static scan of `Zeta23Ext/Bridge/*.lean`
and `StableRankTrace.lean`: no `axiom`, `opaque`, `unsafe`, `admit`,
`native_decide`, `implemented_by` or `extern`.

`Zeta23Ext.lean` now imports `Zeta23Ext.Bridge.Main`, so the orphan guard in
`tests/test_zeta23ext_imports.py` passes (12 of 12 in that file and
`test_hunt_probe_discipline.py`).

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
hypothesis" can take it honestly with the hypothesis in `status.scope`. Two things
stand in the way, and neither is the mathematics. Mechanically, Palomar replays the
selected project, and `hunts/frontier_math/zeta23ext` does not assemble on `main`
(issue #101, three modules the Bridge never imports); the surface in
`lean/palomar-bridge/` is authored and prechecked but cannot be submitted until
#101 is fixed or the Bridge is moved to a package that builds at the root.
Editorially, the entry advertises a refinement of a theorem already registered from
the upstream repository, conditional on a third party's unformalised numerics, and
whether that clears the notability floor is the registry's call, not a claim this
document can make for it. Recommendation: fix #101 (or split the Bridge and
`StableRankTrace` into a package of their own that depends on `Zeta23`), then submit
the conditional theorem as it stands, with S10 named. Do not wait for S10 in Lean;
that is a separate, large project and the theorem's value does not depend on it.

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

Nothing here bears on the Riemann Hypothesis (`docs/08`). The package root still
does not assemble (#101). S10 is not a Lean fact and no claim is made that the
Arb run is a proof in the sense this laboratory's Lean arm uses the word. The
constants inside the proofs (`1600 A₀ L²` for the strips, `12 w/L` for the limit,
`2 m² δ` for the block error) are not sharp and were not tuned; every consumer
takes them as `∀ᶠ T`. Aristotle's calibration question from Batch 11 remains
open and is the owner's to spend on.
