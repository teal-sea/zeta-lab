<!-- Landed from an audit agent, 2026-08-12. Wording adjusted for the
hunts/ lexical rules; no factual content altered. -->

# Audit: `thefundamentaltheor3m/Sphere-Packing-Lean`

Clone: `git clone --depth 1 https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean.git`
→ `/tmp/claude-0/-home-user-zeta-lab/b36e7360-bacb-5ff5-9319-18b0b8b964ba/scratchpad/sphere-packing-lean`
(direct clone succeeded; mirror not needed).
HEAD = `bad3de916074748eb88b7d1ee6dbf9494361ad17`, branch `main`, dated **2026-08-05**
(i.e. the current tip, not a stale snapshot). 77 `.lean` files, 18,194 lines.

Everything below is quoted from files in that clone.

---

## 0. Headline correction: the repo is NOT sorry-free, and the main theorem is a `sorry`

`SpherePacking/MainTheorem.lean` in full:

```lean
theorem SpherePacking.MainTheorem : SpherePackingConstant 8 = E8Packing.density :=
  sorry
```

Real (non-comment, non-test-file) `sorry`s, 61 of them across 19 files:

| file | count |
|---|---|
| `MagicFunction/b/Schwartz.lean` | 12 |
| `MagicFunction/a/Schwartz.lean` | 11 |
| `MagicFunction/a/Integrability/Integrability.lean` | 6 |
| `MagicFunction/PolyFourierCoeffBound.lean` | 4 |
| **`CohnElkies/LPBound.lean`** | **3** (+1 commented) |
| **`CohnElkies/Prereqs.lean`** | **3** |
| `ModularForms/FG.lean`, `MagicFunction/b/Eigenfunction.lean`, `MagicFunction/a/Eigenfunction.lean`, `MagicFunction/a/IntegralEstimates/{I2,I4,I6}.lean`, `ForMathlib/InvPowSummability.lean` | 2 each |
| `ModularForms/DimensionFormulas.lean`, `MainTheorem.lean`, `MagicFunction/{a,b}/SpecialValues.lean`, `ForMathlib/CauchyGoursat/OpenRectangular.lean`, `Basic/PeriodicPacking.lean` | 1 each |

The "formally complete Feb 2026" report is **not** borne out by this repository's `main`
as of 2026-08-05. Whatever was announced, it is not what is in this tree.

---

## 1. Inventory of the relevant statements

### 1a. Poisson summation: `SpherePacking/CohnElkies/Prereqs.lean`

The file opens with (lines 8–11):

```
## THIS FILE SHOULD EVENTUALLY BE REMOVED AND THE REFERENCES IN COHN-ELKIES MUST BE REPLACED WITH
## THE RIGHT ONES (NOT THE ONES FROM HERE). THIS FILE IS JUST A TEMPORARY SOLUTION TO MAKE THE
## COHN-ELKIES FILE WORK.
```

Context (lines 38–39):

```lean
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
```

The hypothesis predicate (line 100), verbatim, note the `sorry` *inside the definition*:

```lean
def PSF_Conditions (f : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  Summable f ∧
  sorry
```

```lean
theorem PSF_L {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ,
  (𝓕 f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) :=
  sorry

-- The version below is on the blueprint. I'm pretty sure it can be removed.
theorem PSF_L' {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : PSF_Conditions f) :
    ∑' ℓ : Λ, f ℓ = (1 / ZLattice.covolume Λ) *
      ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ, (𝓕 f m)
    := by
  simpa using PSF_L Λ hf 0
```

```lean
namespace SchwartzMap

theorem PoissonSummation_Lattices (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
  (v : EuclideanSpace ℝ (Fin d)) :
  ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
    ∑' m : LinearMap.BilinForm.dualSubmodule (innerₗ _) Λ,
      (𝓕 ⇑f m) * exp (2 * π * I * ⟪v, m⟫_[ℝ]) := by
  sorry

end SchwartzMap
```

**This is the entire Poisson-summation content of the repository.** Three statements,
all `sorry`, one of them with a `sorry` in its own hypothesis. It is a stub file that
the authors have labelled as such. `grep -rn "Poisson\|poissonSummation"` over
`SpherePacking/` returns only these declarations plus one call site
(`LPBound.lean:372`) and comments.

The blueprint agrees. `blueprint/src/subsections/fourier-analysis.tex:86` states the
theorem, tags `\lean{SchwartzMap.PoissonSummation_Lattices}`, and its proof environment
reads:

```
\begin{proof}
  One possible proof would be by induction on $d$. However, there are numerous nuances involved,
  particularly in manipulating nested infinite sums. Ideas would be appreciated.
\end{proof}
```

(The `\leanok` on the `\begin{theorem}` line means the *statement* is formalised, not the
proof; the proof environment carries no `\leanok`.)

### 1b. The LP bound: `SpherePacking/CohnElkies/LPBound.lean`

Hypotheses are `variable`s (lines 55–64):

```lean
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
-- The Cohn-Elkies conditions:
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
```

The two headline results (lines 533 and 642):

```lean
theorem LinearProgrammingBound' (hd : 0 < d) (hf : Summable f) :
  P.density ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
  volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
```

```lean
theorem LinearProgrammingBound (hd : 0 < d) (hf : Summable f) : SpherePackingConstant d ≤
  (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
  := by
```

These are the Fourier-positivity conditions asked about: `hCohnElkies₂` is *pointwise
nonnegativity of the Fourier transform of a Schwartz function*, stated as a hypothesis and
never derived. There is no positive-definiteness API, no `PosDef`, no reusable "positive
Fourier transform" structure, `grep` for `PosDef`, `posdef`, `positive definite` over
`SpherePacking/` returns nothing.

The proof chain is not closed. `LPBound.lean` has three genuine `sorry`s, all summability
side-conditions inside `calc_steps`, at lines 358, 388, 392, 467 (one is a `case summable
=> sorry`); e.g. line 467 guards

```lean
have hSummable : Summable
  (fun (m : ↥(LinearMap.BilinForm.dualSubmodule (innerₗ _) P.lattice)) =>
  (𝓕 ⇑f m).re * (norm (∑' x : ↑(P.centers ∩ D),
  exp (2 * π * I * ⟪↑x, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2)) := by
  sorry
```

and line 372 is the call `exact SchwartzMap.PoissonSummation_Lattices P.lattice f _`, i.e.
the LP bound is proved *from* the sorried Poisson formula.

### 1c. `IsDecayingMap`, `SpherePacking/ForMathlib/InvPowSummability.lean:37`

```lean
def IsDecayingMap (X : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ x ∈ X, ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ k * ‖f x‖ ≤ C
```

with the companion predicate (line 29)

```lean
def Inv_Pow_Norm_Summable_Over_Set_Euclidean (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Summable (fun x : X => 1 / ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ (d + 1))
```

and the usable result (line 168):

```lean
theorem Summable_of_Inv_Pow_Summable
  (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Inv_Pow_Norm_Summable_Over_Set_Euclidean X)
  (hf : IsDecayingMap X f) :
  Summable (fun x : X => f x)
```

This part **is** proved (`IsDecayingMap.subset`, `Summable_of_Inv_Pow_Summable'`,
`SchwartzMap.IsDecaying`). But note: `IsDecayingMap` demands decay faster than *every*
polynomial (`∀ k : ℕ`), it is a Schwartz-strength decay condition, not the `O(|x|^{-b})`
for a single `b > 1` that a compactly supported kernel would want. And the two remaining
`sorry`s in this file (`extracted_1` at line 233, `Summable_Inverse_Powers_of_Finite_Orbits`
at line 251) are exactly the lemmas that would supply `Inv_Pow_Norm_Summable_Over_Set_Euclidean`
for a lattice orbit, so the summability half is also open where it touches lattices.

### 1d. Toolchain / pin / licence

- `lean-toolchain`: `leanprover/lean4:v4.32.0`
- `lakefile.toml`: `[[require]] name = "mathlib" … rev = "v4.32.0"`, plus `checkdecls`;
  `[[lean_lib]] name = "SpherePacking"`; `autoImplicit = false`, `relaxedAutoImplicit = false`.
- `lake-manifest.json`: mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997` (`v4.32.0`).
- `LICENSE`: Apache 2.0. Per-file headers likewise Apache 2.0.
- The sources use the new Lean **module system** (`module`, `public import`,
  `@[expose] public section`) throughout, which is a v4.32-era feature.

---

## 2. The key question: can this API state our bridge?

### (a) Dimension and smoothness

**Dimension.** `PSF_L` / `PoissonSummation_Lattices` are stated over
`EuclideanSpace ℝ (Fin d)` with `[Fact (0 < d)]`, so `d = 1` is *type-correct*. There is
no `n ≥ 2` restriction. But `d = 1` buys nothing here, because the statement is unproved.

**Smoothness.** Both are stated only for `SchwartzMap _ ℂ` (or for the placeholder
`PSF_Conditions`, whose second conjunct is literally `sorry`). Our `c2` is continuous,
compactly supported on `[-1,1]`, with a corner at 0, **not** `C^∞`, therefore **not**
Schwartz, therefore outside the hypothesis of `PoissonSummation_Lattices` as stated.
There is no weaker-hypothesis variant in the repo: `HasCompactSupport`, `tsupport`,
`ContinuousMap`-valued Poisson results, none appear anywhere in `SpherePacking/`.

**The cheapest repair is not to repair this repo at all**, because upstream Mathlib
(the very version this repo pins, `v4.32.0`) already contains the 1-D statement we
need with hypotheses `c2` satisfies. From
`Mathlib/Analysis/Fourier/PoissonSummation.lean` at tag `v4.32.0`:

```lean
/-- **Poisson's summation formula**, assuming that both `f` and its Fourier transform decay as
`|x| ^ (-b)` for some `1 < b`. (This is the one-dimensional case of Corollary VII.2.6 of Stein and
Weiss, *Introduction to Fourier analysis on Euclidean spaces*.) -/
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ}
    (hb : 1 < b) (hf : f =O[cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)
```

and, more general still,

```lean
/-- **Poisson's summation formula**, most general form. -/
theorem Real.tsum_eq_tsum_fourier {f : C(ℝ, ℂ)}
    (h_norm :
      ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle)
```

**Hypotheses required: continuity plus polynomial decay. No smoothness at all.** Applied
in the orientation we need, physical-side function `ĉ2 = |ĝ|²` (continuous, nonneg,
`O(|x|^{-2})` since `ĝ = O(|x|^{-1})`), dual-side function `c2` (compactly supported, hence
`O(|x|^{-b})` for every `b`), both `=O[cocompact ℝ] (|·|^(-2))` hypotheses hold and
`b = 2 > 1`. The corner of `c2` at 0 is irrelevant: continuity is all that is asked of the
transformed side, and `c2` appears only through `𝓕 f`, which is not required to be smooth.

The only real work left on that side is the **spacing-`s` rescaling**: Mathlib's statement
is for the lattice `ℤ`, ours for `sℤ`, so a substitution `x ↦ x/s` and the corresponding
`𝓕` scaling lemma are needed. That is routine, and it is work you would do against Mathlib,
not against this repo.

### (b) Finite vs infinite lattice sum with an explicit error term

**Absent. Completely.** There is no truncation lemma, no tail bound, no
finite-vs-infinite comparison with an error term anywhere in the repository. `grep` for
`truncat`, `tail_`, and manual reading of `InvPowSummability.lean`, `Prereqs.lean` and
`LPBound.lean` turns up only *qualitative* summability (`Summable`, `IsDecayingMap`,
`Summable_of_Inv_Pow_Summable`) with no quantitative remainder.

Structurally this is unsurprising: the Cohn–Elkies argument never truncates. It goes
finite-cluster → *periodic* packing (`PeriodicSpherePacking`, `P.numReps'`, fundamental
domain `D`) and then applies Poisson to the exact infinite lattice sum. The passage from
general to periodic packings is `periodic_constant_eq_constant` in
`SpherePacking/Basic/PeriodicPacking.lean` (which itself carries a `sorry` at line 1221),
and it is a **supremum/approximation** argument about packing *densities*, not a bound on
a per-configuration functional with an error term. It gives no one-sided inequality of the
shape you need, in either direction.

So the actual bridge you are missing is not in this repo, and its absence is by design of
the mathematics, not an oversight.

---

## 3. Reusability as a dependency

- **Packaged as a library**: yes, technically, `lakefile.toml` declares
  `[[lean_lib]] name = "SpherePacking"` with root `SpherePacking.lean`, licence Apache 2.0,
  so `require`-ing it is legally and mechanically possible.
- **Built for reuse**: no. The parts you would want live in a file whose own header says
  it "SHOULD EVENTUALLY BE REMOVED"; the API is threaded through section `variable`s and
  `include` clauses (`hReal`, `hRealFourier`, `hCohnElkies₁`, `hCohnElkies₂`), several
  declarations are `private`, and internal TODOs like "HUGE TODO: Get the periodic density
  formula in terms of some `D`" sit in the proof of the headline theorem. It is a
  single-goal project, not a reusable analysis library.
- **Requiring it imports its `sorry`s.** Downstream, `SchwartzMap.PoissonSummation_Lattices`
  would typecheck and be usable, and would be an axiom-tainted lie. Anything you proved
  from it would be worth nothing. Under Zeta Lab's rule that "the Lean arm counts nothing
  with a `sorry`", depending on this package is disqualifying on its own.
- **Pin conflict with `anthropics/zeta-23-lean`**: yes, hard conflict.
  This repo: toolchain `leanprover/lean4:v4.32.0`, mathlib `rev = "v4.32.0"`.
  `zeta-lab/lean` (and, per the task, `zeta-23-lean`): toolchain
  `leanprover/lean4:v4.33.0-rc2`, mathlib `rev = "v4.33.0-rc2"`.
  Lake resolves exactly one mathlib revision per dependency tree, and the toolchains differ
  too, so a shared build is impossible without forking one side onto the other's pin.
  Bumping this repo to v4.33.0-rc2 is plausible (they run `auto-update-lean/patch-v4.32.1`
  and `patch-v4.32.2` branches, so bumps are routine for them) but it is a fork you would
  have to maintain, for content that is `sorry` anyway.

---

## 4. Bandlimited positivity / Beurling–Selberg / LP-bound material

- **Beurling–Selberg**: absent. `grep -rn "Beurling\|Selberg"` over `SpherePacking/` →
  nothing.
- **Bandlimited**: absent. `grep -rn "bandlimit\|BandLimit"` → nothing. No Paley–Wiener,
  no `HasCompactSupport` anywhere.
- **Positive-definiteness**: absent as a concept. The only positivity in the repo is the
  *hypothesis* `hCohnElkies₂ : ∀ x, (𝓕 f x).re ≥ 0` and two small consequences that are
  proved:

  ```lean
  theorem f_nonneg_at_zero : 0 ≤ (f 0).re
  theorem f_zero_pos : 0 < (f 0).re
  ```

  (`LPBound.lean:103, 114`), i.e. "`f̂ ≥ 0` and `f ≠ 0` implies `f(0) > 0`", via
  Fourier inversion and `Continuous.integral_zero_iff_zero_of_nonneg`
  (`Prereqs.lean:206`, proved). That last one is a genuinely reusable little lemma
  ("a continuous nonneg integrable function with zero integral is zero"), but it is
  a two-line Mathlib-flavoured fact, not scaffolding.
- **The LP bound as a pattern**: the *Cohn–Elkies* LP bound is here (`LinearProgrammingBound`,
  §1b), modulo three summability `sorry`s and the sorried Poisson formula. What is *not*
  here is any construction of the LP witness function's positivity, the magic function `g`
  is defined (`MagicFunction/g/Basic.lean`: `g : 𝓢(ℝ⁸, ℂ) := ((π * I) / 8640) • a + (I / (240 * π)) • b`)
  with `g_zero : g 0 = 1` and `fourier_g_zero` proved, but conditions
  `g(x) ≤ 0` for `‖x‖ ≥ √2` and `ĝ ≥ 0` (blueprint `\eqref{eqn:g1}`, `\eqref{eqn:g2}`) are
  not formalised at all. So there is no worked example in this repo of *proving* a Fourier
  transform nonnegative, which is precisely the skill your other open piece needs.

---

## 5. Verdict

**(iv), shading into (iii): not relevant as a dependency; marginally useful as a
proof-pattern reference.**

Specifics:

1. The one theorem in the repo that names your problem,
   `SchwartzMap.PoissonSummation_Lattices`: **is a `sorry`**, as is `PSF_L`, as is the
   hypothesis predicate `PSF_Conditions` (`Summable f ∧ sorry`). There is nothing to reuse
   because nothing is proved.
2. Even taken as a *statement*, it is Schwartz-only, and `c2` is not Schwartz (corner at 0).
   Meanwhile Mathlib's own `Real.tsum_eq_tsum_fourier_of_rpow_decay` needs only
   continuity + `O(|x|^{-b})`, `b > 1`, which `c2` and `ĉ2 = |ĝ|²` both satisfy with `b = 2`.
   **The sphere-packing repo's Poisson result is strictly weaker than what you already have
   for free.**
3. The finite-to-infinite comparison with an explicit error term, the actual bridge, is
   simply not present, in any form, and could not be, because Cohn–Elkies routes through
   periodicity rather than truncation.
4. Depending on it would import `sorry`s and force a Mathlib fork off `v4.33.0-rc2`.

### Cheapest route to the bridge, given what I read

- **Infinite side: do it in Mathlib, in 1-D, not via this repo.** Instantiate
  `Real.tsum_eq_tsum_fourier_of_rpow_decay` (or the `C(ℝ,ℂ)` form
  `Real.tsum_eq_tsum_fourier`) with `f = ĉ2`, `b = 2`. The obligations are: `Continuous ĉ2`,
  `ĉ2 =O[cocompact ℝ] (|·|^(-2))` (from `ĝ = O(|x|^{-1})`, a one-line integration by parts
  on the finite window), and `𝓕 ĉ2 = c2 =O[cocompact ℝ] (|·|^(-2))` (trivial from compact
  support). Then a rescaling `x ↦ x/s` to move from `ℤ` to `sℤ`. No smoothness anywhere;
  the corner never enters. This makes `b_inf(s,y)` a theorem rather than a computation.
- **Bridge side: nothing off the shelf exists; you must build it, and you should build it
  as a truncation estimate, not as a periodisation.** The measured data you cite,
  finite clusters approaching the limit *from below* at resonance (m=4: +0.0240, m=32:
  +0.0056, limit +0.0135 at s=2.0), says the finite-`m` value is not monotone in `m`
  and crosses the limit, so no clean one-sided lemma of the form "finite ≤ infinite" is
  available and you should stop looking for one to borrow. The tractable statement is
  two-sided with an explicit `m`-dependent remainder:
  `|b_m(s,y) − b_inf(s,y)| ≤ E(m,s,y)` with `E → 0`, obtained from the *compact support of
  `c2`*, because `c2` vanishes outside `[-1,1]`, the dual sum is already finite
  (`|2πk/s| < 1`), and the error in the finite cluster is a boundary/edge term over
  `O(1)` pairs near the cluster ends, not a tail of a divergent series. That is an
  elementary, self-contained estimate in `zeta-23-lean` against Mathlib alone.
- **For the Beurling–Selberg / positivity piece**: this repo offers no help either
  (no bandlimited, no positive-definite, no Beurling, no Selberg, and the magic function's
  own positivity conditions are unformalised). The one transferable micro-lemma is
  `Continuous.integral_zero_iff_zero_of_nonneg` (`SpherePacking/CohnElkies/Prereqs.lean:206`),
  which is proved and is a candidate to re-derive (not depend on) if you ever need
  "nonneg continuous with zero integral ⇒ zero".

### Files worth reading once, as pattern, if anything

- `SpherePacking/CohnElkies/LPBound.lean`: how to organise an LP-bound proof under
  `variable`/`include` hypothesis bundles, and the `calc`-chain shape of the
  Cohn–Elkies argument.
- `SpherePacking/ForMathlib/InvPowSummability.lean`: the `IsDecayingMap` +
  inverse-power-summability idiom for lattice summability.
- `blueprint/src/subsections/{fourier-analysis,cohn-elkies}.tex`: a clean prose statement
  of what a lattice Poisson formula should look like, and an honest record of which proofs
  are open.
