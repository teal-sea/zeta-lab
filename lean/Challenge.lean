/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Advertised statement: a source-admissible variational identity

This module is the small, trusted surface a mathematical reader should audit.
It restates, self-containedly and over Mathlib alone, the principal theorems of
the Zeta Lab "Pub 1" development.  All three declarations advertised below are
compared by Comparator against the proof development.

## What the theorems say

Fix the interval `I = [-1/2, 1/2]` and the kernel

```
F₁(x) = |x| - 4x² + Σ_{k≥0} a_k |x|^{2k+3},    a_k = 2^{2k+3} k! / (2k+2)!
```

Let `A = I + T` be the operator `(Av)(s) = v(s) + ∫_I F₁(s-t) v(t) dt`, and let
`w = A⁻¹1` be the profile solving `w + Tw = 1` on `I`.  Write

```
⟨1,v⟩ = ∫_I v,        ⟨Av,v⟩ = ∫_I v² + ∬_{I²} F₁(s-t) v(s) v(t),
c*    = ⟨1, A⁻¹1⟩ = ∫_I w.
```

The theorem states that over the **source-admissible class** `𝒜_source` (the
scalar profiles `v(s) = φ(Ls)²` induced by even, radially nonincreasing,
`C²` windows `φ` supported exactly on `[-L/2, L/2]` with `0 ≤ φ ≤ 1`, uniform
`L¹` bounds on `φ''` and `(φ²)''`, and `L ≥ 8`):

```
sup_{v ∈ 𝒜_source} ⟨1,v⟩² / ⟨Av,v⟩ = c*,
inf_{v ∈ 𝒜_source} ⟨Av,v⟩ / ⟨1,v⟩² = 1/c*.
```

Both orientations are advertised because the orientation is load-bearing: it is
the quotient with `⟨1,v⟩²` in the **numerator** whose supremum is `c*`, and its
reciprocal whose infimum is `1/c*`.  The two are not interchangeable.

The statement is existential in `w`, `C₁` and `C₂`, so it carries its own
non-vacuity: the profile is asserted to exist, and the admissible class is
asserted to be populated with the uniform constants for which the identity
holds.  No hypothesis is assumed.

## The three advertised declarations

`pub1_strong_closure` and `pub1_strong_closure_reciprocal` state the two
orientations for an arbitrary profile `w`, taking `IsProfile w` as the
hypothesis that fixes which `w` is meant.  `pub1_strong_closure_exists`
additionally asserts that such a `w` exists, and so carries both orientations
with no hypothesis at all.  The first two are therefore not corollaries of the
third: they are universally quantified in `w`, where the third is existential.
All three are proved in the `Solution` module and all three are compared.

Every definition below is a verbatim copy of the corresponding definition in
the proof development (`ZetaLean.Pub1`), re-declared here in the namespace
`ZetaLean.Palomar` so that this file depends on Mathlib alone.
-/

namespace ZetaLean.Palomar

/-! ### The kernel `F₁` -/

/-- The coefficients `a_k = 2^{2k+3} k! / (2k+2)!` of the kernel's tail. -/
noncomputable def aCoef (k : ℕ) : ℝ :=
  2 ^ (2 * k + 3) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

/-- The kernel `F₁(x) = |x| - 4x² + Σ_k a_k |x|^{2k+3}`. -/
noncomputable def F1 (x : ℝ) : ℝ :=
  |x| - 4 * x ^ 2 + ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3)

/-! ### Clamping to `I` -/

/-- Clamp a real to `I = [-1/2, 1/2]`. -/
noncomputable def clampI (s : ℝ) : ℝ := max (-(1 / 2)) (min (1 / 2) s)

/-- The clamped kernel.  On `I × I` it *is* `F₁(s-t)`; off it, it repeats the
boundary values, which keeps the rows bounded everywhere. -/
noncomputable def clampedKernel (s t : ℝ) : ℝ := F1 (clampI s - clampI t)

/-! ### The quadratic form -/

/-- `⟪1, v⟫ = ∫_I v`. -/
noncomputable def massI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s

/-- `‖v‖₂² = ∫_I v²`. -/
noncomputable def normSqI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2

/-- `⟪T v, v⟫ = ∬_{I²} F₁(s-t) v(s) v(t)`. -/
noncomputable def kerForm (v : ℝ → ℝ) : ℝ :=
  ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (v s * v t)

/-- `⟪A v, v⟫ = ‖v‖₂² + ⟪T v, v⟫`, the energy of the source functional. -/
noncomputable def energyA (v : ℝ → ℝ) : ℝ := normSqI v + kerForm v

/-! ### The profile `w = A⁻¹1` -/

/-- `w` solves `w + T w = 1` on `I`.  The equation is stated with the clamped
kernel, which on `I` is the genuine one; off `I` it extends `w` boundedly. -/
def IsProfile (w : ℝ → ℝ) : Prop :=
  Continuous w ∧ (∃ C, ∀ s, |w s| ≤ C) ∧
    ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t * w t) = 1

/-- **The constant.**  `c* = ⟨1, A⁻¹1⟩ = ∫_I w`. -/
noncomputable def cStar (w : ℝ → ℝ) : ℝ := massI w

/-! ### The two quotients -/

/-- The **maximizing** quotient `c(v) = ⟨1,v⟩² / ⟨Av,v⟩`. -/
noncomputable def quot (v : ℝ → ℝ) : ℝ := massI v ^ 2 / energyA v

/-- The **reciprocal** quotient `⟨Av,v⟩ / ⟨1,v⟩²`, whose infimum is `1/c*`. -/
noncomputable def recipQuot (v : ℝ → ℝ) : ℝ := energyA v / massI v ^ 2

/-! ### The source-admissible class -/

/-- A **source window**: the window class the admissible profiles come from. -/
structure SourceWindow (φ : ℝ → ℝ) (L C₁ C₂ : ℝ) : Prop where
  /-- The window regime `L ≥ 8` of the construction. -/
  scale : 8 ≤ L
  /-- `φ ∈ C²`; together with `support` this is `φ ∈ C_c²(ℝ)`. -/
  smooth : ContDiff ℝ 2 φ
  /-- `φ` is even. -/
  even : ∀ u, φ (-u) = φ u
  /-- Amplitude floor. -/
  nonneg : ∀ u, 0 ≤ φ u
  /-- Amplitude ceiling: `0 ≤ φ ≤ 1`, no other normalization. -/
  le_one : ∀ u, φ u ≤ 1
  /-- `supp φ = [-L/2, L/2]`, exactly — not a proper subset. -/
  support : ∀ u, φ u ≠ 0 ↔ |u| < L / 2
  /-- `φ` is nonincreasing in `|u|`.  This is the nontrivial source constraint. -/
  radial : ∀ u₁ u₂ : ℝ, |u₁| ≤ |u₂| → φ u₂ ≤ φ u₁
  /-- `‖φ''‖₁ ≤ C₁`, uniformly in `L`. -/
  secondDerivL1 : ∫ u, |iteratedDeriv 2 φ u| ≤ C₁
  /-- `‖(φ²)''‖₁ ≤ C₂`, uniformly in `L`. -/
  sqSecondDerivL1 : ∫ u, |iteratedDeriv 2 (fun y => φ y ^ 2) u| ≤ C₂

/-- The scalar profile induced by a window, `φ²(u) = v(u/L)`, i.e.
`v(s) = φ(Ls)²`. -/
def InducedProfile (v φ : ℝ → ℝ) (L : ℝ) : Prop := ∀ s, v s = (φ (L * s)) ^ 2

/-- **The source-admissible class `𝒜_source`** with uniform constants `C₁, C₂`:
the scalar profiles induced by source-admissible windows. -/
def sourceAdmissible (C₁ C₂ : ℝ) : Set (ℝ → ℝ) :=
  {v | ∃ (φ : ℝ → ℝ) (L : ℝ), SourceWindow φ L C₁ C₂ ∧ InducedProfile v φ L}

/-! ### The advertised theorems -/

/-- **Source-admissible strong closure**, the supremum orientation.

For the profile `w = A⁻¹1`, the supremum of `⟨1,v⟩²/⟨Av,v⟩` over the
source-admissible class is `c* = ⟨1,w⟩`.  The only assumption is `IsProfile w`,
which says that `w` is the profile the statement is about, rather than imposing
a further condition on it. -/
theorem pub1_strong_closure {w : ℝ → ℝ} (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) := by
  sorry

/-- **The reciprocal orientation.**  The infimum of `⟨Av,v⟩/⟨1,v⟩²` over the
same class is `1/c*`.  It is advertised alongside the supremum because the
orientation is load-bearing: the two quotients are different quantities and the
one with `⟨1,v⟩²` in the numerator is the one that is maximized. -/
theorem pub1_strong_closure_reciprocal {w : ℝ → ℝ} (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ := by
  sorry

/-- **Source-admissible strong closure.**

There is a profile `w = A⁻¹1` and uniform constants `C₁, C₂` for which

```
sup_{v ∈ 𝒜_source} ⟨1,v⟩²/⟨Av,v⟩ = c*   and   inf_{v ∈ 𝒜_source} ⟨Av,v⟩/⟨1,v⟩² = 1/c*.
```

The supremum is attained as a least upper bound and the infimum as a greatest
lower bound, both over the image of the source-admissible class. -/
theorem pub1_strong_closure_exists :
    ∃ (w : ℝ → ℝ) (C₁ C₂ : ℝ), IsProfile w ∧
      IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) ∧
      IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ := by
  sorry

end ZetaLean.Palomar
