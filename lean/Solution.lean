/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1

/-!
# Proved solution

This module imports the full proof development (`ZetaLean.Pub1`) and proves the
statement advertised in `Challenge.lean`.

Following the Palomar layout, this module does **not** import `Challenge`: the
two modules independently declare the same names, and Comparator checks that
each compared declaration has the same statement in both.  The definitions
below are therefore verbatim copies of the ones in `Challenge.lean`, which are
themselves verbatim copies of the development's own definitions
(`ZetaLean.Pub1`).

Each copy is definitionally equal to its original, so the bridge lemmas after
them are `rfl`.  The single exception is `SourceWindow`: a structure declared
twice is two distinct inductive types, so `sourceAdmissible_eq` transports the
ten fields in both directions instead.
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
  /-- `supp φ = [-L/2, L/2]`, exactly, not a proper subset. -/
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

/-! ### The definitional bridges to the proof development -/

theorem aCoef_eq : aCoef = AristotleE1.aCoef := rfl

theorem F1_eq : F1 = ZetaLean.Pub1.F1 := rfl

theorem clampI_eq : clampI = ZetaLean.Pub1.clampI := rfl

theorem clampedKernel_eq : clampedKernel = ZetaLean.Pub1.clampedKernel := rfl

theorem massI_eq : massI = ZetaLean.Pub1.massI := rfl

theorem normSqI_eq : normSqI = ZetaLean.Pub1.normSqI := rfl

theorem kerForm_eq : kerForm = ZetaLean.Pub1.kerForm := rfl

theorem energyA_eq : energyA = ZetaLean.Pub1.energyA := rfl

theorem isProfile_eq : IsProfile = ZetaLean.Pub1.IsProfile := rfl

theorem cStar_eq : cStar = ZetaLean.Pub1.cStar := rfl

theorem quot_eq : quot = ZetaLean.Pub1.quot := rfl

theorem recipQuot_eq : recipQuot = ZetaLean.Pub1.recipQuot := rfl

theorem inducedProfile_eq : InducedProfile = ZetaLean.Pub1.InducedProfile := rfl

/-- The two `SourceWindow` structures carry the same ten fields, so each
transports to the other. -/
theorem sourceWindow_iff (φ : ℝ → ℝ) (L C₁ C₂ : ℝ) :
    SourceWindow φ L C₁ C₂ ↔ ZetaLean.Pub1.SourceWindow φ L C₁ C₂ := by
  constructor
  · intro h
    exact
      { scale := h.scale
        smooth := h.smooth
        even := h.even
        nonneg := h.nonneg
        le_one := h.le_one
        support := h.support
        radial := h.radial
        secondDerivL1 := h.secondDerivL1
        sqSecondDerivL1 := h.sqSecondDerivL1 }
  · intro h
    exact
      { scale := h.scale
        smooth := h.smooth
        even := h.even
        nonneg := h.nonneg
        le_one := h.le_one
        support := h.support
        radial := h.radial
        secondDerivL1 := h.secondDerivL1
        sqSecondDerivL1 := h.sqSecondDerivL1 }

theorem sourceAdmissible_eq (C₁ C₂ : ℝ) :
    sourceAdmissible C₁ C₂ = ZetaLean.Pub1.sourceAdmissible C₁ C₂ := by
  ext v
  constructor
  · rintro ⟨φ, L, hw, hind⟩
    exact ⟨φ, L, (sourceWindow_iff φ L C₁ C₂).mp hw, hind⟩
  · rintro ⟨φ, L, hw, hind⟩
    exact ⟨φ, L, (sourceWindow_iff φ L C₁ C₂).mpr hw, hind⟩

/-! ### The advertised theorems -/

/-- **Source-admissible strong closure**, the supremum orientation.

For the profile `w = A⁻¹1`, the supremum of `⟨1,v⟩²/⟨Av,v⟩` over the
source-admissible class is `c* = ⟨1,w⟩`.  The only assumption is `IsProfile w`,
which says that `w` is the profile the statement is about, rather than imposing
a further condition on it. -/
theorem pub1_strong_closure {w : ℝ → ℝ} (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) := by
  obtain ⟨C₁, C₂, h⟩ := ZetaLean.Pub1.pub1_strong_closure hw
  exact ⟨C₁, C₂, by rw [sourceAdmissible_eq C₁ C₂]; exact h⟩

/-- **The reciprocal orientation.**  The infimum of `⟨Av,v⟩/⟨1,v⟩²` over the
same class is `1/c*`.  It is advertised alongside the supremum because the
orientation is load-bearing: the two quotients are different quantities and the
one with `⟨1,v⟩²` in the numerator is the one that is maximized. -/
theorem pub1_strong_closure_reciprocal {w : ℝ → ℝ} (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ := by
  obtain ⟨C₁, C₂, h⟩ := ZetaLean.Pub1.pub1_strong_closure_reciprocal hw
  exact ⟨C₁, C₂, by rw [sourceAdmissible_eq C₁ C₂]; exact h⟩

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
  obtain ⟨w, C₁, C₂, hw, hlub, hglb⟩ := ZetaLean.Pub1.pub1_strong_closure_exists
  refine ⟨w, C₁, C₂, hw, ?_, ?_⟩
  · rw [sourceAdmissible_eq C₁ C₂]; exact hlub
  · rw [sourceAdmissible_eq C₁ C₂]; exact hglb

end ZetaLean.Palomar
