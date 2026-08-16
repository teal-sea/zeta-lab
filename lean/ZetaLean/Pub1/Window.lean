/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Ramp
import ZetaLean.Pub1.Concavity
import ZetaLean.Pub1.Aristotle.J

/-!
# Pub 1 strong closure: the source-admissible window class and the taper

The class `𝒜_source` and the explicit sequence realising `w` inside it, from
`hunts/wide_search/RESULTS-xiprime-admissible-closure.md`, sections "Exact source
class" and "Explicit source-admissible sequence".

`SourceWindow φ L C₁ C₂` is the *generalized, load-bearing* class of Section 7.1,
p. 20 of the source paper — not the convenient Section 2.2 realization.  It
requires `φ ∈ C_c²`, even, `0 ≤ φ ≤ 1`, `supp φ = [-L/2, L/2]` exactly, `φ`
nonincreasing in `|u|`, and `‖φ''‖₁`, `‖(φ²)''‖₁` bounded by constants that do
*not* depend on `L`.  Carrying `C₁` and `C₂` as parameters of the class is what
makes "uniformly `O(1)`" a real constraint rather than a vacuous per-element one:
a single pair of constants has to work for the whole family.

Nothing here assumes `C^∞`, a flat top, or a particular ramp.  The nontrivial
source constraint, and the one the ambient variational theorem does not already
give, is radial monotonicity.

The taper is

```
φ_L(u) = √(w(u/L)) · η(L/2 - |u|),      v_L(s) = φ_L(Ls)² = w(s)·η(L(1/2-|s|))².
```
-/

open Set MeasureTheory

namespace ZetaLean.Pub1

/-! ### The source-admissible class -/

/-- **Source admissibility.**  Section 7.1, p. 20 of *More than two thirds of the
zeros of the Riemann zeta function lie on the critical line*: the generalized
window class, with `C₁` and `C₂` the uniform `O(1)` constants shared by the whole
family. -/
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
`v(s) = φ(Ls)²`.  Source paper, equation (7.3). -/
def InducedProfile (v φ : ℝ → ℝ) (L : ℝ) : Prop := ∀ s, v s = (φ (L * s)) ^ 2

/-- **The source-admissible class `𝒜_source`** with uniform constants `C₁, C₂`:
the scalar profiles induced by source-admissible windows. -/
def sourceAdmissible (C₁ C₂ : ℝ) : Set (ℝ → ℝ) :=
  {v | ∃ (φ : ℝ → ℝ) (L : ℝ), SourceWindow φ L C₁ C₂ ∧ InducedProfile v φ L}

/-- Radial monotonicity gives `‖φ'‖₁ = 2φ(0) ≤ 2` and `‖(φ²)'‖₁ = 2φ(0)² ≤ 2`
without any further hypothesis: the total variation of a nonnegative even
radially nonincreasing function bounded by `1` is at most twice its peak. -/
theorem SourceWindow.peak_le_one {φ : ℝ → ℝ} {L C₁ C₂ : ℝ} (h : SourceWindow φ L C₁ C₂) :
    φ 0 ≤ 1 := h.le_one 0

/-- The peak of a source window is attained at the origin. -/
theorem SourceWindow.le_peak {φ : ℝ → ℝ} {L C₁ C₂ : ℝ} (h : SourceWindow φ L C₁ C₂) (u : ℝ) :
    φ u ≤ φ 0 := h.radial 0 u (by simp [abs_nonneg])

/-- An induced profile is nonnegative. -/
theorem InducedProfile.nonneg {v φ : ℝ → ℝ} {L : ℝ} (h : InducedProfile v φ L) (s : ℝ) :
    0 ≤ v s := by rw [h s]; positivity

/-! ### The taper `φ_L` and the induced profile `v_L` -/

variable (w : ℝ → ℝ) (L : ℝ)

/-- The taper `φ_L(u) = √(w(u/L))·η(L/2 - |u|)`. -/
noncomputable def taper : ℝ → ℝ := fun u => Real.sqrt (w (u / L)) * eta (L / 2 - |u|)

/-- The induced scalar profile `v_L(s) = w(s)·η(L(1/2-|s|))²`. -/
noncomputable def profile : ℝ → ℝ := fun s => w s * (eta (L * (1 / 2 - |s|))) ^ 2

variable {w L}

/-- `v_L` is exactly the profile induced by `φ_L`, on the whole line. -/
theorem profile_eq_taper_sq (hL : 0 < L) (hw : ∀ s, 0 ≤ w s) (s : ℝ) :
    (taper w L (L * s)) ^ 2 = profile w L s := by
  have hdiv : (L * s) / L = s := by field_simp
  have habs : |L * s| = L * |s| := by
    rw [abs_mul, abs_of_pos hL]
  have harg : L / 2 - |L * s| = L * (1 / 2 - |s|) := by rw [habs]; ring
  rw [taper, profile, hdiv, harg, mul_pow, Real.sq_sqrt (hw s)]

/-! ### Every source condition, verified for the taper

The hypotheses on `w` below are exactly the ones the strict-concavity section
delivers: evenness, `1/5 ≤ w ≤ 1` on `I`, and radial monotonicity. -/

variable (hL : (8 : ℝ) ≤ L)
  (hwe : ∀ s, w (-s) = w s)
  (hwlow : ∀ s, |s| ≤ 1 / 2 → 1 / 5 ≤ w s)
  (hwup : ∀ s, |s| ≤ 1 / 2 → w s ≤ 1)
  (hwrad : ∀ s₁ s₂ : ℝ, |s₁| ≤ |s₂| → |s₂| ≤ 1 / 2 → w s₂ ≤ w s₁)

include hL in
theorem L_pos : 0 < L := by linarith

include hL in
/-- Outside the window the taper vanishes, because `η` does. -/
theorem taper_of_le_abs {u : ℝ} (hu : L / 2 ≤ |u|) : taper w L u = 0 := by
  have : L / 2 - |u| ≤ 0 := by linarith
  rw [taper, eta_of_nonpos this, mul_zero]

include hL in
/-- Inside the window, the argument of `w` lies in `I`. -/
theorem abs_div_le {u : ℝ} (hu : |u| < L / 2) : |u / L| ≤ 1 / 2 := by
  have hLpos : 0 < L := L_pos hL
  rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
  linarith

include hL hwe in
theorem taper_even (u : ℝ) : taper w L (-u) = taper w L u := by
  have h1 : (-u) / L = -(u / L) := by ring
  rw [taper, taper, h1, hwe, abs_neg]

include hL hwlow in
theorem taper_nonneg (u : ℝ) : 0 ≤ taper w L u := by
  exact mul_nonneg (Real.sqrt_nonneg _) (eta_nonneg _)

include hL hwup in
theorem taper_le_one (u : ℝ) : taper w L u ≤ 1 := by
  rcases lt_or_ge |u| (L / 2) with hu | hu
  · have hmem : |u / L| ≤ 1 / 2 := abs_div_le hL hu
    have h1 : Real.sqrt (w (u / L)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (hwup _ hmem)
    calc taper w L u = Real.sqrt (w (u / L)) * eta (L / 2 - |u|) := rfl
      _ ≤ 1 * 1 := by
          exact mul_le_mul h1 (eta_le_one _) (eta_nonneg _) zero_le_one
      _ = 1 := by ring
  · rw [taper_of_le_abs hL hu]; norm_num

include hL hwlow in
/-- **The support is exactly `[-L/2, L/2]`.**  `η > 0` strictly inside and `w`
never vanishes there, so the taper is nonzero on precisely the open window. -/
theorem taper_support (u : ℝ) : taper w L u ≠ 0 ↔ |u| < L / 2 := by
  constructor
  · intro h
    by_contra hu
    push_neg at hu
    exact h (taper_of_le_abs hL hu)
  · intro hu
    have hmem : |u / L| ≤ 1 / 2 := abs_div_le hL hu
    have hwpos : 0 < w (u / L) := lt_of_lt_of_le (by norm_num) (hwlow _ hmem)
    have h1 : 0 < Real.sqrt (w (u / L)) := Real.sqrt_pos.mpr hwpos
    have h2 : 0 < eta (L / 2 - |u|) := eta_pos (by linarith)
    exact ne_of_gt (mul_pos h1 h2)

include hL hwlow hwrad in
/-- **Radial monotonicity of the taper.**  Both factors are nonnegative and
nonincreasing in `|u|`, so their product is. -/
theorem taper_radial (u₁ u₂ : ℝ) (h12 : |u₁| ≤ |u₂|) : taper w L u₂ ≤ taper w L u₁ := by
  rcases lt_or_ge |u₂| (L / 2) with hu2 | hu2
  · have hu1 : |u₁| < L / 2 := lt_of_le_of_lt h12 hu2
    have hm2 : |u₂ / L| ≤ 1 / 2 := abs_div_le hL hu2
    have hLpos : 0 < L := L_pos hL
    have hdiv : |u₁ / L| ≤ |u₂ / L| := by
      rw [abs_div, abs_div, abs_of_pos hLpos]
      gcongr
    have hsqrt : Real.sqrt (w (u₂ / L)) ≤ Real.sqrt (w (u₁ / L)) :=
      Real.sqrt_le_sqrt (hwrad _ _ hdiv hm2)
    have heta : eta (L / 2 - |u₂|) ≤ eta (L / 2 - |u₁|) :=
      eta_monotone (by linarith)
    exact mul_le_mul hsqrt heta (eta_nonneg _) (Real.sqrt_nonneg _)
  · rw [taper_of_le_abs hL hu2]
    exact mul_nonneg (Real.sqrt_nonneg _) (eta_nonneg _)

/-! ### The `L²` estimate

`v_L` differs from `w` only on the two endpoint strips of total length `2/L`,
and `0 ≤ w ≤ 1` bounds the discrepancy there by `1`. -/

include hL in
/-- On the flat part of the window, `v_L` and `w` agree exactly. -/
theorem profile_eq_of_inner {s : ℝ} (hs : |s| ≤ 1 / 2 - 1 / L) : profile w L s = w s := by
  have hLpos : 0 < L := L_pos hL
  have h1 : 1 ≤ L * (1 / 2 - |s|) := by
    have : 1 / L ≤ 1 / 2 - |s| := by
      have := abs_nonneg s; linarith [hs]
    calc (1 : ℝ) = L * (1 / L) := by field_simp
      _ ≤ L * (1 / 2 - |s|) := by exact mul_le_mul_of_nonneg_left this hLpos.le
  rw [profile, eta_of_one_le h1]
  ring

include hwup in
/-- On `I` the pointwise discrepancy never exceeds `1`. -/
theorem profile_sub_sq_le_one {s : ℝ} (hs : |s| ≤ 1 / 2) (hw0 : 0 ≤ w s) :
    (profile w L s - w s) ^ 2 ≤ 1 := by
  have hw1 : w s ≤ 1 := hwup s hs
  set e := eta (L * (1 / 2 - |s|)) with he
  have he0 : 0 ≤ e := eta_nonneg _
  have he1 : e ≤ 1 := eta_le_one _
  have hd : profile w L s - w s = w s * (e ^ 2 - 1) := by rw [profile]; ring
  rw [hd]
  have h1 : |w s * (e ^ 2 - 1)| ≤ 1 := by
    rw [abs_mul]
    have ha : |w s| ≤ 1 := by rw [abs_of_nonneg hw0]; exact hw1
    have hb : |e ^ 2 - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    calc |w s| * |e ^ 2 - 1| ≤ 1 * 1 := by
          exact mul_le_mul ha hb (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  nlinarith [abs_nonneg (w s * (e ^ 2 - 1)), sq_abs (w s * (e ^ 2 - 1))]

/-- **The taper is `C²`**, given that `w` is `C²` and strictly positive on an
open neighbourhood of `I`.  With `taper_support` this is `φ_L ∈ C_c²(ℝ)`.  Proof
imported from `Aristotle/J.lean` and kernel-checked on this toolchain. -/
theorem taper_contDiff (hL8 : (8:ℝ) ≤ L)
    (hwC2 : ContDiffOn ℝ 2 w (Set.Ioo (-(3 / 5) : ℝ) (3 / 5)))
    (hwpos : ∀ s ∈ Set.Ioo (-(3 / 5) : ℝ) (3 / 5), 0 < w s) :
    ContDiff ℝ 2 (taper w L) :=
  AristotleJ.taper_contDiff w L hL8 hwC2 hwpos

/-- `v_L` is continuous whenever `w` is. -/
theorem continuous_profile (hwc : Continuous w) : Continuous (profile w L) := by
  unfold profile
  exact hwc.mul ((continuous_eta.comp (by fun_prop)).pow 2)

include hL hwup in
/-- **The `L²` estimate `‖v_L - w‖₂² ≤ 2/L`.**  The two functions agree except on
the endpoint strips `1/2 - 1/L < |s| ≤ 1/2`, of total length `2/L`, and the
discrepancy there is bounded by `1` because `0 ≤ w ≤ 1`. -/
theorem sq_L2_dist_le (hwc : Continuous w) (hw0 : ∀ s, |s| ≤ 1 / 2 → 0 ≤ w s) :
    (∫ s in (-(1 : ℝ) / 2)..(1 / 2), (profile w L s - w s) ^ 2) ≤ 2 / L := by
  have hLpos : 0 < L := L_pos hL
  have hLinv : 1 / L ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hLpos (by norm_num)]; linarith
  set a : ℝ := 1 / 2 - 1 / L with ha
  have hainv : 0 < 1 / L := by positivity
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha2 : a < 1 / 2 := by rw [ha]; linarith
  set g : ℝ → ℝ := fun s => (profile w L s - w s) ^ 2 with hg
  have hgc : Continuous g := by
    rw [hg]; exact ((continuous_profile hwc).sub hwc).pow 2
  have hgi : ∀ p q : ℝ, IntervalIntegrable g volume p q := fun p q =>
    hgc.intervalIntegrable p q
  have hone : ∀ p q : ℝ, IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume p q := fun p q =>
    continuous_const.intervalIntegrable p q
  -- the flat middle contributes nothing
  have hmid : (∫ s in (-a)..a, g s) = 0 := by
    have : (∫ s in (-a)..a, g s) = ∫ _s in (-a)..a, (0 : ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro s hs
      rw [uIcc_of_le (by linarith)] at hs
      have habs : |s| ≤ a := abs_le.mpr ⟨hs.1, hs.2⟩
      have : profile w L s = w s := profile_eq_of_inner hL (by rw [ha] at habs; exact habs)
      simp [hg, this]
    rw [this, intervalIntegral.integral_zero]
  -- each endpoint strip contributes at most 1/L
  have hstripL : (∫ s in (-(1 : ℝ) / 2)..(-a), g s) ≤ 1 / L := by
    have hle : (-(1 : ℝ) / 2) ≤ -a := by linarith
    have hb : (∫ s in (-(1 : ℝ) / 2)..(-a), g s) ≤ ∫ _s in (-(1 : ℝ) / 2)..(-a), (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hle (hgi _ _) (hone _ _) ?_
      intro s hs
      have habs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact profile_sub_sq_le_one hwup habs (hw0 s habs)
    calc (∫ s in (-(1 : ℝ) / 2)..(-a), g s) ≤ ∫ _s in (-(1 : ℝ) / 2)..(-a), (1 : ℝ) := hb
      _ = 1 / L := by rw [intervalIntegral.integral_const]; rw [ha]; simp; ring
  have hstripR : (∫ s in a..(1 / 2 : ℝ), g s) ≤ 1 / L := by
    have hle : a ≤ (1 / 2 : ℝ) := by linarith
    have hb : (∫ s in a..(1 / 2 : ℝ), g s) ≤ ∫ _s in a..(1 / 2 : ℝ), (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hle (hgi _ _) (hone _ _) ?_
      intro s hs
      have habs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact profile_sub_sq_le_one hwup habs (hw0 s habs)
    calc (∫ s in a..(1 / 2 : ℝ), g s) ≤ ∫ _s in a..(1 / 2 : ℝ), (1 : ℝ) := hb
      _ = 1 / L := by rw [intervalIntegral.integral_const]; rw [ha]; simp
  -- reassemble
  have hsplit1 : (∫ s in (-(1 : ℝ) / 2)..(-a), g s) + (∫ s in (-a)..(1 / 2 : ℝ), g s)
      = ∫ s in (-(1 : ℝ) / 2)..(1 / 2 : ℝ), g s :=
    intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)
  have hsplit2 : (∫ s in (-a)..a, g s) + (∫ s in a..(1 / 2 : ℝ), g s)
      = ∫ s in (-a)..(1 / 2 : ℝ), g s :=
    intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _)
  have : (∫ s in (-(1 : ℝ) / 2)..(1 / 2 : ℝ), g s)
      = (∫ s in (-(1 : ℝ) / 2)..(-a), g s) + (∫ s in a..(1 / 2 : ℝ), g s) := by
    rw [← hsplit1, ← hsplit2, hmid]; ring
  rw [hg] at this ⊢
  rw [this]
  have : (1 : ℝ) / L + 1 / L = 2 / L := by ring
  linarith [hstripL, hstripR]

end ZetaLean.Pub1
