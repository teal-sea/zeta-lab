/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Setting
import ZetaLean.Pub1.Window
import ZetaLean.Pub1.Concavity

/-!
# Pub 1 strong closure: the principal theorem

```
      sup_{v ∈ 𝒜_source}  ⟨1,v⟩² / ⟨Av,v⟩  =  ⟨1, A⁻¹1⟩  =  c*,
      inf_{v ∈ 𝒜_source}  ⟨Av,v⟩ / ⟨1,v⟩²  =  1/c*.
```

The orientation is load-bearing and is pinned by proving both: it is the
quotient with `⟨1,v⟩²` in the *numerator* that is maximized, and its reciprocal
that is minimized.  `orientation_not_symmetric` records that the two are not
interchangeable.

`StrongClosureData` is the interface: it names exactly the analytic facts the
argument consumes.  Fields marked *discharged* below have unconditional proofs
in this development; the rest are the remaining formal obligations, and are
listed in `ZetaLean/Pub1/OBLIGATIONS.md`.
-/

open Filter Topology MeasureTheory Set

namespace ZetaLean.Pub1

/-! ### The two quotients -/

/-- The **maximizing** quotient `c(v) = ⟨1,v⟩² / ⟨Av,v⟩`. -/
noncomputable def quot (v : ℝ → ℝ) : ℝ := massI v ^ 2 / energyA v

/-- The **reciprocal** quotient `⟨Av,v⟩ / ⟨1,v⟩²`, whose infimum is `1/c*`. -/
noncomputable def recipQuot (v : ℝ → ℝ) : ℝ := energyA v / massI v ^ 2

theorem recipQuot_eq_inv (v : ℝ → ℝ) : recipQuot v = (quot v)⁻¹ := by
  rw [recipQuot, quot, inv_div]

/-- Members of the source-admissible class are continuous: they are squares of
`C²` windows. -/
theorem sourceAdmissible_continuous {C₁ C₂ : ℝ} {v : ℝ → ℝ}
    (hv : v ∈ sourceAdmissible C₁ C₂) : Continuous v := by
  obtain ⟨φ, L, hφ, hind⟩ := hv
  have : v = fun s => (φ (L * s)) ^ 2 := funext hind
  rw [this]
  exact ((hφ.smooth.continuous.comp (continuous_const.mul continuous_id)).pow 2)

/-- Members of the source-admissible class are nonnegative. -/
theorem sourceAdmissible_nonneg {C₁ C₂ : ℝ} {v : ℝ → ℝ}
    (hv : v ∈ sourceAdmissible C₁ C₂) (s : ℝ) : 0 ≤ v s := by
  obtain ⟨φ, L, -, hind⟩ := hv
  rw [hind s]; positivity

/-- Admissible profiles are strictly positive on the open interval: the support
condition says `φ ≠ 0` exactly on `(-L/2, L/2)`, which pulls back to `(-1/2,1/2)`. -/
theorem sourceAdmissible_pos {C₁ C₂ : ℝ} {v : ℝ → ℝ} (hv : v ∈ sourceAdmissible C₁ C₂)
    {s : ℝ} (hs : s ∈ Ioo (-(1 : ℝ) / 2) (1 / 2)) : 0 < v s := by
  obtain ⟨φ, L, hφ, hind⟩ := hv
  have hL : (0 : ℝ) < L := by linarith [hφ.scale]
  have hsabs : |s| < 1 / 2 := abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩
  have habs : |L * s| < L / 2 := by
    rw [abs_mul, abs_of_pos hL]
    nlinarith
  have hne : φ (L * s) ≠ 0 := (hφ.support (L * s)).mpr habs
  have hpos : 0 < φ (L * s) := lt_of_le_of_ne (hφ.nonneg _) (Ne.symm hne)
  rw [hind s]
  exact pow_pos hpos 2

/-- **Discharged.**  Every source-admissible profile has strictly positive
energy: it is positive on the open interval, and `A` is coercive with constant
`5/9`. -/
theorem energyA_pos_of_admissible {C₁ C₂ : ℝ} {v : ℝ → ℝ}
    (hv : v ∈ sourceAdmissible C₁ C₂) : 0 < energyA v := by
  have hc : Continuous v := sourceAdmissible_continuous hv
  have hns : 0 < normSqI v := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((hc.pow 2).intervalIntegrable _ _) ?_ (by norm_num)
    intro x hx
    exact pow_pos (sourceAdmissible_pos hv hx) 2
  have := energyA_coercive v hc
  linarith

/-- **Discharged.**  `c* = ⟨1, w⟩ ≥ 1/5 > 0`, from the amplitude floor on `w`. -/
theorem cStar_pos_of_lower {w : ℝ → ℝ} (hwc : Continuous w)
    (h5 : ∀ s : ℝ, |s| ≤ 1 / 2 → 1 / 5 ≤ w s) : 0 < cStar w := by
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun _ : ℝ => (1 : ℝ) / 5) (g := w) (a := -(1 : ℝ) / 2) (b := 1 / 2)
    (by norm_num) (continuous_const.intervalIntegrable _ _) (hwc.intervalIntegrable _ _)
    (fun x hx => h5 x (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  rw [cStar, massI]
  have hval : ((1 : ℝ) / 2 - -(1 : ℝ) / 2) * ((1 : ℝ) / 5) = 1 / 5 := by norm_num
  rw [intervalIntegral.integral_const, smul_eq_mul, hval] at hmono
  linarith

/-! ### The interface -/

/-- The analytic inputs the strong-closure theorem consumes, named one by one so
that what is proved and what is still open can be read off. -/
structure StrongClosureData (w : ℝ → ℝ) (C₁ C₂ : ℝ) : Prop where
  /-- `w` solves `Aw = 1`.  *Discharged* by `exists_profile`. -/
  isProfile : IsProfile w
  /-- `⟨Aw, w⟩ = ⟨1, w⟩`, the representation identity at `v = w`. -/
  energy_w : energyA w = massI w
  /-- `c* = ⟨1, w⟩ > 0`. -/
  cStar_pos : 0 < massI w
  /-- **The ambient upper bound**, energy Cauchy-Schwarz: `⟨1,v⟩² ≤ c*·⟨Av,v⟩`
  for every `v`, admissible or not. -/
  upper : ∀ v : ℝ → ℝ, Continuous v → massI v ^ 2 ≤ massI w * energyA v
  /-- The constructed sequence lies in the source-admissible class. -/
  member : ∀ n : ℕ, profile w (8 + (n : ℝ)) ∈ sourceAdmissible C₁ C₂
  /-- Every admissible profile has strictly positive energy. -/
  energy_pos : ∀ v ∈ sourceAdmissible C₁ C₂, 0 < energyA v
  /-- **`L²` continuity of the quotient** along the constructed sequence. -/
  quot_tendsto : Tendsto (fun n : ℕ => quot (profile w (8 + (n : ℝ)))) atTop (𝓝 (massI w))

/-! ### The principal theorem -/

variable {w : ℝ → ℝ} {C₁ C₂ : ℝ}

/-- **Every** source-admissible profile is below `c*`.  This half needs nothing
about admissibility: it is the ambient variational theorem. -/
theorem quot_le_cStar (h : StrongClosureData w C₁ C₂) {v : ℝ → ℝ}
    (hv : v ∈ sourceAdmissible C₁ C₂) : quot v ≤ cStar w := by
  have hden : 0 < energyA v := h.energy_pos v hv
  rw [quot, cStar, div_le_iff₀ hden]
  exact h.upper v (sourceAdmissible_continuous hv)

/-- **PUB 1 SOURCE-ADMISSIBLE STRONG CLOSURE.**

`sup_{v ∈ 𝒜_source} ⟨1,v⟩²/⟨Av,v⟩ = ⟨1, A⁻¹1⟩ = c*`.

The upper bound is energy Cauchy-Schwarz, valid for every `v`; the reverse
inequality is supplied by the explicit endpoint-tapered sequence, which lies in
the class and whose quotient converges to `c*`. -/
theorem pub1_strong_closure_of_data (h : StrongClosureData w C₁ C₂) :
    IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) := by
  constructor
  · rintro q ⟨v, hv, rfl⟩
    exact quot_le_cStar h hv
  · intro b hb
    have hle : ∀ n : ℕ, quot (profile w (8 + (n : ℝ))) ≤ b := fun n =>
      hb ⟨profile w (8 + (n : ℝ)), h.member n, rfl⟩
    exact le_of_tendsto h.quot_tendsto (Eventually.of_forall hle)

/-- The same statement as an `sSup`. -/
theorem pub1_strong_closure_sSup_of_data (h : StrongClosureData w C₁ C₂) :
    sSup (quot '' sourceAdmissible C₁ C₂) = cStar w :=
  (pub1_strong_closure_of_data h).csSup_eq
    ⟨quot (profile w 8), ⟨profile w (8 + ((0 : ℕ) : ℝ)), h.member 0, by norm_num⟩⟩

/-- **The reciprocal orientation.**

`inf_{v ∈ 𝒜_source} ⟨Av,v⟩/⟨1,v⟩² = 1/c*`.  Proving both this and
`pub1_strong_closure` is what pins the orientation: the maximized quotient is
the one with `⟨1,v⟩²` in the numerator. -/
theorem pub1_strong_closure_reciprocal_of_data (h : StrongClosureData w C₁ C₂)
    (hmass : ∀ v ∈ sourceAdmissible C₁ C₂, massI v ≠ 0) :
    IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ := by
  have hcpos : 0 < cStar w := h.cStar_pos
  have hqpos : ∀ v ∈ sourceAdmissible C₁ C₂, 0 < quot v := by
    intro v hv
    have hden : 0 < energyA v := h.energy_pos v hv
    have hnum : 0 < massI v ^ 2 := by
      have := hmass v hv; positivity
    exact div_pos hnum hden
  constructor
  · rintro q ⟨v, hv, rfl⟩
    rw [recipQuot_eq_inv]
    have := one_div_le_one_div_of_le (hqpos v hv) (quot_le_cStar h hv)
    simpa [one_div] using this
  · intro b hb
    have hle : ∀ n : ℕ, b ≤ (quot (profile w (8 + (n : ℝ))))⁻¹ := by
      intro n
      have := hb ⟨profile w (8 + (n : ℝ)), h.member n, rfl⟩
      rwa [recipQuot_eq_inv] at this
    have htend : Tendsto (fun n : ℕ => (quot (profile w (8 + (n : ℝ))))⁻¹) atTop
        (𝓝 (cStar w)⁻¹) := h.quot_tendsto.inv₀ (ne_of_gt hcpos)
    exact ge_of_tendsto htend (Eventually.of_forall hle)

/-- The two orientations are genuinely different quantities: for a profile whose
energy differs from its mass squared, the quotient and its reciprocal disagree.
This is a guard against silently swapping numerator and denominator. -/
theorem orientation_not_symmetric {v : ℝ → ℝ} (hE : 0 < energyA v) (hm : massI v ≠ 0)
    (hne : massI v ^ 2 ≠ energyA v) : quot v ≠ recipQuot v := by
  rw [quot, recipQuot]
  intro hcontra
  have h2 : massI v ^ 2 ≠ 0 := by positivity
  rw [div_eq_div_iff (ne_of_gt hE) h2] at hcontra
  apply hne
  nlinarith [hcontra, sq_nonneg (massI v ^ 2 - energyA v)]

/-! ### Discharged inputs

The `L²` closure of the construction is unconditional: it follows from the
`2/L` estimate proved in `ZetaLean.Pub1.Window`. -/

/-- **`L²` convergence of the induced profiles**, unconditionally.  This is the
`‖v_L - w‖₂² ≤ 2/L` estimate, pushed to the limit. -/
theorem tendsto_L2_zero (hwc : Continuous w)
    (hwup : ∀ s, |s| ≤ 1 / 2 → w s ≤ 1) (hw0 : ∀ s, |s| ≤ 1 / 2 → 0 ≤ w s) :
    Tendsto (fun n : ℕ => normSqI (fun s => profile w (8 + (n : ℝ)) s - w s)) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      normSqI (fun s => profile w (8 + (n : ℝ)) s - w s) ≤ 2 / (8 + (n : ℝ)) := by
    intro n
    have hL : (8 : ℝ) ≤ 8 + (n : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact sq_L2_dist_le hL hwup hwc hw0
  have hnn : ∀ n : ℕ, 0 ≤ normSqI (fun s => profile w (8 + (n : ℝ)) s - w s) := fun n =>
    normSqI_nonneg _
  have htop : Tendsto (fun n : ℕ => 2 / (8 + (n : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (8 : ℝ) + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ 8 tendsto_natCast_atTop_atTop
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
  exact squeeze_zero hnn hbound htop

end ZetaLean.Pub1
