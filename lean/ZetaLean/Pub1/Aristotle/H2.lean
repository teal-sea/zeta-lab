import Mathlib

namespace AristotleH2

open MeasureTheory

/-! ### Auxiliary lemmas -/

/-- A continuous two-variable kernel is continuous in its second variable. -/
private lemma kernel_slice_cont {K : ℝ → ℝ → ℝ}
    (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2) (s : ℝ) :
    Continuous fun t : ℝ => K s t :=
  hKc.comp (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (by fun_prop)

/-- Row-bound estimate: if `|v| ≤ M` and the row `∫ |K s ·| ≤ θ`, then the integral operator
applied to `v` is bounded by `M * θ`. -/
private lemma abs_integral_kernel_le {K : ℝ → ℝ → ℝ}
    (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    {v : ℝ → ℝ} (hvc : Continuous v) {M θ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, |v t| ≤ M) {s : ℝ}
    (hrow : (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) ≤ θ) :
    |∫ t in (-(1:ℝ)/2)..(1/2), K s t * v t| ≤ M * θ := by
  have hle : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
  have hKs : Continuous fun t : ℝ => K s t := kernel_slice_cont hKc s
  have h1 : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * v t|
      ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K s t * v t| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have h2 : (∫ t in (-(1:ℝ)/2)..(1/2), |K s t * v t|)
      ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K s t| * M := by
    apply intervalIntegral.integral_mono_on hle
    · exact ((hKs.mul hvc).abs).intervalIntegrable _ _
    · exact (hKs.abs.mul continuous_const).intervalIntegrable _ _
    · intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have h3 : (∫ t in (-(1:ℝ)/2)..(1/2), |K s t| * M)
      = (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) * M := by
    simp [intervalIntegral.integral_mul_const]
  have h4 := h1.trans (h2.trans (le_of_eq h3))
  calc |∫ t in (-(1:ℝ)/2)..(1/2), K s t * v t|
      ≤ (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) * M := h4
    _ ≤ θ * M := by nlinarith
    _ = M * θ := by ring

/-- If a bounded function satisfies a self-improving bound `C ↦ a + b * C` with `b < 1`,
then it is bounded by the fixed point `a / (1 - b)`. -/
private lemma sup_fixed_bound (v : ℝ → ℝ) (hb : ∃ C, ∀ s, |v s| ≤ C)
    (a b : ℝ) (hb1 : b < 1)
    (hstep : ∀ C : ℝ, 0 ≤ C → (∀ s, |v s| ≤ C) → ∀ s, |v s| ≤ a + b * C) :
    ∀ s, |v s| ≤ a / (1 - b) := by
  set S : Set ℝ := {C : ℝ | ∀ s, |v s| ≤ C} with hS
  have hne : S.Nonempty := hb
  have hbdd : BddBelow S := ⟨0, fun C hC => le_trans (abs_nonneg (v 0)) (hC 0)⟩
  set M := sInf S with hM
  have hMmem : ∀ s, |v s| ≤ M := fun s => le_csInf hne (fun C hC => hC s)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (v 0)) (hMmem 0)
  have hle : M ≤ a + b * M := csInf_le hbdd (hstep M hM0 hMmem)
  have hfix : M ≤ a / (1 - b) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  exact fun s => (hMmem s).trans hfix

/-! ### Main theorems -/

theorem solution_bounds
    (K : ℝ → ℝ → ℝ) (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K s t) ≤ 4 / 9)
    (w : ℝ → ℝ) (hwc : Continuous w) (hwb : ∃ C, ∀ s, |w s| ≤ C)
    (hw : ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t) = 1) :
    (∀ s : ℝ, 1 / 5 ≤ w s) ∧ (∀ s : ℝ, w s ≤ 1) := by
  have hle : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
  have habs : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) ≤ 4 / 9 := by
    intro s
    have h : (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) = ∫ t in (-(1:ℝ)/2)..(1/2), K s t :=
      intervalIntegral.integral_congr (fun x _ => abs_of_nonneg (hKnn s x))
    rw [h]; exact hrow s
  have hstep : ∀ C : ℝ, 0 ≤ C → (∀ s, |w s| ≤ C) → ∀ s, |w s| ≤ 1 + (4/9) * C := by
    intro C hC0 hCb s
    have hI : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t| ≤ C * (4/9) :=
      abs_integral_kernel_le hKc hwc hC0 hCb (habs s)
    have hIb := abs_le.mp hI
    have hws : w s = 1 - ∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t := by
      have := hw s; linarith
    rw [hws, abs_le]
    constructor <;> linarith [hIb.1, hIb.2]
  have hbnd : ∀ s, |w s| ≤ 9 / 5 := by
    have := sup_fixed_bound w hwb 1 (4/9) (by norm_num) hstep
    intro s
    have h := this s
    norm_num at h
    linarith
  have hlow : ∀ s : ℝ, 1 / 5 ≤ w s := by
    intro s
    have hI : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t| ≤ (9/5) * (4/9) :=
      abs_integral_kernel_le hKc hwc (by norm_num) hbnd (habs s)
    have hIb := abs_le.mp hI
    have := hw s
    linarith [hIb.2]
  refine ⟨hlow, ?_⟩
  intro s
  have hInn : 0 ≤ ∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t := by
    apply intervalIntegral.integral_nonneg hle
    intro t _
    exact mul_nonneg (hKnn s t) (le_trans (by norm_num) (hlow t))
  have := hw s
  linarith

theorem solution_unique
    (K : ℝ → ℝ → ℝ) (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) ≤ θ)
    (w₁ w₂ : ℝ → ℝ) (hc₁ : Continuous w₁) (hc₂ : Continuous w₂)
    (hb₁ : ∃ C, ∀ s, |w₁ s| ≤ C) (hb₂ : ∃ C, ∀ s, |w₂ s| ≤ C)
    (he₁ : ∀ s : ℝ, w₁ s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w₁ t) = 1)
    (he₂ : ∀ s : ℝ, w₂ s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w₂ t) = 1) :
    ∀ s, w₁ s = w₂ s := by
  set d : ℝ → ℝ := fun s => w₁ s - w₂ s with hd
  have hdc : Continuous d := hc₁.sub hc₂
  have hdb : ∃ C, ∀ s, |d s| ≤ C := by
    obtain ⟨C₁, hC₁⟩ := hb₁
    obtain ⟨C₂, hC₂⟩ := hb₂
    refine ⟨C₁ + C₂, fun s => ?_⟩
    have h1 := abs_le.mp (hC₁ s)
    have h2 := abs_le.mp (hC₂ s)
    simp only [hd]
    rw [abs_le]
    constructor <;> linarith
  have hsplit : ∀ s : ℝ, (∫ t in (-(1:ℝ)/2)..(1/2), K s t * d t)
      = (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w₁ t)
        - (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w₂ t) := by
    intro s
    have hKs : Continuous fun t : ℝ => K s t := kernel_slice_cont hKc s
    have h : (∫ t in (-(1:ℝ)/2)..(1/2), K s t * d t)
        = ∫ t in (-(1:ℝ)/2)..(1/2), (K s t * w₁ t - K s t * w₂ t) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp [hd, mul_sub]
    rw [h]
    exact intervalIntegral.integral_sub ((hKs.mul hc₁).intervalIntegrable _ _)
      ((hKs.mul hc₂).intervalIntegrable _ _)
  have heq : ∀ s : ℝ, d s = -(∫ t in (-(1:ℝ)/2)..(1/2), K s t * d t) := by
    intro s
    rw [hsplit s]
    have h1 := he₁ s
    have h2 := he₂ s
    simp only [hd]
    linarith
  have hstep : ∀ C : ℝ, 0 ≤ C → (∀ s, |d s| ≤ C) → ∀ s, |d s| ≤ 0 + θ * C := by
    intro C hC0 hCb s
    have hI : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * d t| ≤ C * θ :=
      abs_integral_kernel_le hKc hdc hC0 hCb (hrow s)
    rw [heq s, abs_neg]
    calc |∫ t in (-(1:ℝ)/2)..(1/2), K s t * d t| ≤ C * θ := hI
      _ = 0 + θ * C := by ring
  have hzero := sup_fixed_bound d hdb 0 θ hθ1 hstep
  intro s
  have h := hzero s
  simp only [zero_div] at h
  have : d s = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  simp only [hd] at this
  linarith

theorem solution_even
    (K : ℝ → ℝ → ℝ) (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKrefl : ∀ s t, K (-s) (-t) = K s t)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) ≤ 4 / 9)
    (w : ℝ → ℝ) (hwc : Continuous w) (hwb : ∃ C, ∀ s, |w s| ≤ C)
    (hw : ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t) = 1) :
    ∀ s : ℝ, w (-s) = w s := by
  have hrefl : ∀ (s : ℝ), (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w (-t))
      = ∫ x in (-(1:ℝ)/2)..(1/2), K (-s) x * w x := by
    intro s
    have h := intervalIntegral.integral_comp_neg (a := (-(1:ℝ)/2)) (b := (1:ℝ)/2)
      (f := fun x : ℝ => K s (-x) * w x)
    simp only [neg_neg] at h
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring] at *
    rw [h, neg_neg]
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    rw [show K s (-x) = K (-s) x by rw [← hKrefl (-s) x, neg_neg]]
  have hrefl_eq : ∀ s : ℝ, w (-s) + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w (-t)) = 1 := by
    intro s
    rw [hrefl s]
    exact hw (-s)
  have hbneg : ∃ C, ∀ s, |w (-s)| ≤ C := by
    obtain ⟨C, hC⟩ := hwb
    exact ⟨C, fun s => hC (-s)⟩
  exact solution_unique K hKc (4/9) (by norm_num) (by norm_num) hrow
    (fun s => w (-s)) w (hwc.comp continuous_neg) hwc hbneg hwb hrefl_eq hw


end AristotleH2