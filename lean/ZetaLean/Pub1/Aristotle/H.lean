import Mathlib

namespace AristotleH

open MeasureTheory

/-! Auxiliary lemmas for the amplitude sandwich and evenness of the solution of
`w + T w = 1` on `I = [-1/2, 1/2]`. -/

private lemma aux_abs_sub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rcases abs_cases x with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases abs_cases y with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases abs_cases (x - y) with ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;> linarith

private lemma aux_cont_shift (K : ℝ → ℝ) (hKc : Continuous K) (s : ℝ) :
    Continuous fun t : ℝ => K (s - t) :=
  hKc.comp (continuous_const.sub continuous_id)

private lemma aux_intble (K g : ℝ → ℝ) (hKc : Continuous K) (hg : Continuous g) (s : ℝ) :
    IntervalIntegrable (fun t => K (s - t) * g t) volume (-(1:ℝ)/2) (1/2) :=
  ((aux_cont_shift K hKc s).mul hg).intervalIntegrable _ _

/-- The least-upper-bound package for a bounded function on `ℝ`. -/
private lemma aux_sup (f : ℝ → ℝ) (hb : ∃ C, ∀ s, |f s| ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ s, |f s| ≤ M) ∧ ∀ N : ℝ, (∀ s, |f s| ≤ N) → M ≤ N := by
  obtain ⟨C, hC⟩ := hb
  have hbdd : BddAbove (Set.range fun s => |f s|) := ⟨C, by rintro _ ⟨s, rfl⟩; exact hC s⟩
  refine ⟨sSup (Set.range fun s => |f s|), ?_, ?_, ?_⟩
  · exact (abs_nonneg (f 0)).trans (le_csSup hbdd ⟨0, rfl⟩)
  · exact fun s => le_csSup hbdd ⟨s, rfl⟩
  · intro N hN
    exact csSup_le ⟨|f 0|, ⟨0, rfl⟩⟩ (by rintro _ ⟨s, rfl⟩; exact hN s)

/-- The row-mass bound: the integral operator shrinks the sup-bound by `4/9`. -/
private lemma aux_key (K : ℝ → ℝ) (hKc : Continuous K)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)|) ≤ 4 / 9)
    (g : ℝ → ℝ) (hgc : Continuous g) (M : ℝ) (hM : ∀ t, |g t| ≤ M) (s : ℝ) :
    |∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * g t| ≤ 4 / 9 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hab : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
  have hc := aux_cont_shift K hKc s
  have h1 : |∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * g t|
      ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t) * g t| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have h2 : (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t) * g t|)
      ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)| * M := by
    refine intervalIntegral.integral_mono_on hab
      (((hc.mul hgc).abs).intervalIntegrable _ _)
      ((hc.abs.mul continuous_const).intervalIntegrable _ _) ?_
    intro x _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have h3 : (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)| * M)
      = (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)|) * M :=
    intervalIntegral.integral_mul_const _ _
  have h4 : (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)|) * M ≤ 4 / 9 * M :=
    mul_le_mul_of_nonneg_right (hrow s) hM0
  linarith [h1, h2, h3.le, h3.ge, h4]

/-- Amplitude sandwich `1/5 ≤ w ≤ 1` on `I = [-1/2, 1/2]`.
The hypothesis `hKeven` is kept as requested, but the proof does not need it. -/
theorem solution_bounds
    (K : ℝ → ℝ) (hKc : Continuous K) (hKnn : ∀ x, 0 ≤ K x) (hKeven : ∀ x, K (-x) = K x)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t)) ≤ 4 / 9)
    (w : ℝ → ℝ) (hwc : Continuous w) (hwb : ∃ C, ∀ s, |w s| ≤ C)
    (hw : ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t) = 1) :
    (∀ s : ℝ, |s| ≤ 1 / 2 → 1 / 5 ≤ w s) ∧ (∀ s : ℝ, |s| ≤ 1 / 2 → w s ≤ 1) := by
  have hab : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
  have hrow' : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)|) ≤ 4 / 9 := by
    intro s
    have : (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)|) = ∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      exact abs_of_nonneg (hKnn _)
    rw [this]; exact hrow s
  obtain ⟨M, hM0, hMle, hMleast⟩ := aux_sup w hwb
  have hkey : ∀ s, |∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t| ≤ 4 / 9 * M :=
    aux_key K hKc hrow' w hwc M hMle
  have hstep : M ≤ 1 + 4 / 9 * M := by
    refine hMleast _ (fun s => ?_)
    have h := hw s
    have h2 := hkey s
    have h3 : w s = 1 - ∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t := by linarith
    rw [h3]
    calc |1 - ∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t|
        ≤ |(1:ℝ)| + |∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t| := aux_abs_sub _ _
      _ ≤ 1 + 4 / 9 * M := by rw [abs_one]; linarith
  have hM95 : M ≤ 9 / 5 := by linarith
  have hlow : ∀ s : ℝ, 1 / 5 ≤ w s := by
    intro s
    have h := hw s
    have h2 := hkey s
    have h3 := abs_le.1 h2
    nlinarith [h3.1, h3.2]
  refine ⟨fun s _ => hlow s, fun s _ => ?_⟩
  have hnn : 0 ≤ ∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t := by
    refine intervalIntegral.integral_nonneg hab (fun u _ => ?_)
    have := hlow u
    have := hKnn (s - u)
    nlinarith
  have := hw s
  linarith

/-- Evenness of the solution of `w + T w = 1`. -/
theorem solution_even
    (K : ℝ → ℝ) (hKc : Continuous K) (hKeven : ∀ x, K (-x) = K x)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K (s - t)|) ≤ 4 / 9)
    (w : ℝ → ℝ) (hwc : Continuous w) (hwb : ∃ C, ∀ s, |w s| ≤ C)
    (hw : ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t) = 1) :
    ∀ s : ℝ, w (-s) = w s := by
  -- the reflected function solves the same equation
  have hrefl : ∀ s : ℝ,
      w (-s) + (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w (-t)) = 1 := by
    intro s
    have hchg : (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w (-t))
        = ∫ t in (-(1:ℝ)/2)..(1/2), K (-s - t) * w t := by
      have h1 : (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w (-t))
          = ∫ t in (-(1:ℝ)/2)..(1/2), (fun x : ℝ => K (-s - x) * w x) (-t) := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        simp only
        have : K (s - x) = K (-s - -x) := by
          rw [← hKeven (s - x)]; ring_nf
        rw [this]
      rw [h1, intervalIntegral.integral_comp_neg (fun x : ℝ => K (-s - x) * w x)]
      norm_num
    rw [hchg]
    exact hw (-s)
  -- the difference solves the homogeneous equation, hence vanishes
  set d : ℝ → ℝ := fun s => w s - w (-s) with hd
  have hdc : Continuous d := hwc.sub (hwc.comp continuous_neg)
  have hdb : ∃ C, ∀ s, |d s| ≤ C := by
    obtain ⟨C, hC⟩ := hwb
    exact ⟨C + C, fun s => (aux_abs_sub _ _).trans (add_le_add (hC s) (hC (-s)))⟩
  have hdeq : ∀ s : ℝ, d s + (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * d t) = 0 := by
    intro s
    have h1 := hw s
    have h2 := hrefl s
    have hsplit : (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * d t)
        = (∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w t)
          - ∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * w (-t) := by
      rw [← intervalIntegral.integral_sub (aux_intble K w hKc hwc s)
        (aux_intble K (fun t => w (-t)) hKc (hwc.comp continuous_neg) s)]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [hd]
      ring
    rw [hsplit]
    simp only [hd]
    linarith
  obtain ⟨D, hD0, hDle, hDleast⟩ := aux_sup d hdb
  have hkey : ∀ s, |∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * d t| ≤ 4 / 9 * D :=
    aux_key K hKc hrow d hdc D hDle
  have hstep : D ≤ 4 / 9 * D := by
    refine hDleast _ (fun s => ?_)
    have h := hdeq s
    have h2 := hkey s
    have h3 : d s = -(∫ t in (-(1:ℝ)/2)..(1/2), K (s - t) * d t) := by linarith
    rw [h3, abs_neg]
    exact h2
  have hD : D = 0 := le_antisymm (by linarith) hD0
  intro s
  have := hDle s
  rw [hD] at this
  have : d s = 0 := abs_eq_zero.1 (le_antisymm this (abs_nonneg _))
  simp only [hd] at this
  linarith


end AristotleH