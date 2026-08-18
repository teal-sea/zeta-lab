import Mathlib

namespace AristotleW

/-- On the open interval `Ioo a b`, pointwise first and second derivatives with a
continuous second derivative give `ContDiffOn ℝ 2`. -/
theorem contDiffOn_two_of_hasDerivAt
    (f D1 D2 : ℝ → ℝ) (a b : ℝ)
    (h1 : ∀ s ∈ Set.Ioo a b, HasDerivAt f (D1 s) s)
    (h2 : ∀ s ∈ Set.Ioo a b, HasDerivAt D1 (D2 s) s)
    (hc : ContinuousOn D2 (Set.Ioo a b)) :
    ContDiffOn ℝ 2 f (Set.Ioo a b) := by
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hd1 : ∀ s ∈ Set.Ioo a b, deriv f s = D1 s := fun s hs => (h1 s hs).deriv
  have hd2 : ∀ s ∈ Set.Ioo a b, deriv D1 s = D2 s := fun s hs => (h2 s hs).deriv
  have step1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) := by
    have hD1 : ContDiffOn ℝ 1 D1 (Set.Ioo a b) := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
        contDiffOn_succ_iff_deriv_of_isOpen hopen]
      refine ⟨fun s hs => (h2 s hs).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      rw [contDiffOn_zero]
      exact hc.congr hd2
    exact hD1.congr hd1
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen hopen]
  exact ⟨fun s hs => (h1 s hs).differentiableAt.differentiableWithinAt, by simp, step1⟩

/-- Continuous functions on the compact interval `Icc a b` are bounded on `Ioo a b`. -/
theorem bounded_of_continuousOn_Icc
    (D1 D2 : ℝ → ℝ) (a b : ℝ)
    (hD1 : ContinuousOn D1 (Set.Icc a b)) (hD2 : ContinuousOn D2 (Set.Icc a b)) :
    ∃ B1 B2 : ℝ, (∀ s ∈ Set.Ioo a b, |D1 s| ≤ B1) ∧ (∀ s ∈ Set.Ioo a b, |D2 s| ≤ B2) := by
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hD1
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hD2
  refine ⟨C1, C2, fun s hs => ?_, fun s hs => ?_⟩
  · simpa [Real.norm_eq_abs] using hC1 s (Set.Ioo_subset_Icc_self hs)
  · simpa [Real.norm_eq_abs] using hC2 s (Set.Ioo_subset_Icc_self hs)


end AristotleW