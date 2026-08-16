import Mathlib

namespace AristotleN

open MeasureTheory intervalIntegral

/-- The split form of a convolution against the even kernel `x ↦ f |x|`. -/
noncomputable def splitKernelIntegral (f v : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ t in (-(1:ℝ)/2)..s, f (s - t) * v t) + ∫ t in s..(1/2:ℝ), f (t - s) * v t

section Aux

/-- Moving endpoint with a parameter: the derivative at `s` of `σ ↦ ∫ t in s..σ, φ σ t`
is `φ s s`. -/
private lemma hasDerivAt_moving (φ : ℝ → ℝ → ℝ)
    (hφ : Continuous fun p : ℝ × ℝ => φ p.1 p.2) (s : ℝ) :
    HasDerivAt (fun σ => ∫ t in s..σ, φ σ t) (φ s s) s := by
  have hcont : ∀ σ : ℝ, Continuous fun t => φ σ t :=
    fun σ => hφ.comp (continuous_const.prodMk continuous_id)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp (hφ.continuousAt (x := (s, s))) ε hε
  filter_upwards [Metric.ball_mem_nhds s hδpos] with σ hσ
  have hσ' : |σ - s| < δ := by
    have := Metric.mem_ball.mp hσ
    rwa [Real.dist_eq] at this
  have h1 : (∫ t in s..σ, φ σ t) - (∫ t in s..s, φ s t) - (σ - s) • φ s s
      = ∫ t in s..σ, (φ σ t - φ s s) := by
    rw [intervalIntegral.integral_sub ((hcont σ).intervalIntegrable _ _)
      (_root_.intervalIntegrable_const), intervalIntegral.integral_const,
      intervalIntegral.integral_same]
    ring
  rw [h1]
  have hb : ∀ t ∈ Set.uIoc s σ, ‖φ σ t - φ s s‖ ≤ ε := by
    intro t ht
    have hts : |t - s| ≤ |σ - s| := by
      rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc ht) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_le]
        exact ⟨by linarith [abs_nonneg (σ - s)], by linarith [le_abs_self (σ - s)]⟩
      · rw [abs_le]
        exact ⟨by linarith [neg_abs_le (σ - s)], by linarith [abs_nonneg (σ - s)]⟩
    have hd : dist ((σ, t) : ℝ × ℝ) (s, s) < δ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq]
      exact max_lt hσ' (lt_of_le_of_lt hts hσ')
    have h2 := hδ hd
    rw [Real.dist_eq] at h2
    rw [Real.norm_eq_abs]
    exact h2.le
  calc ‖∫ t in s..σ, (φ σ t - φ s s)‖ ≤ ε * |σ - s| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = ε * ‖σ - s‖ := by rw [Real.norm_eq_abs]

/-- Differentiation under the integral sign, left form. -/
private lemma hasDerivAt_param_left (g v : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hv : Continuous v)
    (a b s : ℝ) :
    HasDerivAt (fun σ => ∫ t in a..b, g (σ - t) * v t)
      (∫ t in a..b, deriv g (s - t) * v t) s := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv_one
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := s - 1 - max a b) (b := s + 1 - min a b)
    ).exists_bound_of_continuousOn hg'c.continuousOn
  have hderiv : ∀ t x : ℝ, HasDerivAt (fun x => g (x - t) * v t) (deriv g (x - t) * v t) x := by
    intro t x
    have h1 : HasDerivAt (fun x : ℝ => g (x - t)) (deriv g (x - t)) x := by
      have := (hgd (x - t)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const t)
      exact this.congr_deriv (by ring)
    exact h1.mul_const (v t)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x t => g (x - t) * v t) (F' := fun x t => deriv g (x - t) * v t)
    (x₀ := s) (s := Metric.ball s 1) (bound := fun t => M * ‖v t‖)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun _ =>
      ((hgc.comp (continuous_const.sub continuous_id)).mul hv).aestronglyMeasurable)
    (((hgc.comp (continuous_const.sub continuous_id)).mul hv).intervalIntegrable a b)
    ((hg'c.comp (continuous_const.sub continuous_id)).mul hv).aestronglyMeasurable
    (Filter.Eventually.of_forall (by
      intro t ht x hx
      have htmem : min a b ≤ t ∧ t ≤ max a b := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc ht) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans (min_le_left a b) h1, le_trans h2 (le_max_right a b)⟩
        · exact ⟨le_trans (min_le_right a b) h1, le_trans h2 (le_max_left a b)⟩
      have hx' : |x - s| < 1 := by
        have := Metric.mem_ball.mp hx
        rwa [Real.dist_eq] at this
      have hxt : x - t ∈ Set.Icc (s - 1 - max a b) (s + 1 - min a b) := by
        rw [Set.mem_Icc]
        rw [abs_lt] at hx'
        constructor <;> [linarith [htmem.2]; linarith [htmem.1]]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _ hxt) (norm_nonneg _)))
    ((continuous_const.mul hv.norm).intervalIntegrable a b)
    (Filter.Eventually.of_forall fun t _ x _ => hderiv t x)
  exact key.2

/-- Differentiation under the integral sign, right form. -/
private lemma hasDerivAt_param_right (g v : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hv : Continuous v)
    (a b s : ℝ) :
    HasDerivAt (fun σ => ∫ t in a..b, g (t - σ) * v t)
      (-∫ t in a..b, deriv g (t - s) * v t) s := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv_one
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := min a b - s - 1) (b := max a b - s + 1)
    ).exists_bound_of_continuousOn hg'c.continuousOn
  have hderiv : ∀ t x : ℝ,
      HasDerivAt (fun x => g (t - x) * v t) (-deriv g (t - x) * v t) x := by
    intro t x
    have h1 : HasDerivAt (fun x : ℝ => g (t - x)) (-deriv g (t - x)) x := by
      have := (hgd (t - x)).hasDerivAt.comp x ((hasDerivAt_id x).const_sub t)
      exact this.congr_deriv (by ring)
    exact h1.mul_const (v t)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x t => g (t - x) * v t) (F' := fun x t => -deriv g (t - x) * v t)
    (x₀ := s) (s := Metric.ball s 1) (bound := fun t => M * ‖v t‖)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun _ =>
      ((hgc.comp (continuous_id.sub continuous_const)).mul hv).aestronglyMeasurable)
    (((hgc.comp (continuous_id.sub continuous_const)).mul hv).intervalIntegrable a b)
    ((((hg'c.comp (continuous_id.sub continuous_const)).neg).mul hv)).aestronglyMeasurable
    (Filter.Eventually.of_forall (by
      intro t ht x hx
      have htmem : min a b ≤ t ∧ t ≤ max a b := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc ht) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans (min_le_left a b) h1, le_trans h2 (le_max_right a b)⟩
        · exact ⟨le_trans (min_le_right a b) h1, le_trans h2 (le_max_left a b)⟩
      have hx' : |x - s| < 1 := by
        have := Metric.mem_ball.mp hx
        rwa [Real.dist_eq] at this
      have hxt : t - x ∈ Set.Icc (min a b - s - 1) (max a b - s + 1) := by
        rw [Set.mem_Icc]
        rw [abs_lt] at hx'
        constructor <;> [linarith [htmem.1]; linarith [htmem.2]]
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_right (hM _ hxt) (norm_nonneg _)))
    ((continuous_const.mul hv.norm).intervalIntegrable a b)
    (Filter.Eventually.of_forall fun t _ x _ => hderiv t x)
  have h2 : (∫ t in a..b, -deriv g (t - s) * v t) = -∫ t in a..b, deriv g (t - s) * v t := by
    simp only [neg_mul]
    exact intervalIntegral.integral_neg
  rw [h2] at key
  exact key.2

/-- Derivative of the left piece `σ ↦ ∫ t in a..σ, g (σ - t) * v t`. -/
private lemma hasDerivAt_left_piece (g v : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hv : Continuous v)
    (a s : ℝ) :
    HasDerivAt (fun σ => ∫ t in a..σ, g (σ - t) * v t)
      ((∫ t in a..s, deriv g (s - t) * v t) + g 0 * v s) s := by
  have hgc : Continuous g := hg.continuous
  have key : (fun σ => ∫ t in a..σ, g (σ - t) * v t)
      = fun σ => (∫ t in a..s, g (σ - t) * v t) + ∫ t in s..σ, g (σ - t) * v t := by
    funext σ
    exact (intervalIntegral.integral_add_adjacent_intervals
      (((hgc.comp (continuous_const.sub continuous_id)).mul hv).intervalIntegrable a s)
      (((hgc.comp (continuous_const.sub continuous_id)).mul hv).intervalIntegrable s σ)).symm
  rw [key]
  have hmov : HasDerivAt (fun σ => ∫ t in s..σ, g (σ - t) * v t) (g 0 * v s) s := by
    have := hasDerivAt_moving (fun σ t => g (σ - t) * v t)
      ((hgc.comp (continuous_fst.sub continuous_snd)).mul (hv.comp continuous_snd)) s
    exact this.congr_deriv (by rw [sub_self])
  exact (hasDerivAt_param_left g v hg hv a s s).add hmov

/-- Derivative of the right piece `σ ↦ ∫ t in σ..b, g (t - σ) * v t`. -/
private lemma hasDerivAt_right_piece (g v : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hv : Continuous v)
    (b s : ℝ) :
    HasDerivAt (fun σ => ∫ t in σ..b, g (t - σ) * v t)
      ((-∫ t in s..b, deriv g (t - s) * v t) - g 0 * v s) s := by
  have hgc : Continuous g := hg.continuous
  have key : (fun σ => ∫ t in σ..b, g (t - σ) * v t)
      = fun σ => -(∫ t in s..σ, g (t - σ) * v t) + ∫ t in s..b, g (t - σ) * v t := by
    funext σ
    have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => g (t - σ) * v t) volume x y :=
      fun x y => (((hgc.comp (continuous_id.sub continuous_const)).mul hv).intervalIntegrable x y)
    rw [← intervalIntegral.integral_symm]
    exact (intervalIntegral.integral_add_adjacent_intervals (hint σ s) (hint s b)).symm
  rw [key]
  have hmov : HasDerivAt (fun σ => -∫ t in s..σ, g (t - σ) * v t) (-(g 0 * v s)) s := by
    have := hasDerivAt_moving (fun σ t => g (t - σ) * v t)
      ((hgc.comp (continuous_snd.sub continuous_fst)).mul (hv.comp continuous_snd)) s
    exact this.neg.congr_deriv (by rw [sub_self])
  exact (hmov.add (hasDerivAt_param_right g v hg hv s b s)).congr_deriv (by ring)

end Aux

theorem splitKernelIntegral_hasDerivAt
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hf0 : f 0 = 0)
    (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) :
    HasDerivAt (splitKernelIntegral f v)
      ((∫ t in (-(1:ℝ)/2)..s, deriv f (s - t) * v t)
        - ∫ t in s..(1/2:ℝ), deriv f (t - s) * v t) s := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hL := hasDerivAt_left_piece f v hf1 hv (-(1:ℝ)/2) s
  have hR := hasDerivAt_right_piece f v hf1 hv (1/2 : ℝ) s
  exact (hL.add hR).congr_deriv (by rw [hf0]; ring)

theorem splitKernelIntegral_hasDerivAt_two
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hf0 : f 0 = 0)
    (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) :
    HasDerivAt
      (fun σ : ℝ => (∫ t in (-(1:ℝ)/2)..σ, deriv f (σ - t) * v t)
        - ∫ t in σ..(1/2:ℝ), deriv f (t - σ) * v t)
      (2 * deriv f 0 * v s
        + ((∫ t in (-(1:ℝ)/2)..s, deriv (deriv f) (s - t) * v t)
           + ∫ t in s..(1/2:ℝ), deriv (deriv f) (t - s) * v t)) s := by
  have hf1 : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' (hf.of_le (by norm_num))
  have hL := hasDerivAt_left_piece (deriv f) v hf1 hv (-(1:ℝ)/2) s
  have hR := hasDerivAt_right_piece (deriv f) v hf1 hv (1/2 : ℝ) s
  exact (hL.sub hR).congr_deriv (by ring)


end AristotleN