import ZetaLean.WScratch.EForm3.Numerics

/-!
# Window estimates

Uniform bounds on `Qim`, a comparison of `Qre y s` with `Qre 0 s`, a lower bound for
`Qre 0 s` on the near field `|s| ≤ 28/5`, and the lower bound for the gain `Shq`.
-/

open scoped BigOperators Real
open MeasureTheory

namespace Retention

/-! ### Transfer lemmas -/

lemma abs_integral_g_mul_le {k M : ℝ → ℝ} (hk : Continuous k) (hM : Continuous M)
    (h : ∀ u : ℝ, |u| ≤ 1/2 → |Real.cos (Real.sqrt 2 * u) * k u| ≤ M u) :
    |∫ u : ℝ, g u * k u| ≤ ∫ u in (-(1/2):ℝ)..(1/2), M u := by
  rw [integral_g_mul_eq]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by norm_num)) ?_
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ (hM.intervalIntegrable _ _) ?_
  · exact ((by fun_prop : Continuous fun u : ℝ =>
      |Real.cos (Real.sqrt 2 * u) * k u|)).intervalIntegrable _ _
  · intro u hu
    rw [Set.mem_Icc] at hu
    exact h u (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)

lemma integral_g_mul_ge {k m : ℝ → ℝ} (hk : Continuous k) (hm : Continuous m)
    (h : ∀ u : ℝ, |u| ≤ 1/2 → m u ≤ Real.cos (Real.sqrt 2 * u) * k u) :
    (∫ u in (-(1/2):ℝ)..(1/2), m u) ≤ ∫ u : ℝ, g u * k u := by
  rw [integral_g_mul_eq]
  refine intervalIntegral.integral_mono_on (by norm_num) (hm.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u : ℝ => Real.cos (Real.sqrt 2 * u) * k u).intervalIntegrable
      _ _) ?_
  intro u hu
  rw [Set.mem_Icc] at hu
  exact h u (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)

/-! ### Pointwise bounds on the window -/

/-- On the window, `cos (√2 u) ≤ 1 - (23/24) u^2`. -/
lemma cos_sqrt2_le {u : ℝ} (hu : |u| ≤ 1/2) :
    Real.cos (Real.sqrt 2 * u) ≤ 1 - (23/24) * u^2 := by
  have h := cos_le_taylor4 (Real.sqrt 2 * u)
  have h2 : (Real.sqrt 2 * u)^2 = 2 * u^2 := by
    rw [mul_pow, sqrt2_sq]
  have h4 : (Real.sqrt 2 * u)^4 = 4 * u^4 := by
    have e : (Real.sqrt 2 * u)^4 = ((Real.sqrt 2 * u)^2)^2 := by ring
    rw [e, h2]; ring
  rw [h2, h4] at h
  have hu2 : u^2 ≤ 1/4 := by
    have := abs_le.1 hu; nlinarith [this.1, this.2]
  nlinarith [sq_nonneg u, sq_nonneg (u^2)]

/-- On the window, `1 - u^2 ≤ cos (√2 u)`. -/
lemma cos_sqrt2_ge (u : ℝ) : 1 - u^2 ≤ Real.cos (Real.sqrt 2 * u) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * u)
  have h2 : (Real.sqrt 2 * u)^2 = 2 * u^2 := by rw [mul_pow, sqrt2_sq]
  rw [h2] at h
  linarith

/-! ### The uniform bound on `Qim` -/

lemma integral_abs_poly : (∫ u in (-(1/2):ℝ)..(1/2), |u| * (1 - (23/24) * u^2)) = 169/768 := by
  have hsplit : (∫ u in (-(1/2):ℝ)..(1/2), |u| * (1 - (23/24) * u^2))
      = (∫ u in (-(1/2):ℝ)..(0:ℝ), |u| * (1 - (23/24) * u^2))
        + ∫ u in (0:ℝ)..(1/2), |u| * (1 - (23/24) * u^2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : (∫ u in (-(1/2):ℝ)..(0:ℝ), |u| * (1 - (23/24) * u^2))
      = ∫ u in (-(1/2):ℝ)..(0:ℝ), (-u + (23/24) * u^3) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 0), Set.mem_Icc] at hu
    show |u| * (1 - (23/24) * u^2) = _
    rw [abs_of_nonpos hu.2]; ring
  have h2 : (∫ u in (0:ℝ)..(1/2), |u| * (1 - (23/24) * u^2))
      = ∫ u in (0:ℝ)..(1/2), (u - (23/24) * u^3) := by
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2), Set.mem_Icc] at hu
    show |u| * (1 - (23/24) * u^2) = _
    rw [abs_of_nonneg hu.1]; ring
  rw [hsplit, h1, h2]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow, integral_id, integral_pow]
  norm_num

/-- The uniform bound `|Qim y s| ≤ (32/31)*(169/768)*y`. -/
lemma abs_Qim_le {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) :
    |Qim y s| ≤ (32/31) * (169/768) * y := by
  have key : |Qim y s| ≤ ∫ u in (-(1/2):ℝ)..(1/2),
      ((32/31) * y) * (|u| * (1 - (23/24) * u^2)) := by
    unfold Qim
    have : (fun u : ℝ => g u * Real.sinh (y * u) * Real.sin (s * u))
        = fun u : ℝ => g u * (Real.sinh (y * u) * Real.sin (s * u)) := by
      funext u; ring
    rw [this]
    refine abs_integral_g_mul_le (by fun_prop) (by fun_prop) ?_
    intro u hu
    have hcos0 : 0 ≤ Real.cos (Real.sqrt 2 * u) := by
      have := g_nonneg u
      rwa [g_of_mem hu] at this
    have hcosle : Real.cos (Real.sqrt 2 * u) ≤ 1 - (23/24) * u^2 := cos_sqrt2_le hu
    have hsinh : |Real.sinh (y * u)| ≤ (32/31) * y * |u| := by
      have h1 : |Real.sinh (y * u)| = Real.sinh |y * u| := by
        rcases le_total 0 (y*u) with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.2 h)]
        · rw [abs_of_nonpos h, abs_of_nonpos (Real.sinh_nonpos_iff.2 h), Real.sinh_neg]
      have habs : |y * u| ≤ 1/4 := by
        rw [abs_mul, abs_of_nonneg hy0]
        nlinarith [abs_nonneg u, hu]
      have h2 : Real.sinh |y * u| ≤ |y * u| * Real.cosh |y * u| :=
        sinh_le_mul_cosh (abs_nonneg _)
      have h3 : Real.cosh |y * u| ≤ 32/31 := cosh_le_of_abs_le_quarter (by rwa [abs_abs])
      rw [h1]
      calc Real.sinh |y * u| ≤ |y * u| * Real.cosh |y * u| := h2
        _ ≤ |y * u| * (32/31) := by
            exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = (32/31) * y * |u| := by rw [abs_mul, abs_of_nonneg hy0]; ring
    have hsin : |Real.sin (s * u)| ≤ 1 := Real.abs_sin_le_one _
    calc |Real.cos (Real.sqrt 2 * u) * (Real.sinh (y * u) * Real.sin (s * u))|
        = Real.cos (Real.sqrt 2 * u) * (|Real.sinh (y*u)| * |Real.sin (s*u)|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcos0]
      _ ≤ (1 - (23/24) * u^2) * ((32/31) * y * |u| * 1) := by
          have h1 : |Real.sinh (y*u)| * |Real.sin (s*u)| ≤ (32/31) * y * |u| * 1 :=
            mul_le_mul hsinh hsin (abs_nonneg _)
              (by positivity)
          have h0 : (0:ℝ) ≤ |Real.sinh (y*u)| * |Real.sin (s*u)| := by positivity
          exact mul_le_mul hcosle h1 h0 (by nlinarith [abs_le.1 hu])
      _ = ((32/31) * y) * (|u| * (1 - (23/24) * u^2)) := by ring
  rw [intervalIntegral.integral_const_mul, integral_abs_poly] at key
  calc |Qim y s| ≤ (32/31) * y * (169/768) := key
    _ = (32/31) * (169/768) * y := by ring

/-! ### Comparison of `Qre y s` with `Qre 0 s` -/

lemma Qre_zero_left (s : ℝ) : Qre 0 s = ∫ u : ℝ, g u * Real.cos (s * u) := by
  unfold Qre
  simp

lemma Qre_diff_le {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) :
    Qre 0 s - Qre y s ≤ (32/31) * y^2 / 24 := by
  have hint1 : Integrable (fun u : ℝ => g u * (Real.cosh (y*u) * Real.cos (s*u))) :=
    integrable_g_mul (by fun_prop)
  have hint2 : Integrable (fun u : ℝ => g u * Real.cos (s * u)) := integrable_g_mul (by fun_prop)
  have hdiff : Qre y s - Qre 0 s
      = ∫ u : ℝ, g u * ((Real.cosh (y*u) - 1) * Real.cos (s*u)) := by
    rw [Qre_zero_left]
    have hQ : Qre y s = ∫ u : ℝ, g u * (Real.cosh (y*u) * Real.cos (s*u)) := by
      unfold Qre; simp_rw [mul_assoc]
    rw [hQ, ← integral_sub hint1 hint2]
    congr 1; funext u; ring
  have hbound : |∫ u : ℝ, g u * ((Real.cosh (y*u) - 1) * Real.cos (s*u))|
      ≤ ∫ u in (-(1/2):ℝ)..(1/2), ((32/31) * y^2 / 2) * u^2 := by
    refine abs_integral_g_mul_le (by fun_prop) (by fun_prop) ?_
    intro u hu
    have hcos0 : 0 ≤ Real.cos (Real.sqrt 2 * u) := by
      have := g_nonneg u; rwa [g_of_mem hu] at this
    have hcos1 : Real.cos (Real.sqrt 2 * u) ≤ 1 := Real.cos_le_one _
    have habs : |y * u| ≤ 1/4 := by
      rw [abs_mul, abs_of_nonneg hy0]; nlinarith [abs_nonneg u, hu]
    have hch : Real.cosh (y*u) - 1 ≤ (y*u)^2/2 * Real.cosh (y*u) := cosh_sub_one_le _
    have hchle : Real.cosh (y*u) ≤ 32/31 := cosh_le_of_abs_le_quarter habs
    have hch0 : 0 ≤ Real.cosh (y*u) - 1 := by linarith [Real.one_le_cosh (y*u)]
    have hcc : Real.cosh (y*u) - 1 ≤ (32/31) * y^2 / 2 * u^2 := by
      nlinarith [sq_nonneg (y*u), sq_nonneg u]
    have hsin : |Real.cos (s * u)| ≤ 1 := Real.abs_cos_le_one _
    calc |Real.cos (Real.sqrt 2 * u) * ((Real.cosh (y*u) - 1) * Real.cos (s*u))|
        = Real.cos (Real.sqrt 2 * u) * ((Real.cosh (y*u) - 1) * |Real.cos (s*u)|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcos0, abs_of_nonneg hch0]
      _ ≤ 1 * ((32/31) * y^2 / 2 * u^2 * 1) := by
          have h1 : (Real.cosh (y*u) - 1) * |Real.cos (s*u)| ≤ (32/31) * y^2/2 * u^2 * 1 :=
            mul_le_mul hcc hsin (abs_nonneg _) (by positivity)
          exact mul_le_mul hcos1 h1 (by positivity) zero_le_one
      _ = ((32/31) * y^2 / 2) * u^2 := by ring
  rw [intervalIntegral.integral_const_mul] at hbound
  have hpow : (∫ u in (-(1/2):ℝ)..(1/2), u^2) = 1/12 := by
    rw [integral_pow]; norm_num
  rw [hpow] at hbound
  rw [← hdiff] at hbound
  have := abs_le.1 hbound
  linarith [this.1]

/-! ### The near field: a lower bound for `Qre 0 s` -/

/-- `fk k = ∫_{-1/2}^{1/2} cos (k u) du`. -/
noncomputable def fk (k : ℝ) : ℝ := ∫ u in (-(1/2):ℝ)..(1/2), Real.cos (k * u)

lemma fk_eq {k : ℝ} (hk : k ≠ 0) : fk k = 2 * Real.sin (k/2) / k := by
  unfold fk
  have h : (0:ℝ)^2 + k^2 ≠ 0 := by positivity
  have h0 := integral_cosh_cos_half 0 k h
  simp only [zero_mul, Real.cosh_zero, one_mul, zero_add] at h0
  rw [h0]
  rw [show (0:ℝ)/2 = 0 by norm_num, Real.cosh_zero]
  field_simp
  ring

lemma fk_poly_lower (k : ℝ) :
    1 - k^2/24 + k^4/1920 - k^6/322560 ≤ fk k := by
  unfold fk
  have hpoly : (∫ u in (-(1/2):ℝ)..(1/2),
      (1 - (k*u)^2/2 + (k*u)^4/24 - (k*u)^6/720))
      = 1 - k^2/24 + k^4/1920 - k^6/322560 := by
    have e : ∀ u : ℝ, (1 - (k*u)^2/2 + (k*u)^4/24 - (k*u)^6/720)
        = 1 - (k^2/2) * u^2 + (k^4/24) * u^4 - (k^6/720) * u^6 := by
      intro u; ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow,
      integral_pow, integral_pow]
    norm_num
    ring
  rw [← hpoly]
  refine intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop) ?_
  intro u _
  exact cos_ge_taylor6 (k*u)

lemma Qre_zero_split (s : ℝ) :
    Qre 0 s = (fk (s + Real.sqrt 2) + fk (s - Real.sqrt 2)) / 2 := by
  rw [Qre_eq_interval]
  unfold fk
  have hint : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * (Real.cosh (0 * u) * Real.cos (s * u))
      = (1/2) * Real.cos ((s + Real.sqrt 2) * u) + (1/2) * Real.cos ((s - Real.sqrt 2) * u) := by
    intro u
    rw [zero_mul, Real.cosh_zero, one_mul, add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

lemma Qre_zero_even (s : ℝ) : Qre 0 (-s) = Qre 0 s := by
  rw [Qre_zero_left, Qre_zero_left]
  congr 1
  funext u
  rw [show (-s) * u = -(s*u) by ring, Real.cos_neg]

/-- Lower bound for `fk` on the "small argument" range. -/
lemma fk_lower_small {k : ℝ} (hk : |k| ≤ 4.1857866) : (0.4131 : ℝ) ≤ fk k := by
  have h := fk_poly_lower k
  have hv : k^2 ≤ 17.520810 := by nlinarith [abs_le.1 hk, sq_nonneg k, abs_nonneg k, sq_abs k]
  have hv0 : (0:ℝ) ≤ k^2 := sq_nonneg k
  have h4 : k^4 = (k^2)^2 := by ring
  have h6 : k^6 = (k^2)^3 := by ring
  rw [h4, h6] at h
  nlinarith [hv, hv0, sq_nonneg (k^2 - 17.520810), sq_nonneg (k^2)]

/-- Lower bound for `fk` on the "large argument" range. -/
lemma fk_lower_large {k : ℝ} (hk1 : 0 < k) (hk2 : k ≤ 7.0142136) : (-0.1164 : ℝ) ≤ fk k := by
  rw [fk_eq (ne_of_gt hk1)]
  rcases le_or_gt 0 (Real.sin (k/2)) with h | h
  · have : 0 ≤ 2 * Real.sin (k/2) / k := by positivity
    linarith
  · -- `sin (k/2) < 0` forces `k/2 > π`
    have hpi : Real.pi < k/2 := by
      by_contra hc
      push_neg at hc
      exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hc) (not_le.2 h)
    have hpil : (3.1415926:ℝ) < Real.pi := by
      have := Real.pi_gt_d20
      norm_num at this ⊢
      linarith
    have hk2pi : (6.2831852:ℝ) < k := by linarith
    have hsin : Real.sin (k/2) = -Real.sin (k/2 - Real.pi) := by
      rw [Real.sin_sub_pi]; ring
    have ht : k/2 - Real.pi ≤ 0.3655574 := by
      have : Real.pi > 3.1415926 := hpil
      linarith
    have hslt : Real.sin (k/2 - Real.pi) ≤ 0.3655574 :=
      le_trans (Real.sin_le (by linarith)) ht
    have hnum : -0.3655574 ≤ Real.sin (k/2) := by rw [hsin]; linarith
    rw [le_div_iff₀ hk1]
    nlinarith [hnum, hk2pi]

/-- The near-field lower bound: `Qre 0 s ≥ 0.1483` for `|s| ≤ 28/5`. -/
lemma Qre_zero_near {s : ℝ} (hs : |s| ≤ 28/5) : (0.1483 : ℝ) ≤ Qre 0 s := by
  -- reduce to `0 ≤ s`
  wlog hs0 : 0 ≤ s generalizing s
  · have := this (s := -s) (by rwa [abs_neg]) (by linarith [not_le.1 hs0])
    rwa [Qre_zero_even] at this
  have hsle : s ≤ 28/5 := le_trans (le_abs_self s) hs
  have h2lb := sqrt2_lb
  have h2ub := sqrt2_ub
  have hp : (0:ℝ) < s + Real.sqrt 2 := by linarith
  have hp2 : s + Real.sqrt 2 ≤ 7.0142136 := by linarith
  have hm : |s - Real.sqrt 2| ≤ 4.1857866 := by
    rw [abs_le]; constructor <;> linarith
  have h1 := fk_lower_large hp hp2
  have h2 := fk_lower_small hm
  rw [Qre_zero_split]
  linarith

/-! ### No damage in the near field -/

lemma no_damage {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) (hs : |s| ≤ 28/5) :
    Qim y s ^ 2 ≤ Qre y s ^ 2 := by
  have h1 : |Qim y s| ≤ (32/31) * (169/768) * y := abs_Qim_le hy0 hy
  have h1' : |Qim y s| ≤ 0.1136 := by
    have : (32/31) * (169/768) * y ≤ (32/31) * (169/768) * (1/2) :=
      mul_le_mul_of_nonneg_left hy (by norm_num)
    linarith [h1, this]
  have h2 : Qre 0 s - Qre y s ≤ (32/31) * y^2 / 24 := Qre_diff_le hy0 hy
  have h2' : Qre 0 s - Qre y s ≤ 0.0108 := by
    have hy2 : y^2 ≤ 1/4 := by nlinarith
    nlinarith [h2, hy2]
  have h3 : (0.1483:ℝ) ≤ Qre 0 s := Qre_zero_near hs
  have h4 : (0.1375:ℝ) ≤ Qre y s := by linarith
  have h5 : |Qim y s| ≤ Qre y s := by linarith
  calc Qim y s ^ 2 = |Qim y s| ^ 2 := (sq_abs _).symm
    _ ≤ Qre y s ^ 2 := by nlinarith [abs_nonneg (Qim y s)]

/-! ### The gain term -/

lemma integral_g_sq_lower : (17/240 : ℝ) ≤ ∫ u : ℝ, g u * u^2 := by
  have h : (∫ u in (-(1/2):ℝ)..(1/2), (u^2 - u^4)) ≤ ∫ u : ℝ, g u * u^2 := by
    refine integral_g_mul_ge (by fun_prop) (by fun_prop) ?_
    intro u _
    have := cos_sqrt2_ge u
    nlinarith [sq_nonneg u]
  have hval : (∫ u in (-(1/2):ℝ)..(1/2), (u^2 - u^4)) = 17/240 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      integral_pow, integral_pow]
    norm_num
  linarith [hval ▸ h]

lemma Qre_two_y_zero (y : ℝ) : Qre (2*y) 0 = ∫ u : ℝ, g u * Real.cosh ((2*y) * u) := by
  unfold Qre
  simp

lemma Shq_half_lower (y : ℝ) : (187/1440 : ℝ) * y^2 ≤ Shq y / 2 := by
  have hA : Qre 0 0 = Aconst := Qre_zero_zero
  have hAg : Aconst = ∫ u : ℝ, g u := by
    rw [← hA]; unfold Qre; simp
  have hint1 : Integrable (fun u : ℝ => g u * Real.cosh ((2*y) * u)) :=
    integrable_g_mul (by fun_prop)
  have hE : Qre (2*y) 0 - Aconst = ∫ u : ℝ, g u * (Real.cosh ((2*y)*u) - 1) := by
    rw [Qre_two_y_zero, hAg]
    have : (∫ u : ℝ, g u) = ∫ u : ℝ, g u * 1 := by simp
    rw [this, ← integral_sub hint1 (integrable_g_mul continuous_const)]
    congr 1; funext u; ring
  have hEge : 2 * y^2 * (17/240) ≤ Qre (2*y) 0 - Aconst := by
    rw [hE]
    have h : (∫ u : ℝ, g u * (2 * y^2 * u^2)) ≤ ∫ u : ℝ, g u * (Real.cosh ((2*y)*u) - 1) := by
      refine integral_mono (integrable_g_mul (by fun_prop)) (by
        have := hint1.sub (integrable_g_mul (continuous_const (y := (1:ℝ))))
        refine this.congr (Filter.Eventually.of_forall (fun u => by simp; ring))) ?_
      intro u
      have hcosh : 1 + ((2*y)*u)^2/2 ≤ Real.cosh ((2*y)*u) := cosh_ge_one_add_sq _
      have hg := g_nonneg u
      have : 2 * y^2 * u^2 ≤ Real.cosh ((2*y)*u) - 1 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hg
    have h2 : 2 * y^2 * (17/240) ≤ ∫ u : ℝ, g u * (2 * y^2 * u^2) := by
      have hrw : (∫ u : ℝ, g u * (2 * y^2 * u^2)) = 2 * y^2 * ∫ u : ℝ, g u * u^2 := by
        rw [← integral_const_mul]
        congr 1; funext u; ring
      rw [hrw]
      have := integral_g_sq_lower
      nlinarith [sq_nonneg y]
    linarith
  have hAlb : (11/12 : ℝ) ≤ Aconst := Aconst_lb
  have hApos : 0 < Aconst := Aconst_pos
  unfold Shq
  have hEnn : 0 ≤ Qre (2*y) 0 - Aconst := by nlinarith [sq_nonneg y]
  nlinarith [hEge, hAlb, hEnn, sq_nonneg y, sq_nonneg (Qre (2*y) 0 - Aconst)]

end Retention
