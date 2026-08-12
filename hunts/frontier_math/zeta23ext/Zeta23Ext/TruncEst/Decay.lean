import RequestProject.Kernel

/-!
# Lemma 1 of `PROBLEM.md`: decay of the interaction `T`

We prove `|T dt y| ≤ Cdec / dt ^ 2` for `dt ≠ 0` and `y ∈ [0, 1/2]`, with the
explicit constant `Cdec = 200`.

The route is the one suggested in `PROBLEM.md`, organised as a single
application of the fundamental theorem of calculus: with
`hf y w = c2core w * cosh (y*w) ^ 2` and `hf1`, `hf2` its first two
derivatives in `w`, the function

  `G w = hf y w * sin (dt*w) / dt + hf1 y w * cos (dt*w) / dt ^ 2`

has derivative `(hf y w + hf2 y w / dt ^ 2) * cos (dt * w)`, which is exactly
the two integrations by parts.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace TruncEst

/-- The interaction `T dt y`. -/
def T (dt y : ℝ) : ℝ :=
  (4 / A ^ 2) * ∫ w in (-1:ℝ)..1, c2 w * Real.cosh (y * w) ^ 2 * Real.cos (dt * w)

/-- The explicit decay constant of Lemma 1. -/
def Cdec : ℝ := 200

/-- `hf y w = c2core w * cosh (y w) ^ 2`, the integrand's non-oscillating factor on `[0,1]`. -/
def hf (y w : ℝ) : ℝ := c2core w * Real.cosh (y * w) ^ 2

/-- `∂_w hf`. -/
def hf1 (y w : ℝ) : ℝ :=
  d1c2 w * Real.cosh (y * w) ^ 2
    + c2core w * (2 * y * Real.cosh (y * w) * Real.sinh (y * w))

/-- `∂_w^2 hf`. -/
def hf2 (y w : ℝ) : ℝ :=
  d2c2 w * Real.cosh (y * w) ^ 2
    + 4 * y * d1c2 w * Real.cosh (y * w) * Real.sinh (y * w)
    + c2core w * (2 * y ^ 2 * (Real.cosh (y * w) ^ 2 + Real.sinh (y * w) ^ 2))

/-! ### Hyperbolic bounds -/

lemma exp_half_le_two : Real.exp (1/2) ≤ 2 := by
  have h1 : Real.exp (1/2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2 : ℝ), h1]

lemma exp_le_two {u : ℝ} (h : |u| ≤ 1/2) : Real.exp u ≤ 2 :=
  le_trans (Real.exp_le_exp.2 (le_trans (le_abs_self u) h)) exp_half_le_two

lemma exp_ge_half {u : ℝ} (h : |u| ≤ 1/2) : (1:ℝ)/2 ≤ Real.exp u := by
  have h1 : Real.exp (-u) ≤ 2 := exp_le_two (by rwa [abs_neg])
  have h2 : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos u, Real.exp_pos (-u)]

lemma cosh_le_of_abs_le_half {u : ℝ} (h : |u| ≤ 1/2) : Real.cosh u ≤ 5/4 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp u ≤ 2 := exp_le_two h
  have h2 : (1:ℝ)/2 ≤ Real.exp u := exp_ge_half h
  have h3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos u, Real.exp_pos (-u)]

lemma cosh_nonneg' (u : ℝ) : 0 ≤ Real.cosh u := (Real.cosh_pos u).le

lemma abs_sinh_le_of_abs_le_half {u : ℝ} (h : |u| ≤ 1/2) : |Real.sinh u| ≤ 3/4 := by
  rw [Real.sinh_eq, abs_le]
  have h1 : Real.exp u ≤ 2 := exp_le_two h
  have h2 : (1:ℝ)/2 ≤ Real.exp u := exp_ge_half h
  have h1' : Real.exp (-u) ≤ 2 := exp_le_two (by rwa [abs_neg])
  have h2' : (1:ℝ)/2 ≤ Real.exp (-u) := exp_ge_half (by rwa [abs_neg])
  constructor <;> linarith

/-- The pointwise bound `|hf2 y w| ≤ 10` for `w ∈ [0,1]`, `y ∈ [0,1/2]`. -/
lemma abs_hf2_le {y w : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |hf2 y w| ≤ 10 := by
  have habs : |y * w| ≤ 1/2 := by
    rw [abs_mul, abs_of_nonneg hy0, abs_of_nonneg hw0]
    nlinarith
  have hc : Real.cosh (y * w) ≤ 5/4 := cosh_le_of_abs_le_half habs
  have hc0 : 0 ≤ Real.cosh (y * w) := cosh_nonneg' _
  have hs : |Real.sinh (y * w)| ≤ 3/4 := abs_sinh_le_of_abs_le_half habs
  have hd2 := abs_d2c2_le hw0 hw1
  have hd1 := abs_d1c2_le hw0 hw1
  have hc2 := abs_c2core_le hw0 hw1
  have e1 : |d2c2 w * Real.cosh (y * w) ^ 2| ≤ (13/4) * (25/16) := by
    rw [abs_mul, abs_pow, abs_of_nonneg hc0]
    exact mul_le_mul hd2 (by nlinarith) (by positivity) (by norm_num)
  have e2 : |4 * y * d1c2 w * Real.cosh (y * w) * Real.sinh (y * w)| ≤ 2 * (7/4) * (5/4) * (3/4) := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg hc0]
    have h4 : |(4:ℝ)| = 4 := by norm_num
    rw [h4]
    have h5 : (4:ℝ) * y ≤ 2 := by linarith
    exact mul_le_mul (mul_le_mul (mul_le_mul h5 hd1 (abs_nonneg _) (by norm_num)) hc hc0
      (by positivity)) hs (abs_nonneg _) (by positivity)
  have e3 : |c2core w * (2 * y ^ 2 * (Real.cosh (y * w) ^ 2 + Real.sinh (y * w) ^ 2))|
      ≤ 1 * (1/2 * (25/16 + 9/16)) := by
    rw [abs_mul]
    have hsq : Real.sinh (y*w) ^ 2 ≤ 9/16 := by
      have := abs_le.1 hs; nlinarith [this.1, this.2]
    have hcsq : Real.cosh (y*w) ^ 2 ≤ 25/16 := by nlinarith
    have hy2 : 2 * y ^ 2 ≤ 1/2 := by nlinarith
    have hin : |2 * y ^ 2 * (Real.cosh (y * w) ^ 2 + Real.sinh (y * w) ^ 2)|
        ≤ 1/2 * (25/16 + 9/16) := by
      rw [abs_of_nonneg (by positivity)]
      apply mul_le_mul hy2 (by linarith) (by positivity) (by norm_num)
    exact mul_le_mul hc2 hin (abs_nonneg _) (by norm_num)
  have hsum : |hf2 y w| ≤ |d2c2 w * Real.cosh (y * w) ^ 2
        + 4 * y * d1c2 w * Real.cosh (y * w) * Real.sinh (y * w)|
      + |c2core w * (2 * y ^ 2 * (Real.cosh (y * w) ^ 2 + Real.sinh (y * w) ^ 2))| := by
    unfold hf2
    exact abs_add_le _ _
  have hsum2 : |d2c2 w * Real.cosh (y * w) ^ 2
        + 4 * y * d1c2 w * Real.cosh (y * w) * Real.sinh (y * w)|
      ≤ |d2c2 w * Real.cosh (y * w) ^ 2|
        + |4 * y * d1c2 w * Real.cosh (y * w) * Real.sinh (y * w)| := abs_add_le _ _
  linarith

/-! ### Derivatives of `hf` -/

lemma hasDerivAt_cosh_sq (y w : ℝ) :
    HasDerivAt (fun w : ℝ => Real.cosh (y * w) ^ 2)
      (2 * y * Real.cosh (y * w) * Real.sinh (y * w)) w := by
  have h1 : HasDerivAt (fun w : ℝ => y * w) y w := by
    simpa using (hasDerivAt_id w).const_mul y
  have h2 : HasDerivAt (fun w : ℝ => Real.cosh (y * w)) (Real.sinh (y * w) * y) w := h1.cosh
  have := h2.pow 2
  convert this using 1
  ring

lemma hasDerivAt_sinh_comp (y w : ℝ) :
    HasDerivAt (fun w : ℝ => Real.sinh (y * w)) (Real.cosh (y * w) * y) w := by
  have h1 : HasDerivAt (fun w : ℝ => y * w) y w := by
    simpa using (hasDerivAt_id w).const_mul y
  exact h1.sinh

lemma hasDerivAt_hf (y w : ℝ) : HasDerivAt (hf y) (hf1 y w) w := by
  have h := (hasDerivAt_c2core w).mul (hasDerivAt_cosh_sq y w)
  exact h

lemma hasDerivAt_hf1 (y w : ℝ) : HasDerivAt (hf1 y) (hf2 y w) w := by
  have hA := (hasDerivAt_d1c2 w).mul (hasDerivAt_cosh_sq y w)
  have hB : HasDerivAt (fun w : ℝ => 2 * y * Real.cosh (y * w) * Real.sinh (y * w))
      (2 * y ^ 2 * (Real.sinh (y * w) ^ 2 + Real.cosh (y * w) ^ 2)) w := by
    have h1 : HasDerivAt (fun w : ℝ => 2 * y * Real.cosh (y * w))
        (2 * y * (Real.sinh (y * w) * y)) w := by
      have h2 : HasDerivAt (fun w : ℝ => y * w) y w := by
        simpa using (hasDerivAt_id w).const_mul y
      exact (h2.cosh).const_mul (2 * y)
    have := h1.mul (hasDerivAt_sinh_comp y w)
    convert this using 1
    ring
  have hC := (hasDerivAt_c2core w).mul hB
  have h := hA.add hC
  convert h using 1
  unfold hf2
  ring

/-! ### The FTC step -/

lemma continuous_hf (y : ℝ) : Continuous (hf y) := by
  unfold hf c2core; fun_prop

lemma continuous_hf1 (y : ℝ) : Continuous (hf1 y) := by
  unfold hf1 d1c2 c2core; fun_prop

lemma continuous_hf2 (y : ℝ) : Continuous (hf2 y) := by
  unfold hf2 d2c2 d1c2 c2core
  fun_prop

/-- The primitive realising the two integrations by parts. -/
def Gaux (y dt w : ℝ) : ℝ :=
  hf y w * Real.sin (dt * w) / dt + hf1 y w * Real.cos (dt * w) / dt ^ 2

lemma hasDerivAt_Gaux {dt : ℝ} (hdt : dt ≠ 0) (y w : ℝ) :
    HasDerivAt (Gaux y dt) ((hf y w + hf2 y w / dt ^ 2) * Real.cos (dt * w)) w := by
  have hlin : HasDerivAt (fun w : ℝ => dt * w) dt w := by
    simpa using (hasDerivAt_id w).const_mul dt
  have h1 : HasDerivAt (fun w : ℝ => hf y w * Real.sin (dt * w) / dt)
      ((hf1 y w * Real.sin (dt * w) + hf y w * (Real.cos (dt * w) * dt)) / dt) w :=
    ((hasDerivAt_hf y w).mul (hlin.sin)).div_const dt
  have h2 : HasDerivAt (fun w : ℝ => hf1 y w * Real.cos (dt * w) / dt ^ 2)
      ((hf2 y w * Real.cos (dt * w) + hf1 y w * (-Real.sin (dt * w) * dt)) / dt ^ 2) w :=
    ((hasDerivAt_hf1 y w).mul (hlin.cos)).div_const (dt ^ 2)
  have h := h1.add h2
  convert h using 1
  field_simp
  ring

/-! ### The decay estimate -/

lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

lemma continuous_integrandFull (dt y : ℝ) :
    Continuous (fun w : ℝ => c2 w * Real.cosh (y * w) ^ 2 * Real.cos (dt * w)) :=
  (continuous_c2.mul (by fun_prop)).mul (by fun_prop)

/-- The integrand is even, so the integral over `[-1,1]` doubles the one over `[0,1]`;
and on `[0,1]` the kernel `c2` is given by its closed form. -/
lemma integral_symm_eq (dt y : ℝ) :
    (∫ w in (-1:ℝ)..1, c2 w * Real.cosh (y * w) ^ 2 * Real.cos (dt * w))
      = 2 * ∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w) := by
  set F : ℝ → ℝ := fun w => c2 w * Real.cosh (y * w) ^ 2 * Real.cos (dt * w) with hF
  have hcont : Continuous F := continuous_integrandFull dt y
  have heven : ∀ w : ℝ, F (-w) = F w := by
    intro w
    simp [hF, c2_neg, mul_neg, Real.cosh_neg, Real.cos_neg]
  have hadd : (∫ w in (-1:ℝ)..1, F w) = (∫ w in (-1:ℝ)..0, F w) + ∫ w in (0:ℝ)..1, F w :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hneg : (∫ w in (-1:ℝ)..0, F w) = ∫ w in (0:ℝ)..1, F w := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1) F
    rw [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun x _ => heven x)
  have hcongr : (∫ w in (0:ℝ)..1, F w) = ∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [hF, hf, c2_of_nonneg hx.1 hx.2]
  rw [hadd, hneg, hcongr]
  ring

@[simp] lemma hf_one (y : ℝ) : hf y 1 = 0 := by simp [hf]

lemma hf1_one (y : ℝ) : hf1 y 1 = d1c2 1 * Real.cosh y ^ 2 := by
  simp [hf1]

lemma hf1_zero (y : ℝ) : hf1 y 0 = d1c2 0 := by
  simp [hf1]

lemma abs_hf1_one_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) : |hf1 y 1| ≤ 3 := by
  have hc : Real.cosh y ≤ 5/4 := cosh_le_of_abs_le_half (by rw [abs_of_nonneg hy0]; linarith)
  have hc0 : 0 ≤ Real.cosh y := cosh_nonneg' _
  have hd := abs_d1c2_le (by norm_num : (0:ℝ) ≤ 1) (le_refl (1:ℝ))
  rw [hf1_one, abs_mul, abs_pow, abs_of_nonneg hc0]
  have : Real.cosh y ^ 2 ≤ 25/16 := by nlinarith
  nlinarith [abs_nonneg (d1c2 1)]

lemma abs_hf1_zero_le : |hf1 (0:ℝ) 0| ≤ 2 := by
  rw [hf1_zero]
  linarith [abs_d1c2_le (le_refl (0:ℝ)) (by norm_num : (0:ℝ) ≤ 1)]

/-- The half-interval oscillatory estimate: two integrations by parts. -/
lemma abs_integral_half_le {dt y : ℝ} (hdt : dt ≠ 0) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    |∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w)| ≤ 15 / dt ^ 2 := by
  have hdt2 : (0:ℝ) < dt ^ 2 := by positivity
  have hcont1 : Continuous (fun w : ℝ => hf y w * Real.cos (dt * w)) :=
    (continuous_hf y).mul (by fun_prop)
  have hcont2 : Continuous (fun w : ℝ => hf2 y w * Real.cos (dt * w)) :=
    (continuous_hf2 y).mul (by fun_prop)
  have hFTC : (∫ w in (0:ℝ)..1, (hf y w + hf2 y w / dt ^ 2) * Real.cos (dt * w))
      = Gaux y dt 1 - Gaux y dt 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_Gaux hdt y x) ?_
    exact ((continuous_hf y).add ((continuous_hf2 y).div_const _)).mul
      (by fun_prop) |>.intervalIntegrable _ _
  have hsplit : (∫ w in (0:ℝ)..1, (hf y w + hf2 y w / dt ^ 2) * Real.cos (dt * w))
      = (∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w))
        + (∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)) / dt ^ 2 := by
    rw [← intervalIntegral.integral_div]
    rw [← intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
      ((hcont2.div_const _).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  -- bound the second integral
  have hb2 : |∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)| ≤ 10 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (C := 10) (f := fun w => hf2 y w * Real.cos (dt * w)) ?_
    · simpa using this
    · intro x hx
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      have h1 : |hf2 y x| ≤ 10 := abs_hf2_le hy0 hy1 hx.1.le hx.2
      have h2 : |Real.cos (dt * x)| ≤ 1 := Real.abs_cos_le_one _
      calc ‖hf2 y x * Real.cos (dt * x)‖ = |hf2 y x| * |Real.cos (dt * x)| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 10 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 10 := by ring
  -- bound the boundary terms
  have hG1 : |Gaux y dt 1| ≤ 3 / dt ^ 2 := by
    have h0 : Gaux y dt 1 = hf1 y 1 * Real.cos (dt * 1) / dt ^ 2 := by
      simp [Gaux, hf_one]
    rw [h0, abs_div, abs_of_pos hdt2, div_le_div_iff_of_pos_right hdt2, abs_mul]
    have := abs_hf1_one_le hy0 hy1
    nlinarith [Real.abs_cos_le_one (dt * 1), abs_nonneg (hf1 y 1),
      abs_nonneg (Real.cos (dt * 1))]
  have hG0 : |Gaux y dt 0| ≤ 2 / dt ^ 2 := by
    have h0 : Gaux y dt 0 = d1c2 0 / dt ^ 2 := by
      simp [Gaux, hf1_zero]
    rw [h0, abs_div, abs_of_pos hdt2, div_le_div_iff_of_pos_right hdt2]
    linarith [abs_d1c2_le (le_refl (0:ℝ)) (by norm_num : (0:ℝ) ≤ 1)]
  have hkey : (∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w))
      = (Gaux y dt 1 - Gaux y dt 0)
        - (∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)) / dt ^ 2 := by
    rw [← hFTC, hsplit]; ring
  rw [hkey]
  have hb2' : |(∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)) / dt ^ 2| ≤ 10 / dt ^ 2 := by
    rw [abs_div, abs_of_pos hdt2]
    gcongr
  calc |(Gaux y dt 1 - Gaux y dt 0)
        - (∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)) / dt ^ 2|
      ≤ |Gaux y dt 1 - Gaux y dt 0|
        + |(∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)) / dt ^ 2| := abs_sub_le' _ _
    _ ≤ (|Gaux y dt 1| + |Gaux y dt 0|)
        + |(∫ w in (0:ℝ)..1, hf2 y w * Real.cos (dt * w)) / dt ^ 2| := by
        gcongr
        exact abs_sub_le' _ _
    _ ≤ 3 / dt ^ 2 + 2 / dt ^ 2 + 10 / dt ^ 2 := by linarith
    _ = 15 / dt ^ 2 := by ring

/-- **Lemma 1**: the explicit decay estimate, with `Cdec = 200`. -/
theorem abs_T_le {dt y : ℝ} (hdt : dt ≠ 0) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    |T dt y| ≤ Cdec / dt ^ 2 := by
  have hdt2 : (0:ℝ) < dt ^ 2 := by positivity
  have h := abs_integral_half_le hdt hy0 hy1
  rw [T, integral_symm_eq, abs_mul, abs_of_pos four_div_A_sq_pos, abs_mul]
  have h2 : |(2:ℝ)| = 2 := by norm_num
  rw [h2]
  have hstep : 2 * |∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w)| ≤ 30 / dt ^ 2 := by
    have : (30:ℝ) / dt ^ 2 = 2 * (15 / dt ^ 2) := by ring
    rw [this]; linarith
  have hnn : 0 ≤ 2 * |∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w)| := by positivity
  calc 4 / A ^ 2 * (2 * |∫ w in (0:ℝ)..1, hf y w * Real.cos (dt * w)|)
      ≤ 6 * (30 / dt ^ 2) := by
        exact mul_le_mul four_div_A_sq_le hstep hnn (by norm_num)
    _ = 180 / dt ^ 2 := by ring
    _ ≤ Cdec / dt ^ 2 := by
        rw [Cdec]
        gcongr
        norm_num

end TruncEst
