import Zeta23Ext.EForm.Decomposition

open scoped BigOperators
open scoped Real
open MeasureTheory

namespace Retention

/-!
# Sharper single-point damage bound

This file refines the uniform bound `Icross y s ≥ - Ichy y` of `Energy.lean` into

  `Icross y s ≥ - Shq y * ((Aconst + 1/4) / 2)`,   `Shq y = ∫ gker u sinh (y u)² du`,

together with the exact identity `Ichy (2 y) = 4 Aconst · Shq y + 4 (Shq y)²`.  Since the pair
term's slack is `2 Ichy (2 y) ≥ 8 Aconst · Shq y` while `n` on-line points can do at most
`4 n · Shq y (Aconst + 1/4)/2` damage, the retention inequality follows whenever
`2 n (Aconst + 1/4) ≤ 8 Aconst`, i.e. (using `Aconst ≥ 3/4`) for `n ≤ 3`.

The two analytic inputs are

* Cauchy–Schwarz for the weight `gker`: `(∫ gker sinh (y u) sin (s u))² ≤ Shq y · Jsq s`;
* the uniform bound `Wcos r = ∫ gker u cos (r u) du ≥ -1/4` on the Fourier transform of the
  window, which gives `Jsq s = (Aconst - Wcos (2 s))/2 ≤ (Aconst + 1/4)/2`.
-/

/-! ## Linearity and Fubini helpers -/

lemma int4 {f1 f2 f3 f4 : ℝ → ℝ} (h1 : Integrable f1) (h2 : Integrable f2)
    (h3 : Integrable f3) (h4 : Integrable f4) :
    ∫ x : ℝ, (f1 x + f2 x - f3 x - f4 x)
      = (∫ x : ℝ, f1 x) + (∫ x : ℝ, f2 x) - (∫ x : ℝ, f3 x) - (∫ x : ℝ, f4 x) := by
  have H12 : Integrable (fun x : ℝ => f1 x + f2 x) := h1.add h2
  have H123 : Integrable (fun x : ℝ => f1 x + f2 x - f3 x) := H12.sub h3
  rw [integral_sub H123 h4, integral_sub H12 h3, integral_add h1 h2]

/-- Four-term version of the autocorrelation identity: if `h (u - v)` splits as a combination
`a₁(u)b₁(v) + a₂(u)b₂(v) - a₃(u)b₃(v) - a₄(u)b₄(v)`, then `∫ c₂ h` is the corresponding
combination of products of one-dimensional integrals against `gker`. -/
lemma master_four (a1 b1 a2 b2 a3 b3 a4 b4 h : ℝ → ℝ)
    (ha1 : Continuous a1) (hb1 : Continuous b1) (ha2 : Continuous a2) (hb2 : Continuous b2)
    (ha3 : Continuous a3) (hb3 : Continuous b3) (ha4 : Continuous a4) (hb4 : Continuous b4)
    (hh : Continuous h)
    (hexp : ∀ u v : ℝ, h (u - v) = a1 u * b1 v + a2 u * b2 v - a3 u * b3 v - a4 u * b4 v) :
    ∫ w : ℝ, c2 w * h w
      = (∫ u : ℝ, gker u * a1 u) * (∫ v : ℝ, gker v * b1 v)
      + (∫ u : ℝ, gker u * a2 u) * (∫ v : ℝ, gker v * b2 v)
      - (∫ u : ℝ, gker u * a3 u) * (∫ v : ℝ, gker v * b3 v)
      - (∫ u : ℝ, gker u * a4 u) * (∫ v : ℝ, gker v * b4 v) := by
  rw [master h hh]
  have key : ∀ u : ℝ, (∫ v : ℝ, gker u * gker v * h (u - v))
      = (gker u * a1 u) * (∫ v : ℝ, gker v * b1 v)
        + (gker u * a2 u) * (∫ v : ℝ, gker v * b2 v)
        - (gker u * a3 u) * (∫ v : ℝ, gker v * b3 v)
        - (gker u * a4 u) * (∫ v : ℝ, gker v * b4 v) := by
    intro u
    have hcong : (∫ v : ℝ, gker u * gker v * h (u - v))
        = ∫ v : ℝ, (gker u * gker v * (a1 u * b1 v) + gker u * gker v * (a2 u * b2 v)
            - gker u * gker v * (a3 u * b3 v) - gker u * gker v * (a4 u * b4 v)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      show gker u * gker v * h (u - v) = _
      rw [hexp u v]; ring
    rw [hcong, int4 (prod_integrand_integrable hb1 (a1 u) u)
        (prod_integrand_integrable hb2 (a2 u) u) (prod_integrand_integrable hb3 (a3 u) u)
        (prod_integrand_integrable hb4 (a4 u) u),
      inner_factor b1 (a1 u) u, inner_factor b2 (a2 u) u, inner_factor b3 (a3 u) u,
      inner_factor b4 (a4 u) u]
  simp_rw [key]
  rw [int4 ((gker_mul_integrable ha1).mul_const _) ((gker_mul_integrable ha2).mul_const _)
      ((gker_mul_integrable ha3).mul_const _) ((gker_mul_integrable ha4).mul_const _),
    integral_mul_const, integral_mul_const, integral_mul_const, integral_mul_const]

/-- Integrals of odd functions against the even window `gker` vanish. -/
lemma gker_odd_integral {f : ℝ → ℝ} (hodd : ∀ u, f (-u) = -f u) :
    ∫ u : ℝ, gker u * f u = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => gker u * f u) volume
  have h2 : (∫ u : ℝ, gker (-u) * f (-u)) = -∫ u : ℝ, gker u * f u := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show gker (-u) * f (-u) = -(gker u * f u)
    rw [gker_even, hodd u]; ring
  rw [h2] at h
  linarith

/-- Restriction of a `gker`-weighted integral to `[-1/2, 1/2]`. -/
lemma gker_integral_interval (f : ℝ → ℝ) :
    ∫ u : ℝ, gker u * f u = ∫ u in (-(1/2):ℝ)..(1/2), Real.cos (Real.sqrt 2 * u) * f u := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc (-(1/2):ℝ) (1/2) → gker x * f x = 0 := by
    intro x hx
    have hx0 : gker x = 0 := by
      refine gker_of_gt ?_
      by_contra h
      push_neg at h
      exact hx ⟨by linarith [(abs_le.1 h).1], (abs_le.1 h).2⟩
    rw [hx0, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  rw [gker_of_le (abs_le.2 ⟨by linarith [hx.1], hx.2⟩)]

/-! ## The elementary bound `sin z / z ≥ -1/4` -/

lemma sin_ge_neg_quarter {z : ℝ} (hz : 0 < z) : -(1/4) * z ≤ Real.sin z := by
  rcases le_or_gt 4 z with h4 | h4
  · have := Real.neg_one_le_sin z; nlinarith
  · rcases le_or_gt z Real.pi with hp | hp
    · have := Real.sin_nonneg_of_nonneg_of_le_pi hz.le hp
      nlinarith
    · have h1 : Real.sin (z - Real.pi) = -Real.sin z := Real.sin_sub_pi z
      have h2 : Real.sin (z - Real.pi) ≤ z - Real.pi := Real.sin_le (by linarith)
      have h3 := Real.pi_gt_three
      nlinarith

lemma cos_int_lower (b : ℝ) : -(1/4:ℝ) ≤ ∫ u in (-(1/2):ℝ)..(1/2), Real.cos (b * u) := by
  rcases eq_or_ne b 0 with rfl | hb
  · norm_num
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hb, integral_cos, smul_eq_mul]
    have hz : Real.sin (b * (1/2)) - Real.sin (b * -(1/2)) = 2 * Real.sin (b * (1/2)) := by
      rw [show b * -(1/2) = -(b * (1/2)) by ring, Real.sin_neg]; ring
    rw [hz]
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · have h := sin_ge_neg_quarter (z := -(b * (1/2))) (by linarith)
      rw [Real.sin_neg] at h
      rw [inv_eq_one_div, div_mul_eq_mul_div, le_div_iff_of_neg hneg]
      nlinarith
    · have h := sin_ge_neg_quarter (z := b * (1/2)) (by linarith)
      rw [inv_eq_one_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith

/-! ## The four window integrals -/

/-- `Wcos s = ∫ gker u cos (s u) du`, the Fourier transform `Φ₂(s)` of the window. -/
noncomputable def Wcos (s : ℝ) : ℝ := ∫ u : ℝ, gker u * Real.cos (s * u)

/-- `Wsinh y s = ∫ gker u sinh (y u) sin (s u) du`. -/
noncomputable def Wsinh (y s : ℝ) : ℝ := ∫ u : ℝ, gker u * (Real.sinh (y * u) * Real.sin (s * u))

/-- `Shq y = ∫ gker u sinh (y u)² du ≥ 0`. -/
noncomputable def Shq (y : ℝ) : ℝ := ∫ u : ℝ, gker u * Real.sinh (y * u) ^ 2

/-- `Jsq s = ∫ gker u sin (s u)² du ≥ 0`. -/
noncomputable def Jsq (s : ℝ) : ℝ := ∫ u : ℝ, gker u * Real.sin (s * u) ^ 2

/-- `Pcos y s = ∫ gker u cosh (y u) cos (s u) du`, the `y`-deformation of `Φ₂(s)`. -/
noncomputable def Pcos (y s : ℝ) : ℝ := ∫ u : ℝ, gker u * (Real.cosh (y * u) * Real.cos (s * u))

/-- `Dcosh y = ∫ gker u (cosh (y u) - 1) du ≥ 0`. -/
noncomputable def Dcosh (y : ℝ) : ℝ := ∫ u : ℝ, gker u * (Real.cosh (y * u) - 1)

lemma Shq_nonneg (y : ℝ) : 0 ≤ Shq y :=
  integral_nonneg fun u => mul_nonneg (gker_nonneg u) (sq_nonneg _)

/-- Uniform lower bound on the Fourier transform of the window: `Φ₂(r) ≥ -1/4`. -/
lemma Wcos_lower (r : ℝ) : -(1/4:ℝ) ≤ Wcos r := by
  rw [Wcos, gker_integral_interval]
  have hint : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * Real.cos (r * u)
      = (Real.cos ((Real.sqrt 2 + r) * u) + Real.cos ((Real.sqrt 2 - r) * u)) / 2 := by
    intro u
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h1 := cos_int_lower (Real.sqrt 2 + r)
  have h2 := cos_int_lower (Real.sqrt 2 - r)
  linarith

/-- `∫ gker u sin (s u)² du = (A - Φ₂(2 s)) / 2`. -/
lemma Jsq_eq (s : ℝ) : Jsq s = (Aconst - Wcos (2 * s)) / 2 := by
  have hpt : ∀ u : ℝ, gker u * Real.sin (s * u) ^ 2
      = (1/2) * gker u - (1/2) * (gker u * Real.cos (2 * s * u)) := by
    intro u
    have hc : Real.cos (2 * s * u) = 1 - 2 * Real.sin (s * u) ^ 2 := by
      rw [show 2 * s * u = 2 * (s * u) by ring, Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (s * u)
      linarith
    rw [hc]; ring
  rw [Jsq]
  simp_rw [hpt]
  rw [integral_sub (gker_integrable.const_mul _)
      ((gker_mul_integrable (f := fun u => Real.cos (2 * s * u)) (by fun_prop)).const_mul _),
    integral_const_mul, integral_const_mul, integral_gker]
  have : Wcos (2 * s) = ∫ u : ℝ, gker u * Real.cos (2 * s * u) := by
    rw [Wcos]
  rw [this]
  ring

lemma Jsq_le (s : ℝ) : Jsq s ≤ (Aconst + 1/4) / 2 := by
  have h := Wcos_lower (2 * s)
  rw [Jsq_eq]
  linarith

/-! ## Cauchy–Schwarz -/

lemma Wsinh_sq_le (y s : ℝ) : (Wsinh y s) ^ 2 ≤ Shq y * Jsq s := by
  have key : ∀ r : ℝ, 0 ≤ Shq y * (r * r) + (-2 * Wsinh y s) * r + Jsq s := by
    intro r
    have hnn : 0 ≤ ∫ u : ℝ, gker u * (r * Real.sinh (y * u) - Real.sin (s * u)) ^ 2 :=
      integral_nonneg fun u => mul_nonneg (gker_nonneg u) (sq_nonneg _)
    have hpt : ∀ u : ℝ, gker u * (r * Real.sinh (y * u) - Real.sin (s * u)) ^ 2
        = (r ^ 2 * (gker u * Real.sinh (y * u) ^ 2)
            - 2 * r * (gker u * (Real.sinh (y * u) * Real.sin (s * u))))
          + gker u * Real.sin (s * u) ^ 2 := by
      intro u; ring
    rw [show (∫ u : ℝ, gker u * (r * Real.sinh (y * u) - Real.sin (s * u)) ^ 2)
        = ∫ u : ℝ, ((r ^ 2 * (gker u * Real.sinh (y * u) ^ 2)
            - 2 * r * (gker u * (Real.sinh (y * u) * Real.sin (s * u))))
          + gker u * Real.sin (s * u) ^ 2) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)] at hnn
    have I1 : Integrable (fun u : ℝ => r ^ 2 * (gker u * Real.sinh (y * u) ^ 2)) :=
      (gker_mul_integrable (f := fun u => Real.sinh (y * u) ^ 2) (by fun_prop)).const_mul _
    have I2 : Integrable
        (fun u : ℝ => 2 * r * (gker u * (Real.sinh (y * u) * Real.sin (s * u)))) :=
      (gker_mul_integrable (f := fun u => Real.sinh (y * u) * Real.sin (s * u))
        (by fun_prop)).const_mul _
    have I3 : Integrable (fun u : ℝ => gker u * Real.sin (s * u) ^ 2) :=
      gker_mul_integrable (f := fun u => Real.sin (s * u) ^ 2) (by fun_prop)
    have I12 : Integrable (fun u : ℝ => r ^ 2 * (gker u * Real.sinh (y * u) ^ 2)
        - 2 * r * (gker u * (Real.sinh (y * u) * Real.sin (s * u)))) := I1.sub I2
    rw [integral_add I12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul] at hnn
    rw [Shq, Wsinh, Jsq]
    nlinarith [hnn]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith

/-! ## The refined damage bound and the pair's slack -/

/-- `Icross y s = Pcos² + Q² - Wsinh²`, hence at least `Pcos y s ^ 2 - Wsinh y s ^ 2`. -/
lemma Icross_ge_Pcos (y s : ℝ) : (Pcos y s) ^ 2 - (Wsinh y s) ^ 2 ≤ Icross y s := by
  have hexp : ∀ u v : ℝ,
      (fun w => Real.cosh (y * w) * Real.cos (s * w)) (u - v)
        = (Real.cosh (y * u) * Real.cos (s * u)) * (Real.cosh (y * v) * Real.cos (s * v))
          + (Real.cosh (y * u) * Real.sin (s * u)) * (Real.cosh (y * v) * Real.sin (s * v))
          - (Real.sinh (y * u) * Real.cos (s * u)) * (Real.sinh (y * v) * Real.cos (s * v))
          - (Real.sinh (y * u) * Real.sin (s * u)) * (Real.sinh (y * v) * Real.sin (s * v)) := by
    intro u v
    show Real.cosh (y * (u - v)) * Real.cos (s * (u - v)) = _
    rw [mul_sub, mul_sub, Real.cosh_sub, Real.cos_sub]
    ring
  have hmaster := master_four
    (fun u => Real.cosh (y * u) * Real.cos (s * u))
    (fun v => Real.cosh (y * v) * Real.cos (s * v))
    (fun u => Real.cosh (y * u) * Real.sin (s * u))
    (fun v => Real.cosh (y * v) * Real.sin (s * v))
    (fun u => Real.sinh (y * u) * Real.cos (s * u))
    (fun v => Real.sinh (y * v) * Real.cos (s * v))
    (fun u => Real.sinh (y * u) * Real.sin (s * u))
    (fun v => Real.sinh (y * v) * Real.sin (s * v))
    (fun w => Real.cosh (y * w) * Real.cos (s * w))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) hexp
  have hodd : (∫ u : ℝ, gker u * (Real.sinh (y * u) * Real.cos (s * u))) = 0 := by
    refine gker_odd_integral (fun u => ?_)
    rw [show y * -u = -(y * u) by ring, show s * -u = -(s * u) by ring, Real.sinh_neg,
      Real.cos_neg]
    ring
  rw [Icross, hmaster, hodd]
  have h2 : 0 ≤ (∫ u : ℝ, gker u * (Real.cosh (y * u) * Real.sin (s * u)))
      * (∫ v : ℝ, gker v * (Real.cosh (y * v) * Real.sin (s * v))) := mul_self_nonneg _
  have h1 : (∫ u : ℝ, gker u * (Real.cosh (y * u) * Real.cos (s * u)))
      * (∫ v : ℝ, gker v * (Real.cosh (y * v) * Real.cos (s * v))) = (Pcos y s) ^ 2 := by
    rw [Pcos, sq]
  have h4 : (∫ u : ℝ, gker u * (Real.sinh (y * u) * Real.sin (s * u)))
      * (∫ v : ℝ, gker v * (Real.sinh (y * v) * Real.sin (s * v))) = (Wsinh y s) ^ 2 := by
    rw [Wsinh, sq]
  rw [h1, h4]
  nlinarith

/-- `Icross y s ≥ - Wsinh y s ^ 2`. -/
lemma Icross_ge_neg_sq (y s : ℝ) : -(Wsinh y s) ^ 2 ≤ Icross y s := by
  have := Icross_ge_Pcos y s
  nlinarith [sq_nonneg (Pcos y s)]

/-- The pair's slack, exactly: `Ichy (2 y) = 4 A · Shq y + 4 (Shq y)²`. -/
lemma Ichy_two_eq (y : ℝ) : Ichy (2 * y) = 4 * Aconst * Shq y + 4 * (Shq y) ^ 2 := by
  have hsplit : Ichy (2 * y)
      = (∫ w : ℝ, c2 w * Real.cosh (2 * y * w)) - ∫ w : ℝ, c2 w := by
    rw [Ichy]
    have : (∫ w : ℝ, c2 w * (Real.cosh (2 * y * w) - 1))
        = ∫ w : ℝ, (c2 w * Real.cosh (2 * y * w) - c2 w) :=
      integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
    rw [this, integral_sub (c2_mul_integrable (by fun_prop))
      (by simpa using c2_mul_integrable (f := fun _ : ℝ => (1:ℝ)) continuous_const)]
  have hexp : ∀ u v : ℝ, (fun w => Real.cosh (2 * y * w)) (u - v)
      = Real.cosh (2 * y * u) * Real.cosh (2 * y * v)
        + (fun _ : ℝ => (0:ℝ)) u * (fun _ : ℝ => (0:ℝ)) v
        - Real.sinh (2 * y * u) * Real.sinh (2 * y * v)
        - (fun _ : ℝ => (0:ℝ)) u * (fun _ : ℝ => (0:ℝ)) v := by
    intro u v
    show Real.cosh (2 * y * (u - v)) = _
    rw [mul_sub, Real.cosh_sub]
    ring
  have hmaster := master_four
    (fun u => Real.cosh (2 * y * u)) (fun v => Real.cosh (2 * y * v))
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    (fun u => Real.sinh (2 * y * u)) (fun v => Real.sinh (2 * y * v))
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    (fun w => Real.cosh (2 * y * w))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) hexp
  have hodd : (∫ u : ℝ, gker u * Real.sinh (2 * y * u)) = 0 := by
    refine gker_odd_integral (fun u => ?_)
    rw [show 2 * y * -u = -(2 * y * u) by ring, Real.sinh_neg]
  have hcosh : (∫ u : ℝ, gker u * Real.cosh (2 * y * u)) = Aconst + 2 * Shq y := by
    have hpt : ∀ u : ℝ, gker u * Real.cosh (2 * y * u)
        = gker u + 2 * (gker u * Real.sinh (y * u) ^ 2) := by
      intro u
      have : Real.cosh (2 * y * u) = 1 + 2 * Real.sinh (y * u) ^ 2 := by
        rw [show 2 * y * u = 2 * (y * u) by ring, Real.cosh_two_mul]
        have := Real.cosh_sq_sub_sinh_sq (y * u)
        linarith
      rw [this]; ring
    rw [show (∫ u : ℝ, gker u * Real.cosh (2 * y * u))
        = ∫ u : ℝ, (gker u + 2 * (gker u * Real.sinh (y * u) ^ 2)) from
      integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add gker_integrable
        ((gker_mul_integrable (f := fun u => Real.sinh (y * u) ^ 2) (by fun_prop)).const_mul _),
      integral_const_mul, integral_gker, Shq]
  rw [hsplit, hmaster, hodd, hcosh, c2_total]
  simp only [mul_zero, sub_zero]
  ring

/-! ## `A ≥ 3/4` -/

lemma Aconst_ge : (3:ℝ)/4 ≤ Aconst := by
  rw [Aconst]
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx0 : 0 < 1 / Real.sqrt 2 := by positivity
  have hx1 : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one h2]
    nlinarith
  have h := Real.sin_gt_sub_cube hx0 hx1
  have hcube : (1 / Real.sqrt 2) ^ 3 / 4 = 1 / (8 * Real.sqrt 2) := by
    field_simp
    nlinarith
  rw [hcube] at h
  have hval : Real.sqrt 2 * (1 / Real.sqrt 2 - 1 / (8 * Real.sqrt 2)) = 7/8 := by
    field_simp
    nlinarith
  nlinarith [Real.sin_le_one (1 / Real.sqrt 2)]

/-- **Refined single-point damage bound.**  One on-line point at offset `s` can erode at most
`Shq y (A + 1/4)/2` of the pair term's energy, uniformly in `s`. -/
lemma Icross_lower_sharp (y s : ℝ) : -(Shq y * ((Aconst + 1/4) / 2)) ≤ Icross y s := by
  have h1 := Icross_ge_neg_sq y s
  have h2 := Wsinh_sq_le y s
  have h3 := Jsq_le s
  have h4 := Shq_nonneg y
  nlinarith

/-! ## Localization of the damage -/

lemma Dcosh_nonneg (y : ℝ) : 0 ≤ Dcosh y :=
  integral_nonneg fun u =>
    mul_nonneg (gker_nonneg u) (by linarith [Real.one_le_cosh (y * u)])

lemma Dcosh_le_half_Shq (y : ℝ) : Dcosh y ≤ Shq y / 2 := by
  have hmono : (∫ u : ℝ, gker u * (Real.cosh (y * u) - 1))
      ≤ ∫ u : ℝ, (1/2) * (gker u * Real.sinh (y * u) ^ 2) := by
    refine integral_mono (gker_mul_integrable (by fun_prop))
      ((gker_mul_integrable (f := fun u => Real.sinh (y * u) ^ 2) (by fun_prop)).const_mul _)
      (fun u => ?_)
    have hc := Real.cosh_sq_sub_sinh_sq (y * u)
    have hg := gker_nonneg u
    nlinarith [mul_nonneg hg (sq_nonneg (Real.cosh (y * u) - 1))]
  rw [Dcosh, Shq]
  rw [integral_const_mul] at hmono
  linarith

/-- The `y`-deformation moves `Φ₂` by at most `Dcosh y`. -/
lemma Pcos_sub_Wcos_abs_le (y s : ℝ) : |Pcos y s - Wcos s| ≤ Dcosh y := by
  have hdiff : Pcos y s - Wcos s
      = ∫ u : ℝ, gker u * ((Real.cosh (y * u) - 1) * Real.cos (s * u)) := by
    rw [Pcos, Wcos, ← integral_sub (gker_mul_integrable (by fun_prop))
      (gker_mul_integrable (f := fun u => Real.cos (s * u)) (by fun_prop))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  rw [hdiff]
  calc |∫ u : ℝ, gker u * ((Real.cosh (y * u) - 1) * Real.cos (s * u))|
      ≤ ∫ u : ℝ, |gker u * ((Real.cosh (y * u) - 1) * Real.cos (s * u))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, gker u * (Real.cosh (y * u) - 1) := by
        refine integral_mono ((gker_mul_integrable (by fun_prop)).abs)
          (gker_mul_integrable (by fun_prop)) (fun u => ?_)
        have hg := gker_nonneg u
        have hch : 0 ≤ Real.cosh (y * u) - 1 := by linarith [Real.one_le_cosh (y * u)]
        have hcos : |Real.cos (s * u)| ≤ 1 := Real.abs_cos_le_one _
        rw [abs_mul, abs_mul, abs_of_nonneg hg, abs_of_nonneg hch]
        nlinarith [mul_nonneg hg hch, abs_nonneg (Real.cos (s * u))]
    _ = Dcosh y := rfl

/-- **Localization of the damage.**  A single on-line point at offset `s` can only erode the
pair term where `Φ₂(s)` is small: the damage `- Icross y s` is at most
`Shq y (A + 1/4)/2 - (|Φ₂(s)| - Shq y / 2)²`. -/
lemma Icross_localized (y s : ℝ) (h : Shq y / 2 ≤ |Wcos s|) :
    (|Wcos s| - Shq y / 2) ^ 2 - Shq y * ((Aconst + 1/4) / 2) ≤ Icross y s := by
  have hbase := Icross_ge_Pcos y s
  have hW := Wsinh_sq_le y s
  have hJ := Jsq_le s
  have hS := Shq_nonneg y
  have hD := Pcos_sub_Wcos_abs_le y s
  have hDS := Dcosh_le_half_Shq y
  have habs : |Wcos s| - Shq y / 2 ≤ |Pcos y s| := by
    have h1 : |Wcos s| - |Pcos y s| ≤ |Wcos s - Pcos y s| := abs_sub_abs_le_abs_sub _ _
    rw [abs_sub_comm] at h1
    linarith
  have hsq : (|Wcos s| - Shq y / 2) ^ 2 ≤ (Pcos y s) ^ 2 := by
    have h0 : (0:ℝ) ≤ |Wcos s| - Shq y / 2 := by linarith
    calc (|Wcos s| - Shq y / 2) ^ 2 ≤ |Pcos y s| ^ 2 := by nlinarith
      _ = (Pcos y s) ^ 2 := sq_abs _
  nlinarith

/-- Where `|Φ₂(s)|` is not small, a single on-line point does no damage at all. -/
lemma Icross_nonneg_of_Wcos_large (y s : ℝ) (h : Shq y / 2 ≤ |Wcos s|)
    (h2 : Shq y * ((Aconst + 1/4) / 2) ≤ (|Wcos s| - Shq y / 2) ^ 2) : 0 ≤ Icross y s := by
  have := Icross_localized y s h
  linarith

/-- The on-line interaction kernel is the square of the Fourier transform: `Icos s = Φ₂(s)²`. -/
lemma Icos_eq_sq (s : ℝ) : Icos s = (Wcos s) ^ 2 := by
  have hexp : ∀ u v : ℝ, (fun w => Real.cos (s * w)) (u - v)
      = Real.cos (s * u) * Real.cos (s * v) + Real.sin (s * u) * Real.sin (s * v)
        - (fun _ : ℝ => (0:ℝ)) u * (fun _ : ℝ => (0:ℝ)) v
        - (fun _ : ℝ => (0:ℝ)) u * (fun _ : ℝ => (0:ℝ)) v := by
    intro u v
    show Real.cos (s * (u - v)) = _
    rw [mul_sub, Real.cos_sub]
    ring
  have hmaster := master_four
    (fun u => Real.cos (s * u)) (fun v => Real.cos (s * v))
    (fun u => Real.sin (s * u)) (fun v => Real.sin (s * v))
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    (fun w => Real.cos (s * w))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) hexp
  have hodd : (∫ u : ℝ, gker u * Real.sin (s * u)) = 0 := by
    refine gker_odd_integral (fun u => ?_)
    rw [show s * -u = -(s * u) by ring, Real.sin_neg]
  rw [Icos, hmaster, hodd, Wcos, sq]
  simp

end Retention
