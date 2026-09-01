import ZetaLean.WScratch.EForm3.Integrability

/-!
# The master identity

`∫ c2 w * cosh (a w) cos (b w) dw = Qre a b ^ 2 - Qim a b ^ 2`.

This is the real form of `∫ c2 w e^{ζ w} dw = ĝ(ζ)^2` for `ζ = a + i b`, proved by Fubini
and a translation.
-/

open scoped BigOperators Real
open MeasureTheory

namespace Retention

/-- The four moment functions. -/
noncomputable def m1 (a b : ℝ) : ℝ → ℝ := fun v => g v * (Real.cosh (a * v) * Real.cos (b * v))
noncomputable def m2 (a b : ℝ) : ℝ → ℝ := fun v => g v * (Real.cosh (a * v) * Real.sin (b * v))
noncomputable def m3 (a b : ℝ) : ℝ → ℝ := fun v => g v * (Real.sinh (a * v) * Real.cos (b * v))
noncomputable def m4 (a b : ℝ) : ℝ → ℝ := fun v => g v * (Real.sinh (a * v) * Real.sin (b * v))

lemma integrable_m1 (a b : ℝ) : Integrable (m1 a b) :=
  integrable_g_mul (by fun_prop)
lemma integrable_m2 (a b : ℝ) : Integrable (m2 a b) :=
  integrable_g_mul (by fun_prop)
lemma integrable_m3 (a b : ℝ) : Integrable (m3 a b) :=
  integrable_g_mul (by fun_prop)
lemma integrable_m4 (a b : ℝ) : Integrable (m4 a b) :=
  integrable_g_mul (by fun_prop)

lemma integral_m1 (a b : ℝ) : ∫ v, m1 a b v = Qre a b := by
  unfold m1 Qre; simp_rw [mul_assoc]

lemma integral_m4 (a b : ℝ) : ∫ v, m4 a b v = Qim a b := by
  unfold m4 Qim; simp_rw [mul_assoc]

/-- An odd integrable function has zero integral. -/
lemma integral_eq_zero_of_odd' {f : ℝ → ℝ} (hodd : ∀ v, f (-v) = -f v) : ∫ v, f v = 0 := by
  have h : ∫ v, f v = - ∫ v, f v := by
    conv_lhs => rw [← integral_neg_eq_self f volume]
    simp_rw [hodd]
    rw [integral_neg]
  linarith

lemma integral_m2 (a b : ℝ) : ∫ v, m2 a b v = 0 := by
  refine integral_eq_zero_of_odd' (fun v => ?_)
  unfold m2
  rw [g_even]
  rw [show a * -v = -(a*v) by ring, show b * -v = -(b*v) by ring, Real.cosh_neg, Real.sin_neg]
  ring

lemma integral_m3 (a b : ℝ) : ∫ v, m3 a b v = 0 := by
  refine integral_eq_zero_of_odd' (fun v => ?_)
  unfold m3
  rw [g_even]
  rw [show a * -v = -(a*v) by ring, show b * -v = -(b*v) by ring, Real.sinh_neg, Real.cos_neg]
  ring

/-- Linearity of the integral for a four-term linear combination. -/
lemma integral_lin4 {f1 f2 f3 f4 : ℝ → ℝ} (h1 : Integrable f1) (h2 : Integrable f2)
    (h3 : Integrable f3) (h4 : Integrable f4) (c1 c2 c3 c4 : ℝ) :
    ∫ v, (c1 * f1 v + c2 * f2 v + c3 * f3 v + c4 * f4 v)
      = c1 * (∫ v, f1 v) + c2 * (∫ v, f2 v) + c3 * (∫ v, f3 v) + c4 * (∫ v, f4 v) := by
  have hI1 : Integrable (fun v => c1 * f1 v) := h1.const_mul c1
  have hI2 : Integrable (fun v => c2 * f2 v) := h2.const_mul c2
  have hI3 : Integrable (fun v => c3 * f3 v) := h3.const_mul c3
  have hI4 : Integrable (fun v => c4 * f4 v) := h4.const_mul c4
  have hI12 : Integrable (fun v => c1 * f1 v + c2 * f2 v) := hI1.add hI2
  have hI123 : Integrable (fun v => c1 * f1 v + c2 * f2 v + c3 * f3 v) := hI12.add hI3
  rw [integral_add hI123 hI4, integral_add hI12 hI3, integral_add hI1 hI2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- The inner integral after the translation. -/
lemma inner_integral (a b u : ℝ) :
    ∫ v, g v * (Real.cosh (a * (v - u)) * Real.cos (b * (v - u)))
      = (Real.cosh (a*u) * Real.cos (b*u)) * Qre a b
        - (Real.sinh (a*u) * Real.sin (b*u)) * Qim a b := by
  have hexp : ∀ v : ℝ, g v * (Real.cosh (a * (v - u)) * Real.cos (b * (v - u)))
      = (Real.cosh (a*u) * Real.cos (b*u)) * m1 a b v
        + (Real.cosh (a*u) * Real.sin (b*u)) * m2 a b v
        + (-(Real.sinh (a*u) * Real.cos (b*u))) * m3 a b v
        + (-(Real.sinh (a*u) * Real.sin (b*u))) * m4 a b v := by
    intro v
    rw [show a * (v - u) = a*v - a*u by ring, show b * (v - u) = b*v - b*u by ring,
      Real.cosh_sub, Real.cos_sub]
    unfold m1 m2 m3 m4
    ring
  simp_rw [hexp]
  rw [integral_lin4 (integrable_m1 a b) (integrable_m2 a b) (integrable_m3 a b)
    (integrable_m4 a b), integral_m1, integral_m2, integral_m3, integral_m4]
  ring

/-- **The master identity.** -/
theorem master (a b : ℝ) :
    ∫ w : ℝ, c2 w * (Real.cosh (a * w) * Real.cos (b * w)) = Qre a b ^ 2 - Qim a b ^ 2 := by
  have hkc : Continuous (fun w : ℝ => Real.cosh (a * w) * Real.cos (b * w)) := by fun_prop
  have h1 : ∀ w : ℝ, c2 w * (Real.cosh (a * w) * Real.cos (b * w))
      = ∫ u, g u * g (u + w) * (Real.cosh (a * w) * Real.cos (b * w)) := by
    intro w
    unfold c2
    rw [integral_mul_const]
  calc ∫ w : ℝ, c2 w * (Real.cosh (a * w) * Real.cos (b * w))
      = ∫ w : ℝ, ∫ u, g u * g (u + w) * (Real.cosh (a * w) * Real.cos (b * w)) := by
        simp_rw [← h1]
    _ = ∫ u : ℝ, ∫ w, g u * g (u + w) * (Real.cosh (a * w) * Real.cos (b * w)) :=
        integral_integral_swap (integrable_prod_c2 hkc)
    _ = ∫ u : ℝ, g u * (∫ w, g (u + w) * (Real.cosh (a * w) * Real.cos (b * w))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        show ∫ w, g u * g (u + w) * (Real.cosh (a * w) * Real.cos (b * w))
            = g u * (∫ w, g (u + w) * (Real.cosh (a * w) * Real.cos (b * w)))
        rw [← integral_const_mul]
        congr 1; funext w; ring
    _ = ∫ u : ℝ, g u * (∫ v, g v * (Real.cosh (a * (v - u)) * Real.cos (b * (v - u)))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        show g u * (∫ w, g (u + w) * (Real.cosh (a * w) * Real.cos (b * w)))
            = g u * (∫ v, g v * (Real.cosh (a * (v - u)) * Real.cos (b * (v - u))))
        congr 1
        have := integral_add_left_eq_self (μ := volume)
          (fun v : ℝ => g v * (Real.cosh (a * (v - u)) * Real.cos (b * (v - u)))) u
        rw [← this]
        congr 1; funext w
        rw [show u + w - u = w by ring]
    _ = ∫ u : ℝ, g u * ((Real.cosh (a*u) * Real.cos (b*u)) * Qre a b
          - (Real.sinh (a*u) * Real.sin (b*u)) * Qim a b) := by
        simp_rw [inner_integral]
    _ = Qre a b ^ 2 - Qim a b ^ 2 := by
        have hsplit : ∀ u : ℝ, g u * ((Real.cosh (a*u) * Real.cos (b*u)) * Qre a b
            - (Real.sinh (a*u) * Real.sin (b*u)) * Qim a b)
            = (Qre a b) * m1 a b u + (- Qim a b) * m4 a b u := by
          intro u; unfold m1 m4; ring
        simp_rw [hsplit]
        have hI1 : Integrable (fun v => (Qre a b) * m1 a b v) := (integrable_m1 a b).const_mul _
        have hI4 : Integrable (fun v => (- Qim a b) * m4 a b v) := (integrable_m4 a b).const_mul _
        rw [integral_add hI1 hI4, integral_const_mul, integral_const_mul, integral_m1, integral_m4]
        ring

end Retention
