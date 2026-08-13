import Zeta23Ext.EForm3.Master

/-!
# Closed forms

`Qre` and `Qim` are Fourier–Laplace transforms of the explicit window `g`, so they have
elementary closed forms, obtained here from explicit antiderivatives.
-/

open scoped BigOperators Real
open MeasureTheory

namespace Retention

/-- Transfer an integral against `g` to an interval integral. -/
lemma integral_g_mul_eq (k : ℝ → ℝ) :
    ∫ u : ℝ, g u * k u = ∫ u in (-(1/2):ℝ)..(1/2), Real.cos (Real.sqrt 2 * u) * k u := by
  have h1 : ∫ u : ℝ, g u * k u = ∫ u in Set.Icc (-(1/2):ℝ) (1/2), g u * k u := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [Set.mem_Icc] at hx
    push_neg at hx
    have : ¬ |x| ≤ 1/2 := by
      rw [abs_le]; push_neg; intro h; exact hx h
    rw [g_of_not_mem this, zero_mul]
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2), Set.mem_Icc] at hu
  show g u * k u = _
  rw [g_of_mem (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)]

lemma Qre_eq_interval (a b : ℝ) :
    Qre a b = ∫ u in (-(1/2):ℝ)..(1/2),
      Real.cos (Real.sqrt 2 * u) * (Real.cosh (a * u) * Real.cos (b * u)) := by
  rw [← integral_g_mul_eq (fun u : ℝ => Real.cosh (a * u) * Real.cos (b * u))]
  unfold Qre
  simp_rw [mul_assoc]

lemma Qim_eq_interval (a b : ℝ) :
    Qim a b = ∫ u in (-(1/2):ℝ)..(1/2),
      Real.cos (Real.sqrt 2 * u) * (Real.sinh (a * u) * Real.sin (b * u)) := by
  rw [← integral_g_mul_eq (fun u : ℝ => Real.sinh (a * u) * Real.sin (b * u))]
  unfold Qim
  simp_rw [mul_assoc]

/-! ### Elementary antiderivatives -/

/-- `∫_{c}^{d} sinh (a u) sin (k u) du` in closed form. -/
lemma integral_sinh_sin (a k : ℝ) (h : a ^ 2 + k ^ 2 ≠ 0) (c d : ℝ) :
    ∫ u in c..d, Real.sinh (a * u) * Real.sin (k * u)
      = (a * Real.cosh (a*d) * Real.sin (k*d) - k * Real.sinh (a*d) * Real.cos (k*d)) / (a^2+k^2)
        - (a * Real.cosh (a*c) * Real.sin (k*c) - k * Real.sinh (a*c) * Real.cos (k*c)) / (a^2+k^2)
        := by
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => (a * Real.cosh (a*u) * Real.sin (k*u)
        - k * Real.sinh (a*u) * Real.cos (k*u)) / (a^2+k^2))
      (Real.sinh (a*u) * Real.sin (k*u)) u := by
    intro u
    have hla : HasDerivAt (fun u : ℝ => a * u) a u := by
      simpa using (hasDerivAt_id u).const_mul a
    have hlk : HasDerivAt (fun u : ℝ => k * u) k u := by
      simpa using (hasDerivAt_id u).const_mul k
    have h1 : HasDerivAt (fun u : ℝ => Real.cosh (a*u)) (Real.sinh (a*u) * a) u :=
      (Real.hasDerivAt_cosh (a*u)).comp u hla
    have h2 : HasDerivAt (fun u : ℝ => Real.sin (k*u)) (Real.cos (k*u) * k) u :=
      (Real.hasDerivAt_sin (k*u)).comp u hlk
    have h3 : HasDerivAt (fun u : ℝ => Real.sinh (a*u)) (Real.cosh (a*u) * a) u :=
      (Real.hasDerivAt_sinh (a*u)).comp u hla
    have h4 : HasDerivAt (fun u : ℝ => Real.cos (k*u)) (-Real.sin (k*u) * k) u :=
      (Real.hasDerivAt_cos (k*u)).comp u hlk
    have h5 := (((h1.const_mul a).mul h2).sub ((h3.const_mul k).mul h4)).div_const (a^2+k^2)
    convert h5 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)]
  exact (Continuous.intervalIntegrable (by fun_prop) c d)

/-- `∫_{c}^{d} cosh (a u) cos (k u) du` in closed form. -/
lemma integral_cosh_cos (a k : ℝ) (h : a ^ 2 + k ^ 2 ≠ 0) (c d : ℝ) :
    ∫ u in c..d, Real.cosh (a * u) * Real.cos (k * u)
      = (a * Real.sinh (a*d) * Real.cos (k*d) + k * Real.cosh (a*d) * Real.sin (k*d)) / (a^2+k^2)
        - (a * Real.sinh (a*c) * Real.cos (k*c) + k * Real.cosh (a*c) * Real.sin (k*c)) / (a^2+k^2)
        := by
  have hderiv : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => (a * Real.sinh (a*u) * Real.cos (k*u)
        + k * Real.cosh (a*u) * Real.sin (k*u)) / (a^2+k^2))
      (Real.cosh (a*u) * Real.cos (k*u)) u := by
    intro u
    have hla : HasDerivAt (fun u : ℝ => a * u) a u := by
      simpa using (hasDerivAt_id u).const_mul a
    have hlk : HasDerivAt (fun u : ℝ => k * u) k u := by
      simpa using (hasDerivAt_id u).const_mul k
    have h1 : HasDerivAt (fun u : ℝ => Real.cosh (a*u)) (Real.sinh (a*u) * a) u :=
      (Real.hasDerivAt_cosh (a*u)).comp u hla
    have h2 : HasDerivAt (fun u : ℝ => Real.sin (k*u)) (Real.cos (k*u) * k) u :=
      (Real.hasDerivAt_sin (k*u)).comp u hlk
    have h3 : HasDerivAt (fun u : ℝ => Real.sinh (a*u)) (Real.cosh (a*u) * a) u :=
      (Real.hasDerivAt_sinh (a*u)).comp u hla
    have h4 : HasDerivAt (fun u : ℝ => Real.cos (k*u)) (-Real.sin (k*u) * k) u :=
      (Real.hasDerivAt_cos (k*u)).comp u hlk
    have h5 := (((h3.const_mul a).mul h4).add ((h1.const_mul k).mul h2)).div_const (a^2+k^2)
    convert h5 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)]
  exact (Continuous.intervalIntegrable (by fun_prop) c d)

lemma integral_cosh_cos_half (a k : ℝ) (h : a^2+k^2 ≠ 0) :
    ∫ u in (-(1/2):ℝ)..(1/2), Real.cosh (a*u) * Real.cos (k*u)
      = 2*(a * Real.sinh (a/2) * Real.cos (k/2) + k * Real.cosh (a/2) * Real.sin (k/2))/(a^2+k^2)
        := by
  rw [integral_cosh_cos a k h]
  rw [show a * -(1/2) = -(a/2) by ring, show k * -(1/2) = -(k/2) by ring,
    show a * (1/2:ℝ) = a/2 by ring, show k * (1/2:ℝ) = k/2 by ring,
    Real.sinh_neg, Real.cosh_neg, Real.cos_neg, Real.sin_neg]
  field_simp
  ring

lemma integral_sinh_sin_half (a k : ℝ) (h : a^2+k^2 ≠ 0) :
    ∫ u in (-(1/2):ℝ)..(1/2), Real.sinh (a*u) * Real.sin (k*u)
      = 2*(a * Real.cosh (a/2) * Real.sin (k/2) - k * Real.sinh (a/2) * Real.cos (k/2))/(a^2+k^2)
        := by
  rw [integral_sinh_sin a k h]
  rw [show a * -(1/2) = -(a/2) by ring, show k * -(1/2) = -(k/2) by ring,
    show a * (1/2:ℝ) = a/2 by ring, show k * (1/2:ℝ) = k/2 by ring,
    Real.sinh_neg, Real.cosh_neg, Real.cos_neg, Real.sin_neg]
  field_simp
  ring

/-- Closed form for `Qim`. -/
lemma Qim_closed (a b : ℝ) (hp : a^2+(b+Real.sqrt 2)^2 ≠ 0) (hm : a^2+(b-Real.sqrt 2)^2 ≠ 0) :
    Qim a b
      = (a * Real.cosh (a/2) * Real.sin ((b+Real.sqrt 2)/2)
          - (b+Real.sqrt 2) * Real.sinh (a/2) * Real.cos ((b+Real.sqrt 2)/2))
            /(a^2+(b+Real.sqrt 2)^2)
        + (a * Real.cosh (a/2) * Real.sin ((b-Real.sqrt 2)/2)
          - (b-Real.sqrt 2) * Real.sinh (a/2) * Real.cos ((b-Real.sqrt 2)/2))
            /(a^2+(b-Real.sqrt 2)^2) := by
  rw [Qim_eq_interval]
  have hint : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * (Real.sinh (a * u) * Real.sin (b * u))
      = (1/2) * (Real.sinh (a*u) * Real.sin ((b + Real.sqrt 2)*u))
        + (1/2) * (Real.sinh (a*u) * Real.sin ((b - Real.sqrt 2)*u)) := by
    intro u
    rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sinh_sin_half a _ hp, integral_sinh_sin_half a _ hm]
  ring

/-- Closed form for `Qre`. -/
lemma Qre_closed (a b : ℝ) (hp : a^2+(b+Real.sqrt 2)^2 ≠ 0) (hm : a^2+(b-Real.sqrt 2)^2 ≠ 0) :
    Qre a b
      = (a * Real.sinh (a/2) * Real.cos ((b+Real.sqrt 2)/2)
          + (b+Real.sqrt 2) * Real.cosh (a/2) * Real.sin ((b+Real.sqrt 2)/2))
            /(a^2+(b+Real.sqrt 2)^2)
        + (a * Real.sinh (a/2) * Real.cos ((b-Real.sqrt 2)/2)
          + (b-Real.sqrt 2) * Real.cosh (a/2) * Real.sin ((b-Real.sqrt 2)/2))
            /(a^2+(b-Real.sqrt 2)^2) := by
  rw [Qre_eq_interval]
  have hint : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * (Real.cosh (a * u) * Real.cos (b * u))
      = (1/2) * (Real.cosh (a*u) * Real.cos ((b + Real.sqrt 2)*u))
        + (1/2) * (Real.cosh (a*u) * Real.cos ((b - Real.sqrt 2)*u)) := by
    intro u
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cosh_cos_half a _ hp, integral_cosh_cos_half a _ hm]
  ring

lemma sqrt2_half : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  rw [eq_div_iff (by positivity), div_mul_eq_mul_div, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

@[simp] lemma Qim_zero_right (a : ℝ) : Qim a 0 = 0 := by
  unfold Qim; simp

@[simp] lemma Qim_zero_left (b : ℝ) : Qim 0 b = 0 := by
  unfold Qim; simp

lemma Aconst_pos : 0 < Aconst := by
  have h1 : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
  have h2 : 1 / Real.sqrt 2 < Real.pi := by
    have hgt : Real.sqrt 2 > 1 := by
      have : Real.sqrt 1 < Real.sqrt 2 := by apply Real.sqrt_lt_sqrt <;> norm_num
      simpa using this
    have : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one (by positivity)]; exact hgt
    linarith [Real.pi_gt_three]
  have hs := Real.sin_pos_of_pos_of_lt_pi h1 h2
  unfold Aconst
  exact mul_pos sqrt2_pos hs

lemma Aconst_ne_zero : Aconst ≠ 0 := ne_of_gt Aconst_pos

lemma Qre_zero_zero : Qre 0 0 = Aconst := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := sqrt2_sq
  rw [Qre_closed 0 0 (by rw [zero_add]; nlinarith) (by rw [zero_sub]; nlinarith)]
  rw [Aconst, ← sqrt2_half]
  simp
  rw [show (-Real.sqrt 2/2 : ℝ) = -(Real.sqrt 2/2) by ring, Real.sin_neg]
  ring

end Retention
