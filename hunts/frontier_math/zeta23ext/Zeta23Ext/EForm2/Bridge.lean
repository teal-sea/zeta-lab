import Zeta23Ext.EForm2.Fourier

/-!
# From the complex transform `Phi2` to real integrals

`Phi2` evaluated at real frequencies, at `s + i y` and at `2 i y` is expressed through the
real quantities `phiR`, `Pre`, `Qim`, `Shq`, `Aconst`.
-/

open scoped BigOperators
open MeasureTheory

namespace Retention.EForm2

/-- Integral of an odd function over a symmetric interval. -/
lemma integral_odd_symm (f : ℝ → ℝ) (a : ℝ) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x in (-a)..a, f x = 0 := by
  have h1 : ∫ x in (-a)..a, f (-x) = ∫ x in (-a)..a, f x := by
    rw [intervalIntegral.integral_comp_neg]
    simp
  have h2 : ∫ x in (-a)..a, f (-x) = ∫ x in (-a)..a, (-f x) := by
    simp_rw [hodd]
  rw [h2, intervalIntegral.integral_neg] at h1
  linarith

/-- Integrals of the window against a factor are interval integrals of `cos (√2 u)`. -/
lemma integral_gwin_mul (F : ℝ → ℂ) :
    (∫ u : ℝ, (gwin u : ℂ) * F u)
      = ∫ u in (-(1/2 : ℝ))..(1/2), (Real.cos (Real.sqrt 2 * u) : ℂ) * F u := by
  have h1 : (∫ u : ℝ, (gwin u : ℂ) * F u)
      = ∫ u in Set.Icc (-(1/2 : ℝ)) (1/2), (gwin u : ℂ) * F u := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro u hu
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    have hu' : 1/2 < |u| := by
      rcases hu with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [gwin_eq_zero hu']
    simp
  rw [h1, intervalIntegral.integral_of_le (by norm_num : (-(1/2 : ℝ)) ≤ 1/2),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro u hu
  simp only [Set.mem_Icc] at hu
  have hg : gwin u = Real.cos (Real.sqrt 2 * u) := by
    unfold gwin
    rw [if_pos (abs_le.2 ⟨by linarith [hu.1], hu.2⟩)]
  show (gwin u : ℂ) * F u = (Real.cos (Real.sqrt 2 * u) : ℂ) * F u
  rw [hg]

lemma Phi2_eval (z : ℂ) :
    Phi2 z = ∫ u in (-(1/2 : ℝ))..(1/2),
      (Real.cos (Real.sqrt 2 * u) : ℂ) * Complex.exp (Complex.I * z * u) :=
  integral_gwin_mul _

/-- The real/imaginary splitting of `Phi2` at `s + i y`. -/
lemma Phi2_shift (y s : ℝ) :
    Phi2 ((s : ℂ) + (y : ℂ) * Complex.I) = (Pre y s : ℂ) + (Qim y s : ℂ) * Complex.I := by
  rw [Phi2_eval]
  have hpt : ∀ u : ℝ, (Real.cos (Real.sqrt 2 * u) : ℂ) *
      Complex.exp (Complex.I * ((s : ℂ) + (y : ℂ) * Complex.I) * u)
      = ((Real.cos (Real.sqrt 2 * u) * (Real.cos (s * u) * Real.cosh (y * u))
            - Real.cos (Real.sqrt 2 * u) * (Real.cos (s * u) * Real.sinh (y * u)) : ℝ) : ℂ)
        + ((Real.cos (Real.sqrt 2 * u) * (Real.sin (s * u) * Real.cosh (y * u))
            - Real.cos (Real.sqrt 2 * u) * (Real.sin (s * u) * Real.sinh (y * u)) : ℝ) : ℂ)
          * Complex.I := by
    intro u
    have h1 : Complex.I * ((s : ℂ) + (y : ℂ) * Complex.I) * u
        = ((-(y * u) : ℝ) : ℂ) + ((s * u : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination ((y : ℂ) * u) * Complex.I_sq
    rw [h1, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_exp, ← Real.cosh_sub_sinh]
    push_cast
    ring
  have hR : (∫ u in (-(1/2 : ℝ))..(1/2),
      (Real.cos (Real.sqrt 2 * u) * (Real.cos (s * u) * Real.cosh (y * u))
        - Real.cos (Real.sqrt 2 * u) * (Real.cos (s * u) * Real.sinh (y * u)))) = Pre y s := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [integral_odd_symm (fun u => Real.cos (Real.sqrt 2 * u) *
        (Real.cos (s * u) * Real.sinh (y * u))) _ (fun x => by
      rw [show Real.sqrt 2 * -x = -(Real.sqrt 2 * x) by ring, show s * -x = -(s * x) by ring,
        show y * -x = -(y * x) by ring, Real.cos_neg, Real.cos_neg, Real.sinh_neg]
      ring)]
    simp [Pre]
  have hJ : (∫ u in (-(1/2 : ℝ))..(1/2),
      (Real.cos (Real.sqrt 2 * u) * (Real.sin (s * u) * Real.cosh (y * u))
        - Real.cos (Real.sqrt 2 * u) * (Real.sin (s * u) * Real.sinh (y * u)))) = Qim y s := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    rw [integral_odd_symm (fun u => Real.cos (Real.sqrt 2 * u) *
        (Real.sin (s * u) * Real.cosh (y * u))) _ (fun x => by
      rw [show Real.sqrt 2 * -x = -(Real.sqrt 2 * x) by ring, show s * -x = -(s * x) by ring,
        show y * -x = -(y * x) by ring, Real.cos_neg, Real.sin_neg, Real.cosh_neg]
      ring)]
    simp [Qim]
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hR, hJ]

/-- At a real frequency the transform is the real cosine transform `phiR`. -/
lemma Phi2_ofReal (r : ℝ) : Phi2 (r : ℂ) = (phiR r : ℂ) := by
  have h : ((r : ℂ)) = ((r : ℂ) + ((0:ℝ) : ℂ) * Complex.I) := by simp
  rw [h, Phi2_shift]
  have h1 : Qim 0 r = 0 := by
    unfold Qim
    simp
  have h2 : Pre 0 r = phiR r := by
    unfold Pre phiR
    simp
  rw [h1, h2]
  simp

/-- The integral of the window is `A`. -/
lemma integral_cos_sqrt_two : (∫ u in (-(1/2:ℝ))..(1/2), Real.cos (Real.sqrt 2 * u)) = Aconst := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) h2]
  simp only [integral_cos]
  have hs : Real.sqrt 2 * (1/2) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff h2]; nlinarith
  rw [show Real.sqrt 2 * -(1/2) = -(Real.sqrt 2 * (1/2)) by ring, hs, Real.sin_neg, smul_eq_mul]
  unfold Aconst
  field_simp
  rw [hsq]
  ring

lemma phiR_zero : phiR 0 = Aconst := by
  unfold phiR
  simp only [zero_mul, Real.cos_zero, mul_one]
  exact integral_cos_sqrt_two

/-- At the purely imaginary frequency `2 i y`. -/
lemma Phi2_two_mul_I (y : ℝ) :
    Phi2 (2 * (y : ℂ) * Complex.I) = ((Aconst + 2 * Shq y : ℝ) : ℂ) := by
  rw [Phi2_eval]
  have hpt : ∀ u : ℝ, (Real.cos (Real.sqrt 2 * u) : ℂ) *
      Complex.exp (Complex.I * (2 * (y : ℂ) * Complex.I) * u)
      = ((Real.cos (Real.sqrt 2 * u) * Real.cosh (2 * y * u)
          - Real.cos (Real.sqrt 2 * u) * Real.sinh (2 * y * u) : ℝ) : ℂ) := by
    intro u
    have h1 : Complex.I * (2 * (y : ℂ) * Complex.I) * u = ((-(2 * y * u) : ℝ) : ℂ) := by
      push_cast
      linear_combination (2 * (y : ℂ) * u) * Complex.I_sq
    rw [h1, ← Complex.ofReal_exp, ← Real.cosh_sub_sinh]
    push_cast
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_odd_symm (fun u => Real.cos (Real.sqrt 2 * u) * Real.sinh (2 * y * u)) _ (fun x => by
      rw [show Real.sqrt 2 * -x = -(Real.sqrt 2 * x) by ring,
        show 2 * y * -x = -(2 * y * x) by ring, Real.cos_neg, Real.sinh_neg]
      ring)]
  have hcosh : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * Real.cosh (2 * y * u)
      = Real.cos (Real.sqrt 2 * u) + 2 * (Real.cos (Real.sqrt 2 * u) * Real.sinh (y * u) ^ 2) := by
    intro u
    have h1 : Real.cosh (2 * y * u) = 2 * Real.sinh (y * u) ^ 2 + 1 := by
      rw [show 2 * y * u = 2 * (y * u) by ring, Real.cosh_two_mul, Real.cosh_sq]
      ring
    rw [h1]
    ring
  simp_rw [hcosh]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_cos_sqrt_two]
  simp [Shq]

lemma Aconst_pos : 0 < Aconst := by
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have h1 : 0 < 1 / Real.sqrt 2 := by positivity
  have h3 : 1 / Real.sqrt 2 < Real.pi := by
    have hs : Real.sqrt 2 ≥ 1 := by
      nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
    have : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one h2]; linarith
    linarith [Real.pi_gt_three]
  exact mul_pos h2 (Real.sin_pos_of_pos_of_lt_pi h1 h3)

lemma Phi2_zero : Phi2 0 = (Aconst : ℂ) := by
  have := Phi2_ofReal 0
  simpa [phiR_zero] using this

end Retention.EForm2
