import Mathlib

namespace AristotleR

open MeasureTheory

noncomputable def normSqI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2

private lemma normSqI_nonneg (v : ℝ → ℝ) : 0 ≤ normSqI v := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u _
  positivity

private lemma expand_sq_integral (z g : ℝ → ℝ) (hz : Continuous z) (hg : Continuous g) (x : ℝ) :
    (∫ s in (-(1:ℝ)/2)..(1/2), (z s - x * g s) ^ 2)
      = normSqI g * (x * x) + (-2 * (∫ s in (-(1:ℝ)/2)..(1/2), z s * g s)) * x + normSqI z := by
  have h1 : ∀ s : ℝ, (z s - x * g s) ^ 2
      = z s ^ 2 - (2 * x) * (z s * g s) + x ^ 2 * (g s ^ 2) := by
    intro s; ring
  simp only [h1]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · simp only [normSqI]; ring
  · exact ((hz.pow 2).intervalIntegrable _ _)
  · exact ((continuous_const.mul (hz.mul hg)).intervalIntegrable _ _)
  · exact (((hz.pow 2).sub (continuous_const.mul (hz.mul hg))).intervalIntegrable _ _)
  · exact ((continuous_const.mul (hg.pow 2)).intervalIntegrable _ _)

private lemma interval_cauchy_schwarz (z g : ℝ → ℝ) (hz : Continuous z) (hg : Continuous g) :
    (∫ s in (-(1:ℝ)/2)..(1/2), z s * g s)
      ≤ Real.sqrt (normSqI z) * Real.sqrt (normSqI g) := by
  set I := ∫ s in (-(1:ℝ)/2)..(1/2), z s * g s
  have key : ∀ x : ℝ, 0 ≤ normSqI g * (x * x) + (-2 * I) * x + normSqI z := by
    intro x
    rw [← expand_sq_integral z g hz hg x]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u _
    positivity
  have hd := discrim_le_zero key
  have hsq : I ^ 2 ≤ normSqI z * normSqI g := by
    simp only [discrim] at hd
    nlinarith
  have h2 : I ≤ Real.sqrt (normSqI z * normSqI g) := by
    have : I ≤ |I| := le_abs_self I
    refine this.trans ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul (normSqI_nonneg z)] at h2

theorem resolvent_linf_bound
    (K : ℝ → ℝ → ℝ) (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K s t) ≤ 4 / 9)
    (z g : ℝ → ℝ) (hz : Continuous z) (hg : Continuous g)
    (Bz Bg : ℝ)
    (hBz : ∀ s : ℝ, |s| ≤ 1/2 → |z s| ≤ Bz)
    (hBzmin : ∀ C : ℝ, (∀ s : ℝ, |s| ≤ 1/2 → |z s| ≤ C) → Bz ≤ C)
    (hBg : ∀ s : ℝ, |s| ≤ 1/2 → |g s| ≤ Bg)
    (heq : ∀ s : ℝ, |s| ≤ 1/2 →
      z s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t) = g s) :
    Bz ≤ (9/5) * Bg := by
  have hBz0 : 0 ≤ Bz := le_trans (abs_nonneg (z 0)) (hBz 0 (by norm_num))
  -- continuity of the kernel in the second variable
  have hKcont : ∀ s : ℝ, Continuous fun t : ℝ => K s t := by
    intro s
    exact hKc.comp (continuous_const.prodMk continuous_id)
  have hstep : ∀ s : ℝ, |s| ≤ 1/2 → |z s| ≤ Bg + (4/9) * Bz := by
    intro s hs
    have hint : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t| ≤ (4/9) * Bz := by
      have hup : (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t)
          ≤ (∫ t in (-(1:ℝ)/2)..(1/2), K s t * Bz) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact (((hKcont s).mul hz).intervalIntegrable _ _)
        · exact (((hKcont s).mul continuous_const).intervalIntegrable _ _)
        · intro u hu
          have hu' : |u| ≤ 1/2 := by
            rw [abs_le]; constructor <;> [linarith [hu.1]; linarith [hu.2]]
          have := (abs_le.mp (hBz u hu')).2
          exact mul_le_mul_of_nonneg_left this (hKnn s u)
      have hlo : (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (-Bz))
          ≤ (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact (((hKcont s).mul continuous_const).intervalIntegrable _ _)
        · exact (((hKcont s).mul hz).intervalIntegrable _ _)
        · intro u hu
          have hu' : |u| ≤ 1/2 := by
            rw [abs_le]; constructor <;> [linarith [hu.1]; linarith [hu.2]]
          have := (abs_le.mp (hBz u hu')).1
          exact mul_le_mul_of_nonneg_left this (hKnn s u)
      have hc1 : (∫ t in (-(1:ℝ)/2)..(1/2), K s t * Bz)
          = (∫ t in (-(1:ℝ)/2)..(1/2), K s t) * Bz :=
        intervalIntegral.integral_mul_const _ _
      have hc2 : (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (-Bz))
          = (∫ t in (-(1:ℝ)/2)..(1/2), K s t) * (-Bz) :=
        intervalIntegral.integral_mul_const _ _
      have hrows := hrow s
      have hrow0 : 0 ≤ (∫ t in (-(1:ℝ)/2)..(1/2), K s t) := by
        apply intervalIntegral.integral_nonneg (by norm_num)
        intro u _
        exact hKnn s u
      rw [hc1] at hup
      rw [hc2] at hlo
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    have hgs := hBg s hs
    have := heq s hs
    have hzs : z s = g s - (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t) := by linarith [this]
    rw [hzs, abs_le]
    have h1 := neg_abs_le (g s)
    have h2 := le_abs_self (g s)
    have h3 := neg_abs_le (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t)
    have h4 := le_abs_self (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t)
    constructor <;> linarith
  have := hBzmin _ hstep
  linarith

theorem resolvent_l2_bound
    (z g : ℝ → ℝ) (hz : Continuous z) (hg : Continuous g)
    (hcoer : (5/9) * normSqI z
      ≤ (∫ s in (-(1:ℝ)/2)..(1/2), z s * g s)) :
    Real.sqrt (normSqI z) ≤ (9/5) * Real.sqrt (normSqI g) := by
  have hcs := interval_cauchy_schwarz z g hz hg
  set a := Real.sqrt (normSqI z) with ha
  set b := Real.sqrt (normSqI g)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have haa : a ^ 2 = normSqI z := Real.sq_sqrt (normSqI_nonneg z)
  rcases eq_or_lt_of_le ha0 with h | h
  · rw [← h]; positivity
  · have h1 : (5/9) * a ^ 2 ≤ a * b := by rw [haa]; linarith
    nlinarith


end AristotleR