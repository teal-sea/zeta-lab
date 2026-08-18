import Mathlib

namespace AristotleY

open MeasureTheory

theorem resolvent_linf_max
    (K : ℝ → ℝ → ℝ) (hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K s t) ≤ 4 / 9)
    (z g : ℝ → ℝ) (hz : Continuous z) (hg : Continuous g) (Bg : ℝ)
    (hBg : ∀ s : ℝ, |s| ≤ 1 / 2 → |g s| ≤ Bg)
    (heq : ∀ s : ℝ, |s| ≤ 1 / 2 →
      z s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * z t) = g s) :
    ∀ s : ℝ, |s| ≤ 1 / 2 → |z s| ≤ (9 / 5) * Bg := by
  have hab : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
  have hK1 : ∀ s : ℝ, Continuous fun t : ℝ => K s t := fun s =>
    hKc.comp (by continuity : Continuous fun t : ℝ => ((s, t) : ℝ × ℝ))
  -- maximum of |z| on the interval
  have hcomp : IsCompact (Set.Icc (-(1:ℝ)/2) (1/2)) := isCompact_Icc
  have hne : (Set.Icc (-(1:ℝ)/2) (1/2)).Nonempty := ⟨0, by constructor <;> norm_num⟩
  obtain ⟨s₀, hs₀S, hs₀max⟩ := hcomp.exists_isMaxOn hne hz.abs.continuousOn
  have hmem : ∀ s : ℝ, |s| ≤ 1/2 → s ∈ Set.Icc (-(1:ℝ)/2) (1/2) := by
    intro s hs
    rcases abs_le.mp hs with ⟨h1, h2⟩
    constructor <;> linarith
  have hs₀abs : |s₀| ≤ 1/2 := by
    rcases hs₀S with ⟨h1, h2⟩
    rw [abs_le]; constructor <;> linarith
  set M : ℝ := |z s₀| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg _
  have hdom : ∀ t ∈ Set.Icc (-(1:ℝ)/2) (1/2), |z t| ≤ M := fun t ht => hs₀max ht
  -- integrability facts
  have hint1 : IntervalIntegrable (fun t => |K s₀ t * z t|) volume (-(1:ℝ)/2) (1/2) :=
    (((hK1 s₀).mul hz).abs).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => K s₀ t * M) volume (-(1:ℝ)/2) (1/2) :=
    ((hK1 s₀).mul continuous_const).intervalIntegrable _ _
  -- bound the integral term
  have key : |∫ t in (-(1:ℝ)/2)..(1/2), K s₀ t * z t| ≤ (4/9) * M := by
    calc |∫ t in (-(1:ℝ)/2)..(1/2), K s₀ t * z t|
        ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K s₀ t * z t| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), K s₀ t * M := by
          refine intervalIntegral.integral_mono_on hab hint1 hint2 ?_
          intro t ht
          rw [abs_mul, abs_of_nonneg (hKnn s₀ t)]
          exact mul_le_mul_of_nonneg_left (hdom t ht) (hKnn s₀ t)
      _ = (∫ t in (-(1:ℝ)/2)..(1/2), K s₀ t) * M := intervalIntegral.integral_mul_const _ _
      _ ≤ (4/9) * M := mul_le_mul_of_nonneg_right (hrow s₀) hM0
  have hMle : M ≤ (9/5) * Bg := by
    have h1 : |z s₀| ≤ |g s₀| + |∫ t in (-(1:ℝ)/2)..(1/2), K s₀ t * z t| := by
      have hz₀ := heq s₀ hs₀abs
      have hzeq : z s₀ = g s₀ - ∫ t in (-(1:ℝ)/2)..(1/2), K s₀ t * z t := by linarith
      rw [hzeq]
      exact abs_sub _ _
    have h2 : |g s₀| ≤ Bg := hBg s₀ hs₀abs
    have : M ≤ Bg + (4/9) * M := by
      rw [hMdef]; linarith
    linarith
  intro s hs
  exact le_trans (hs₀max (hmem s hs)) hMle


end AristotleY