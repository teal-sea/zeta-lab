import Mathlib

namespace AristotleO

open MeasureTheory intervalIntegral Finset

private lemma hd_left (s c : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => -(c / ((k : ℝ) + 1)) * (s - u) ^ (k + 1)) (c * (s - t) ^ k) t := by
  have h1 : HasDerivAt (fun u : ℝ => s - u) (-1) t := (hasDerivAt_id t).const_sub s
  have h2 : HasDerivAt (fun u : ℝ => (s - u) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * (s - t) ^ (k + 1 - 1) * (-1)) t := h1.pow (k + 1)
  have h3 := h2.const_mul (-(c / ((k : ℝ) + 1)))
  refine h3.congr_deriv ?_
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma hd_right (s c : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (c / ((k : ℝ) + 1)) * (u - s) ^ (k + 1)) (c * (t - s) ^ k) t := by
  have h1 : HasDerivAt (fun u : ℝ => u - s) 1 t := (hasDerivAt_id t).sub_const s
  have h2 : HasDerivAt (fun u : ℝ => (u - s) ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * (t - s) ^ (k + 1 - 1) * 1) t := h1.pow (k + 1)
  have h3 := h2.const_mul ((c / ((k : ℝ) + 1)))
  refine h3.congr_deriv ?_
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

private lemma pow_sub_aux (n : ℕ) (s t : ℝ) :
    t ^ n = ∑ i ∈ range (n + 1), (t - s) ^ i * s ^ (n - i) * (n.choose i : ℝ) := by
  have h := add_pow (t - s) s n
  simpa using h

/-- Binomial expansion used on the left piece. -/
private lemma binom_left (m n : ℕ) (s t : ℝ) :
    ∑ i ∈ range (n + 1),
        ((n.choose i : ℝ) * s ^ (n - i) * (-1) ^ i) * (s - t) ^ (m + i)
      = (s - t) ^ m * t ^ n := by
  rw [pow_sub_aux n s t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((-1 : ℝ)) ^ i * (s - t) ^ i = (t - s) ^ i := by
    rw [← mul_pow]; ring_nf
  rw [pow_add]
  linear_combination ((n.choose i : ℝ) * s ^ (n - i) * (s - t) ^ m) * h

/-- Binomial expansion used on the right piece. -/
private lemma binom_right (m n : ℕ) (s t : ℝ) :
    ∑ i ∈ range (n + 1),
        ((n.choose i : ℝ) * s ^ (n - i)) * (t - s) ^ (m + i)
      = (t - s) ^ m * t ^ n := by
  rw [pow_sub_aux n s t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

theorem integral_abs_pow_mul_pow (m n : ℕ) (s : ℝ) (hs : |s| ≤ 1/2) :
    (∫ t in (-(1:ℝ)/2)..(1/2), |s - t| ^ m * t ^ n)
      = ∑ i ∈ range (n + 1),
          (n.choose i : ℝ) * s ^ (n - i)
            * ((-1) ^ i * (s + 1/2) ^ (m + i + 1) + (1/2 - s) ^ (m + i + 1))
            / (m + i + 1) := by
  have habs := abs_le.mp hs
  have hs1 : -(1:ℝ)/2 ≤ s := by linarith [habs.1]
  have hs2 : s ≤ (1:ℝ)/2 := habs.2
  have hcont : Continuous fun t : ℝ => |s - t| ^ m * t ^ n :=
    (((continuous_const.sub continuous_id).abs).pow m).mul (continuous_pow n)
  have hcontL : Continuous fun t : ℝ => (s - t) ^ m * t ^ n :=
    ((continuous_const.sub continuous_id).pow m).mul (continuous_pow n)
  have hcontR : Continuous fun t : ℝ => (t - s) ^ m * t ^ n :=
    ((continuous_id.sub continuous_const).pow m).mul (continuous_pow n)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := -(1:ℝ)/2) (b := s) (c := (1:ℝ)/2) (f := fun t : ℝ => |s - t| ^ m * t ^ n)
    (hcont.intervalIntegrable (μ := volume) _ _) (hcont.intervalIntegrable (μ := volume) _ _)
  rw [← hsplit]
  -- rewrite the absolute values on each piece
  have hL : (∫ t in (-(1:ℝ)/2)..s, |s - t| ^ m * t ^ n)
      = ∫ t in (-(1:ℝ)/2)..s, (s - t) ^ m * t ^ n := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs1] at ht
    rw [abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ s - t)]
  have hR : (∫ t in s..(1:ℝ)/2, |s - t| ^ m * t ^ n)
      = ∫ t in s..(1:ℝ)/2, (t - s) ^ m * t ^ n := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hs2] at ht
    have : |s - t| = t - s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - s)]
    rw [this]
  rw [hL, hR]
  -- antiderivatives
  have hFL : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∑ i ∈ range (n + 1),
      -(((n.choose i : ℝ) * s ^ (n - i) * (-1) ^ i) / (((m + i : ℕ) : ℝ) + 1))
        * (s - u) ^ (m + i + 1)) ((s - t) ^ m * t ^ n) t := by
    intro t
    have h := HasDerivAt.sum (u := range (n + 1))
      (fun i _ => hd_left s ((n.choose i : ℝ) * s ^ (n - i) * (-1) ^ i) (m + i) t)
    have e : (∑ i ∈ range (n + 1), fun u : ℝ =>
        -(((n.choose i : ℝ) * s ^ (n - i) * (-1) ^ i) / (((m + i : ℕ) : ℝ) + 1))
          * (s - u) ^ (m + i + 1))
        = fun u : ℝ => ∑ i ∈ range (n + 1),
          -(((n.choose i : ℝ) * s ^ (n - i) * (-1) ^ i) / (((m + i : ℕ) : ℝ) + 1))
            * (s - u) ^ (m + i + 1) := by
      funext u; simp [Finset.sum_apply]
    rw [e] at h
    exact h.congr_deriv (binom_left m n s t)
  have hFR : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∑ i ∈ range (n + 1),
      (((n.choose i : ℝ) * s ^ (n - i)) / (((m + i : ℕ) : ℝ) + 1))
        * (u - s) ^ (m + i + 1)) ((t - s) ^ m * t ^ n) t := by
    intro t
    have h := HasDerivAt.sum (u := range (n + 1))
      (fun i _ => hd_right s ((n.choose i : ℝ) * s ^ (n - i)) (m + i) t)
    have e : (∑ i ∈ range (n + 1), fun u : ℝ =>
        (((n.choose i : ℝ) * s ^ (n - i)) / (((m + i : ℕ) : ℝ) + 1)) * (u - s) ^ (m + i + 1))
        = fun u : ℝ => ∑ i ∈ range (n + 1),
          (((n.choose i : ℝ) * s ^ (n - i)) / (((m + i : ℕ) : ℝ) + 1)) * (u - s) ^ (m + i + 1) := by
      funext u; simp [Finset.sum_apply]
    rw [e] at h
    exact h.congr_deriv (binom_right m n s t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFL x)
        (hcontL.intervalIntegrable (μ := volume) _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFR x)
        (hcontR.intervalIntegrable (μ := volume) _ _)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : ((m : ℝ) + (i : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [show s - -(1:ℝ)/2 = s + 1/2 by ring]
  rw [show (s : ℝ) - s = 0 by ring]
  rw [zero_pow (by omega : m + i + 1 ≠ 0)]
  field_simp
  ring


end AristotleO