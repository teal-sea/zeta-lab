import Mathlib

namespace AristotleF

noncomputable def aCoef (k : ℕ) : ℝ :=
  2 ^ (2 * k + 3) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

noncomputable def F1 (x : ℝ) : ℝ :=
  |x| - 4 * x ^ 2 + ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3)

private lemma aCoef_nonneg (k : ℕ) : 0 ≤ aCoef k := by
  unfold aCoef; positivity

/-- Since `k ! * k ! ∣ (2 * k + 2)!`, the coefficients are bounded by `8 * 4 ^ k / k !`. -/
private lemma aCoef_le (k : ℕ) : aCoef k ≤ 8 * 4 ^ k / (Nat.factorial k : ℝ) := by
  have hfs : (Nat.factorial k) * (Nat.factorial k) ≤ Nat.factorial (2 * k + 2) :=
    le_trans (Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add k k)) (Nat.factorial_le (by omega))
  have hle : ((Nat.factorial k : ℝ)) * (Nat.factorial k : ℝ) ≤ (Nat.factorial (2 * k + 2) : ℝ) := by
    exact_mod_cast hfs
  have e1 : aCoef k = (8 * 4 ^ k * (Nat.factorial k : ℝ)) / (Nat.factorial (2 * k + 2) : ℝ) := by
    have h2 : (2 : ℝ) ^ (2 * k + 3) = 8 * 4 ^ k := by
      rw [pow_add, pow_mul]; norm_num [mul_comm]
    rw [aCoef, h2]
  have e2 : 8 * 4 ^ k / (Nat.factorial k : ℝ)
      = (8 * 4 ^ k * (Nat.factorial k : ℝ)) / ((Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)) := by
    field_simp
  rw [e1, e2]
  gcongr

theorem F1_summable_global (x : ℝ) :
    Summable fun k : ℕ => aCoef k * |x| ^ (2 * k + 3) := by
  have hexp : Summable fun k : ℕ => (4 * x ^ 2) ^ k / (Nat.factorial k : ℝ) :=
    Real.summable_pow_div_factorial _
  have hs : Summable fun k : ℕ => 8 * |x| ^ 3 * ((4 * x ^ 2) ^ k / (Nat.factorial k : ℝ)) :=
    hexp.mul_left _
  refine hs.of_nonneg_of_le (fun k => mul_nonneg (aCoef_nonneg k) (by positivity)) (fun k => ?_)
  have hx : |x| ^ (2 * k + 3) = |x| ^ 3 * (x ^ 2) ^ k := by
    rw [pow_add, pow_mul, sq_abs]; ring
  have h1 : aCoef k * |x| ^ (2 * k + 3)
      ≤ (8 * 4 ^ k / (Nat.factorial k : ℝ)) * |x| ^ (2 * k + 3) :=
    mul_le_mul_of_nonneg_right (aCoef_le k) (by positivity)
  refine h1.trans_eq ?_
  rw [hx, mul_pow]
  have hk : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  first
  | (field_simp; ring)
  | field_simp

theorem F1_nonneg_global (x : ℝ) : 0 ≤ F1 x := by
  have hsum := F1_summable_global x
  have h0 : ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3)
      = aCoef 0 * |x| ^ 3 + ∑' k : ℕ, aCoef (k + 1) * |x| ^ (2 * (k + 1) + 3) := by
    rw [hsum.tsum_eq_zero_add]
  have ha0 : aCoef 0 = 4 := by norm_num [aCoef, Nat.factorial]
  have htail : 0 ≤ ∑' k : ℕ, aCoef (k + 1) * |x| ^ (2 * (k + 1) + 3) :=
    tsum_nonneg (fun k => mul_nonneg (aCoef_nonneg (k + 1)) (by positivity))
  have hkey : 0 ≤ |x| - 4 * x ^ 2 + 4 * |x| ^ 3 := by
    have h : |x| - 4 * x ^ 2 + 4 * |x| ^ 3 = |x| * (1 - 2 * |x|) ^ 2 := by
      rw [← sq_abs x]; ring
    rw [h]; positivity
  unfold F1
  rw [h0, ha0]
  linarith


end AristotleF