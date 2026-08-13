import Mathlib

open Finset

namespace ShcTaylor

/-- The truncated series for `sinh t / t`, i.e. `∑_{k<n} t^(2k) / (2k+1)!`. -/
noncomputable def shcPartial (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range n, t ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℝ)

/-- The termwise-divided series: it sums to `sinh t / t` for `t ≠ 0` and to `1` at `t = 0`. -/
private lemma hasSum_shc (t : ℝ) :
    HasSum (fun k : ℕ => t ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℝ))
      (if t = 0 then 1 else Real.sinh t / t) := by
  by_cases h : t = 0
  · subst h
    rw [if_pos rfl]
    have hz : ∀ b : ℕ, b ≠ 0 →
        (0 : ℝ) ^ (2 * b) / (Nat.factorial (2 * b + 1) : ℝ) = 0 := by
      intro b hb
      have : 2 * b ≠ 0 := by omega
      simp [zero_pow this]
    simpa using hasSum_single (f := fun k : ℕ =>
      (0 : ℝ) ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℝ)) 0 hz
  · rw [if_neg h]
    have h1 := (Real.hasSum_sinh t).div_const t
    refine h1.congr_fun ?_
    intro k
    rw [div_div, pow_succ]
    field_simp

/-- `2 ^ k * (2n+1)! ≤ (2*(n+k)+1)!`. -/
private lemma factorial_pow_le (n k : ℕ) :
    2 ^ k * Nat.factorial (2 * n + 1) ≤ Nat.factorial (2 * (n + k) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : 2 * Nat.factorial (2 * (n + k) + 1) ≤
        Nat.factorial (2 * (n + (k + 1)) + 1) := by
      have h1 : 2 * (n + (k + 1)) + 1 = (2 * (n + k) + 1) + 1 + 1 := by ring
      rw [h1, Nat.factorial_succ, Nat.factorial_succ]
      have : 2 ≤ (2 * (n + k) + 1) + 1 := by omega
      calc 2 * Nat.factorial (2 * (n + k) + 1)
          ≤ ((2 * (n + k) + 1) + 1) * Nat.factorial (2 * (n + k) + 1) := by
            exact Nat.mul_le_mul_right _ this
        _ ≤ ((2 * (n + k) + 1) + 1 + 1) * (((2 * (n + k) + 1) + 1) *
              Nat.factorial (2 * (n + k) + 1)) := by
            exact Nat.le_mul_of_pos_left _ (by omega)
    calc 2 ^ (k + 1) * Nat.factorial (2 * n + 1)
        = 2 * (2 ^ k * Nat.factorial (2 * n + 1)) := by ring
      _ ≤ 2 * Nat.factorial (2 * (n + k) + 1) := by omega
      _ ≤ _ := hstep

/-- Termwise bound on the tail of the series, for `|t| ≤ 1`. -/
private lemma abs_term_le (n k : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    |t ^ (2 * (k + n)) / (Nat.factorial (2 * (k + n) + 1) : ℝ)|
      ≤ 1 / (Nat.factorial (2 * n + 1) : ℝ) * (1 / 2) ^ k := by
  have hfpos : (0 : ℝ) < (Nat.factorial (2 * (k + n) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hnum : |t ^ (2 * (k + n))| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg t) ht
  have hden : (2 : ℝ) ^ k * (Nat.factorial (2 * n + 1) : ℝ)
      ≤ (Nat.factorial (2 * (k + n) + 1) : ℝ) := by
    have := factorial_pow_le n k
    have h2 : n + k = k + n := by ring
    rw [h2] at this
    exact_mod_cast this
  rw [abs_div, abs_of_pos hfpos]
  have hpos : (0 : ℝ) < 2 ^ k * (Nat.factorial (2 * n + 1) : ℝ) := by
    have : (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    positivity
  have : |t ^ (2 * (k + n))| / (Nat.factorial (2 * (k + n) + 1) : ℝ)
      ≤ 1 / (2 ^ k * (Nat.factorial (2 * n + 1) : ℝ)) := by
    apply div_le_div₀ zero_le_one hnum hpos hden
  refine this.trans_eq ?_
  rw [one_div, one_div, one_div, mul_inv, mul_comm, inv_pow]

/-- **Truncation bound for `sinh t / t`, uniform down to `t = 0`.**

`sinhOverId t` is `sinh t / t` away from `0` and `1` at `0` — the removable
branch. The point of the statement is that the bound is uniform on `|t| ≤ 1`
INCLUDING at `t = 0`, which is why it cannot be obtained by dividing the
corresponding bound for `sinh` by `|t|`. -/
theorem shc_taylor (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : |t| ≤ 1) :
    |(if t = 0 then 1 else Real.sinh t / t) - shcPartial n t|
      ≤ 1 / (Nat.factorial (2 * n + 1) : ℝ) * 2 := by
  set f : ℕ → ℝ := fun k => t ^ (2 * k) / (Nat.factorial (2 * k + 1) : ℝ)
  have hs : HasSum f (if t = 0 then 1 else Real.sinh t / t) := hasSum_shc t
  have hsum : Summable f := hs.summable
  have hsplit : ∑ i ∈ range n, f i + ∑' i, f (i + n) = ∑' i, f i :=
    hsum.sum_add_tsum_nat_add n
  have htsum : ∑' i, f i = (if t = 0 then 1 else Real.sinh t / t) := hs.tsum_eq
  have hshc : shcPartial n t = ∑ i ∈ range n, f i := rfl
  have hkey : (if t = 0 then 1 else Real.sinh t / t) - shcPartial n t
      = ∑' i, f (i + n) := by
    rw [hshc, ← htsum, ← hsplit]; ring
  rw [hkey]
  -- comparison series
  set g : ℕ → ℝ := fun k => 1 / (Nat.factorial (2 * n + 1) : ℝ) * (1 / 2) ^ k with hgdef
  have hgsum : Summable g := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hbound : ∀ k, |f (k + n)| ≤ g k := by
    intro k
    exact abs_term_le n k t ht
  have habs : Summable fun k => |f (k + n)| :=
    hgsum.of_nonneg_of_le (fun k => abs_nonneg _) hbound
  calc |∑' i, f (i + n)| ≤ ∑' i, |f (i + n)| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun i => f (i + n)) (by simpa [Real.norm_eq_abs] using habs)
    _ ≤ ∑' i, g i := habs.tsum_le_tsum hbound hgsum
    _ = 1 / (Nat.factorial (2 * n + 1) : ℝ) * 2 := by
        rw [hgdef, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

end ShcTaylor

#print axioms ShcTaylor.shc_taylor
