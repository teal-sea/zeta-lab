import Mathlib

/-!
# A summation bound for separated points

If the points `s 0 < s 1 < ...` have consecutive gaps at least `δ`, and a nonnegative weight
`f i` is bounded both by `K` and (away from `s i = 0`) by `C / (s i)^2`, then the total weight is
at most `2 K + (10/3) C / δ^2`.
-/

open scoped BigOperators

namespace Retention.EForm2

/-- `∑_{k=1}^{N+1} 1/k² ≤ 5/3 - 1/(N + 3/2)`. -/
lemma sum_inv_sq_le_aux (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 5/3 - 1 / ((N : ℝ) + 3/2) := by
  induction N with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have key : (1 : ℝ) / (((M : ℕ) : ℝ) + 1 + 1) ^ 2
          ≤ 1 / ((M : ℝ) + 3/2) - 1 / ((M : ℝ) + 5/2) := by
        have h : 1 / ((M : ℝ) + 3/2) - 1 / ((M : ℝ) + 5/2)
            = 1 / (((M : ℝ) + 3/2) * ((M : ℝ) + 5/2)) := by
          field_simp
          ring
        rw [h]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
      push_cast at ih key ⊢
      rw [show ((M:ℝ) + 1 + 3/2) = (M:ℝ) + 5/2 by ring]
      linarith

/-- `∑_{k=1}^{N} 1/k² ≤ 5/3`. -/
lemma sum_inv_sq_le (N : ℕ) : ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 5/3 := by
  cases N with
  | zero => norm_num
  | succ M =>
      have h := sum_inv_sq_le_aux M
      have : (0:ℝ) < 1 / ((M : ℝ) + 3/2) := by positivity
      linarith

/-- Bound for a one-sided tail: the head term is bounded by `K`, the `k`-th further term by
`C / ((k+1) δ)²`. -/
lemma sum_tail_bound (M : ℕ) (g : ℕ → ℝ) (C δ K : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (h0 : 0 < M → g 0 ≤ K)
    (hk : ∀ k, k + 1 < M → g (k + 1) ≤ C / (((k : ℝ) + 1) * δ) ^ 2) :
    ∑ k ∈ Finset.range M, g k ≤ K + (5/3) * C / δ ^ 2 := by
  have hδ2 : (0:ℝ) < δ ^ 2 := by positivity
  cases M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      have : 0 ≤ (5/3) * C / δ ^ 2 := by positivity
      linarith
  | succ M' =>
      rw [Finset.sum_range_succ']
      have hhead : g 0 ≤ K := h0 (Nat.succ_pos _)
      have htail : ∑ k ∈ Finset.range M', g (k + 1)
          ≤ ∑ k ∈ Finset.range M', C / (((k : ℝ) + 1) * δ) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro k hk'
        exact hk k (by simpa using Nat.succ_lt_succ (Finset.mem_range.1 hk'))
      have hrw : ∑ k ∈ Finset.range M', C / (((k : ℝ) + 1) * δ) ^ 2
          = (C / δ ^ 2) * ∑ k ∈ Finset.range M', (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [mul_pow]
        field_simp
      have hsum := sum_inv_sq_le M'
      have hCd : 0 ≤ C / δ ^ 2 := by positivity
      have : ∑ k ∈ Finset.range M', C / (((k : ℝ) + 1) * δ) ^ 2 ≤ (5/3) * C / δ ^ 2 := by
        rw [hrw]
        have := mul_le_mul_of_nonneg_left hsum hCd
        calc (C / δ ^ 2) * ∑ k ∈ Finset.range M', (1 : ℝ) / ((k : ℝ) + 1) ^ 2
            ≤ (C / δ ^ 2) * (5/3) := this
          _ = (5/3) * C / δ ^ 2 := by ring
      linarith

/-- Consecutive separation implies a linear lower bound on the increments. -/
lemma sep_mono {n : ℕ} (s : ℕ → ℝ) (δ : ℝ)
    (hsep : ∀ i, i + 1 < n → s i + δ ≤ s (i + 1)) :
    ∀ j, j < n → ∀ i, i ≤ j → s i + ((j : ℝ) - (i : ℝ)) * δ ≤ s j := by
  intro j
  induction j with
  | zero =>
      intro _ i hi
      interval_cases i
      simp
  | succ j ih =>
      intro hj i hi
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have hij : i ≤ j := Nat.lt_succ_iff.1 h
        have h1 := ih (by omega) i hij
        have h2 := hsep j hj
        push_cast
        push_cast at h1
        linarith
      · have : i = j + 1 := le_antisymm hi h
        subst this
        simp

/-- The summation bound for `δ`-separated points. -/
lemma sum_le_of_separated {n : ℕ} (s : ℕ → ℝ) (δ K C : ℝ) (f : ℕ → ℝ)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsep : ∀ i, i + 1 < n → s i + δ ≤ s (i + 1))
    (hfK : ∀ i, i < n → f i ≤ K)
    (hfC : ∀ i, i < n → s i ≠ 0 → f i ≤ C / (s i) ^ 2) :
    ∑ i ∈ Finset.range n, f i ≤ 2 * K + (10/3) * C / δ ^ 2 := by
  have hδ2 : (0:ℝ) < δ ^ 2 := by positivity
  have hmono := sep_mono s δ hsep
  have hCd : 0 ≤ (5/3) * C / δ ^ 2 := by positivity
  -- a general step: if `|s i| ≥ (k : ℝ) * δ` with `k ≥ 1` then `f i ≤ C / (k δ)^2`
  have step : ∀ i, i < n → ∀ k : ℝ, 0 < k → k * δ ≤ |s i| → f i ≤ C / (k * δ) ^ 2 := by
    intro i hi k hk hik
    have hpos : 0 < k * δ := mul_pos hk hδ
    have hs0 : s i ≠ 0 := by
      intro h
      rw [h] at hik
      simp at hik
      nlinarith
    have h1 := hfC i hi hs0
    have h2 : (k * δ) ^ 2 ≤ (s i) ^ 2 := by
      nlinarith [sq_abs (s i), abs_nonneg (s i)]
    calc f i ≤ C / (s i) ^ 2 := h1
      _ ≤ C / (k * δ) ^ 2 := by
          apply div_le_div_of_nonneg_left hC (by positivity) h2
  by_cases hT : ∃ i, i < n ∧ s i < 0
  · -- let `m` be the largest index with `s m < 0`
    classical
    set T : Finset ℕ := (Finset.range n).filter (fun i => s i < 0) with hTdef
    have hTne : T.Nonempty := by
      obtain ⟨i, hi, hsi⟩ := hT
      exact ⟨i, by simp [hTdef, Finset.mem_filter, Finset.mem_range, hi, hsi]⟩
    set m := T.max' hTne with hm
    have hmT : m ∈ T := T.max'_mem hTne
    have hmn : m < n := by
      have := Finset.mem_filter.1 hmT
      exact Finset.mem_range.1 this.1
    have hsm : s m < 0 := (Finset.mem_filter.1 hmT).2
    have hmax : ∀ i, i < n → m < i → 0 ≤ s i := by
      intro i hi hmi
      by_contra h
      push_neg at h
      have : i ∈ T := by simp [hTdef, Finset.mem_filter, Finset.mem_range, hi, h]
      exact absurd (Finset.le_max' T i this) (by omega)
    -- lower part: indices `i ≤ m`
    have hlow : ∀ i, i ≤ m → ((m : ℝ) - (i : ℝ)) * δ ≤ |s i| := by
      intro i hi
      have h1 := hmono m hmn i hi
      have : s i ≤ s m - ((m : ℝ) - i) * δ := by linarith
      have h2 : s i < 0 := by
        have hnn : 0 ≤ ((m : ℝ) - i) * δ := by
          have : (i:ℝ) ≤ (m:ℝ) := by exact_mod_cast hi
          nlinarith
        linarith
      rw [abs_of_neg h2]
      linarith
    have hpartA : ∑ i ∈ Finset.range (m + 1), f i ≤ K + (5/3) * C / δ ^ 2 := by
      have hre : ∑ i ∈ Finset.range (m + 1), f i
          = ∑ k ∈ Finset.range (m + 1), f (m + 1 - 1 - k) :=
        (Finset.sum_range_reflect (fun i => f i) (m + 1)).symm
      rw [hre]
      refine sum_tail_bound (m + 1) (fun k => f (m + 1 - 1 - k)) C δ K hδ hC hK
        (fun _ => by simpa using hfK m hmn) ?_
      intro k hk
      have hkm : k + 1 ≤ m := by omega
      have hidx : m + 1 - 1 - (k + 1) = m - (k + 1) := by omega
      simp only [hidx]
      have hbound : ((k : ℝ) + 1) * δ ≤ |s (m - (k + 1))| := by
        have := hlow (m - (k + 1)) (by omega)
        have hc : ((m - (k + 1) : ℕ) : ℝ) = (m : ℝ) - ((k : ℝ) + 1) := by
          have : ((m - (k+1) : ℕ) : ℝ) = (m : ℝ) - ((k + 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub hkm]
          rw [this]; push_cast; ring
        rw [hc] at this
        have heq : (m : ℝ) - ((m : ℝ) - ((k : ℝ) + 1)) = (k : ℝ) + 1 := by ring
        rw [heq] at this
        exact this
      exact step _ (by omega) ((k : ℝ) + 1) (by positivity) hbound
    -- upper part: indices `i > m`
    have hpartB : ∑ i ∈ Finset.Ico (m + 1) n, f i ≤ K + (5/3) * C / δ ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine sum_tail_bound (n - (m + 1)) (fun k => f (m + 1 + k)) C δ K hδ hC hK
        (fun hpos => by simpa using hfK (m + 1) (by omega)) ?_
      intro k hk
      have hkn : m + 1 + (k + 1) < n := by omega
      have hs : 0 ≤ s (m + 1 + (k + 1)) := hmax _ hkn (by omega)
      have h1 := hmono (m + 1 + (k + 1)) hkn (m + 1) (by omega)
      have hsm1 : 0 ≤ s (m + 1) := hmax (m+1) (by omega) (by omega)
      have hbound : ((k : ℝ) + 1) * δ ≤ |s (m + 1 + (k + 1))| := by
        rw [abs_of_nonneg hs]
        have hc : ((m + 1 + (k + 1) : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
          push_cast; ring
        rw [hc] at h1
        linarith
      exact step _ hkn ((k : ℝ) + 1) (by positivity) hbound
    have hsplit := Finset.sum_range_add_sum_Ico f (show m + 1 ≤ n by omega)
    have : ∑ i ∈ Finset.range n, f i
        = ∑ i ∈ Finset.range (m + 1), f i + ∑ i ∈ Finset.Ico (m + 1) n, f i := hsplit.symm
    rw [this]
    have h4 : (10/3) * C / δ ^ 2 = 2 * ((5/3) * C / δ ^ 2) := by ring
    linarith
  · -- all points are nonnegative
    push_neg at hT
    have hnn : ∀ i, i < n → 0 ≤ s i := fun i hi => hT i hi
    have h4 : (10/3) * C / δ ^ 2 = 2 * ((5/3) * C / δ ^ 2) := by ring
    refine le_trans ?_ (by linarith : K + (5/3) * C / δ ^ 2 ≤ 2 * K + (10/3) * C / δ ^ 2)
    refine sum_tail_bound n f C δ K hδ hC hK (fun hpos => hfK 0 hpos) ?_
    intro k hk
    have h1 := hmono (k + 1) hk 0 (Nat.zero_le _)
    have h2 : 0 ≤ s 0 := hnn 0 (by omega)
    have hbound : ((k : ℝ) + 1) * δ ≤ |s (k + 1)| := by
      rw [abs_of_nonneg (hnn (k+1) hk)]
      push_cast at h1
      linarith
    exact step _ hk ((k : ℝ) + 1) (by positivity) hbound

end Retention.EForm2
