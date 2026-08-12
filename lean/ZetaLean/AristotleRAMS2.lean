/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

/-!
# Exact partial summation and the RC2 endpoint energy

This file records an exact finite Abel (partial) summation identity for a real
sequence indexed by the positive naturals, and derives from it two rigorous
estimates that feed the RC2 endpoint energy of `TwoRangeWeights`
(`twoRangeEndpointEnergy` there is exactly a lower `n^2 / x^2` weighted sum plus
an upper `x^2 / n^2` weighted sum):

* the lower-range bound `∑_{n ≤ N} b n * n ^ 2 ≤ C * N ^ 3 * (1 + log N)` under a
  prefix bound `prefixMass b n ≤ C * n * (1 + log n)`;
* the cutoff-independent upper-range inverse-square tail bound
  `∑_{X < n ≤ W} b n / n ^ 2 ≤ 10 * C * (1 + log X) / X`, whose right-hand side
  does not depend on the cutoff `W`.

Both are consequences of the same exact identity; no asymptotic notation is used
and every constant is explicit.

The module is self-contained over Mathlib: it deliberately avoids importing
`ZetaLean.MeanSquareAssembly`, so that it compiles independently of the rest of
the `HigherXi` chain, while living in the same namespace so that the statements
can be applied directly to `twoRangeEndpointEnergy` data.
-/

namespace ZetaLean.HigherXi

open Finset

/-! ## Prefix masses -/

/-- The prefix mass `∑_{n = 1}^{N} b n` of a real sequence. -/
noncomputable def prefixMass (b : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, b n

@[simp] theorem prefixMass_zero (b : ℕ → ℝ) : prefixMass b 0 = 0 := by
  simp [prefixMass]

theorem prefixMass_succ (b : ℕ → ℝ) (N : ℕ) :
    prefixMass b (N + 1) = prefixMass b N + b (N + 1) := by
  rw [prefixMass, prefixMass, Finset.sum_Icc_succ_top (by omega)]

theorem prefixMass_nonneg {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (N : ℕ) :
    0 ≤ prefixMass b N :=
  Finset.sum_nonneg fun n _ => hb n

/-! ## Exact Abel summation -/

/-- Exact Abel summation over a half-open range: for `X ≤ W`,
`∑_{X < n ≤ W} b n * w n` equals the terminal mass times `w W` plus the
telescoped sum of the running masses against the backward differences of `w`. -/
theorem sum_mul_eq_prefixMass_abel_Ioc (b w : ℕ → ℝ) (X W : ℕ) (hXW : X ≤ W) :
    ∑ n ∈ Finset.Ioc X W, b n * w n =
      (prefixMass b W - prefixMass b X) * w W +
        ∑ n ∈ Finset.Ico X W,
          (prefixMass b n - prefixMass b X) * (w n - w (n + 1)) := by
  induction W, hXW using Nat.le_induction with
  | base => simp
  | succ W hXW ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), ih,
        Finset.sum_Ico_succ_top hXW, prefixMass_succ]
      ring

/-- Exact finite Abel summation on `Finset.Icc 1 N`:
`∑_{n = 1}^{N} b n * w n = prefixMass b N * w N
  + ∑_{n = 1}^{N - 1} prefixMass b n * (w n - w (n + 1))`. -/
theorem sum_mul_eq_prefixMass_abel (b w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, b n * w n =
      prefixMass b N * w N +
        ∑ n ∈ Finset.Icc 1 (N - 1), prefixMass b n * (w n - w (n + 1)) := by
  have h := sum_mul_eq_prefixMass_abel_Ioc b w 0 N (Nat.zero_le N)
  simp only [prefixMass_zero, sub_zero] at h
  rw [show Finset.Ioc 0 N = Finset.Icc 1 N by
        ext n; simp [Nat.lt_iff_add_one_le]] at h
  rw [h]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · rw [Finset.sum_eq_sum_Ico_succ_bot hN]
    have hset : Finset.Ico (0 + 1) N = Finset.Icc 1 (N - 1) := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc, zero_add]
      omega
    rw [hset]
    simp

/-- The same finite Abel identity with its difference range written directly
as `Ico 1 N`.  This is the statement submitted in the narrow Aristotle
control job. -/
theorem finite_abel_summation (b w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, b n * w n) =
      prefixMass b N * w N +
        ∑ n ∈ Finset.Ico 1 N,
          prefixMass b n * (w n - w (n + 1)) := by
  induction N with
  | zero => simp [prefixMass]
  | succ N ih =>
    have hP : prefixMass b (N + 1) = prefixMass b N + b (N + 1) := by
      simp [prefixMass, Finset.sum_Icc_succ_top (Nat.le_add_left 1 N)]
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), ih, hP]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [prefixMass]
      ring
    · rw [Finset.sum_Ico_succ_top hN]
      ring

/-! ## Elementary logarithmic estimates -/

theorem one_add_log_natCast_nonneg (n : ℕ) : 0 ≤ 1 + Real.log n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have := Real.log_nonneg this
    linarith

/-- The weight `t ↦ (1 + log t) / t` is nonincreasing along the naturals from
`1` on. -/
theorem log_weight_div_antitone {X W : ℕ} (hX : 1 ≤ X) (hXW : X ≤ W) :
    (1 + Real.log W) / (W : ℝ) ≤ (1 + Real.log X) / (X : ℝ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hW0 : (0 : ℝ) < W := by
    exact_mod_cast lt_of_lt_of_le hX hXW
  have hXW' : (X : ℝ) ≤ W := by exact_mod_cast hXW
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hkey : Real.log W - Real.log X ≤ (W : ℝ) / X - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (W:ℝ)/X by positivity)
    rwa [Real.log_div hW0.ne' hX0.ne'] at this
  have e : (X : ℝ) * ((W : ℝ) / X - 1) = (W : ℝ) - X := by field_simp
  have h1 : (X : ℝ) * (Real.log W - Real.log X) ≤ (W : ℝ) - X := by
    have := mul_le_mul_of_nonneg_left hkey hX0.le
    rwa [e] at this
  have h2 : (X : ℝ) * Real.log X ≤ (W : ℝ) * Real.log X :=
    mul_le_mul_of_nonneg_right hXW' hlogX
  rw [div_le_div_iff₀ hW0 hX0]
  nlinarith

/-- The algebraic core of the telescoping step: if `B - A ≤ 1 / m` and
`1 / m ≤ B`, then the inverse-square increment at `m + 1` is absorbed by the
decrement of `t ↦ (2 + log t) / t`. -/
theorem log_invSq_step_algebra {m A B : ℝ} (hm : 0 < m)
    (hL : B - A ≤ 1 / m) (hB : 1 / m ≤ B) :
    (1 + B) / (m + 1) ^ 2 + (2 + B) / (m + 1) ≤ (2 + A) / m := by
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have hstep : (1 + B) / (m + 1) ^ 2 + (2 + B) / (m + 1) ≤ (2 + (B - 1 / m)) / m := by
    have hD : (2 + (B - 1 / m)) / m - ((1 + B) / (m + 1) ^ 2 + (2 + B) / (m + 1)) =
        (B - 1 / m) / (m * (m + 1) ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ (B - 1 / m) / (m * (m + 1) ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  refine hstep.trans ?_
  rw [div_le_div_iff_of_pos_right hm]
  linarith

/-- The one-step telescoping estimate behind the inverse-square logarithmic
tail: `(1 + log (n+1)) / (n+1)^2 + (2 + log (n+1)) / (n+1) ≤ (2 + log n) / n`
for every positive natural `n`. -/
theorem log_invSq_step {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 +
        (2 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) ≤
      (2 + Real.log n) / (n : ℝ) := by
  have hm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) by positivity)
    rw [Real.log_div (by linarith) hm0.ne'] at h
    have he : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp
      ring
    rw [he] at h
    exact h
  rcases eq_or_lt_of_le hm with heq | hlt
  · -- `n = 1`: the estimate is the numerical fact `log 2 ≤ 1`
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    rw [← heq]
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h2, Real.log_one]
    norm_num
    linarith
  · -- `n ≥ 2`: here `log (n+1) ≥ 1 ≥ 1 / n`
    have hm2 : (2 : ℝ) ≤ (n : ℝ) := by
      have hn2 : 2 ≤ n := by
        by_contra hcon
        have : n = 1 := by omega
        rw [this] at hlt
        norm_num at hlt
      exact_mod_cast hn2
    have hB1 : (1 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hinv : 1 / (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
      have : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one hm0]; linarith
      linarith
    exact log_invSq_step_algebra hm0 hL hinv

/-- The telescoped inverse-square logarithmic tail: for `1 ≤ X` and every cutoff
`W`, `∑_{X < n ≤ W} (1 + log n) / n ^ 2 ≤ (2 + log X) / X`. -/
theorem log_invSq_tail_le {X : ℕ} (hX : 1 ≤ X) (W : ℕ) :
    ∑ n ∈ Finset.Ioc X W, (1 + Real.log n) / (n : ℝ) ^ 2 ≤
      (2 + Real.log X) / (X : ℝ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  rcases Nat.lt_or_ge W X with hWX | hXW
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · have key : ∀ W, X ≤ W →
        (∑ n ∈ Finset.Ioc X W, (1 + Real.log n) / (n : ℝ) ^ 2) +
          (2 + Real.log W) / (W : ℝ) ≤ (2 + Real.log X) / (X : ℝ) := by
      intro W hXW
      induction W, hXW using Nat.le_induction with
      | base => simp
      | succ W hXW ih =>
          have hW1 : 1 ≤ W := le_trans hX hXW
          have hstep := log_invSq_step hW1
          rw [Finset.sum_Ioc_succ_top (by omega)]
          have hcast : ((W + 1 : ℕ) : ℝ) = (W : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          linarith
    have hmain := key W hXW
    have hW0 : (0 : ℝ) < W := by
      exact_mod_cast lt_of_lt_of_le hX hXW
    have hlogW : 0 ≤ Real.log W :=
      Real.log_nonneg (by exact_mod_cast le_trans hX hXW)
    have : 0 ≤ (2 + Real.log W) / (W : ℝ) := by positivity
    linarith

/-- The same tail estimate over the closed-open range starting at `X`, in the
normalized shape used below. -/
theorem log_invSq_Ico_le {X : ℕ} (hX : 1 ≤ X) (W : ℕ) :
    ∑ n ∈ Finset.Ico X W, (1 + Real.log n) / (n : ℝ) ^ 2 ≤
      3 * (1 + Real.log X) / (X : ℝ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hsub : Finset.Ico X W ⊆ insert X (Finset.Ioc X W) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_insert, Finset.mem_Ioc]
    rcases eq_or_lt_of_le hn.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h, by omega⟩
  have hnn : ∀ n : ℕ, 0 ≤ (1 + Real.log n) / (n : ℝ) ^ 2 :=
    fun n => div_nonneg (one_add_log_natCast_nonneg n) (by positivity)
  have h1 : ∑ n ∈ Finset.Ico X W, (1 + Real.log n) / (n : ℝ) ^ 2 ≤
      ∑ n ∈ insert X (Finset.Ioc X W), (1 + Real.log n) / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
  have hnotmem : X ∉ Finset.Ioc X W := by simp
  rw [Finset.sum_insert hnotmem] at h1
  have h2 := log_invSq_tail_le hX W
  have h3 : (1 + Real.log X) / (X : ℝ) ^ 2 ≤ (1 + Real.log X) / (X : ℝ) := by
    apply div_le_div_of_nonneg_left (one_add_log_natCast_nonneg X) hX0
    nlinarith [hX0, show (1 : ℝ) ≤ (X : ℝ) by exact_mod_cast hX]
  have h4 : (2 + Real.log X) / (X : ℝ) ≤ 2 * (1 + Real.log X) / (X : ℝ) := by
    rw [div_le_div_iff_of_pos_right hX0]
    linarith
  have h5 : 3 * (1 + Real.log X) / (X : ℝ) =
      (1 + Real.log X) / (X : ℝ) + 2 * (1 + Real.log X) / (X : ℝ) := by
    field_simp
    ring
  rw [h5]
  linarith

/-! ## The RC2 endpoint-energy estimates -/

/-- **Lower-range endpoint energy.**  If `b` is nonnegative and its prefix mass
obeys `prefixMass b n ≤ C * n * (1 + log n)`, then the `n ^ 2`-weighted sum over
`n ≤ N` is at most `C * N ^ 3 * (1 + log N)`. -/
theorem sum_mul_sq_le_of_prefixMass_le {b : ℕ → ℝ} {C : ℝ} (N : ℕ)
    (hb : ∀ n, 0 ≤ b n)
    (hpre : ∀ n, 1 ≤ n → prefixMass b n ≤ C * n * (1 + Real.log n)) :
    ∑ n ∈ Finset.Icc 1 N, b n * (n : ℝ) ^ 2 ≤ C * (N : ℝ) ^ 3 * (1 + Real.log N) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · have habel := sum_mul_eq_prefixMass_abel b (fun n => (n : ℝ) ^ 2) N
    have hneg : ∑ n ∈ Finset.Icc 1 (N - 1),
        prefixMass b n * (((n : ℝ) ^ 2) - (((n + 1 : ℕ) : ℝ) ^ 2)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro n _
      have h1 : 0 ≤ prefixMass b n := prefixMass_nonneg hb n
      have h2 : ((n : ℝ) ^ 2) - (((n + 1 : ℕ) : ℝ) ^ 2) ≤ 0 := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    have hterm : prefixMass b N * (N : ℝ) ^ 2 ≤ C * (N : ℝ) ^ 3 * (1 + Real.log N) := by
      have h := hpre N hN
      have hsq : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
      calc prefixMass b N * (N : ℝ) ^ 2 ≤ (C * N * (1 + Real.log N)) * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h hsq
        _ = C * (N : ℝ) ^ 3 * (1 + Real.log N) := by ring
    rw [habel]
    linarith

/-- **Upper-range inverse-square tail, independent of the cutoff.**  If `b` is
nonnegative and its prefix mass obeys `prefixMass b n ≤ C * n * (1 + log n)`,
then for every `1 ≤ X` and every cutoff `W`,
`∑_{X < n ≤ W} b n / n ^ 2 ≤ 10 * C * (1 + log X) / X`.  The bound does not
depend on `W`. -/
theorem tail_div_sq_le_of_prefixMass_le {b : ℕ → ℝ} {C : ℝ} {X : ℕ} (W : ℕ)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hb : ∀ n, 0 ≤ b n)
    (hpre : ∀ n, 1 ≤ n → prefixMass b n ≤ C * n * (1 + Real.log n)) :
    ∑ n ∈ Finset.Ioc X W, b n / (n : ℝ) ^ 2 ≤
      10 * C * (1 + Real.log X) / (X : ℝ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  rcases Nat.lt_or_ge W X with hWX | hXW
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · have hW1 : 1 ≤ W := le_trans hX hXW
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
    set w : ℕ → ℝ := fun n => ((n : ℝ) ^ 2)⁻¹ with hw
    have hrewrite : ∑ n ∈ Finset.Ioc X W, b n / (n : ℝ) ^ 2 =
        ∑ n ∈ Finset.Ioc X W, b n * w n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hw, div_eq_mul_inv]
    rw [hrewrite, sum_mul_eq_prefixMass_abel_Ioc b w X W hXW]
    -- the terminal term
    have hterm : (prefixMass b W - prefixMass b X) * w W ≤
        C * (1 + Real.log X) / (X : ℝ) := by
      have h1 : prefixMass b W - prefixMass b X ≤ C * W * (1 + Real.log W) := by
        have := prefixMass_nonneg hb X
        have := hpre W hW1
        linarith
      have hwW : 0 ≤ w W := by rw [hw]; positivity
      have h2 : (prefixMass b W - prefixMass b X) * w W ≤
          (C * W * (1 + Real.log W)) * w W := mul_le_mul_of_nonneg_right h1 hwW
      have h3 : (C * W * (1 + Real.log W)) * w W =
          C * ((1 + Real.log W) / (W : ℝ)) := by
        rw [hw]
        field_simp
      have h4 : (1 + Real.log W) / (W : ℝ) ≤ (1 + Real.log X) / (X : ℝ) :=
        log_weight_div_antitone hX hXW
      have h5 : C * ((1 + Real.log W) / (W : ℝ)) ≤
          C * ((1 + Real.log X) / (X : ℝ)) := mul_le_mul_of_nonneg_left h4 hC
      have h6 : C * ((1 + Real.log X) / (X : ℝ)) = C * (1 + Real.log X) / (X : ℝ) := by
        ring
      rw [h3] at h2
      linarith
    -- the telescoped sum
    have hsum : ∑ n ∈ Finset.Ico X W,
        (prefixMass b n - prefixMass b X) * (w n - w (n + 1)) ≤
          9 * C * (1 + Real.log X) / (X : ℝ) := by
      have hbound : ∀ n ∈ Finset.Ico X W,
          (prefixMass b n - prefixMass b X) * (w n - w (n + 1)) ≤
            3 * C * ((1 + Real.log n) / (n : ℝ) ^ 2) := by
        intro n hn
        simp only [Finset.mem_Ico] at hn
        have hn1 : 1 ≤ n := le_trans hX hn.1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hdiff : 0 ≤ w n - w (n + 1) := by
          rw [hw]
          simp only
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          have : ((n : ℝ)) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
          have h2 : (((n : ℝ) + 1) ^ 2)⁻¹ ≤ ((n : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) this
          linarith
        have hP : prefixMass b n - prefixMass b X ≤ C * n * (1 + Real.log n) := by
          have := prefixMass_nonneg hb X
          have := hpre n hn1
          linarith
        have hstep : (C * n * (1 + Real.log n)) * (w n - w (n + 1)) ≤
            3 * C * ((1 + Real.log n) / (n : ℝ) ^ 2) := by
          have hkey : (n : ℝ) * (w n - w (n + 1)) ≤ 3 / (n : ℝ) ^ 2 := by
            rw [hw]
            simp only
            have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
            rw [hcast]
            have hexp : (n : ℝ) * (((n : ℝ) ^ 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹) =
                (2 * (n : ℝ) + 1) / ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by
              field_simp
              ring
            rw [hexp, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hn0, sq_nonneg ((n : ℝ) - 1)]
          have hCn : 0 ≤ C * (1 + Real.log n) :=
            mul_nonneg hC (one_add_log_natCast_nonneg n)
          have := mul_le_mul_of_nonneg_left hkey hCn
          calc (C * n * (1 + Real.log n)) * (w n - w (n + 1))
              = C * (1 + Real.log n) * ((n : ℝ) * (w n - w (n + 1))) := by ring
            _ ≤ C * (1 + Real.log n) * (3 / (n : ℝ) ^ 2) := this
            _ = 3 * C * ((1 + Real.log n) / (n : ℝ) ^ 2) := by ring
        calc (prefixMass b n - prefixMass b X) * (w n - w (n + 1))
            ≤ (C * n * (1 + Real.log n)) * (w n - w (n + 1)) :=
              mul_le_mul_of_nonneg_right hP hdiff
          _ ≤ 3 * C * ((1 + Real.log n) / (n : ℝ) ^ 2) := hstep
      have h1 := Finset.sum_le_sum hbound
      have h2 : ∑ n ∈ Finset.Ico X W, 3 * C * ((1 + Real.log n) / (n : ℝ) ^ 2) =
          3 * C * ∑ n ∈ Finset.Ico X W, (1 + Real.log n) / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
      have h3 := log_invSq_Ico_le hX W
      have h4 : 3 * C * ∑ n ∈ Finset.Ico X W, (1 + Real.log n) / (n : ℝ) ^ 2 ≤
          3 * C * (3 * (1 + Real.log X) / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : 3 * C * (3 * (1 + Real.log X) / (X : ℝ)) =
          9 * C * (1 + Real.log X) / (X : ℝ) := by ring
      rw [h2] at h1
      linarith
    have hfinal : C * (1 + Real.log X) / (X : ℝ) + 9 * C * (1 + Real.log X) / (X : ℝ) =
        10 * C * (1 + Real.log X) / (X : ℝ) := by ring
    linarith

end ZetaLean.HigherXi
