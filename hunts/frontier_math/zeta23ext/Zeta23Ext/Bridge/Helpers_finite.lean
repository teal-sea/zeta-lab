/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

/-!
# Helpers for the finite steps S11, S13, S15 (bridge/finite)

Elementary facts about the kernel `k`, `w = k²`, sorted ordinates and seven-point windows that
the finite combinatorial steps share.  Nothing here is about ζ.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators

namespace Zeta23Ext.Bridge

/-! ### The kernel is even, `w ≥ 0`, and `|k| ≤ 1` -/

lemma Kfun_neg (x : ℝ) : Kfun (-x) = Kfun x := by
  unfold Kfun
  simp only [mul_neg, neg_mul, Real.cos_neg]

lemma kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
  unfold kfun; rw [Kfun_neg]

lemma wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
  unfold wfun; rw [kfun_neg]

lemma wfun_sub_comm (a b : ℝ) : wfun (a - b) = wfun (b - a) := by
  rw [← wfun_neg, neg_sub]

lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _

/-- `cos(√2 t) ≥ 0` on `[−1/2, 1/2]` since `√2/2 < π/2`. -/
lemma cos_sqrt_two_mul_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ Real.cos (Real.sqrt 2 * t) := by
  obtain ⟨h1, h2⟩ := ht
  have hs : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]

/-- `|K(x)| ≤ K(0)`: the integrand of `K(0)` is the nonnegative envelope of that of `K(x)`. -/
lemma abs_Kfun_le_Kfun_zero (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hle : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  refine (intervalIntegral.abs_integral_le_integral_abs hle).trans ?_
  refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro t ht
    rw [abs_mul, abs_of_nonneg (cos_sqrt_two_mul_nonneg ht)]
    calc Real.cos (Real.sqrt 2 * t) * |Real.cos (2 * Real.pi * x * t)|
        ≤ Real.cos (Real.sqrt 2 * t) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (cos_sqrt_two_mul_nonneg ht)
      _ = Real.cos (Real.sqrt 2 * t) := mul_one _

lemma abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := by
  unfold kfun
  rw [abs_div]
  rcases eq_or_ne (Kfun 0) 0 with h | h
  · rw [h, abs_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (abs_pos.mpr h)]
    exact (abs_Kfun_le_Kfun_zero x).trans (le_abs_self _)

lemma wfun_le_one (x : ℝ) : wfun x ≤ 1 := by
  unfold wfun
  rw [← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) (abs_kfun_le_one x)

/-! ### Sorted ordinates and seven-point windows -/

section Sorted

variable {m : ℕ}

/-- The sorted ordinates `y : Fin m → ℝ`, extended by `0` beyond `m`. -/
def sortedExt (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0

lemma sortedExt_of_lt (y : Fin m → ℝ) {n : ℕ} (h : n < m) : sortedExt y n = y ⟨n, h⟩ := by
  unfold sortedExt; rw [dif_pos h]

lemma sortedExt_mono {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
    sortedExt y a ≤ sortedExt y b := by
  rw [sortedExt_of_lt y (lt_of_le_of_lt hab hb), sortedExt_of_lt y hb]
  exact hy.monotone (Fin.mk_le_mk.mpr hab)

/-- The six gaps of the seven-point window starting at index `i`. -/
def windowGaps (Y : ℕ → ℝ) (i : ℕ) : Fin 6 → ℝ := fun j => Y (i + ((j : ℕ) + 1)) - Y (i + j)

lemma pts_windowGaps (Y : ℕ → ℝ) (i : ℕ) (k : Fin 7) :
    pts (windowGaps Y i) k = Y (i + k) - Y i := by
  unfold pts windowGaps
  simp only [Fin.sum_univ_six]
  fin_cases k <;> simp

lemma sum_windowGaps (Y : ℕ → ℝ) (i : ℕ) : ∑ j, windowGaps Y i j = Y (i + 6) - Y i := by
  unfold windowGaps
  simp only [Fin.sum_univ_six]
  simp

/-- `F6` on the gaps of a window, in terms of the ordinates. -/
lemma F6_windowGaps (p : ℕ) (Y : ℕ → ℝ) (i : ℕ) :
    F6 p (windowGaps Y i) = (1 / (p : ℝ)) * (Y (i + 6) - Y i)
      + ∑ a : Fin 7, ∑ b : Fin 7,
          if (a : ℕ) < (b : ℕ) then
            (2 / ((7 : ℝ) - (((b : ℕ) - (a : ℕ) : ℕ) : ℝ))) * wfun (Y (i + b) - Y (i + a))
          else 0 := by
  unfold F6
  rw [sum_windowGaps]
  congr 1
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [pts_windowGaps, pts_windowGaps,
    show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]

/-- `Σ_{i<n} (f(i+6) − f(i)) = Σ_{i<6} (f(n+i) − f(i))`. -/
lemma sum_shift_six_sub (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 6) - f i) = ∑ i ∈ range 6, (f (n + i) - f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [sum_range_succ, sum_range_zero, add_zero, add_assoc, Nat.reduceAdd, zero_add]
    ring

end Sorted

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms abs_kfun_le_one
#print axioms wfun_le_one
#print axioms pts_windowGaps
#print axioms F6_windowGaps
#print axioms sum_shift_six_sub

end Zeta23Ext.Bridge
