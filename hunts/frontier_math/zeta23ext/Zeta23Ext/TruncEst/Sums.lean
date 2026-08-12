import Zeta23Ext.TruncEst.Decay

/-!
# The finite and infinite lattice sums, and the two-sided truncation estimate

This file defines

* `Hnum n = ∑_{k=1}^n 1/k`, the harmonic number;
* `bM m s y = (2/m) * ∑_{d=1}^{m-1} (m - d) * T (d*s) y`;
* `bInf s y = 2 * ∑_{d=1}^∞ T (d*s) y`;

and establishes the **Main statement** of `PROBLEM.md`:

  `|bM m s y - bInf s y| ≤ (2*Cdec/s^2) * (Hnum (m-1)/m + 1/(m - 1/2))`

for `m ≥ 1`, `s > 0`, `y ∈ [0,1/2]`, following the three steps
(difference identity, head, tail).
-/

noncomputable section

open Real MeasureTheory Finset

namespace TruncEst

/-- The harmonic number `H n = ∑_{k=1}^{n} 1/k`. -/
def Hnum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

/-- The finite-cluster sum. -/
def bM (m : ℕ) (s y : ℝ) : ℝ :=
  (2 / m) * ∑ d ∈ Finset.Ico 1 m, ((m : ℝ) - d) * T (d * s) y

/-- The infinite-lattice sum. -/
def bInf (s y : ℝ) : ℝ := 2 * ∑' d : ℕ, T (((d : ℝ) + 1) * s) y

/-! ### Summability and termwise bounds -/

lemma cast_shift {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : ((k + (m - 1) : ℕ) : ℝ) + 1 = (k : ℝ) + m := by
  push_cast [Nat.cast_sub hm]
  ring

lemma abs_T_shift_le {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) (k : ℕ) :
    |T (((k : ℝ) + 1) * s) y| ≤ (Cdec / s ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hne : ((k : ℝ) + 1) * s ≠ 0 := by positivity
  have h := abs_T_le (dt := ((k : ℝ) + 1) * s) (y := y) hne hy0 hy1
  have hval : Cdec / (((k : ℝ) + 1) * s) ^ 2 = (Cdec / s ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    field_simp
  rwa [hval] at h

lemma summable_inv_sq_shift : Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => 1 / (n:ℝ)^2) := (Real.summable_one_div_nat_pow).2 one_lt_two
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n:ℝ))^2) 1).2 h
  simpa using h2

lemma summable_majorant (s : ℝ) :
    Summable (fun k : ℕ => (Cdec / s ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)) :=
  summable_inv_sq_shift.mul_left _

lemma summable_T {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    Summable (fun k : ℕ => T (((k : ℝ) + 1) * s) y) :=
  Summable.of_norm_bounded (summable_majorant s)
    (fun k => by simpa [Real.norm_eq_abs] using abs_T_shift_le hs hy0 hy1 k)

lemma summable_abs_T {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    Summable (fun k : ℕ => |T (((k : ℝ) + 1) * s) y|) :=
  (summable_T hs hy0 hy1).abs

lemma summable_abs_T_tail {m : ℕ} (hm : 1 ≤ m) {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1/2) : Summable (fun k : ℕ => |T (((k : ℝ) + m) * s) y|) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => |T (((n : ℝ) + 1) * s) y|)
    (m - 1)).2 (summable_abs_T hs hy0 hy1)
  exact h.congr (fun k => by rw [cast_shift hm k])

lemma summable_inv_sq_tail {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k : ℕ => 1 / ((k:ℝ) + m) ^ 2) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2)
    (m - 1)).2 summable_inv_sq_shift
  exact h.congr (fun k => by rw [cast_shift hm k])

/-! ### The tail of `∑ 1/d²` -/

lemma tsum_inv_sq_tail_le {m : ℕ} (hm : 1 ≤ m) :
    ∑' k : ℕ, (1 / ((k:ℝ) + m)^2) ≤ 1 / ((m:ℝ) - 1/2) := by
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro n
  have hstep : ∀ k : ℕ, (1 / ((k:ℝ) + m)^2) ≤ 1/((k:ℝ) + m - 1/2) - 1/(((k:ℝ)+1)+m-1/2) := by
    intro k
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have h1 : (0:ℝ) < (k:ℝ) + m - 1/2 := by linarith
    have h2 : (0:ℝ) < ((k:ℝ)+1) + m - 1/2 := by linarith
    rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2),
      div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg ((k:ℝ) + m)]
  calc ∑ k ∈ range n, (1 / ((k:ℝ) + m)^2)
      ≤ ∑ k ∈ range n, (1/((k:ℝ) + m - 1/2) - 1/(((k:ℝ)+1)+m-1/2)) :=
        Finset.sum_le_sum (fun k _ => hstep k)
    _ = 1/((0:ℝ) + m - 1/2) - 1/((n:ℝ)+m-1/2) := by
        have h := Finset.sum_range_sub' (fun k : ℕ => 1/((k:ℝ) + m - 1/2)) n
        simpa using h
    _ ≤ 1 / ((m:ℝ) - 1/2) := by
        have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        have hd : (0:ℝ) < (n:ℝ)+m-1/2 := by linarith
        have h3 : 0 < 1/((n:ℝ)+m-1/2) := one_div_pos.2 hd
        simp only [zero_add]
        linarith

/-! ### Step 1: the difference identity -/

lemma bM_eq_range {m : ℕ} (s y : ℝ) :
    bM m s y = (2 / m) * ∑ k ∈ Finset.range (m - 1), ((m : ℝ) - ((k : ℝ) + 1))
      * T (((k : ℝ) + 1) * s) y := by
  unfold bM
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring_nf

lemma difference_identity {m : ℕ} (hm : 1 ≤ m) {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1/2) :
    bM m s y - bInf s y
      = -((2 / m) * ∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y)
        - 2 * ∑' k : ℕ, T (((k : ℝ) + m) * s) y := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsum := (summable_T hs hy0 hy1).sum_add_tsum_nat_add (m - 1)
  have htsum : (∑' k : ℕ, T ((((k + (m - 1) : ℕ) : ℝ) + 1) * s) y)
      = ∑' k : ℕ, T (((k : ℝ) + m) * s) y :=
    tsum_congr (fun k => by rw [cast_shift hm k])
  have hhead : (2 / m) * ∑ k ∈ Finset.range (m - 1), ((m : ℝ) - ((k : ℝ) + 1))
        * T (((k : ℝ) + 1) * s) y
      = 2 * (∑ k ∈ Finset.range (m - 1), T (((k : ℝ) + 1) * s) y)
        - (2 / m) * ∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp
  rw [bM_eq_range, hhead, bInf, ← hsum, htsum]
  ring

/-! ### Steps 2 and 3: head and tail estimates -/

lemma head_bound {m : ℕ} (hm : 1 ≤ m) {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    |(2 / m) * ∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y|
      ≤ (2 * Cdec / s ^ 2) * (Hnum (m - 1) / m) := by
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hterm : ∀ k ∈ Finset.range (m - 1),
      |((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y| ≤ (Cdec / s ^ 2) * (1 / ((k : ℝ) + 1)) := by
    intro k _
    have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
    rw [abs_mul, abs_of_pos hk]
    have h := abs_T_shift_le hs hy0 hy1 k
    calc ((k : ℝ) + 1) * |T (((k : ℝ) + 1) * s) y|
        ≤ ((k : ℝ) + 1) * ((Cdec / s ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left h hk.le
      _ = (Cdec / s ^ 2) * (1 / ((k : ℝ) + 1)) := by
          field_simp
  have hsum : |∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y|
      ≤ (Cdec / s ^ 2) * Hnum (m - 1) := by
    calc |∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y|
        ≤ ∑ k ∈ Finset.range (m - 1), |((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (m - 1), (Cdec / s ^ 2) * (1 / ((k : ℝ) + 1)) :=
          Finset.sum_le_sum hterm
      _ = (Cdec / s ^ 2) * Hnum (m - 1) := by rw [Hnum, Finset.mul_sum]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / (m:ℝ))]
  calc 2 / (m:ℝ) * |∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y|
      ≤ 2 / (m:ℝ) * ((Cdec / s ^ 2) * Hnum (m - 1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2 * Cdec / s ^ 2) * (Hnum (m - 1) / m) := by field_simp

lemma tail_bound {m : ℕ} (hm : 1 ≤ m) {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    |2 * ∑' k : ℕ, T (((k : ℝ) + m) * s) y| ≤ (2 * Cdec / s ^ 2) * (1 / ((m : ℝ) - 1/2)) := by
  have hsummable := summable_abs_T_tail hm hs hy0 hy1
  have hbound : ∀ k : ℕ, |T (((k : ℝ) + m) * s) y| ≤ (Cdec / s ^ 2) * (1 / ((k : ℝ) + m) ^ 2) := by
    intro k
    have h := abs_T_shift_le hs hy0 hy1 (k + (m - 1))
    rwa [cast_shift hm k] at h
  have hsummable2 : Summable (fun k : ℕ => (Cdec / s ^ 2) * (1 / ((k : ℝ) + m) ^ 2)) :=
    (summable_inv_sq_tail hm).mul_left _
  have hC : (0:ℝ) ≤ Cdec / s ^ 2 := by rw [Cdec]; positivity
  have hkey : ∑' k : ℕ, |T (((k : ℝ) + m) * s) y| ≤ (Cdec / s ^ 2) * (1 / ((m : ℝ) - 1/2)) := by
    calc ∑' k : ℕ, |T (((k : ℝ) + m) * s) y|
        ≤ ∑' k : ℕ, (Cdec / s ^ 2) * (1 / ((k : ℝ) + m) ^ 2) :=
          Summable.tsum_le_tsum hbound hsummable hsummable2
      _ = (Cdec / s ^ 2) * ∑' k : ℕ, (1 / ((k : ℝ) + m) ^ 2) := tsum_mul_left
      _ ≤ (Cdec / s ^ 2) * (1 / ((m : ℝ) - 1/2)) :=
          mul_le_mul_of_nonneg_left (tsum_inv_sq_tail_le hm) hC
  have habs : |∑' k : ℕ, T (((k : ℝ) + m) * s) y| ≤ ∑' k : ℕ, |T (((k : ℝ) + m) * s) y| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k : ℕ => T (((k : ℝ) + m) * s) y)
        (by simpa [Real.norm_eq_abs] using hsummable)
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc 2 * |∑' k : ℕ, T (((k : ℝ) + m) * s) y|
      ≤ 2 * ((Cdec / s ^ 2) * (1 / ((m : ℝ) - 1/2))) :=
        mul_le_mul_of_nonneg_left (habs.trans hkey) (by norm_num)
    _ = (2 * Cdec / s ^ 2) * (1 / ((m : ℝ) - 1/2)) := by ring

/-! ### The main two-sided estimate -/

/-- **Main statement of `PROBLEM.md`**, with the explicit constant `Cdec = 200`. -/
theorem abs_bM_sub_bInf_le {m : ℕ} (hm : 1 ≤ m) {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1/2) :
    |bM m s y - bInf s y|
      ≤ (2 * Cdec / s ^ 2) * (Hnum (m - 1) / m + 1 / ((m : ℝ) - 1/2)) := by
  rw [difference_identity hm hs hy0 hy1]
  have h1 := head_bound hm hs hy0 hy1
  have h2 := tail_bound hm hs hy0 hy1
  have habs := abs_sub_le'
    (-((2 / (m:ℝ)) * ∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y))
    (2 * ∑' k : ℕ, T (((k : ℝ) + m) * s) y)
  rw [abs_neg] at habs
  calc |-((2 / (m:ℝ)) * ∑ k ∈ Finset.range (m - 1), ((k : ℝ) + 1) * T (((k : ℝ) + 1) * s) y)
      - 2 * ∑' k : ℕ, T (((k : ℝ) + m) * s) y|
      ≤ (2 * Cdec / s ^ 2) * (Hnum (m - 1) / m)
        + (2 * Cdec / s ^ 2) * (1 / ((m : ℝ) - 1/2)) := by linarith
    _ = (2 * Cdec / s ^ 2) * (Hnum (m - 1) / m + 1 / ((m : ℝ) - 1/2)) := by ring

end TruncEst
