import Mathlib

namespace AristotleV

noncomputable def aCoef (k : ℕ) : ℝ :=
  2 ^ (2 * k + 3) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

noncomputable def dCoef (k : ℕ) : ℝ := aCoef k * ((2 * k + 3) * (2 * k + 2) : ℝ)

private lemma factorial_cast_pos (n : ℕ) : (0 : ℝ) < (Nat.factorial n : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

private lemma aCoef_pos (k : ℕ) : 0 < aCoef k := by
  unfold aCoef
  apply div_pos
  · exact mul_pos (by positivity) (factorial_cast_pos k)
  · exact factorial_cast_pos _

private lemma dCoef_pos (k : ℕ) : 0 < dCoef k := by
  unfold dCoef
  have h := aCoef_pos k
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 : (0 : ℝ) < (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2) := by nlinarith
  exact mul_pos h h2

private lemma aCoef_rec (k : ℕ) :
    aCoef (k + 1) * ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 4)) = aCoef k * (4 * ((k : ℝ) + 1)) := by
  have hf : Nat.factorial (2 * (k + 1) + 2)
      = (2 * k + 4) * ((2 * k + 3) * Nat.factorial (2 * k + 2)) := by
    have h1 : 2 * (k + 1) + 2 = (2 * k + 3) + 1 := by ring
    rw [h1, Nat.factorial_succ]
    have h2 : 2 * k + 3 = (2 * k + 2) + 1 := by ring
    rw [h2, Nat.factorial_succ]
    try ring
  have hpow : (2 : ℝ) ^ (2 * (k + 1) + 3) = 4 * 2 ^ (2 * k + 3) := by
    rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by ring, pow_add]
    ring
  have hp : (0 : ℝ) < (Nat.factorial (2 * k + 2) : ℝ) := factorial_cast_pos _
  unfold aCoef
  rw [hf, Nat.factorial_succ, hpow]
  push_cast
  field_simp
  try ring

private lemma dCoef_rec (k : ℕ) :
    dCoef (k + 1) * ((2 * (k : ℝ) + 3) ^ 2) = dCoef k * (2 * (2 * (k : ℝ) + 5)) := by
  have h := aCoef_rec k
  unfold dCoef
  push_cast
  nlinarith [h, aCoef_pos k, aCoef_pos (k + 1)]

private lemma aCoef_step {k : ℕ} (hk : 20 ≤ k) :
    aCoef (k + 1) ≤ (42 / 946 : ℝ) * aCoef k := by
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h := aCoef_rec k
  have hpos : (0 : ℝ) < (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 4) := by nlinarith
  have ha := aCoef_pos k
  refine le_of_mul_le_mul_right ?_ hpos
  rw [h]
  have key : 4 * ((k : ℝ) + 1) ≤ 42 / 946 * ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 4)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (by linarith : (0:ℝ) ≤ 84 * (k : ℝ) + 82)]
  nlinarith [mul_le_mul_of_nonneg_left key ha.le]

private lemma dCoef_step {k : ℕ} (hk : 20 ≤ k) :
    dCoef (k + 1) ≤ (90 / 1849 : ℝ) * dCoef k := by
  have hkR : (20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h := dCoef_rec k
  have hpos : (0 : ℝ) < (2 * (k : ℝ) + 3) ^ 2 := by nlinarith
  have hd := dCoef_pos k
  refine le_of_mul_le_mul_right ?_ hpos
  rw [h]
  have key : 2 * (2 * (k : ℝ) + 5) ≤ 90 / 1849 * ((2 * (k : ℝ) + 3) ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (by linarith : (0:ℝ) ≤ 360 * (k : ℝ) + 884)]
  nlinarith [mul_le_mul_of_nonneg_left key hd.le]

private lemma aCoef_geom (m : ℕ) : aCoef (m + 20) ≤ aCoef 20 * (42 / 946 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
      have hstep : aCoef (n + 20 + 1) ≤ (42 / 946 : ℝ) * aCoef (n + 20) :=
        aCoef_step (by omega)
      have h2 : (42 / 946 : ℝ) * aCoef (n + 20)
          ≤ (42 / 946 : ℝ) * (aCoef 20 * (42 / 946 : ℝ) ^ n) := by
        apply mul_le_mul_of_nonneg_left ih (by norm_num)
      have : aCoef (n + 1 + 20) ≤ (42 / 946 : ℝ) * (aCoef 20 * (42 / 946 : ℝ) ^ n) := by
        have e : n + 1 + 20 = n + 20 + 1 := by omega
        rw [e]; linarith
      calc aCoef (n + 1 + 20) ≤ (42 / 946 : ℝ) * (aCoef 20 * (42 / 946 : ℝ) ^ n) := this
        _ = aCoef 20 * (42 / 946 : ℝ) ^ (n + 1) := by ring

private lemma dCoef_geom (m : ℕ) : dCoef (m + 20) ≤ dCoef 20 * (90 / 1849 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
      have hstep : dCoef (n + 20 + 1) ≤ (90 / 1849 : ℝ) * dCoef (n + 20) :=
        dCoef_step (by omega)
      have h2 : (90 / 1849 : ℝ) * dCoef (n + 20)
          ≤ (90 / 1849 : ℝ) * (dCoef 20 * (90 / 1849 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      have : dCoef (n + 1 + 20) ≤ (90 / 1849 : ℝ) * (dCoef 20 * (90 / 1849 : ℝ) ^ n) := by
        have e : n + 1 + 20 = n + 20 + 1 := by omega
        rw [e]; linarith
      calc dCoef (n + 1 + 20) ≤ (90 / 1849 : ℝ) * (dCoef 20 * (90 / 1849 : ℝ) ^ n) := this
        _ = dCoef 20 * (90 / 1849 : ℝ) ^ (n + 1) := by ring

private lemma aCoef_tail_summable : Summable (fun j : ℕ => aCoef (j + 20)) := by
  have hg : Summable (fun m : ℕ => aCoef 20 * (42 / 946 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le (fun m => (aCoef_pos _).le) aCoef_geom hg

private lemma dCoef_tail_summable : Summable (fun j : ℕ => dCoef (j + 20)) := by
  have hg : Summable (fun m : ℕ => dCoef 20 * (90 / 1849 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le (fun m => (dCoef_pos _).le) dCoef_geom hg

theorem aCoef_tail_le :
    ∑' j : ℕ, aCoef (j + 20) ≤ 45088768 / 2828846926917599723269509375 := by
  have hg : Summable (fun m : ℕ => aCoef 20 * (42 / 946 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : ∑' j : ℕ, aCoef (j + 20) ≤ ∑' m : ℕ, aCoef 20 * (42 / 946 : ℝ) ^ m :=
    Summable.tsum_le_tsum aCoef_geom aCoef_tail_summable hg
  have h2 : ∑' m : ℕ, aCoef 20 * (42 / 946 : ℝ) ^ m = aCoef 20 * (1 - 42 / 946 : ℝ)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have h3 : aCoef 20 * (1 - 42 / 946 : ℝ)⁻¹
      = 45088768 / 2828846926917599723269509375 := by
    norm_num [aCoef, Nat.factorial]
  calc ∑' j : ℕ, aCoef (j + 20) ≤ ∑' m : ℕ, aCoef 20 * (42 / 946 : ℝ) ^ m := h1
    _ = aCoef 20 * (1 - 42 / 946 : ℝ)⁻¹ := h2
    _ = 45088768 / 2828846926917599723269509375 := h3

theorem dCoef_tail_le :
    ∑' j : ℕ, dCoef (j + 20) ≤ 666953056256 / 23065890935073171953452059375 := by
  have hg : Summable (fun m : ℕ => dCoef 20 * (90 / 1849 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : ∑' j : ℕ, dCoef (j + 20) ≤ ∑' m : ℕ, dCoef 20 * (90 / 1849 : ℝ) ^ m :=
    Summable.tsum_le_tsum dCoef_geom dCoef_tail_summable hg
  have h2 : ∑' m : ℕ, dCoef 20 * (90 / 1849 : ℝ) ^ m = dCoef 20 * (1 - 90 / 1849 : ℝ)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have h3 : dCoef 20 * (1 - 90 / 1849 : ℝ)⁻¹
      = 666953056256 / 23065890935073171953452059375 := by
    norm_num [dCoef, aCoef, Nat.factorial]
  calc ∑' j : ℕ, dCoef (j + 20) ≤ ∑' m : ℕ, dCoef 20 * (90 / 1849 : ℝ) ^ m := h1
    _ = dCoef 20 * (1 - 90 / 1849 : ℝ)⁻¹ := h2
    _ = 666953056256 / 23065890935073171953452059375 := h3

theorem dCoef_summable : Summable dCoef :=
  (summable_nat_add_iff 20).mp dCoef_tail_summable


end AristotleV