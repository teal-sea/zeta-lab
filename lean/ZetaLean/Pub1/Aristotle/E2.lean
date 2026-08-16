import Mathlib

namespace AristotleE2

/-!
# The row bound for the `F1` kernel on `I = [-1/2, 1/2]`

`F1 x = |x| - 4 x ^ 2 + ∑' k, aCoef k * |x| ^ (2 * k + 3)` with
`aCoef k = 2 ^ (2 * k + 3) * k ! / (2 * k + 2)!`.

The two results are:

* `F1_continuous` : `F1` is continuous (the series is entire, being dominated on
  every ball by a multiple of `∑ (4 r ^ 2) ^ k / k !`);
* `F1_row_bound` : for `|s| ≤ 1/2`, `∫ t in -1/2..1/2, F1 (s - t) ≤ 4/9`.

For the row bound, writing `a = s + 1/2 ∈ [0, 1]` and using that `F1` is even,
`∫ t in -1/2..1/2, F1 (s - t) = ∫ x in 0..a, F1 + ∫ x in 0..(1 - a), F1`.
On `[0, 1]` the kernel is bounded above by the polynomial
`x - 4 x ^ 2 + 4 x ^ 3 + (4/3) x ^ 5 + (16/45) x ^ 7 + (12/125) x ^ 9`
(the first three coefficients of the series are exact, the remaining ones are
summed by a geometric tail bound), and the resulting polynomial inequality is
closed using `a ^ n + (1 - a) ^ n ≤ 1` together with the identity
`1/6 - J a - J (1 - a) = a (1 - a) (a ^ 2 + (1 - a) ^ 2)` for
`J x = x ^ 2 / 2 - 4 x ^ 3 / 3 + x ^ 4`.
-/

open MeasureTheory

noncomputable def aCoef (k : ℕ) : ℝ :=
  2 ^ (2 * k + 3) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

noncomputable def F1 (x : ℝ) : ℝ :=
  |x| - 4 * x ^ 2 + ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3)

private lemma aCoef_pos (k : ℕ) : 0 < aCoef k := by
  unfold aCoef
  positivity

private lemma aCoef_nonneg (k : ℕ) : 0 ≤ aCoef k := (aCoef_pos k).le

private lemma pow_le_one_of_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      nlinarith [pow_nonneg ha0 m]

private lemma pow_le_self_of_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    a ^ n ≤ a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ]
  nlinarith [pow_le_one_of_le_one ha0 ha1 m, pow_nonneg ha0 m]

private lemma aCoef_le_exp (k : ℕ) : aCoef k ≤ 8 * 4 ^ k / (Nat.factorial k : ℝ) := by
  have hfk : (0:ℝ) < (Nat.factorial k : ℝ) := by positivity
  have hdvd : (Nat.factorial k * Nat.factorial k) ∣ Nat.factorial (2 * k + 2) := by
    have h1 : (Nat.factorial k * Nat.factorial k) ∣ Nat.factorial (k + k) :=
      Nat.factorial_mul_factorial_dvd_factorial_add k k
    exact h1.trans (Nat.factorial_dvd_factorial (by omega))
  have hle : (Nat.factorial k * Nat.factorial k : ℝ) ≤ (Nat.factorial (2 * k + 2) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  have hf2 : (0:ℝ) < (Nat.factorial (2 * k + 2) : ℝ) := by positivity
  unfold aCoef
  rw [div_le_div_iff₀ hf2 hfk]
  have h2 : (2:ℝ) ^ (2 * k + 3) = 8 * 4 ^ k := by
    have h4 : (4:ℝ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    rw [h4, pow_add]
    ring
  rw [h2]
  nlinarith [hle, hfk, pow_pos (show (0:ℝ) < 4 by norm_num) k]

private lemma summable_aCoef_pow (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun k : ℕ => aCoef k * r ^ (2 * k + 3)) := by
  have hu : Summable (fun k : ℕ => 8 * r ^ 3 * ((4 * r ^ 2) ^ k / (Nat.factorial k : ℝ))) :=
    (Real.summable_pow_div_factorial (4 * r ^ 2)).mul_left _
  refine hu.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (aCoef_nonneg k) (pow_nonneg hr _)
  · have h1 : aCoef k ≤ 8 * 4 ^ k / (Nat.factorial k : ℝ) := aCoef_le_exp k
    have h2 : r ^ (2 * k + 3) = r ^ 3 * (r ^ 2) ^ k := by
      rw [← pow_mul]
      ring
    have h4 : (0:ℝ) ≤ r ^ 3 * (r ^ 2) ^ k := by positivity
    calc aCoef k * r ^ (2 * k + 3) ≤ (8 * 4 ^ k / (Nat.factorial k : ℝ)) * (r ^ 3 * (r ^ 2) ^ k) := by
          rw [h2]; exact mul_le_mul_of_nonneg_right h1 h4
      _ = 8 * r ^ 3 * ((4 * r ^ 2) ^ k / (Nat.factorial k : ℝ)) := by
          rw [mul_pow]; ring

private lemma continuous_tail : Continuous (fun x : ℝ => ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3)) := by
  rw [continuous_iff_continuousAt]
  intro x
  set R : ℝ := |x| + 1 with hR
  have hR0 : (0:ℝ) ≤ R := by positivity
  have hcont : ContinuousOn (fun x : ℝ => ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3))
      (Metric.ball (0:ℝ) R) := by
    refine continuousOn_tsum (fun k => ?_) (summable_aCoef_pow R hR0) (fun k y hy => ?_)
    · exact (continuous_const.mul ((continuous_abs.pow _))).continuousOn
    · have hy' : |y| ≤ R := by
        have : |y| < R := by simpa [Real.dist_eq] using hy
        exact this.le
      have habs : |aCoef k * |y| ^ (2 * k + 3)| = aCoef k * |y| ^ (2 * k + 3) :=
        abs_of_nonneg (mul_nonneg (aCoef_nonneg k) (pow_nonneg (abs_nonneg y) _))
      rw [Real.norm_eq_abs, habs]
      have hpow : |y| ^ (2 * k + 3) ≤ R ^ (2 * k + 3) := by gcongr
      exact mul_le_mul_of_nonneg_left hpow (aCoef_nonneg k)
  have hxball : x ∈ Metric.ball (0:ℝ) R := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, hR]
    linarith
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds hxball)

theorem F1_continuous : Continuous F1 := by
  unfold F1
  exact ((continuous_abs.sub (continuous_const.mul (continuous_pow 2))).add continuous_tail)

private lemma aCoef_succ_mul (k : ℕ) :
    aCoef (k + 1) * ((2 * (k:ℝ) + 3) * (2 * (k:ℝ) + 4)) = aCoef k * (4 * ((k:ℝ) + 1)) := by
  unfold aCoef
  have e : 2 * (k + 1) + 2 = ((2 * k + 2) + 1) + 1 := by ring
  rw [e, Nat.factorial_succ ((2 * k + 2) + 1), Nat.factorial_succ (2 * k + 2),
    Nat.factorial_succ k]
  have e2 : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by ring
  rw [e2, pow_add]
  push_cast
  field_simp
  ring

private lemma aCoef_step (k : ℕ) (hk : 3 ≤ k) : aCoef (k + 1) ≤ aCoef k / 5 := by
  have hk' : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hid := aCoef_succ_mul k
  have hpos := aCoef_pos (k + 1)
  have hkk : (0:ℝ) ≤ 4 * (k:ℝ) ^ 2 - 6 * (k:ℝ) - 8 := by nlinarith
  have h2 : (4 * (k:ℝ) + 4) * (5 * aCoef (k + 1)) ≤ (4 * (k:ℝ) + 4) * aCoef k := by nlinarith
  have h3 : 5 * aCoef (k + 1) ≤ aCoef k :=
    le_of_mul_le_mul_left h2 (by positivity)
  linarith

private lemma aCoef_geom (j : ℕ) : aCoef (j + 3) ≤ aCoef 3 * (1 / 5) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
      have h1 : aCoef (n + 3 + 1) ≤ aCoef (n + 3) / 5 := aCoef_step (n + 3) (by omega)
      have h2 : aCoef (n + 3) / 5 ≤ (aCoef 3 * (1 / 5) ^ n) / 5 := by linarith
      have : aCoef (n + 1 + 3) ≤ (aCoef 3 * (1 / 5) ^ n) / 5 := by
        have e : n + 1 + 3 = n + 3 + 1 := by ring
        rw [e]; linarith
      calc aCoef (n + 1 + 3) ≤ (aCoef 3 * (1 / 5) ^ n) / 5 := this
        _ = aCoef 3 * (1 / 5) ^ (n + 1) := by rw [pow_succ]; ring

private lemma aCoef_three : aCoef 3 = 8 / 105 := by
  unfold aCoef
  norm_num [Nat.factorial]

private lemma summable_aCoef : Summable aCoef := by
  simpa using summable_aCoef_pow 1 zero_le_one

private lemma summable_aCoef_shift : Summable (fun j : ℕ => aCoef (j + 3)) :=
  (summable_nat_add_iff 3).mpr summable_aCoef

private lemma tail_bound : ∑' j : ℕ, aCoef (j + 3) ≤ 12 / 125 := by
  have hgeom : Summable (fun j : ℕ => aCoef 3 * (1 / 5 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : ∑' j : ℕ, aCoef (j + 3) ≤ ∑' j : ℕ, aCoef 3 * (1 / 5 : ℝ) ^ j :=
    Summable.tsum_le_tsum aCoef_geom summable_aCoef_shift hgeom
  have h2 : ∑' j : ℕ, aCoef 3 * (1 / 5 : ℝ) ^ j = aCoef 3 * (5 / 4) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [h2, aCoef_three] at h1
  linarith

private lemma tsum_le_poly (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑' k : ℕ, aCoef k * x ^ (2 * k + 3)
      ≤ 4 * x ^ 3 + (4 / 3) * x ^ 5 + (16 / 45) * x ^ 7 + (12 / 125) * x ^ 9 := by
  have hsum : Summable (fun k : ℕ => aCoef k * x ^ (2 * k + 3)) := summable_aCoef_pow x hx0
  have hsplit := hsum.sum_add_tsum_nat_add 3
  have hhead : ∑ i ∈ Finset.range 3, aCoef i * x ^ (2 * i + 3)
      = 4 * x ^ 3 + (4 / 3) * x ^ 5 + (16 / 45) * x ^ 7 := by
    have h0 : aCoef 0 = 4 := by norm_num [aCoef, Nat.factorial]
    have h1 : aCoef 1 = 4 / 3 := by norm_num [aCoef, Nat.factorial]
    have h2 : aCoef 2 = 16 / 45 := by norm_num [aCoef, Nat.factorial]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, h0, h1, h2]
    norm_num
  have hshift : Summable (fun j : ℕ => aCoef (j + 3) * x ^ 9) :=
    summable_aCoef_shift.mul_right _
  have hterm : ∀ j : ℕ, aCoef (j + 3) * x ^ (2 * (j + 3) + 3) ≤ aCoef (j + 3) * x ^ 9 := by
    intro j
    have hx : x ^ (2 * (j + 3) + 3) ≤ x ^ 9 := by
      have e : 2 * (j + 3) + 3 = 9 + 2 * j := by ring
      rw [e, pow_add]
      nlinarith [pow_le_one_of_le_one hx0 hx1 (2 * j), pow_nonneg hx0 9,
        pow_nonneg hx0 (2 * j)]
    exact mul_le_mul_of_nonneg_left hx (aCoef_nonneg _)
  have htail : ∑' j : ℕ, aCoef (j + 3) * x ^ (2 * (j + 3) + 3) ≤ (12 / 125) * x ^ 9 := by
    have h1 : ∑' j : ℕ, aCoef (j + 3) * x ^ (2 * (j + 3) + 3) ≤ ∑' j : ℕ, aCoef (j + 3) * x ^ 9 :=
      Summable.tsum_le_tsum hterm
        ((summable_nat_add_iff 3).mpr hsum) hshift
    have h2 : ∑' j : ℕ, aCoef (j + 3) * x ^ 9 = (∑' j : ℕ, aCoef (j + 3)) * x ^ 9 :=
      tsum_mul_right
    rw [h2] at h1
    have h3 : (∑' j : ℕ, aCoef (j + 3)) * x ^ 9 ≤ (12 / 125) * x ^ 9 :=
      mul_le_mul_of_nonneg_right tail_bound (by positivity)
    linarith
  rw [← hsplit, hhead]
  linarith

private lemma F1_le_U (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    F1 x ≤ x - 4 * x ^ 2 + 4 * x ^ 3 + (4 / 3) * x ^ 5 + (16 / 45) * x ^ 7 + (12 / 125) * x ^ 9 := by
  have habs : |x| = x := abs_of_nonneg hx0
  have h := tsum_le_poly x hx0 hx1
  unfold F1
  rw [habs]
  linarith

private lemma integral_U (c : ℝ) :
    (∫ x in (0:ℝ)..c,
        (x - 4 * x ^ 2 + 4 * x ^ 3 + (4 / 3) * x ^ 5 + (16 / 45) * x ^ 7 + (12 / 125) * x ^ 9))
      = c ^ 2 / 2 - 4 * c ^ 3 / 3 + c ^ 4 + (2 / 9) * c ^ 6 + (2 / 45) * c ^ 8
        + (6 / 625) * c ^ 10 := by
  have hd : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => t ^ 2 / 2 - 4 * t ^ 3 / 3 + t ^ 4 + (2 / 9) * t ^ 6 + (2 / 45) * t ^ 8
        + (6 / 625) * t ^ 10)
      (y - 4 * y ^ 2 + 4 * y ^ 3 + (4 / 3) * y ^ 5 + (16 / 45) * y ^ 7 + (12 / 125) * y ^ 9) y := by
    intro y
    have h := ((((((hasDerivAt_pow 2 y).div_const 2).sub
      (((hasDerivAt_pow 3 y).const_mul (4:ℝ)).div_const 3)).add
      (hasDerivAt_pow 4 y)).add ((hasDerivAt_pow 6 y).const_mul (2/9:ℝ))).add
      ((hasDerivAt_pow 8 y).const_mul (2/45:ℝ))).add ((hasDerivAt_pow 10 y).const_mul (6/625:ℝ))
    exact h.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  · norm_num
  · apply Continuous.intervalIntegrable
    fun_prop

private lemma integral_F1_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ x in (0:ℝ)..c, F1 x)
      ≤ c ^ 2 / 2 - 4 * c ^ 3 / 3 + c ^ 4 + (2 / 9) * c ^ 6 + (2 / 45) * c ^ 8
        + (6 / 625) * c ^ 10 := by
  have hcont : Continuous (fun x : ℝ =>
      x - 4 * x ^ 2 + 4 * x ^ 3 + (4 / 3) * x ^ 5 + (16 / 45) * x ^ 7 + (12 / 125) * x ^ 9) := by
    fun_prop
  have h1 : (∫ x in (0:ℝ)..c, F1 x)
      ≤ ∫ x in (0:ℝ)..c,
          (x - 4 * x ^ 2 + 4 * x ^ 3 + (4 / 3) * x ^ 5 + (16 / 45) * x ^ 7 + (12 / 125) * x ^ 9) :=
    intervalIntegral.integral_mono_on hc0 (F1_continuous.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) (fun x hx => F1_le_U x hx.1 (hx.2.trans hc1))
  rwa [integral_U c] at h1

private lemma V_add_le (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a + b = 1) :
    (a ^ 2 / 2 - 4 * a ^ 3 / 3 + a ^ 4 + (2 / 9) * a ^ 6 + (2 / 45) * a ^ 8 + (6 / 625) * a ^ 10)
      + (b ^ 2 / 2 - 4 * b ^ 3 / 3 + b ^ 4 + (2 / 9) * b ^ 6 + (2 / 45) * b ^ 8
        + (6 / 625) * b ^ 10) ≤ 4 / 9 := by
  have ha1 : a ≤ 1 := by linarith
  have hb1 : b ≤ 1 := by linarith
  have key : ∀ n : ℕ, n ≠ 0 → a ^ n + b ^ n ≤ 1 := by
    intro n hn
    have h1 : a ^ n ≤ a := pow_le_self_of_le_one ha0 ha1 hn
    have h2 : b ^ n ≤ b := pow_le_self_of_le_one hb0 hb1 hn
    linarith
  have h6 := key 6 (by norm_num)
  have h8 := key 8 (by norm_num)
  have h10 := key 10 (by norm_num)
  have hpoly : (a ^ 2 / 2 - 4 * a ^ 3 / 3 + a ^ 4) + (b ^ 2 / 2 - 4 * b ^ 3 / 3 + b ^ 4) ≤ 1 / 6 := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_nonneg (mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - a))
      (add_nonneg (sq_nonneg a) (sq_nonneg (1 - a)))]
  linarith

theorem F1_row_bound (s : ℝ) (hs : |s| ≤ 1 / 2) :
    (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t)) ≤ 4 / 9 := by
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have heven : ∀ x : ℝ, F1 (-x) = F1 x := by
    intro x
    unfold F1
    simp [abs_neg]
  have e1 : (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t)) = ∫ x in (s - 1/2)..(s + 1/2), F1 x := by
    rw [intervalIntegral.integral_comp_sub_left F1 s]
    rw [show s - -(1:ℝ)/2 = s + 1/2 from by ring]
  have e2 : (∫ x in (s - 1/2)..(0:ℝ), F1 x) + (∫ x in (0:ℝ)..(s + 1/2), F1 x)
      = ∫ x in (s - 1/2)..(s + 1/2), F1 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (F1_continuous.intervalIntegrable _ _) (F1_continuous.intervalIntegrable _ _)
  have e3 : (∫ x in (0:ℝ)..(1/2 - s), F1 x) = ∫ x in (s - 1/2)..(0:ℝ), F1 x := by
    have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := 1/2 - s) F1
    simp only [heven] at h
    rw [h, show -(1/2 - s) = s - 1/2 from by ring, neg_zero]
  have hb1 := integral_F1_le (1/2 - s) (by linarith) (by linarith)
  have hb2 := integral_F1_le (s + 1/2) (by linarith) (by linarith)
  have hsum := V_add_le (1/2 - s) (s + 1/2) (by linarith) (by linarith) (by ring)
  rw [e1, ← e2, ← e3]
  linarith


end AristotleE2