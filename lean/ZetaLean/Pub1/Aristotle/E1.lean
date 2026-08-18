import Mathlib

namespace AristotleE1

open MeasureTheory

noncomputable def aCoef (k : ℕ) : ℝ :=
  2 ^ (2 * k + 3) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

noncomputable def F1 (x : ℝ) : ℝ :=
  |x| - 4 * x ^ 2 + ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3)

private lemma aCoef_pos (k : ℕ) : 0 < aCoef k := by
  have h1 : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (0:ℝ) < (Nat.factorial (2 * k + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * k + 2)
  unfold aCoef
  positivity

private lemma aCoef_succ (k : ℕ) :
    aCoef (k + 1) = aCoef k * (4 * ((k : ℝ) + 1)) / ((2 * (k:ℝ) + 4) * (2 * (k:ℝ) + 3)) := by
  have e : Nat.factorial (2 * (k + 1) + 2)
      = (2 * k + 4) * ((2 * k + 3) * Nat.factorial (2 * k + 2)) := by
    have h : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
    rw [h, Nat.factorial_succ, Nat.factorial_succ]
  have h2 : (0:ℝ) < (Nat.factorial (2 * k + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * k + 2)
  unfold aCoef
  rw [e, Nat.factorial_succ]
  have hp : (2:ℝ) ^ (2 * (k+1) + 3) = 4 * 2 ^ (2 * k + 3) := by
    rw [show 2 * (k+1) + 3 = (2 * k + 3) + 2 by ring, pow_add]; ring
  rw [hp]
  push_cast
  field_simp

private lemma aCoef_le_half (k : ℕ) : aCoef k ≤ 4 * (1/2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num [aCoef, Nat.factorial]
  | succ n ih =>
      have hpos := aCoef_pos n
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hd : (0:ℝ) < (2 * (n:ℝ) + 4) * (2 * (n:ℝ) + 3) := by nlinarith
      have hstep : aCoef (n + 1) ≤ aCoef n * (1/2 : ℝ) := by
        rw [aCoef_succ n, div_le_iff₀ hd]
        nlinarith [mul_nonneg hpos.le (show (0:ℝ) ≤ 2 * (n:ℝ) ^ 2 + 3 * n + 2 by nlinarith)]
      have : aCoef n * (1/2:ℝ) ≤ (4 * (1/2:ℝ) ^ n) * (1/2) := by nlinarith
      calc aCoef (n+1) ≤ aCoef n * (1/2:ℝ) := hstep
        _ ≤ (4 * (1/2:ℝ) ^ n) * (1/2) := this
        _ = 4 * (1/2:ℝ) ^ (n+1) := by ring

private lemma aCoef_zero : aCoef 0 = 4 := by norm_num [aCoef, Nat.factorial]

private lemma aCoef_one : aCoef 1 = 4 / 3 := by norm_num [aCoef, Nat.factorial]

private lemma aCoef_two : aCoef 2 = 16 / 45 := by norm_num [aCoef, Nat.factorial]

private lemma aCoef_three : aCoef 3 = 8 / 105 := by norm_num [aCoef, Nat.factorial]

private lemma aCoef_tail_bound (j : ℕ) : aCoef (j + 3) ≤ (8/105) * (8/45 : ℝ) ^ j := by
  induction j with
  | zero => norm_num [aCoef_three]
  | succ n ih =>
      have hpos := aCoef_pos (n + 3)
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hd : (0:ℝ) < (2 * ((n + 3 : ℕ) : ℝ) + 4) * (2 * ((n + 3 : ℕ) : ℝ) + 3) := by
        push_cast; nlinarith
      have hstep : aCoef (n + 3 + 1) ≤ aCoef (n + 3) * (8/45 : ℝ) := by
        rw [aCoef_succ (n + 3), div_le_iff₀ hd]
        push_cast
        nlinarith [mul_nonneg hpos.le
          (show (0:ℝ) ≤ 16 * (n:ℝ) ^ 2 + 62 * (n:ℝ) + 60 by positivity)]
      have hgeom : (0:ℝ) < (8/45 : ℝ) ^ n := by positivity
      calc aCoef (n + 1 + 3) = aCoef (n + 3 + 1) := by ring_nf
        _ ≤ aCoef (n + 3) * (8/45 : ℝ) := hstep
        _ ≤ ((8/105) * (8/45 : ℝ) ^ n) * (8/45) := by nlinarith
        _ = (8/105) * (8/45 : ℝ) ^ (n+1) := by ring

theorem F1_summable (x : ℝ) (hx : |x| ≤ 1) :
    Summable fun k : ℕ => aCoef k * |x| ^ (2 * k + 3) := by
  have hgeom : Summable fun k : ℕ => 4 * (1/2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
  apply Summable.of_nonneg_of_le _ _ hgeom
  · intro k
    have := (aCoef_pos k).le
    positivity
  · intro k
    have h1 : |x| ^ (2 * k + 3) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    have h2 : aCoef k ≤ 4 * (1/2:ℝ) ^ k := aCoef_le_half k
    have h3 : (0:ℝ) ≤ |x| ^ (2 * k + 3) := by positivity
    nlinarith [(aCoef_pos k).le]

theorem F1_nonneg (x : ℝ) (hx : |x| ≤ 1) : 0 ≤ F1 x := by
  have hs := F1_summable x hx
  have hterm : ∀ k : ℕ, 0 ≤ aCoef k * |x| ^ (2 * k + 3) := by
    intro k
    have := (aCoef_pos k).le
    positivity
  have hle : aCoef 0 * |x| ^ (2 * 0 + 3) ≤ ∑' k : ℕ, aCoef k * |x| ^ (2 * k + 3) :=
    hs.le_tsum 0 (fun i _ => hterm i)
  have h0 : aCoef 0 * |x| ^ (2 * 0 + 3) = 4 * |x| ^ 3 := by
    rw [aCoef_zero]
  rw [h0] at hle
  have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have habs : 0 ≤ |x| := abs_nonneg x
  have key : 0 ≤ |x| - 4 * x ^ 2 + 4 * |x| ^ 3 := by
    rw [hsq]
    nlinarith [sq_nonneg (1 - 2 * |x|)]
  unfold F1
  linarith

theorem F1_even (x : ℝ) : F1 (-x) = F1 x := by
  unfold F1
  simp [abs_neg]

private noncomputable def hUp (x : ℝ) : ℝ :=
  x - 4 * x ^ 2 + 4 * x ^ 3 + (4/3) * x ^ 5 + (16/45) * x ^ 7 + (24/259) * x ^ 9

private lemma F1_le_hUp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : F1 x ≤ hUp x := by
  have hax : |x| = x := abs_of_nonneg hx0
  have hs : Summable fun k : ℕ => aCoef k * |x| ^ (2 * k + 3) := by
    apply F1_summable; rw [hax]; exact hx1
  have hsplit := hs.sum_add_tsum_nat_add (k := 3)
  -- bound the tail
  have hgeom : Summable fun j : ℕ => ((8/105) * (8/45 : ℝ) ^ j) * x ^ 9 :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (8/105)).mul_right _
  have htail_sum : Summable fun j : ℕ => aCoef (j + 3) * |x| ^ (2 * (j + 3) + 3) :=
    (summable_nat_add_iff 3).2 hs
  have htail_le : ∀ j : ℕ,
      aCoef (j + 3) * |x| ^ (2 * (j + 3) + 3) ≤ ((8/105) * (8/45 : ℝ) ^ j) * x ^ 9 := by
    intro j
    rw [hax]
    have hxp : x ^ (2 * (j + 3) + 3) ≤ x ^ 9 := by
      apply pow_le_pow_of_le_one hx0 hx1
      omega
    have h1 : (0:ℝ) ≤ x ^ (2 * (j + 3) + 3) := by positivity
    have h2 : (0:ℝ) ≤ x ^ 9 := by positivity
    have h3 := aCoef_tail_bound j
    have h4 := (aCoef_pos (j + 3)).le
    nlinarith
  have htail : (∑' j : ℕ, aCoef (j + 3) * |x| ^ (2 * (j + 3) + 3)) ≤ (24/259) * x ^ 9 := by
    have := Summable.tsum_le_tsum htail_le htail_sum hgeom
    have hval : (∑' j : ℕ, ((8/105) * (8/45 : ℝ) ^ j) * x ^ 9) = (24/259) * x ^ 9 := by
      rw [tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [hval] at this
    exact this
  have hfin : (∑ i ∈ Finset.range 3, aCoef i * |x| ^ (2 * i + 3))
      = 4 * x ^ 3 + (4/3) * x ^ 5 + (16/45) * x ^ 7 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, aCoef_zero, aCoef_one, aCoef_two, hax]
    norm_num
  unfold F1 hUp
  simp only [hax] at hsplit hfin ⊢
  rw [← hsplit, hfin]
  simp only [hax] at htail
  linarith

private lemma hUp_integral : (∫ x in (0:ℝ)..1, hUp x) = 1/6 + 2/9 + 2/45 + 12/1295 := by
  unfold hUp
  have hd : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => t ^ 2 / 2 - 4 * t ^ 3 / 3 + t ^ 4 + (2 / 9) * t ^ 6 + (2 / 45) * t ^ 8
        + (12 / 1295) * t ^ 10)
      (y - 4 * y ^ 2 + 4 * y ^ 3 + (4 / 3) * y ^ 5 + (16 / 45) * y ^ 7 + (24 / 259) * y ^ 9) y := by
    intro y
    have h := ((((((hasDerivAt_pow 2 y).div_const 2).sub
      (((hasDerivAt_pow 3 y).const_mul (4:ℝ)).div_const 3)).add
      (hasDerivAt_pow 4 y)).add ((hasDerivAt_pow 6 y).const_mul (2/9:ℝ))).add
      ((hasDerivAt_pow 8 y).const_mul (2/45:ℝ))).add ((hasDerivAt_pow 10 y).const_mul (12/1295:ℝ))
    exact h.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  · norm_num
  · apply Continuous.intervalIntegrable
    fun_prop

/-- A globally continuous function agreeing with `F1` on `[-1, 1]`. -/
private noncomputable def F1trunc (x : ℝ) : ℝ :=
  x - 4 * x ^ 2 + ∑' k : ℕ, aCoef k * (min |x| 1) ^ (2 * k + 3)

private lemma F1trunc_continuous : Continuous F1trunc := by
  have hc : Continuous fun x : ℝ => ∑' k : ℕ, aCoef k * (min |x| 1) ^ (2 * k + 3) := by
    apply continuous_tsum (u := fun k : ℕ => 4 * (1/2:ℝ) ^ k)
    · intro i; fun_prop
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
    · intro n x
      have h0 : (0:ℝ) ≤ min |x| 1 := le_min (abs_nonneg x) zero_le_one
      have h1 : min |x| 1 ≤ 1 := min_le_right _ _
      have hp : (min |x| 1) ^ (2 * n + 3) ≤ 1 := pow_le_one₀ h0 h1
      have hpn : (0:ℝ) ≤ (min |x| 1) ^ (2 * n + 3) := pow_nonneg h0 _
      have hA := aCoef_le_half n
      have hA0 := (aCoef_pos n).le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
  exact (by fun_prop : Continuous fun x : ℝ => x - 4 * x ^ 2).add hc

private lemma F1_eq_F1trunc {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : F1 x = F1trunc x := by
  have hax : |x| = x := abs_of_nonneg hx0
  have hmin : min |x| 1 = |x| := min_eq_left (by rw [hax]; exact hx1)
  unfold F1 F1trunc
  rw [hmin, hax]

private lemma F1_intervalIntegrable : IntervalIntegrable F1 volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
  refine (F1trunc_continuous.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
  intro x hx
  exact (F1_eq_F1trunc hx.1 hx.2).symm

theorem F1_integral_le : (∫ x in (0:ℝ)..1, F1 x) ≤ 4 / 9 := by
  have hcont : Continuous hUp := by unfold hUp; fun_prop
  have hint : IntervalIntegrable hUp volume 0 1 := hcont.intervalIntegrable _ _
  have h1 : (∫ x in (0:ℝ)..1, F1 x) ≤ ∫ x in (0:ℝ)..1, hUp x :=
    intervalIntegral.integral_mono_on (by norm_num) F1_intervalIntegrable hint
      (fun x hx => F1_le_hUp hx.1 hx.2)
  rw [hUp_integral] at h1
  linarith


end AristotleE1