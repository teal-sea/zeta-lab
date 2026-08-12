import Mathlib

open Polynomial

/-- If two reals are both closer to `c` than `|c|`, they have the same (nonzero) sign,
so their product is positive. -/
private lemma mul_pos_of_close_to_nonzero {a b c : ℝ} (ha : |a - c| < |c|) (hb : |b - c| < |c|) :
    0 < a * b := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · rw [abs_of_neg hc] at ha hb
    rw [abs_sub_lt_iff] at ha hb
    exact mul_pos_of_neg_of_neg (by linarith [ha.2]) (by linarith [hb.2])
  · rw [hc] at ha; simp at ha; exact absurd ha (not_lt.mpr (abs_nonneg _))
  · rw [abs_of_pos hc] at ha hb
    rw [abs_sub_lt_iff] at ha hb
    exact mul_pos (by linarith [ha.2]) (by linarith [hb.2])

theorem sign_change_of_odd_multiplicity (p : Polynomial ℝ) (hp : p ≠ 0) (x : ℝ)
    (hodd : Odd (p.rootMultiplicity x)) :
    ∃ ε > 0, ∀ y z, x - ε < y → y < x → x < z → z < x + ε → p.eval y * p.eval z < 0 := by
  set m := p.rootMultiplicity x with hm
  set q := p /ₘ (X - C x) ^ m with hqdef
  have hfac : (X - C x) ^ m * q = p := pow_mul_divByMonic_rootMultiplicity_eq p x
  have hqx : q.eval x ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero x hp
  -- Choose `ε` so that `q` stays within `|q.eval x|` of `q.eval x` on the `ε`-ball around `x`.
  have hcont : ContinuousAt (fun t => q.eval t) x := (q.continuous).continuousAt
  obtain ⟨ε, hε, hball⟩ :=
    Metric.continuousAt_iff.mp hcont |q.eval x| (abs_pos.mpr hqx)
  refine ⟨ε, hε, fun y z hy1 hy2 hz1 hz2 => ?_⟩
  have hqy : |q.eval y - q.eval x| < |q.eval x| := by
    have := hball (x := y) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simpa [Real.dist_eq] using this
  have hqz : |q.eval z - q.eval x| < |q.eval x| := by
    have := hball (x := z) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simpa [Real.dist_eq] using this
  have hqprod : 0 < q.eval y * q.eval z := mul_pos_of_close_to_nonzero hqy hqz
  have hevy : p.eval y = (y - x) ^ m * q.eval y := by
    rw [← hfac]; simp
  have hevz : p.eval z = (z - x) ^ m * q.eval z := by
    rw [← hfac]; simp
  have hkey : ((y - x) * (z - x)) ^ m < 0 :=
    hodd.pow_neg (mul_neg_of_neg_of_pos (by linarith) (by linarith))
  calc p.eval y * p.eval z
      = ((y - x) * (z - x)) ^ m * (q.eval y * q.eval z) := by
        rw [hevy, hevz, mul_pow]; ring
    _ < 0 := mul_neg_of_neg_of_pos hkey hqprod
