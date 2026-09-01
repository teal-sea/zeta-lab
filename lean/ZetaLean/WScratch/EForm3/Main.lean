import Mathlib
import ZetaLean.WScratch.EForm3.Counting
import ZetaLean.WScratch.EForm3.Gap

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# The retention inequality under `2π` separation

Main results:

* `retention_gap` — the exact gap identity.
* `retention_of_damage` — the retention inequality holds as soon as the total damage
  `∑_j (Qim² - Qre²)` is at most `Shq y / 2`.
* `retention_separated_of_le` — the retention inequality for **every** `n`, every `t` and every
  `y ∈ [0, 1/2]`, provided consecutive offsets are separated by any `d ≥ 4`.
* `retention_separated` — the case `d = 2π` asked for in `PROBLEM.md`.
* `retention_le_three` — the case `n ≤ 3`, with no separation hypothesis.
-/

namespace Retention

theorem retention_gap (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) :
    Eng (fun w => Fsum n x w + Pfun y t w)
      = Eng (Fsum n x) + 4
        + (1 / Aconst ^ 2) * (4 * ∑ j ∈ Finset.range n,
            (Qre y (x j - t) ^ 2 - Qim y (x j - t) ^ 2) + 2 * Shq y) := by
  have hA : Aconst ≠ 0 := Aconst_ne_zero
  rw [energy_FP, energy_F, Shq]
  field_simp
  ring

theorem retention_of_damage (n : ℕ) (x : ℕ → ℝ) (y t : ℝ)
    (hdam : ∑ j ∈ Finset.range n, (Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2) ≤ Shq y / 2) :
    (199/200) * Eng (Fsum n x) + (n : ℝ)/200 + 4
      ≤ Eng (fun w => Fsum n x w + Pfun y t w) := by
  have hA2 : (0:ℝ) < Aconst ^ 2 := pow_pos Aconst_pos 2
  have hsum : ∑ j ∈ Finset.range n, (Qre y (x j - t) ^ 2 - Qim y (x j - t) ^ 2)
      = - ∑ j ∈ Finset.range n, (Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hbr : (0:ℝ) ≤ 4 * ∑ j ∈ Finset.range n,
      (Qre y (x j - t) ^ 2 - Qim y (x j - t) ^ 2) + 2 * Shq y := by
    rw [hsum]
    linarith only [hdam]
  have hnn : (0:ℝ) ≤ (1 / Aconst ^ 2) * (4 * ∑ j ∈ Finset.range n,
      (Qre y (x j - t) ^ 2 - Qim y (x j - t) ^ 2) + 2 * Shq y) :=
    mul_nonneg (by positivity) hbr
  have hn := energy_F_ge n x
  rw [retention_gap]
  linarith only [hnn, hn]

/-- **Retention under separation `d ≥ 4`.**  For every `n`, every centre `t`, every
`y ∈ [0, 1/2]` and every configuration whose consecutive offsets differ by at least `d ≥ 4`,
the retention inequality `(199/200) E[F] + n/200 + 4 ≤ E[F + P]` holds. -/
theorem retention_separated_of_le {n : ℕ} {x : ℕ → ℝ} {y t d : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2)
    (hd : 4 ≤ d) (hsep : ∀ i, i + 1 < n → x i + d ≤ x (i+1)) :
    (199/200) * Eng (Fsum n x) + (n : ℝ)/200 + 4
      ≤ Eng (fun w => Fsum n x w + Pfun y t w) := by
  refine retention_of_damage n x y t ?_
  have h1 := separated_damage_of_le (t := t) hy0 hy hd hsep
  have h2 := Shq_half_lower y
  have h3 : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
  linarith only [h1, h2, h3]

/-- **Retention under `2π`-separation**, the case `PROBLEM.md` asks for.  It is a special case
of `retention_separated_of_le`, since our constants in fact reach the separation `4 < 2π`. -/
theorem retention_separated {n : ℕ} {x : ℕ → ℝ} {y t : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2)
    (hsep : ∀ i, i + 1 < n → x i + 2 * Real.pi ≤ x (i+1)) :
    (199/200) * Eng (Fsum n x) + (n : ℝ)/200 + 4
      ≤ Eng (fun w => Fsum n x w + Pfun y t w) := by
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  exact retention_separated_of_le hy0 hy (by linarith) hsep

/-- **The case `n ≤ 3`, with no separation hypothesis at all.**  Three offsets can damage at
most `3 · 0.0383 y² = 0.1149 y²`, which is below the gain `Shq y / 2 ≥ 0.12986 y²`. -/
theorem retention_le_three {n : ℕ} {x : ℕ → ℝ} {y t : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2)
    (hn : n ≤ 3) :
    (199/200) * Eng (Fsum n x) + (n : ℝ)/200 + 4
      ≤ Eng (fun w => Fsum n x w + Pfun y t w) := by
  refine retention_of_damage n x y t ?_
  have hterm : ∀ j ∈ Finset.range n,
      Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2 ≤ y^2 * (383/10000) :=
    fun j _ => uniform_damage hy0 hy
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hn' : (n:ℝ) ≤ 3 := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h2 := Shq_half_lower y
  have h3 : (0:ℝ) ≤ y^2 := sq_nonneg y
  have h4 : (0:ℝ) ≤ (3 - (n:ℝ)) * (y^2 * (383/10000)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith only [hsum, h2, h3, h4]

end Retention

#print axioms Retention.retention_le_three
#print axioms Retention.uniform_damage
#print axioms Retention.retention_gap
#print axioms Retention.retention_of_damage
#print axioms Retention.retention_separated
#print axioms Retention.retention_separated_of_le
#print axioms Retention.separated_damage
#print axioms Retention.Gsum_le
#print axioms Retention.Qim_far_sq
#print axioms Retention.Qim_far_first_order
#print axioms Retention.no_damage
#print axioms Retention.Shq_half_lower
#print axioms Retention.energy_F_ge
#print axioms Retention.energy_FP
#print axioms Retention.master
