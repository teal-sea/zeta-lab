import Mathlib

/-!
# Taylor bounds for `sin` and `cos`

Mathlib provides `Real.sin_le` and `Real.one_sub_sq_div_two_le_cos`; we bootstrap from these,
by four successive monotonicity arguments, up to the sixth-order lower bound

`cos x ≥ 1 - x^2/2 + x^4/24 - x^6/720`,

which is what the near-field estimate needs (Mathlib's `Real.cos_bound` is only useful
for `|x| ≤ 1`, and we need arguments up to about `2.1`).
-/

open scoped Real

namespace Retention

/-- If `f 0 = 0` and `f` has a nonnegative derivative on `[0, ∞)`, then `f ≥ 0` there. -/
lemma nonneg_of_deriv_nonneg {f F : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (F x) x)
    (h0 : f 0 = 0) (hF : ∀ x, 0 ≤ x → 0 ≤ F x) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici (0:ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hf x).continuousAt.continuousWithinAt) ?_ ?_
    · exact fun x _ => ((hf x).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [(hf x).deriv]
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact hF x (le_of_lt hx)
  intro x hx
  have := hmono (Set.self_mem_Ici) (Set.mem_Ici.2 hx) hx
  rwa [h0] at this

/-- `x - x^3/6 ≤ sin x` for `x ≥ 0`. -/
lemma sin_ge_taylor3 {x : ℝ} (hx : 0 ≤ x) : x - x^3/6 ≤ Real.sin x := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ Real.sin z - (z - z^3/6) := by
    refine nonneg_of_deriv_nonneg (F := fun z => Real.cos z - (1 - z^2/2)) ?_ (by simp) ?_
    · intro z
      have h1 : HasDerivAt (fun z : ℝ => Real.sin z) (Real.cos z) z := Real.hasDerivAt_sin z
      have hp3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * z ^ 2) z :=
        (hasDerivAt_pow 3 z).congr_deriv (by norm_num)
      have h2 : HasDerivAt (fun z : ℝ => z - z^3/6) (1 - z^2/2) z :=
        ((hasDerivAt_id' z).sub (hp3.div_const 6)).congr_deriv (by ring)
      have h3 : HasDerivAt (fun z : ℝ => Real.sin z - (z - z^3/6))
          (Real.cos z - (1 - z^2/2)) z := h1.sub h2
      exact h3
    · intro z _
      have := Real.one_sub_sq_div_two_le_cos (x := z)
      linarith
  linarith [key x hx]

/-- `cos x ≤ 1 - x^2/2 + x^4/24` for `x ≥ 0` (hence for all `x`, by evenness). -/
lemma cos_le_taylor4 (x : ℝ) : Real.cos x ≤ 1 - x^2/2 + x^4/24 := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ (1 - z^2/2 + z^4/24) - Real.cos z := by
    refine nonneg_of_deriv_nonneg (F := fun z => (-z + z^3/6) + Real.sin z) ?_ (by simp) ?_
    · intro z
      have hp2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * z) z :=
        (hasDerivAt_pow 2 z).congr_deriv (by norm_num)
      have hp4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * z ^ 3) z :=
        (hasDerivAt_pow 4 z).congr_deriv (by norm_num)
      have h1 : HasDerivAt (fun z : ℝ => 1 - z^2/2 + z^4/24) (-z + z^3/6) z :=
        (((hasDerivAt_const z (1:ℝ)).sub (hp2.div_const 2)).add
          (hp4.div_const 24)).congr_deriv (by ring)
      have h2 : HasDerivAt (fun z : ℝ => Real.cos z) (-Real.sin z) z := Real.hasDerivAt_cos z
      have h3 : HasDerivAt (fun z : ℝ => (1 - z^2/2 + z^4/24) - Real.cos z)
          ((-z + z^3/6) + Real.sin z) z := (h1.sub h2).congr_deriv (by ring)
      exact h3
    · intro z hz
      have := sin_ge_taylor3 hz
      linarith
  rcases le_total 0 x with h | h
  · linarith [key x h]
  · have : Real.cos x = Real.cos (-x) := (Real.cos_neg x).symm
    have h2 := key (-x) (by linarith)
    rw [this]
    have : (-x)^2 = x^2 := by ring
    have h4 : (-x)^4 = x^4 := by ring
    rw [this, h4] at h2
    linarith

/-- `sin x ≤ x - x^3/6 + x^5/120` for `x ≥ 0`. -/
lemma sin_le_taylor5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x^3/6 + x^5/120 := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ (z - z^3/6 + z^5/120) - Real.sin z := by
    refine nonneg_of_deriv_nonneg (F := fun z => (1 - z^2/2 + z^4/24) - Real.cos z) ?_ (by simp) ?_
    · intro z
      have hp3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * z ^ 2) z :=
        (hasDerivAt_pow 3 z).congr_deriv (by norm_num)
      have hp5 : HasDerivAt (fun x : ℝ => x ^ 5) (5 * z ^ 4) z :=
        (hasDerivAt_pow 5 z).congr_deriv (by norm_num)
      have h1 : HasDerivAt (fun z : ℝ => z - z^3/6 + z^5/120) (1 - z^2/2 + z^4/24) z :=
        (((hasDerivAt_id' z).sub (hp3.div_const 6)).add
          (hp5.div_const 120)).congr_deriv (by ring)
      have h3 : HasDerivAt (fun z : ℝ => (z - z^3/6 + z^5/120) - Real.sin z)
          ((1 - z^2/2 + z^4/24) - Real.cos z) z := h1.sub (Real.hasDerivAt_sin z)
      exact h3
    · intro z _
      linarith [cos_le_taylor4 z]
  linarith [key x hx]

/-- `1 - x^2/2 + x^4/24 - x^6/720 ≤ cos x`, for every real `x`. -/
lemma cos_ge_taylor6 (x : ℝ) : 1 - x^2/2 + x^4/24 - x^6/720 ≤ Real.cos x := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ Real.cos z - (1 - z^2/2 + z^4/24 - z^6/720) := by
    refine nonneg_of_deriv_nonneg
      (F := fun z => (z - z^3/6 + z^5/120) - Real.sin z) ?_ (by simp) ?_
    · intro z
      have hp2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * z) z :=
        (hasDerivAt_pow 2 z).congr_deriv (by norm_num)
      have hp4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * z ^ 3) z :=
        (hasDerivAt_pow 4 z).congr_deriv (by norm_num)
      have hp6 : HasDerivAt (fun x : ℝ => x ^ 6) (6 * z ^ 5) z :=
        (hasDerivAt_pow 6 z).congr_deriv (by norm_num)
      have h1 : HasDerivAt (fun z : ℝ => 1 - z^2/2 + z^4/24 - z^6/720)
          (-z + z^3/6 - z^5/120) z :=
        ((((hasDerivAt_const z (1:ℝ)).sub (hp2.div_const 2)).add
          (hp4.div_const 24)).sub (hp6.div_const 720)).congr_deriv (by ring)
      have h3 : HasDerivAt (fun z : ℝ => Real.cos z - (1 - z^2/2 + z^4/24 - z^6/720))
          ((z - z^3/6 + z^5/120) - Real.sin z) z :=
        ((Real.hasDerivAt_cos z).sub h1).congr_deriv (by ring)
      exact h3
    · intro z hz
      linarith [sin_le_taylor5 hz]
  rcases le_total 0 x with h | h
  · linarith [key x h]
  · have hc : Real.cos x = Real.cos (-x) := (Real.cos_neg x).symm
    have h2 := key (-x) (by linarith)
    have e2 : (-x)^2 = x^2 := by ring
    have e4 : (-x)^4 = x^4 := by ring
    have e6 : (-x)^6 = x^6 := by ring
    rw [e2, e4, e6] at h2
    rw [hc]
    linarith

end Retention
