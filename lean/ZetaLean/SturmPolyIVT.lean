import Mathlib

/-!
# Sign change of a real polynomial forces a root

If a real polynomial takes values of opposite signs at `a` and `b` (with `a < b`),
then it has a root strictly between `a` and `b`.  The proof is the intermediate
value theorem applied to the (continuous) evaluation map of the polynomial.
-/

/-- Polynomial evaluation is continuous on any set. -/
theorem Polynomial.continuousOn_eval_real (p : Polynomial ℝ) (s : Set ℝ) :
    ContinuousOn (fun x => p.eval x) s :=
  p.continuous_aeval.continuousOn

/-- If `p.eval a * p.eval b < 0` with `a < b`, then `p` has a root in `(a, b)`. -/
theorem polynomial_sign_change_has_root (p : Polynomial ℝ) (a b : ℝ) (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ x, a < x ∧ x < b ∧ p.IsRoot x := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuousOn_eval_real _
  rcases mul_neg_iff.1 h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · -- `p.eval a > 0 > p.eval b`
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo' hab.le hcont (Set.mem_Ioo.2 ⟨hB, hA⟩)
    exact ⟨x, hx.1, hx.2, hx0⟩
  · -- `p.eval a < 0 < p.eval b`
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Ioo hab.le hcont (Set.mem_Ioo.2 ⟨hA, hB⟩)
    exact ⟨x, hx.1, hx.2, hx0⟩
