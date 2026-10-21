import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Reversal averaging and finite adversaries. Abstract deduction only: this file
does not assert that any transcendental entry in adversary.json has been
checked by Lean. Those entries are checked separately by verify.py.
-/

open Finset

namespace ReversalMinimax

variable {X : Type*}

def symmetrize (R : X → X) (f : X → ℝ) (x : X) : ℝ :=
  (f x + f (R x)) / 2

theorem symmetrize_invariant (R : X → X) (hR : Function.Involutive R)
    (f : X → ℝ) (x : X) :
    symmetrize R f (R x) = symmetrize R f x := by
  simp only [symmetrize, hR x]
  ring

theorem symmetrize_preserves_floor (R : X → X) (f : X → ℝ) (c : ℝ)
    (hc : ∀ x, c ≤ f x) : ∀ x, c ≤ symmetrize R f x := by
  intro x
  dsimp [symmetrize]
  linarith [hc x, hc (R x)]

/-- A convex feasible function class stable under reversal loses no floor
when restricted to invariant functions. Supremum attainment is unnecessary. -/
theorem invariant_floor_iff (R : X → X) (hR : Function.Involutive R)
    (C : Set (X → ℝ))
    (hrev : ∀ f ∈ C, (fun x => f (R x)) ∈ C)
    (hmid : ∀ f ∈ C, ∀ g ∈ C, (fun x => (f x + g x) / 2) ∈ C)
    (c : ℝ) :
    (∃ f ∈ C, ∀ x, c ≤ f x) ↔
      ∃ f ∈ C, (∀ x, f (R x) = f x) ∧ ∀ x, c ≤ f x := by
  constructor
  · rintro ⟨f, hf, hc⟩
    refine ⟨symmetrize R f, hmid f hf (fun x => f (R x)) (hrev f hf), ?_, ?_⟩
    · exact symmetrize_invariant R hR f
    · exact symmetrize_preserves_floor R f c hc
  · rintro ⟨f, hf, _, hc⟩
    exact ⟨f, hf, hc⟩

variable {ι : Type*} [Fintype ι]

/-- Any finite probability distribution upper-bounds a uniform floor.
The upper bound on the expectation is an explicit hypothesis. -/
theorem finite_adversary (p f : ι → ℝ) (c U : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hc : ∀ i, c ≤ f i) (hupper : ∑ i, p i * f i ≤ U) : c ≤ U := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hc i) (hp i))
  calc c = ∑ i, p i * c := by rw [← Finset.sum_mul, hpsum, one_mul]
       _ ≤ ∑ i, p i * f i := h
       _ ≤ U := hupper

/-- Exact coefficient-budget step, separately for each span and pressure.
It applies without any sign condition on the features. -/
theorem budget_bound (a feature : ι → ℝ) (budget cap : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = budget)
    (hcap : ∀ i, feature i ≤ cap) :
    ∑ i, a i * feature i ≤ budget * cap := by
  calc (∑ i, a i * feature i) ≤ ∑ i, a i * cap :=
         Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcap i) (ha i))
       _ = budget * cap := by rw [← Finset.sum_mul, hsum]

theorem recorded_targets_excluded :
    (7914014 : ℝ) / 1000000000 < 19791 / 2500000 ∧
    (7914014 : ℝ) / 1000000000 < 791685781 / 100000000000 := by
  constructor <;> norm_num

/-- Arithmetic after the 21 transcendental moment bounds have been supplied.
No hypothesis here asserts those moment bounds. This is only their exact
rational combination, which is independently checked by the Python verifier. -/
theorem concrete_budget_arithmetic :
    2 * ((634884759717 : ℝ) / 10^15 + 10127109795 / 10^15 +
      73116002704 / 10^15 + 45872037949 / 10^15 +
      83018119185 / 10^15 + 58811254374 / 10^15) +
      (93 / 23000) * (1509184664171 / 10^12)
      = 182022320819207 / 23000000000000000 := by norm_num

theorem concrete_budget_lt_target :
    (182022320819207 : ℝ) / 23000000000000000 < 7914014 / 1000000000 := by
  norm_num

#print axioms symmetrize_invariant
#print axioms symmetrize_preserves_floor
#print axioms invariant_floor_iff
#print axioms finite_adversary
#print axioms budget_bound
#print axioms recorded_targets_excluded
#print axioms concrete_budget_arithmetic
#print axioms concrete_budget_lt_target

end ReversalMinimax
