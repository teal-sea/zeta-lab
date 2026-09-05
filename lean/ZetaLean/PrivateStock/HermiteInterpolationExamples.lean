import ZetaLean.PrivateStock.HermiteInterpolation
import Mathlib

open scoped Polynomial
open Finset Polynomial

-- Characteristic two: ordinary second derivatives cannot specify this jet,
-- while Hasse derivatives correctly recover the quadratic coefficient.
example : (hasseDeriv 2 (X ^ 2 : (ZMod 2)[X])).eval 0 = 1 := by
  have h := congrArg (Polynomial.eval (0 : ZMod 2))
    (hasseDeriv_natDegree_eq_C (X ^ 2 : (ZMod 2)[X]))
  simpa using h

example : derivative (derivative (X ^ 2 : (ZMod 2)[X])) = 0 := by
  norm_num
  simpa using congrArg C (show (2 : ZMod 2) = 0 from rfl)

-- Arbitrary characteristic-two data at the two field elements, with order three
-- at each, determines a unique polynomial of degree strictly less than six.
example (v : (x : ({0, 1} : Finset (ZMod 2))) → Fin 3 → ZMod 2) :
    ∃! p : (ZMod 2)[X], p.degree < 6 ∧
      ∀ (x : ({0, 1} : Finset (ZMod 2))) (k : Fin 3),
        (hasseDeriv k p).eval (x : ZMod 2) = v x k := by
  simpa using existsUnique_hermiteInterpolation ({0, 1} : Finset (ZMod 2)) (fun _ ↦ 3) v

-- No positivity hypotheses on the individual orders or on the total are needed.
set_option linter.unnecessarySimpa false in
example : ∃! p : ℚ[X], p.degree < 0 := by
  simpa using existsUnique_hermiteInterpolation (∅ : Finset ℚ) (fun _ ↦ 0)
    (fun x ↦ False.elim (Finset.notMem_empty _ x.property))

#print axioms Polynomial.pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero
#print axioms Polynomial.sum_rootMultiplicity_le_natDegree
#print axioms Polynomial.eq_zero_of_degree_lt_of_hasseDeriv_eval_eq_zero
#print axioms Polynomial.eq_of_degree_lt_of_hasseDeriv_eval_eq
#print axioms Polynomial.hermiteEvaluation_injective
#print axioms Polynomial.hermiteEvaluation_surjective
#print axioms Polynomial.existsUnique_hermiteInterpolation

