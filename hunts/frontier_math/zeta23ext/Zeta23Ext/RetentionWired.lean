import Mathlib
import Zeta23Ext.EForm3.Main
import Zeta23Ext.RetentionAlgebra

/-!
# The retention algebra, discharged on the development's own objects

`Zeta23Ext/RetentionAlgebra.lean` proves two identities over abstract reals,
which is what let them be machine-proved without this package present. That
form is not yet load-bearing: the hypotheses `hgap`, `hsym`, `hdiag` and `hEF`
have to come from the tree's own theorems before the identities say anything
about the retention chain.

This file discharges all four, from `Retention.retention_gap`,
`Retention.energy_F`, `Retention.Qre_zero_even` and `Retention.Qre_zero_zero`.
Nothing here is new mathematics; it is the wiring that makes the abstract
lemmas concrete, and it is separated from them precisely because the abstract
statements had to be provable against Mathlib alone.
-/

open scoped BigOperators
open Finset

namespace Retention

/-- **The exact retention margin**, on this development's objects.

The amount by which `(199/200)·E[F] + n/200 + 4 ≤ E[F+P]` holds is the
repulsion slack `(1/200)(E[F] − n)` plus the damage budget. Composed with
`energy_repulsion` below, this is the identity showing that the repulsion
term is not optional: the weaker route discards it by using `n ≤ E[F]` in
place of the energy identity. -/
theorem margin_identity (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) :
    Eng (fun w => Fsum n x w + Pfun y t w)
        - ((199/200) * Eng (Fsum n x) + (n : ℝ)/200 + 4)
      = (1/200) * (Eng (Fsum n x) - (n : ℝ))
        + (1 / Aconst ^ 2) * (2 * Shq y
            - 4 * ∑ j ∈ Finset.range n, (Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2)) := by
  refine RetentionAlgebra.margin_eq n Aconst (Eng (Fsum n x))
    (Eng (fun w => Fsum n x w + Pfun y t w)) (Shq y)
    (fun j => Qim y (x j - t) ^ 2 - Qre y (x j - t) ^ 2) Aconst_ne_zero ?_
  rw [retention_gap]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => by ring)

/-- **The repulsion is exactly the slack in `n ≤ E[F]`.**

`E[F] − n` is twice the strictly-upper-triangular sum of `Qre 0 (x j − x k)²`,
so the inequality `energy_F_ge` discards precisely that quantity. -/
theorem energy_repulsion (n : ℕ) (x : ℕ → ℝ) :
    Eng (Fsum n x) - (n : ℝ)
      = (2 / Aconst ^ 2) * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          (if j < k then Qre 0 (x j - x k) ^ 2 else 0) := by
  refine RetentionAlgebra.energy_sub_card n Aconst
    (fun j k => Qre 0 (x j - x k) ^ 2) Aconst_ne_zero ?_ ?_
    (Eng (Fsum n x)) (energy_F n x)
  · intro j k
    have h : x k - x j = -(x j - x k) := by ring
    rw [h, Qre_zero_even]
  · intro j
    rw [sub_self, Qre_zero_zero]

end Retention

#print axioms Retention.margin_identity
#print axioms Retention.energy_repulsion
