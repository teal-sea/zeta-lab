import Mathlib
import ZetaLean.Rigor

/-!
# Certified Dirichlet Partial Sums

Infrastructure for rigorously evaluating partial sums of a Dirichlet series
`∑ aₙ n^{-s}` from certified enclosures of the individual terms.

The enclosures themselves come from *outside* the kernel (the Oracle Boundary
Pattern: `lean/oracle_dh.py` computes each term `aₙ n^{-s}` with `mpmath.iv`
and emits a `ComplexInterval` per term into `ZetaLean/OracleDH.lean`). What
is proved *here* is the glue the oracle cannot fake: if each term enclosure
contains its term, the folded sum encloses the partial sum
(`ComplexInterval.contains_sumList`), by induction from the soundness lemmas
in `ZetaLean/Rigor.lean`.

The kernel-checked bound tying `n^{-s} = exp(-s log n)` to a computed
enclosure now exists: `ZetaLean/IntervalCExp.lean`'s
`ComplexInterval.contains_dirichletTerm` composes certified `log`
(`Interval.logQ`) and certified complex `exp` (`Complex.exp_bound` through
`ComplexInterval.expC`), so individual term enclosures no longer need the
oracle at all.  The tail bound for the analytic continuation exists too:
`ZetaLean/DHTailBound.lean`'s `DH_tail_bound` bounds `DH` minus any `5K`-term
partial sum explicitly on all of `Re s > 0`, via the block-regrouped series
and the identity theorem.  What remains open of Rung 3 Phase B is only
assembly: enclosing the finite sum tightly enough, at the centre and on the
sphere, to discharge the two disk inequalities of
`davenport_heilbronn_of_certified_disk`.  Until that lands, any number about
`DH` itself is still an oracle's, exactly as `rigor.py` labels its own
uncertified steps.
-/

namespace ZetaLean.ComplexInterval

/-- Fold a list of enclosures into an enclosure of the sum. -/
def sumList (l : List ComplexInterval) : ComplexInterval :=
  l.foldr add (exact 0 0)

/-- Soundness of `sumList`: termwise containment gives containment of the
partial sum. This is the kernel-checked half of the Oracle Boundary Pattern. -/
theorem contains_sumList {l : List ComplexInterval} {zs : List ℂ}
    (h : List.Forall₂ (fun b z => b.contains z) l zs) :
    (sumList l).contains zs.sum := by
  induction h with
  | nil => simpa [sumList] using contains_zero
  | cons h₁ _ ih => simpa [sumList] using contains_add h₁ ih

end ZetaLean.ComplexInterval
