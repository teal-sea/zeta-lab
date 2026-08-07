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

What this deliberately does **not** yet provide (the open mountain of Rung 3
Phase B): a kernel-checked bound tying `n^{-s} = exp(-s log n)` to the
oracle's enclosure — i.e. certified `exp`/`log` evaluation inside Lean, e.g.
via `Complex.exp_bound` — and a tail bound for the analytic continuation
(the raw series does not converge absolutely at the off-line zero,
`Re s ≈ 0.808`). Until those exist, the oracle's numbers are inputs, not
theorems, exactly as `rigor.py` labels its own uncertified steps.
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
