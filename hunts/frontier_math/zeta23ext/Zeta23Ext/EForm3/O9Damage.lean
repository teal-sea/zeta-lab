import Zeta23Ext.BandCert.Phi

/-!
# The damage enclosure, as an interval object

`arm_identification.py` records the identity that makes this file possible:

    ghat z = Phi2 (-I * z)

so, since `Phi2` has real coefficients and `Dam y s = -Re (ghat (y + I s))^2`,

    Dam y s = -Re (Phi2 (s + I y))^2.

`BandDual.phiC` already encloses `Phi2 (X + I Y)` (`phiC_mem`), so the damage
enclosure is three compositions on top of it: evaluate `phiC` on the cell,
square with `CIv.mul`, negate the real part.  Nothing new is needed from
`Leaves.lean`.

`damageIv` is stated at the single depth `y = 1/2`, which is the binding one;
the reduction of every `y ∈ [0,1/2]` to it is a separate obligation
(`D y s / y^2 ≤ 4 * D (1/2) s`) and is **not** discharged here.
-/

namespace Retention

open BandDual

/-- The depth this table is built at. -/
def yHalf : EIv := EIv.ofQ 1 2

/-- `sinh (y/2)` at `y = 1/2`. -/
def shHalf : EIv := (sinhCoshSmall (EIv.divInt yHalf 2)).1

/-- `cosh (y/2)` at `y = 1/2`. -/
def chHalf : EIv := (sinhCoshSmall (EIv.divInt yHalf 2)).2

/-- The cell `[lo/2^64, hi/2^64]` as an interval. -/
def cellIv (lo hi : ℤ) : EIv := some ⟨lo, hi⟩

/-- `Dam (1/2) s = -Re (Phi2 (s + I/2))^2`, enclosed over the cell. -/
def damageIv (lo hi : ℤ) : EIv :=
  let p := phiC (cellIv lo hi) yHalf shHalf chHalf
  EIv.neg (CIv.mul p p).1

/-!
## The soundness obligation, stated but deliberately NOT asserted here

The seam between this table and the analysis is

    damageIv_mem : (cellIv lo hi).mem s →
      (damageIv lo hi).mem (-(Phi2 (s + I/2) ^ 2).re)

whose proof is `phiC_mem` (its `y ≠ 0` side condition is met, `y = 1/2`),
then `CIv.mul_mem` to square, then `EIv.neg_mem` on the real part.

It is **not written in this file, and no `sorry` stands in for it**: this
package has been sorry-free throughout and a placeholder here would be the
first, which would cost more than the lemma is worth.  The statement is
recorded in `hunts/frontier_math/O9-BRIEF.md` as an obligation for a prover.
Until it exists, `O9Check.lean` checks the table and proves nothing about
`Dam`.
-/

end Retention
