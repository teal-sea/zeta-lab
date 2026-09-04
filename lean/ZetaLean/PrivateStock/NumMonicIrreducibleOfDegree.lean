import Mathlib.Algebra.Polynomial.Monic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting monic irreducible polynomials of a given degree

Over a finite field `F`, the monic irreducible polynomials of degree `d` are the "primes" of
`F[T]` of norm `|F| ^ d`; see the sentence after Equation (1.4) of Sawin–Shusterman. This module
records the count of such polynomials as a natural number.

The count is finite because `F[X]` has only finitely many polynomials of any fixed degree, but we
do not need that here: `Nat.card` is `0` on infinite types, so the definition makes sense as
stated.
-/

set_option autoImplicit false

open scoped Polynomial

/-- The number of monic irreducible polynomials of degree `d` over a finite field `F`. -/
noncomputable def Polynomial.numMonicIrreducibleOfDegree (F : Type*) [Field F] [Finite F]
    (d : ℕ) : ℕ :=
  Nat.card {P : F[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d}
