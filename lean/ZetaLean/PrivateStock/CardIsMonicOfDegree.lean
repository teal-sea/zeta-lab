import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The number of monic polynomials of a given degree over a finite field

A monic polynomial of degree `n` over `F` is `X ^ n` plus an arbitrary polynomial of degree
less than `n`, and the latter are parametrised by their `n` coefficients. Hence there are
exactly `|F| ^ n` of them.

This is the count that makes `|f| = |F| ^ deg(f)` the right notion of norm on `F[T]`, and it is
the total against which the counts of monic *irreducible* polynomials
(`Polynomial.numMonicIrreducibleOfDegree`) are compared.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

/-- Monic polynomials of degree `n` over `F` correspond to polynomials of degree `< n`, hence
to their `n` coefficients. -/
noncomputable def isMonicOfDegreeEquivFun (F : Type*) [Field F] (n : ℕ) :
    {f : F[X] // IsMonicOfDegree f n} ≃ (Fin n → F) :=
  (Equiv.subtypeEquivRight fun f ↦
      (isMonicOfDegree_iff' f n).trans and_comm).trans <|
    (monicEquivDegreeLT n).trans (degreeLTEquiv F n).toEquiv

/-- Over a finite field `F` there are exactly `|F| ^ n` monic polynomials of degree `n`. -/
theorem card_isMonicOfDegree (F : Type*) [Field F] [Finite F] (n : ℕ) :
    Nat.card {f : F[X] // Polynomial.IsMonicOfDegree f n} = Nat.card F ^ n := by
  rw [Nat.card_congr (isMonicOfDegreeEquivFun F n), Nat.card_fun, Nat.card_fin]

end Polynomial
