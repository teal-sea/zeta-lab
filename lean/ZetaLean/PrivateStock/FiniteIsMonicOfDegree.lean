import ZetaLean.PrivateStock.CardIsMonicOfDegree

/-!
# Finiteness of the set of monic polynomials of a given degree

Over a finite field `F`, the monic polynomials of degree `n` are parametrised by their `n`
lower-order coefficients (`Polynomial.isMonicOfDegreeEquivFun`), so there are only finitely many
of them. This is the finiteness underlying the count `Polynomial.card_isMonicOfDegree`.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

/-- Over a finite field there are only finitely many monic polynomials of a given degree. -/
theorem finite_isMonicOfDegree {F : Type*} [Field F] [Finite F] (n : ℕ) :
    Finite {f : F[X] // Polynomial.IsMonicOfDegree f n} :=
  Finite.of_equiv _ (isMonicOfDegreeEquivFun F n).symm

end Polynomial
