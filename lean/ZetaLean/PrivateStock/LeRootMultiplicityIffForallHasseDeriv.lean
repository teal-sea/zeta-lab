import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Root multiplicity via Hasse derivatives

A root `x` of a nonzero polynomial `P` has multiplicity at least `l` exactly when the first `l`
Hasse derivatives of `P` vanish at `x`.

Unlike the characterisation through the ordinary derivative, this one is valid over an arbitrary
commutative ring: the `k`-th Hasse derivative plays the role of `P⁽ᵏ⁾ / k!`, which is what the
Taylor expansion of `P` at `x` actually needs, and no division by `k!` ever takes place. This is
the form one wants in characteristic `p`, where `hasseDeriv p` is not determined by `derivative`.

The proof is the Taylor expansion and nothing else. `Polynomial.taylor x` is the algebra
automorphism `P ↦ P.comp (X + C x)` of `R[X]`; it carries `(X - C x) ^ l` to `X ^ l`, so

`(X - C x) ^ l ∣ P  ↔  X ^ l ∣ taylor x P  ↔  ∀ k < l, (taylor x P).coeff k = 0`,

and `Polynomial.taylor_coeff` identifies `(taylor x P).coeff k` with `(hasseDeriv k P).eval x`.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

/-- The multiplicity of `x` as a root of a nonzero polynomial `P` is at least `l` if and only if
the Hasse derivatives `hasseDeriv k P` for `k < l` all vanish at `x`. -/
theorem le_rootMultiplicity_iff_forall_hasseDeriv_eval_eq_zero {R : Type*} [CommRing R]
    [IsDomain R] {P : R[X]} (hP : P ≠ 0) (x : R) (l : ℕ) :
    l ≤ P.rootMultiplicity x ↔ ∀ k < l, (Polynomial.hasseDeriv k P).eval x = 0 := by
  -- `taylorEquiv x` and `taylor x` agree as functions, definitionally.
  have hcoe : ∀ p : R[X], taylorEquiv x p = taylor x p := fun _ ↦ rfl
  -- The Taylor automorphism sends `(X - C x) ^ l` to `X ^ l`.
  have ht : taylor x ((X - C x) ^ l) = X ^ l := by
    rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  rw [le_rootMultiplicity_iff hP, ← map_dvd_iff (taylorEquiv x), hcoe, hcoe, ht, X_pow_dvd_iff]
  exact forall₂_congr fun k _ ↦ by rw [taylor_coeff]

end Polynomial
