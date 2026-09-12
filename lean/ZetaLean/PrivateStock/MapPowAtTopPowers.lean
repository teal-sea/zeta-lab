import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The filter `atTop` on the powers of `q`

Theorem 1.1 of Sawin–Shusterman is an asymptotic as `X → ∞` through the powers of `q`, i.e. along
the filter `atTop` on the submonoid `Submonoid.powers q ⊆ ℕ`. When `1 < q`, the map
`m ↦ q ^ m` is an order isomorphism from `ℕ` onto `Submonoid.powers q`, so that filter is the
pushforward of `atTop` on `ℕ`; this lets one replace a statement indexed by `Submonoid.powers q`
with the corresponding statement indexed by the exponent.
-/

set_option autoImplicit false

/-- For `1 < q`, the exponent map `m ↦ q ^ m : ℕ → Submonoid.powers q` pushes `atTop` forward to
`atTop`. -/
theorem Submonoid.map_pow_atTop_powers {q : ℕ} (hq : 1 < q) :
    Filter.map (fun m : ℕ ↦ (⟨q ^ m, m, rfl⟩ : Submonoid.powers q)) Filter.atTop =
      Filter.atTop := by
  -- `m ↦ q ^ m` is monotone, and above the base point `q ^ 0 = 1` it is a Galois insertion:
  -- every element of `Submonoid.powers q` is `q ^ k` for some `k`, and `q ^ a ≤ q ^ k ↔ a ≤ k`.
  refine Filter.map_atTop_eq_of_gc_preorder ?_ ⟨1, 0, rfl⟩ ?_
  · intro a b hab
    exact Nat.pow_le_pow_right hq.le hab
  · rintro ⟨c, k, rfl⟩ -
    refine ⟨k, Subtype.ext rfl, fun a ↦ ?_⟩
    exact Nat.pow_le_pow_iff_right hq
