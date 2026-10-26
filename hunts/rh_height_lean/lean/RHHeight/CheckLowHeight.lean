module

public import RHHeight.LowHeight

/-! Pins the statement of the piece `low_height` of hunt #137 and prints the axioms of every
declaration in `RHHeight/LowHeight.lean`. `low_height` is one of the four pieces the skeleton
consumes (`RHHeight/Skeleton.lean`); it is not the target `RHHeight50`. -/

open Complex

-- `LowHeight` unfolded: Mathlib's own `riemannZeta`, the open strip, `0 < Im ρ ≤ 3`.
example : RHHeight.LowHeight =
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 3 → False := rfl

-- The plan's target signature for the piece, verbatim, is met by `low_height`.
example : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 0 < ρ.im → ρ.im ≤ 3 → False :=
  RHHeight.low_height

-- It fills the `LowHeight` slot of the skeleton's reduction; the other three pieces and hunt
-- #133's input stay hypotheses here.
example (hΓ : RHHeight.GammaIncrement) (hH : RHHeight.HorizontalLegs)
    (hE : RHHeight.ExactArgument) (h10 : RHHeight.TenZerosOnLine) : RHHeight.RHHeight50 :=
  RHHeight.rhHeight50_of_pieces hΓ hH hE RHHeight.low_height h10

#check @RHHeight.low_height
#print axioms RHHeight.norm_tail_one_le
#print axioms RHHeight.norm_zeta_sub_main_one_le
#print axioms RHHeight.riemannZeta_ne_zero_of_im_le_three
#print axioms RHHeight.low_height
