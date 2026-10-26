module

public import RHHeight.ExactArgument

/-! Pins the piece `exact_argument` of hunt #137 by type and prints the axioms of every
declaration in `RHHeight/ExactArgument.lean`. The piece is one of the four hypotheses of
`rhHeight50_of_four`; it is not the target `RHHeight50`. -/

open Complex

-- The skeleton's `Prop`, unfolded: Mathlib's `riemannZeta`, `zeta23`'s `Ncount` and `mu`.
example : RHHeight.ExactArgument =
    ∀ T₁ T₂ : ℝ, 1 ≤ T₁ → T₁ < T₂ →
      (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₁ * I)).re) →
      (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + T₂ * I)).re) →
      (Zeta23.Ncount T₁ T₂ : ℝ) = (∫ t in T₁..T₂, Zeta23.mu t) +
        ((riemannZeta (1 / 2 + T₂ * I)).arg - (riemannZeta (1 / 2 + T₁ * I)).arg) / Real.pi :=
  rfl

-- The theorem proves that `Prop` as stated.
example : RHHeight.ExactArgument := RHHeight.exact_argument

-- With the piece proved, the integer step of the skeleton needs the two enclosures only.
example (hΓ : RHHeight.GammaIncrement) (hH : RHHeight.HorizontalLegs) :
    Zeta23.Ncount 3 52 = 10 :=
  RHHeight.count_eq_ten_of hΓ hH RHHeight.exact_argument

#check @RHHeight.exact_argument
#print axioms RHHeight.goodHeight_of_re_pos
#print axioms RHHeight.integral_logDeriv_horizontal
#print axioms RHHeight.integral_logDeriv_vertical
#print axioms RHHeight.halfContour_logDeriv_riemannZeta
#print axioms RHHeight.im_halfContour_logDeriv_riemannZeta
#print axioms RHHeight.exact_argument
#print axioms RHHeight.exact_argument_holds
