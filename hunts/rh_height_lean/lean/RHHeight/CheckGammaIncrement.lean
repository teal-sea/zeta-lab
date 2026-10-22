module

public import RHHeight.GammaIncrement

/-! Pins the piece `gamma_increment` of hunt #137 by type and prints the axioms of every
theorem in `RHHeight/GammaIncrement.lean`. The piece is one of the four hypotheses of
`rhHeight50_of_four`; it is not the target `RHHeight50`. -/

-- The skeleton's `Prop`, unfolded: `zeta23`'s `mu` integrated over `[3, 52]`.
example : RHHeight.GammaIncrement =
    ((92 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..52, Zeta23.mu t ∧
      ∫ t in (3 : ℝ)..52, Zeta23.mu t ≤ 109 / 10) :=
  rfl

-- `mu` is `zeta23`'s density `(1/2π) Re ψ(1/4 + iτ/2) - log π/(2π)`, `ψ = Γ'/Γ`.
example (τ : ℝ) : Zeta23.mu τ =
    (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
      - Real.log Real.pi / (2 * Real.pi) :=
  rfl

-- The theorem proves that `Prop` as stated.
example : RHHeight.GammaIncrement := RHHeight.gamma_increment

-- With the piece proved, the integer step of the skeleton needs the other two pieces only.
example (hH : RHHeight.HorizontalLegs) (hE : RHHeight.ExactArgument) :
    Zeta23.Ncount 3 52 = 10 :=
  RHHeight.count_eq_ten_of RHHeight.gamma_increment hH hE

#check @RHHeight.gamma_increment
#check @RHHeight.GammaSide.abs_integral_mu_sub_le
#print axioms RHHeight.GammaSide.abs_mu_sub_muMain_le
#print axioms RHHeight.GammaSide.hasDerivAt_muPrim
#print axioms RHHeight.GammaSide.continuous_muMain
#print axioms RHHeight.GammaSide.hasDerivAt_six_div
#print axioms RHHeight.GammaSide.abs_integral_mu_sub_le
#print axioms RHHeight.GammaSide.log_one_sub_bounds
#print axioms RHHeight.GammaSide.log_10817_div_16_mem
#print axioms RHHeight.GammaSide.log_37_div_16_mem
#print axioms RHHeight.GammaSide.pi_gt_6283_div_2000
#print axioms RHHeight.GammaSide.pi_lt_3927_div_1250
#print axioms RHHeight.GammaSide.log_pi_mem
#print axioms RHHeight.GammaSide.two_pi_mul_muPrim_sub
#print axioms RHHeight.gamma_increment
#print axioms RHHeight.gamma_increment_holds
