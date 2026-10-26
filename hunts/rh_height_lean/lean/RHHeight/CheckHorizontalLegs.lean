module

public import RHHeight.HorizontalLegs

/-! Pins the statement of the piece `horizontal_legs` of hunt #137 and prints the axioms of its
declarations. `horizontal_legs` is one of the four pieces the skeleton consumes
(`RHHeight/Skeleton.lean`); it is not the target `RHHeight50`. -/

open Complex

-- `HorizontalLegs` unfolded: Mathlib's own `riemannZeta`, the two legs, the two arguments.
example : RHHeight.HorizontalLegs =
    ((∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re) ∧
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
    -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧
      (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0) := rfl

-- The plan's target signature for the piece, verbatim, is met by `horizontal_legs`.
example : (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 3 * I)).re) ∧
    (∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, 0 < (riemannZeta (σ + 52 * I)).re) ∧
    -(1 / 5 : ℝ) ≤ (riemannZeta (1 / 2 + 3 * I)).arg ∧ (riemannZeta (1 / 2 + 3 * I)).arg ≤ 0 ∧
    -(1 / 3 : ℝ) ≤ (riemannZeta (1 / 2 + 52 * I)).arg ∧
      (riemannZeta (1 / 2 + 52 * I)).arg ≤ 0 :=
  RHHeight.horizontal_legs

-- It fills the `HorizontalLegs` slot of the skeleton's reduction; the other three pieces and
-- hunt #133's input stay hypotheses here.
example (hΓ : RHHeight.GammaIncrement) (hE : RHHeight.ExactArgument) (hL : RHHeight.LowHeight)
    (h10 : RHHeight.TenZerosOnLine) : RHHeight.RHHeight50 :=
  RHHeight.rhHeight50_of_pieces hΓ RHHeight.horizontal_legs hE hL h10

#check @RHHeight.horizontal_legs
#check @RHHeight.Legs.re_pos_of_segment
#print axioms RHHeight.horizontal_legs
#print axioms RHHeight.horizontalLegs
#print axioms RHHeight.re_zeta_pos_bottom
#print axioms RHHeight.re_zeta_pos_top
#print axioms RHHeight.arg_zeta_bottom
#print axioms RHHeight.arg_zeta_top
#print axioms RHHeight.Legs.cBoxG_contains
#print axioms RHHeight.Legs.mainBoxG_contains
#print axioms RHHeight.Legs.norm_le_normUp
#print axioms RHHeight.Legs.log_le_logTab
#print axioms RHHeight.Legs.norm_cpow_sub_le
#print axioms RHHeight.Legs.norm_cN_le
#print axioms RHHeight.Legs.norm_cN_sub_le
#print axioms RHHeight.Legs.norm_mainTerm_sub_le
#print axioms RHHeight.Legs.norm_zeta_sub_mainTerm_le
#print axioms RHHeight.Legs.re_pos_of_segment
#print axioms RHHeight.Legs.zeta_mem_pointBox
#print axioms RHHeight.Legs.arg_mem_of_box
#print axioms RHHeight.Legs.H3S1.seg
#print axioms RHHeight.Legs.H3S2.seg
#print axioms RHHeight.Legs.H3S3.seg
#print axioms RHHeight.Legs.H52S1.seg
#print axioms RHHeight.Legs.H52S2.seg
#print axioms RHHeight.Legs.H52S3.seg
#print axioms RHHeight.Legs.H52S4.seg
#print axioms RHHeight.Legs.H52S5.seg
#print axioms RHHeight.Legs.H52S6.seg
#print axioms RHHeight.Legs.Arg3.arg_bounds
#print axioms RHHeight.Legs.Arg52.arg_bounds
