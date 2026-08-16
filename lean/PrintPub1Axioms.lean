import ZetaLean.Pub1

/-! Axiom audit for the Pub 1 source-admissible strong-closure development.
Run with `lake env lean PrintPub1Axioms.lean`. -/

open ZetaLean.Pub1

-- the principal theorem, both orientations
#print axioms ZetaLean.Pub1.pub1_strong_closure
#print axioms ZetaLean.Pub1.pub1_strong_closure_sSup
#print axioms ZetaLean.Pub1.pub1_strong_closure_reciprocal
#print axioms ZetaLean.Pub1.orientation_not_symmetric
#print axioms ZetaLean.Pub1.pub1_strong_closure_of_member
#print axioms ZetaLean.Pub1.pub1_strong_closure_of_sourceWindow
#print axioms ZetaLean.Pub1.pub1_strong_closure_reciprocal_of_member
#print axioms ZetaLean.Pub1.strongClosureData_of_member
#print axioms ZetaLean.Pub1.sourceWindow_taper

-- the exact rational comparisons
#print axioms ZetaLean.Pub1.concavity_margin
#print axioms ZetaLean.Pub1.concavity_margin_lesioned
#print axioms ZetaLean.Pub1.uSecondDerivBound_lt

-- the analytic chain
#print axioms ZetaLean.Pub1.secondDeriv_lt_of_certificate
#print axioms ZetaLean.Pub1.radial_antitone
#print axioms ZetaLean.Pub1.sq_L2_dist_le
#print axioms ZetaLean.Pub1.tendsto_L2_zero
#print axioms ZetaLean.Pub1.energyA_coercive
#print axioms ZetaLean.Pub1.exists_profile
#print axioms ZetaLean.Pub1.massI_sq_le_of_profile
#print axioms ZetaLean.Pub1.energyA_eq_massI_of_profile
#print axioms ZetaLean.Pub1.energyA_pos_of_admissible
#print axioms ZetaLean.Pub1.cStar_pos_of_lower
#print axioms ZetaLean.Pub1.F1_row_bound
#print axioms ZetaLean.Pub1.taper_radial
#print axioms ZetaLean.Pub1.taper_support
-- obligation A: the F1'' = 2 delta_0 + q step
#print axioms ZetaLean.Pub1.pub1_kernel_second_deriv
#print axioms ZetaLean.Pub1.splitKernel_second_deriv
#print axioms ZetaLean.Pub1.F1_eq_fKer
#print axioms ZetaLean.Pub1.fKer_deriv_zero
-- obligation B: the exact residual certificate
#print axioms ZetaLean.Pub1.r0_identity
#print axioms ZetaLean.Pub1.r0Sum_lt_decimal
#print axioms ZetaLean.Pub1.r0Sum2_lt_decimal
#print axioms ZetaLean.Pub1.deriv_deriv_r0Sum
#print axioms AristotleR.resolvent_linf_bound
#print axioms AristotleR.resolvent_l2_bound
-- obligation C
#print axioms ZetaLean.Pub1.profile_pos
-- obligation D (first half)
#print axioms AristotleT.taper_second_deriv_L1_bound
#print axioms AristotleU.taper_sq_second_deriv_L1_bound
-- path 1: interior C2 regularity of w
#print axioms ZetaLean.Pub1.w_contDiffOn
#print axioms ZetaLean.Pub1.w_second_deriv_bound
#print axioms ZetaLean.Pub1.w_deriv_bound
#print axioms ZetaLean.Pub1.deriv_w_zero
-- path 2: certificate ingredients
#print axioms ZetaLean.Pub1.integral_r0_sq
#print axioms ZetaLean.Pub1.r0_l2_le
#print axioms ZetaLean.Pub1.q_abs_le
#print axioms ZetaLean.Pub1.zpp_arith
#print axioms ZetaLean.Pub1.concavity_closes
#print axioms ZetaLean.Pub1.truncKernel_second_deriv
-- obligation D
#print axioms ZetaLean.Pub1.taper_contDiff_of_profile
#print axioms ZetaLean.Pub1.taper_secondDeriv_L1_of_profile
#print axioms ZetaLean.Pub1.eta_contDiff
#print axioms ZetaLean.Pub1.taper_contDiff
#print axioms ZetaLean.Pub1.profile_bounds
#print axioms ZetaLean.Pub1.profile_even
#print axioms ZetaLean.Pub1.quot_tendsto_cStar
#print axioms AristotleD.integral_ramp_deriv_sq
#print axioms AristotleD.integral_abs_ramp_second_deriv
