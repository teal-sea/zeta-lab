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
#print axioms ZetaLean.Pub1.eta_contDiff
#print axioms ZetaLean.Pub1.taper_contDiff
#print axioms ZetaLean.Pub1.profile_bounds
#print axioms ZetaLean.Pub1.profile_even
#print axioms ZetaLean.Pub1.quot_tendsto_cStar
#print axioms AristotleD.integral_ramp_deriv_sq
#print axioms AristotleD.integral_abs_ramp_second_deriv
