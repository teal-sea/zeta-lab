import ZetaLean.Pub1

/-! Axiom audit for the Pub 1 source-admissible strong-closure development.
Run with `lake env lean PrintPub1Axioms.lean`. -/

open ZetaLean.Pub1

-- THE TWO HEADLINE THEOREMS, unconditional
#print axioms ZetaLean.Pub1.pub1_strong_closure
#print axioms ZetaLean.Pub1.pub1_strong_closure_reciprocal
#print axioms ZetaLean.Pub1.pub1_strong_closure_exists
#print axioms ZetaLean.Pub1.strongClosureData_final
#print axioms ZetaLean.Pub1.member_final
#print axioms ZetaLean.Pub1.sourceWindow_taper_final
#print axioms ZetaLean.Pub1.orientation_not_symmetric

-- the certificate
#print axioms ZetaLean.Pub1.zpp_bound
#print axioms ZetaLean.Pub1.zpp_identity
#print axioms ZetaLean.Pub1.r0_identity
#print axioms ZetaLean.Pub1.integral_r0_sq
#print axioms ZetaLean.Pub1.q_abs_le
#print axioms ZetaLean.Pub1.q_sub_qM_abs_le
#print axioms ZetaLean.Pub1.zFun_linf
#print axioms ZetaLean.Pub1.zFun_l2
#print axioms ZetaLean.Pub1.zpp_arith_final
#print axioms ZetaLean.Pub1.concavity_margin
#print axioms ZetaLean.Pub1.concavity_margin_lesioned

-- regularity and concavity
#print axioms ZetaLean.Pub1.pub1_kernel_second_deriv
#print axioms ZetaLean.Pub1.w_contDiffOn
#print axioms ZetaLean.Pub1.w_second_deriv_lt
#print axioms ZetaLean.Pub1.w_radial
#print axioms ZetaLean.Pub1.profile_pos
#print axioms ZetaLean.Pub1.profile_bounds
#print axioms ZetaLean.Pub1.exists_profile

-- admissibility
#print axioms ZetaLean.Pub1.taper_contDiff_of_profile
#print axioms ZetaLean.Pub1.taper_secondDeriv_L1_of_profile
#print axioms ZetaLean.Pub1.taper_sq_secondDeriv_L1_of_profile
#print axioms ZetaLean.Pub1.sq_L2_dist_le
#print axioms ZetaLean.Pub1.quot_tendsto_cStar
