import ZetaLean.HardyRamanujantheorem

/-! Axiom audit for the Mertens / Hardy-Ramanujan constant chain tightened by
hunt r_4218d4.  Run from `lean/` with

    lake env lean ../hunts/r_4218d4/PrintMertensAxioms.lean

Every line must print exactly `[propext, Classical.choice, Quot.sound]`, and
none may report a `sorry`. -/

-- the three theorems whose constants moved
#print axioms ZetaLean.Mertens.mertens_first_theorem
#print axioms ZetaLean.Mertens.mertens_second_theorem
#print axioms ZetaLean.HardyRamanujan.sum_sq_dev_le

-- the steps the tightening went through
#print axioms ZetaLean.Mertens.log_le_div_exp_one
#print axioms ZetaLean.Mertens.psi_le_const_mul_self'
#print axioms ZetaLean.Mertens.sum_log_div_sq_le
#print axioms ZetaLean.Mertens.log_sub_one_le_sum_vonMangoldt_div
#print axioms ZetaLean.Mertens.abs_sum_vonMangoldt_div_sub_log_le
#print axioms ZetaLean.Mertens.mertens_second_theorem_of_two_le

-- and the downstream statements, which must be unchanged in shape
#print axioms ZetaLean.HardyRamanujan.turan_variance
#print axioms ZetaLean.HardyRamanujan.hardy_ramanujan
