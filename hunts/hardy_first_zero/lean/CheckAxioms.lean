module

public import HardyFirstZero.FirstZero

/-! Prints the statement and axioms of every theorem `RESULTS.md` calls kernel-checked. -/

-- Pin the unconditional statement as well as its axiom dependencies.
example : ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50),
    riemannZeta (1 / 2 + t * Complex.I) = 0 := @HardyFirstZero.first_zero_on_line

#check @HardyFirstZero.first_zero_on_line
#print axioms HardyFirstZero.first_zero_on_line
#print axioms HardyFirstZero.zeta_product_re_neg
#print axioms HardyFirstZero.exists_zero_of_sign_data
#print axioms HardyFirstZero.gammaR_re_pos
#print axioms HardyFirstZero.gammaR_re_pos_first
#print axioms HardyFirstZero.first_zero_on_line_of_zeta_product
#print axioms HardyFirstZero.corrected_trapezoid
#print axioms HardyFirstZero.zeta_em4_error
#print axioms HardyFirstZero.em30_bound
