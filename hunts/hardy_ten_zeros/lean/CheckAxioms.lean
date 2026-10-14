module

public import HardyTenZeros.TenZeros

/-! Prints the statements and axioms of every theorem `RESULTS.md` calls kernel-checked. -/

open Complex

-- Pin the unconditional statements by type, as well as their axiom dependencies.
example : ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
    ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0 :=
  @HardyTenZeros.ten_zeros_on_line_below_fifty
example : ∃ t ∈ Set.Ioo (1413 / 100 : ℝ) (707 / 50), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyFirstZero.first_zero_on_line
example : ∃ t ∈ Set.Ioo (2102 / 100 : ℝ) (2103 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_2102
example : ∃ t ∈ Set.Ioo (2501 / 100 : ℝ) (2502 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_2501
example : ∃ t ∈ Set.Ioo (3042 / 100 : ℝ) (3043 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_3042
example : ∃ t ∈ Set.Ioo (3293 / 100 : ℝ) (3294 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_3293
example : ∃ t ∈ Set.Ioo (3758 / 100 : ℝ) (3759 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_3758
example : ∃ t ∈ Set.Ioo (4091 / 100 : ℝ) (4092 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_4091
example : ∃ t ∈ Set.Ioo (4332 / 100 : ℝ) (4333 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_4332
example : ∃ t ∈ Set.Ioo (4800 / 100 : ℝ) (4801 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_4800
example : ∃ t ∈ Set.Ioo (4977 / 100 : ℝ) (4978 / 100), riemannZeta (1 / 2 + t * I) = 0 :=
  HardyTenZeros.zero_in_4977

#check @HardyTenZeros.ten_zeros_on_line_below_fifty
#print axioms HardyTenZeros.ten_zeros_on_line_below_fifty
#print axioms HardyFirstZero.first_zero_on_line
#print axioms HardyTenZeros.zero_in_2102
#print axioms HardyTenZeros.zero_in_2501
#print axioms HardyTenZeros.zero_in_3042
#print axioms HardyTenZeros.zero_in_3293
#print axioms HardyTenZeros.zero_in_3758
#print axioms HardyTenZeros.zero_in_4091
#print axioms HardyTenZeros.zero_in_4332
#print axioms HardyTenZeros.zero_in_4800
#print axioms HardyTenZeros.zero_in_4977
#print axioms HardyTenZeros.le_phi_tail
#print axioms HardyTenZeros.gammaR_re_pos_tail
#print axioms HardyTenZeros.gammaR_re_pos_short
#print axioms HardyTenZeros.window_132_fails_at_4977
#print axioms HardyTenZeros.emN_bound
#print axioms HardyTenZeros.cBox_contains
#print axioms HardyTenZeros.zeta_mem_mainBox
#print axioms HardyTenZeros.contains_cpow_mul_coarsen
#print axioms HardyTenZeros.zero_of_tables
