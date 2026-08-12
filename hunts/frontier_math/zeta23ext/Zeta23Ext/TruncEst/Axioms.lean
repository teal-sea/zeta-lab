import Zeta23Ext.TruncEst.Kernel
import Zeta23Ext.TruncEst.Decay
import Zeta23Ext.TruncEst.Sums
import Zeta23Ext.TruncEst.Poisson
import Zeta23Ext.TruncEst.Autocorrelation

/-!
# Axiom audit

`PROBLEM.md` asks to end with `#print axioms` for every theorem.  Every
declaration of the development is listed below; each one depends only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace TruncEst

#print axioms TruncEst.AC_even
#print axioms TruncEst.A_ne_zero
#print axioms TruncEst.A_sq_gt
#print axioms TruncEst.A_sq_pos
#print axioms TruncEst.Fs_eq_zero
#print axioms TruncEst.T_eq_full
#print axioms TruncEst.T_neg
#print axioms TruncEst.abs_T_le
#print axioms TruncEst.abs_T_shift_le
#print axioms TruncEst.abs_bM_sub_bInf_le
#print axioms TruncEst.abs_c2core_le
#print axioms TruncEst.abs_d1c2_le
#print axioms TruncEst.abs_d2c2_le
#print axioms TruncEst.abs_hf1_one_le
#print axioms TruncEst.abs_hf1_zero_le
#print axioms TruncEst.abs_hf2_le
#print axioms TruncEst.abs_integral_half_le
#print axioms TruncEst.abs_one_sub_le
#print axioms TruncEst.abs_sinh_le_of_abs_le_half
#print axioms TruncEst.abs_sub_le'
#print axioms TruncEst.autocorr_integrand_eq_zero
#print axioms TruncEst.autocorr_of_mem
#print axioms TruncEst.autocorr_of_one_lt
#print axioms TruncEst.bInf_eq_poisson
#print axioms TruncEst.bM_eq_range
#print axioms TruncEst.c2_eq_autocorrelation
#print axioms TruncEst.c2_eq_zero_of_one_le
#print axioms TruncEst.c2_eq_zero_of_one_lt
#print axioms TruncEst.c2_neg
#print axioms TruncEst.c2_of_nonneg
#print axioms TruncEst.cast_shift
#print axioms TruncEst.continuous_Fs
#print axioms TruncEst.continuous_c2
#print axioms TruncEst.continuous_c2core
#print axioms TruncEst.continuous_hf
#print axioms TruncEst.continuous_hf1
#print axioms TruncEst.continuous_hf2
#print axioms TruncEst.continuous_integrandFull
#print axioms TruncEst.continuous_phi
#print axioms TruncEst.cosh_le_of_abs_le_half
#print axioms TruncEst.cosh_nonneg'
#print axioms TruncEst.difference_identity
#print axioms TruncEst.eventually_cocompact_abs_gt
#print axioms TruncEst.exp_ge_half
#print axioms TruncEst.exp_half_le_two
#print axioms TruncEst.exp_le_two
#print axioms TruncEst.four_div_A_sq_le
#print axioms TruncEst.four_div_A_sq_pos
#print axioms TruncEst.fourier_Fs
#print axioms TruncEst.g_eq_cos
#print axioms TruncEst.g_eq_zero
#print axioms TruncEst.g_even
#print axioms TruncEst.hasCompactSupport_phi
#print axioms TruncEst.hasDerivAt_Gaux
#print axioms TruncEst.hasDerivAt_antideriv
#print axioms TruncEst.hasDerivAt_c2core
#print axioms TruncEst.hasDerivAt_cosh_sq
#print axioms TruncEst.hasDerivAt_d1c2
#print axioms TruncEst.hasDerivAt_hf
#print axioms TruncEst.hasDerivAt_hf1
#print axioms TruncEst.hasDerivAt_sinh_comp
#print axioms TruncEst.hd_lin
#print axioms TruncEst.hd_lin2
#print axioms TruncEst.head_bound
#print axioms TruncEst.hf1_one
#print axioms TruncEst.hf1_zero
#print axioms TruncEst.integrable_phi_mul
#print axioms TruncEst.integral_exp_phi
#print axioms TruncEst.integral_g
#print axioms TruncEst.integral_sin_phi
#print axioms TruncEst.integral_symm_eq
#print axioms TruncEst.isBigO_Fs
#print axioms TruncEst.isBigO_fourier_Fs
#print axioms TruncEst.phi_eq_zero
#print axioms TruncEst.phi_neg
#print axioms TruncEst.poisson_T
#print axioms TruncEst.poisson_rhs_finite
#print axioms TruncEst.rpow_neg_two_eq
#print axioms TruncEst.sqrt2_lb
#print axioms TruncEst.sqrt2_mul
#print axioms TruncEst.sqrt2_pos
#print axioms TruncEst.sqrt2_sq
#print axioms TruncEst.sqrt2_ub
#print axioms TruncEst.summable_T
#print axioms TruncEst.summable_abs_T
#print axioms TruncEst.summable_abs_T_tail
#print axioms TruncEst.summable_inv_sq_shift
#print axioms TruncEst.summable_inv_sq_tail
#print axioms TruncEst.summable_majorant
#print axioms TruncEst.tail_bound
#print axioms TruncEst.tsum_inv_sq_tail_le

end TruncEst
