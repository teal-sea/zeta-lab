/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.HigherXi

/-!
# Power margins absorb logarithmic losses

The logarithmic-frequency mean-value estimate carries a finite power of
`log H`.  This file isolates the asymptotic fact used by the `URMS2-051`
parameter witness: every strictly negative real power of `H` absorbs every
fixed natural power of `log H`.
-/

namespace ZetaLean.HigherXi

open Filter Topology

/-- A negative real power absorbs every fixed natural logarithmic power. -/
theorem tendsto_rpow_neg_mul_log_pow_atTop (eta : ℝ) (k : ℕ) (heta : 0 < eta) :
    Tendsto (fun H : ℝ => H ^ (-eta) * Real.log H ^ k) atTop (𝓝 0) := by
  have h :=
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) heta).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  rw [Real.rpow_natCast]
  rw [Real.rpow_neg hH.le]
  ring

/-- Equivalent exponent-difference form, convenient for bridge parameters. -/
theorem tendsto_rpow_sub_mul_log_pow_atTop
    (alpha delta : ℝ) (k : ℕ) (hmargin : alpha < delta) :
    Tendsto (fun H : ℝ => H ^ (alpha - delta) * Real.log H ^ k) atTop (𝓝 0) := by
  convert tendsto_rpow_neg_mul_log_pow_atTop (delta - alpha) k (sub_pos.mpr hmargin) using 1
  · ext H
    congr 2
    ring

/-- The exact `URMS2-051` mean-value margin is `6/25`. -/
theorem urms2_051_meanValue_exponent :
    ((alpha : ℝ) - (delta : ℝ)) = -(6 / 25 : ℝ) := by
  norm_num [alpha, delta]

/-- At `alpha=51/100` and `delta=3/4`, every fixed logarithmic loss is
absorbed by the exact power saving `H^(-6/25)`. -/
theorem tendsto_urms2_051_power_margin (k : ℕ) :
    Tendsto
      (fun H : ℝ => H ^ ((alpha : ℝ) - (delta : ℝ)) * Real.log H ^ k)
      atTop (𝓝 0) := by
  exact tendsto_rpow_sub_mul_log_pow_atTop (alpha : ℝ) (delta : ℝ) k (by
    norm_num [alpha, delta])

/-- The single harmonic loss from `LogMeanValue` is covered in particular. -/
theorem tendsto_urms2_051_harmonic_envelope :
    Tendsto
      (fun H : ℝ => H ^ ((alpha : ℝ) - (delta : ℝ)) * (1 + Real.log H))
      atTop (𝓝 0) := by
  have hzero := tendsto_rpow_neg_atTop_nhds_zero_of_pos (show 0 < (6 / 25 : ℝ) by norm_num)
  have hlog := tendsto_urms2_051_power_margin 1
  convert hzero.add hlog using 1
  · ext H
    rw [urms2_051_meanValue_exponent]
    simp only [pow_one]
    ring

/-- The actual cutoff `W = H^gamma` contributes the affine logarithmic
envelope `1 + gamma * log H`; its rational factor does not consume any of the
`6/25` exponent margin. -/
theorem tendsto_urms2_051_cutoff_harmonic_envelope :
    Tendsto
      (fun H : ℝ => H ^ ((alpha : ℝ) - (delta : ℝ)) *
        (1 + (gamma : ℝ) * Real.log H))
      atTop (𝓝 0) := by
  have hzero := tendsto_rpow_neg_atTop_nhds_zero_of_pos (show 0 < (6 / 25 : ℝ) by norm_num)
  have hlog := (tendsto_urms2_051_power_margin 1).const_mul (gamma : ℝ)
  convert hzero.add hlog using 1
  · ext H
    rw [urms2_051_meanValue_exponent]
    simp only [pow_one]
    ring

end ZetaLean.HigherXi
