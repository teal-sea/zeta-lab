import Zeta23Ext.EForm3.O9Comp
import Zeta23Ext.EForm3.ShcTaylor

/-!
# `shcSmall` is sound

`ShcTaylor.shc_taylor` bounds the truncation error of the divided series
uniformly on `|t| ≤ 1`, including at `t = 0`. `shcSmall` is the interval
evaluation of that same truncation through `hornerI sinhL`. This file joins
them, which is what turns the removable branch from an expression into an
enclosure.

Two facts do the work:

* `hornerR sinhL (t*t)` is exactly `shcPartial 11 t` — the same eleven terms,
  written in Horner form with `x = t²` rather than as a sum over `k`;
* `2 / 23!` is below the package's widening budget `RB = 1/10^21`, so the one
  ulp of `EIv.widen` already covers the truncation.
-/

namespace Retention

open BandDual

/-- The Horner form over `sinhL` is the divided series' partial sum. -/
theorem hornerR_sinhL_eq (t : ℝ) :
    hornerR sinhL (t * t) = ShcTaylor.shcPartial 11 t := by
  simp [hornerR, sinhL, ShcTaylor.shcPartial, Finset.sum_range_succ,
    Nat.factorial]
  ring

/-- The truncation of the divided series is inside one ulp. -/
theorem shc_trunc_le (t : ℝ) (ht : |t| ≤ 1) :
    |(if t = 0 then 1 else Real.sinh t / t) - hornerR sinhL (t * t)| ≤ RB := by
  rw [hornerR_sinhL_eq]
  refine le_trans (ShcTaylor.shc_taylor 11 (by norm_num) t ht) ?_
  rw [RB]
  norm_num [Nat.factorial]

/-- **`shcSmall` encloses the removable branch.**

The value at `0` is `1`, which is why the boxes reaching `y = 0` are ordinary:
this lemma has no `t ≠ 0` hypothesis to discharge. -/
theorem shcSmall_mem {a : EIv} {v : ℝ} (ha : EIv.mem a v) (hv : |v| ≤ 1) :
    EIv.mem (shcSmall a) (if v = 0 then 1 else Real.sinh v / v) := by
  have hx2 : EIv.mem (EIv.sqr a) (v * v) := EIv.sqr_mem ha
  have hh := hornerI_mem sinhL sinhL_pos hx2
  exact widen_of_abs hh (shc_trunc_le v hv)

end Retention

#print axioms Retention.hornerR_sinhL_eq
#print axioms Retention.shc_trunc_le
#print axioms Retention.shcSmall_mem
