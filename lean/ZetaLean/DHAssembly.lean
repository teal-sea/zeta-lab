/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.Rigor
import ZetaLean.IntervalCExp
import ZetaLean.DHTailBound

/-!
# Assembly: a certified enclosure of `DH` at a strip point

`ZetaLean/DHTailBound.lean` bounds `DH` minus a partial sum;
`ZetaLean/IntervalCExp.lean` encloses each partial-sum term in a computed
rational box.  This file gives the glue and the missing coefficient piece:

* `DH_mem_of_partial_enclosure` — if a rectangle `B` contains the `5K`-term
  partial sum at `s` and `r` dominates the tail bound, then `B.inflate r`
  contains `DH s`.  This is the K-generic assembly theorem: instantiating
  rung 3's two disk inequalities is, from here, a computation.
* `Interval.inv'` / `Interval.contains_sqrt_of_sq` — reciprocal and
  square-root enclosures for the rational interval layer (the DH coefficient
  `κ` is a quotient of square roots, so coefficient boxes need both).
* `kappaI` / `contains_kappaI` — a concrete rational enclosure of `κ`,
  `0.28407 < κ < 0.28408`, kernel-checked from `Real.sqrt` squaring bounds.
  With it, every DH partial-sum term `dh_coeff n · n^{-s}` is a product of
  boxes the layer already encloses.
-/

open Complex Finset

namespace ZetaLean

namespace Interval

/-- Reciprocal of an interval strictly right of zero. -/
def inv' (x : Interval) (hx : 0 < x.lo) : Interval :=
  { lo := 1 / x.hi,
    hi := 1 / x.lo,
    le := one_div_le_one_div_of_le hx x.le }

theorem contains_inv' {x : Interval} (hx : 0 < x.lo) {t : ℝ}
    (ht : x.contains t) : (x.inv' hx).contains t⁻¹ := by
  have hxlo : (0 : ℝ) < (x.lo : ℝ) := by exact_mod_cast hx
  have ht0 : 0 < t := lt_of_lt_of_le hxlo ht.1
  have hxhi : (0 : ℝ) < (x.hi : ℝ) := lt_of_lt_of_le ht0 ht.2
  constructor
  · show ((1 / x.hi : ℚ) : ℝ) ≤ t⁻¹
    rw [show ((1 / x.hi : ℚ) : ℝ) = ((x.hi : ℝ))⁻¹ by push_cast; ring,
      inv_le_inv₀ hxhi ht0]
    exact ht.2
  · show t⁻¹ ≤ ((1 / x.lo : ℚ) : ℝ)
    rw [show ((1 / x.lo : ℚ) : ℝ) = ((x.lo : ℝ))⁻¹ by push_cast; ring,
      inv_le_inv₀ ht0 hxlo]
    exact ht.1

/-- A square-root enclosure from squaring bounds: if `lo² ≤ t ≤ hi²` with
`0 ≤ lo ≤ hi`, then `[lo, hi]` contains `√t`. -/
theorem contains_sqrt_of_sq {lo hi : ℚ} (h0 : 0 ≤ lo) (hle : lo ≤ hi)
    {t : ℝ} (h1 : ((lo : ℝ)) ^ 2 ≤ t) (h2 : t ≤ ((hi : ℝ)) ^ 2) :
    (Interval.mk lo hi hle).contains (Real.sqrt t) := by
  have h0' : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast h0
  have hhi' : (0 : ℝ) ≤ (hi : ℝ) := le_trans h0' (by exact_mod_cast hle)
  constructor
  · show ((lo : ℝ)) ≤ Real.sqrt t
    calc (lo : ℝ) = Real.sqrt (((lo : ℝ)) ^ 2) := by
          rw [Real.sqrt_sq h0']
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt h1
  · show Real.sqrt t ≤ ((hi : ℝ))
    calc Real.sqrt t ≤ Real.sqrt (((hi : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = (hi : ℝ) := Real.sqrt_sq hhi'

end Interval

namespace DH

/-! ### The assembly theorem -/

/-- **Assembly, K-generic.**  If the rectangle `B` contains the `5K`-term
partial sum of the DH series at `s = sre + i·sim` (as the enclosures of
`ZetaLean/IntervalCExp.lean` plus `ComplexInterval.contains_sumList`
produce), and the rational `r` dominates the certified tail bound of
`DH_tail_bound`, then `B.inflate r` contains `DH s`.  Rung 3's two disk
inequalities are, from here, instantiations of this theorem. -/
theorem DH_mem_of_partial_enclosure {sre sim : ℚ} (hsre : 0 < sre)
    {K : ℕ} (hK : 2 ≤ K) {B : ComplexInterval}
    (hB : B.contains (∑ n ∈ range (K * 5),
      (dh_coeff n : ℂ) * (n : ℂ) ^ (-(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ))))
    {r : ℚ}
    (hr : (3 + dh_kappa) * ‖(⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ)‖
        * (5 : ℝ) ^ (-(sre : ℝ) - 1)
        * ((((K : ℝ)) - 1) ^ (-(sre : ℝ)) / (sre : ℝ)) ≤ (r : ℝ)) :
    (B.inflate r).contains (DH (⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ)) := by
  have hs : 0 < (⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ).re := by
    show (0 : ℝ) < (sre : ℝ)
    exact_mod_cast hsre
  have htail := DH_tail_bound (s := (⟨(sre : ℝ), (sim : ℝ)⟩ : ℂ)) hs hK
  exact ComplexInterval.contains_inflate hB (htail.trans hr)

/-! ### The κ enclosure

`κ = (√(10 − 2√5) − 2)/(√5 − 1)`.  The enclosure is derived from rational
squaring bounds on the two roots, so it is as fine as the chosen rationals —
here eight digits, plenty for coefficient boxes whose width is dominated by
the series tail. -/

private lemma sqrt5_bounds :
    ((22360679 / 10000000 : ℚ) : ℝ) ≤ Real.sqrt 5
      ∧ Real.sqrt 5 ≤ ((22360680 / 10000000 : ℚ) : ℝ) := by
  have h := Interval.contains_sqrt_of_sq
    (lo := 22360679 / 10000000) (hi := 22360680 / 10000000)
    (by norm_num) (by norm_num) (t := 5) (by push_cast; norm_num)
    (by push_cast; norm_num)
  exact ⟨h.1, h.2⟩

private lemma R_bounds :
    ((23511409 / 10000000 : ℚ) : ℝ) ≤ Real.sqrt (10 - 2 * Real.sqrt 5)
      ∧ Real.sqrt (10 - 2 * Real.sqrt 5) ≤ ((23511412 / 10000000 : ℚ) : ℝ) := by
  obtain ⟨hf1, hf2⟩ := sqrt5_bounds
  have h := Interval.contains_sqrt_of_sq
    (lo := 23511409 / 10000000) (hi := 23511412 / 10000000)
    (by norm_num) (by norm_num) (t := 10 - 2 * Real.sqrt 5)
    (by push_cast at hf2 ⊢; nlinarith) (by push_cast at hf1 ⊢; nlinarith)
  exact ⟨h.1, h.2⟩

/-- The concrete rational enclosure of `κ ≈ 0.28407904`. -/
def kappaI : Interval :=
  { lo := 2840788 / 10000000,
    hi := 2840794 / 10000000,
    le := by norm_num }

theorem contains_kappaI : kappaI.contains dh_kappa := by
  obtain ⟨hf1, hf2⟩ := sqrt5_bounds
  obtain ⟨hr1, hr2⟩ := R_bounds
  unfold dh_kappa kappaI
  have hden : (0 : ℝ) < Real.sqrt 5 - 1 := by
    push_cast at hf1
    nlinarith
  constructor
  · show ((2840788 / 10000000 : ℚ) : ℝ)
      ≤ (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)
    rw [le_div_iff₀ hden]
    push_cast at hr1 hf2 ⊢
    nlinarith
  · show (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)
      ≤ ((2840794 / 10000000 : ℚ) : ℝ)
    rw [div_le_iff₀ hden]
    push_cast at hr2 hf1 ⊢
    nlinarith

end DH

end ZetaLean
