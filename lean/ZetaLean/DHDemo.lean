/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.IntervalCExp
import ZetaLean.DHAssembly

/-!
# The first certified enclosure of a Davenport-Heilbronn value

An end-to-end instantiation of the rung 3 assembly pipeline at the tame
point `s₀ = 3/2 + 3i`: coefficient boxes from `kappaI`, term boxes from
`dirichletTermBox`, ten containment steps for the partial sum, the certified
tail radius `2/5` from `DH_tail_bound`'s expression, and
`DH_mem_of_partial_enclosure` to conclude

* `DH_demo_enclosure` — `DH (3/2 + 3i)` lies in a computed rational
  rectangle, kernel-checked with no oracle input anywhere; and
* `DH_demo_ne_zero` — that rectangle excludes the origin, so
  `DH (3/2 + 3i) ≠ 0`: the first kernel-certified fact about a *value* of
  the Davenport-Heilbronn function.

The point is deliberately tame (`K = 2`, ten series terms, tail `2/5`): the
theorem is the template.  Scaling the same instantiation to the oracle point
`0.808517 + 85.699348i` needs no new mathematics — only the offline kernel
compute priced in `HANDOFF.md` (weeks, per the measured `norm_num` cost per
term), or a faster certified evaluation to be formalized first.
-/

open Complex Finset ZetaLean.ComplexInterval

namespace ZetaLean.DH

/-- The demo point `s₀ = 3/2 + 3i` as an exact box. -/
def demoS : ComplexInterval := ComplexInterval.exact (3 / 2) 3

/-- The demo point as a complex number. -/
noncomputable def demoPt : ℂ := ⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩

/-- Term box for `m^{-s₀}`: Taylor order 8, 64-bit coarsening, `kE = 4`. -/
def demoTerm (kL m : ℕ) : ComplexInterval :=
  dirichletTermBox 8 64 kL 4 m demoS

/-- The κ coefficient box, in `ℂ`. -/
def kappaC : ComplexInterval := { re := kappaI, im := ZetaLean.Interval.exact 0 }

private lemma contains_kappaC : kappaC.contains ((dh_kappa : ℝ) : ℂ) :=
  ⟨by rw [Complex.ofReal_re]; exact contains_kappaI,
   by rw [Complex.ofReal_im]; simpa [kappaC] using ZetaLean.Interval.contains_exact 0⟩

/-- The ten-term partial-sum box at `s₀`. -/
def demoB : ComplexInterval :=
  ((((((((ComplexInterval.exact 0 0).add
    ((ComplexInterval.exact 1 0).mul (demoTerm 0 1))).add
    (kappaC.mul (demoTerm 2 2))).add
    (kappaC.neg.mul (demoTerm 2 3))).add
    ((ComplexInterval.exact (-1) 0).mul (demoTerm 3 4))).add
    (ComplexInterval.exact 0 0)).add
    ((ComplexInterval.exact 1 0).mul (demoTerm 3 6))).add
    (kappaC.mul (demoTerm 3 7))).add
    (kappaC.neg.mul (demoTerm 4 8)) |>.add
    ((ComplexInterval.exact (-1) 0).mul (demoTerm 4 9))

private lemma demoS_contains : demoS.contains demoPt :=
  ComplexInterval.contains_exact (3 / 2) 3

/-- Containment of one demo term box, side conditions by `norm_num`. -/
private lemma term_contains {kL m : ℕ} (hm : 0 < m)
    (h0 : 0 < (m : ℚ) / 2 ^ kL) (h2 : (m : ℚ) / 2 ^ kL < 2)
    (hb : normBound (demoS.neg.mul
      { re := ZetaLean.Interval.logQ 8 kL (m : ℚ), im := ZetaLean.Interval.exact 0 })
      ≤ 2 ^ 4) :
    (demoTerm kL m).contains ((m : ℂ) ^ (-demoPt)) :=
  contains_dirichletTermBox (by norm_num) hm demoS_contains h0 h2 hb

/-- The coefficient values at `n = 0 … 9`, by reduction of `dh_coeff`. -/
private lemma coeff0 : dh_coeff 0 = 0 := rfl
private lemma coeff1 : dh_coeff 1 = 1 := rfl
private lemma coeff2 : dh_coeff 2 = dh_kappa := rfl
private lemma coeff3 : dh_coeff 3 = -dh_kappa := rfl
private lemma coeff4 : dh_coeff 4 = -1 := rfl
private lemma coeff5 : dh_coeff 5 = 0 := rfl
private lemma coeff6 : dh_coeff 6 = 1 := rfl
private lemma coeff7 : dh_coeff 7 = dh_kappa := rfl
private lemma coeff8 : dh_coeff 8 = -dh_kappa := rfl
private lemma coeff9 : dh_coeff 9 = -1 := rfl

private lemma contains_one : (ComplexInterval.exact 1 0).contains ((1 : ℝ) : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [ComplexInterval.exact, ZetaLean.Interval.exact, ZetaLean.Interval.contains]

private lemma contains_negOne :
    (ComplexInterval.exact (-1) 0).contains ((-1 : ℝ) : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [ComplexInterval.exact, ZetaLean.Interval.exact, ZetaLean.Interval.contains]

private lemma contains_negKappa : kappaC.neg.contains ((-dh_kappa : ℝ) : ℂ) := by
  have h := ComplexInterval.contains_neg contains_kappaC
  rwa [show -((dh_kappa : ℝ) : ℂ) = ((-dh_kappa : ℝ) : ℂ) by push_cast; ring] at h

/-- The partial-sum containment: `demoB` contains the ten-term sum. -/
private lemma demoB_contains :
    demoB.contains (∑ n ∈ range (2 * 5),
      (dh_coeff n : ℂ) * (n : ℂ) ^ (-demoPt)) := by
  have hz : ∀ (c : ℝ) (v : ℂ), c = 0 → (ComplexInterval.exact 0 0).contains ((c : ℝ) * v) := by
    intro c v hc
    rw [hc]
    simpa using contains_zero
  have h0 := hz (dh_coeff 0) (((0 : ℕ) : ℂ) ^ (-demoPt)) coeff0
  have h5 := hz (dh_coeff 5) (((5 : ℕ) : ℂ) ^ (-demoPt)) coeff5
  have h1 := ComplexInterval.contains_mul (coeff1 ▸ contains_one)
    (term_contains (kL := 0) (m := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h2 := ComplexInterval.contains_mul (coeff2 ▸ contains_kappaC)
    (term_contains (kL := 2) (m := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h3 := ComplexInterval.contains_mul (coeff3 ▸ contains_negKappa)
    (term_contains (kL := 2) (m := 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h4 := ComplexInterval.contains_mul (coeff4 ▸ contains_negOne)
    (term_contains (kL := 3) (m := 4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h6 := ComplexInterval.contains_mul (coeff6 ▸ contains_one)
    (term_contains (kL := 3) (m := 6) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h7 := ComplexInterval.contains_mul (coeff7 ▸ contains_kappaC)
    (term_contains (kL := 3) (m := 7) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h8 := ComplexInterval.contains_mul (coeff8 ▸ contains_negKappa)
    (term_contains (kL := 4) (m := 8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  have h9 := ComplexInterval.contains_mul (coeff9 ▸ contains_negOne)
    (term_contains (kL := 4) (m := 9) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
        ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
        ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
        ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
        ZetaLean.Interval.sub, Finset.sum_range_succ]))
  change demoB.contains (∑ n ∈ range 10, (dh_coeff n : ℂ) * (n : ℂ) ^ (-demoPt))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [demoB]
  exact ComplexInterval.contains_add (ComplexInterval.contains_add
    (ComplexInterval.contains_add (ComplexInterval.contains_add
      (ComplexInterval.contains_add (ComplexInterval.contains_add
        (ComplexInterval.contains_add (ComplexInterval.contains_add
          (ComplexInterval.contains_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9

/-- **The first certified enclosure of a Davenport-Heilbronn value.**
`DH (3/2 + 3i)` lies in the computed box inflated by the certified tail
radius `2/5`.  Kernel-checked end to end; no oracle input anywhere. -/
theorem DH_demo_enclosure : (demoB.inflate (2 / 5)).contains (DH demoPt) := by
  refine DH_mem_of_partial_enclosure (by norm_num) (K := 2) (by norm_num)
    demoB_contains ?_
  -- the tail bound at s₀: (3+κ)·‖s₀‖·5^{-5/2}·(1^{-3/2}/(3/2)) ≤ 2/5
  have hκ : dh_kappa ≤ ((2840794 / 10000000 : ℚ) : ℝ) := contains_kappaI.2
  have hκ0 : (0 : ℝ) ≤ dh_kappa := by exact_mod_cast dh_kappa_nonneg
  have hs : ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ)‖ ≤ 4.5 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    show |((3 / 2 : ℚ) : ℝ)| + |((3 : ℚ) : ℝ)| ≤ _
    rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
    norm_num
  have hone : (((2 : ℕ) : ℝ) - 1) ^ (-((3 / 2 : ℚ) : ℝ)) = 1 := by
    norm_num [Real.one_rpow]
  have h5 : (5 : ℝ) ^ (-((3 / 2 : ℚ) : ℝ) - 1) ≤ 1 / 25 := by
    have he : -((3 / 2 : ℚ) : ℝ) - 1 ≤ ((-2 : ℤ) : ℝ) := by push_cast; norm_num
    calc (5 : ℝ) ^ (-((3 / 2 : ℚ) : ℝ) - 1)
        ≤ (5 : ℝ) ^ ((-2 : ℤ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) he
      _ = 1 / 25 := by
          rw [Real.rpow_intCast]
          norm_num
  have hnorm0 : (0 : ℝ) ≤ ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ)‖ := norm_nonneg _
  have h50 : (0 : ℝ) ≤ (5 : ℝ) ^ (-((3 / 2 : ℚ) : ℝ) - 1) := Real.rpow_nonneg (by norm_num) _
  rw [hone]
  push_cast at hκ ⊢
  nlinarith [mul_le_mul (mul_le_mul (by linarith : 3 + dh_kappa ≤ 3.2840794) hs
      hnorm0 (by linarith)) h5 h50
      (by norm_num : (0 : ℝ) ≤ 3.2840794 * 4.5)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DH (3/2 + 3i) ≠ 0`, kernel-checked** — the enclosure stays away from
the origin, so the first certified fact about a DH *value* follows. -/
theorem DH_demo_ne_zero : DH demoPt ≠ 0 := by
  have h := normLower_le_norm DH_demo_enclosure
  intro h0
  rw [h0, norm_zero] at h
  have : (0 : ℝ) < ((normLower (demoB.inflate (2 / 5)) : ℚ) : ℝ) := by
    norm_num [demoB, demoTerm, kappaC, kappaI, demoS, normLower, inflate,
      ZetaLean.Interval.distToZero, dirichletTermBox, expCr, expSmall, expSumC,
      smulQ, powI, coarsen, ZetaLean.Interval.coarsen, halveC, normBound, mul,
      add, neg, ComplexInterval.exact, ZetaLean.Interval.exact,
      ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
      ZetaLean.Interval.sub, ZetaLean.Interval.halve, ZetaLean.Interval.logQ,
      ZetaLean.Interval.log2I, ZetaLean.Interval.log1, ZetaLean.Interval.logSum,
      ZetaLean.Interval.logRem, ZetaLean.Interval.exp1, ZetaLean.Interval.expSum,
      ZetaLean.Interval.expRem, Nat.factorial, Finset.sum_range_succ,
      Finset.sum_range_zero]
  linarith

end ZetaLean.DH
