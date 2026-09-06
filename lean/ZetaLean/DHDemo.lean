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

* `DH_demo_enclosure`: `DH (3/2 + 3i)` lies in a computed rational
  rectangle, kernel-checked with no oracle input anywhere; and
* `DH_demo_ne_zero`: that rectangle excludes the origin, so
  `DH (3/2 + 3i) ≠ 0`: the first kernel-certified fact about a *value* of
  the Davenport-Heilbronn function.

The point is deliberately tame (`K = 2`, ten series terms, tail `2/5`): the
theorem is the template.  Scaling the same instantiation to the oracle point
`0.808517 + 85.699348i` needs no new mathematics, only the offline kernel
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

/-! ### The same enclosure through the order-2 tail bound

`ZetaLean/DHTailBound2.lean`'s corrections at the same `K = 2`: the
partial-sum box gains the trapezoid endpoint `dhBlock/2` and the closed-form
integral `−dhAnti`, and the certified tail radius drops from `2/5` to
`1/10`: the `K^{-(σ+2)}` exponent demonstrated at the smallest possible
scale (the true order-2 radius here is ≈ 0.008; `1/10` is what survives the
deliberately crude norm bounds below).  The corrections cost five extra
`demoTerm` boxes at `m = 11 … 14`, reused for both `dhBlock` and `dhAnti`
via `m^{1-s₀} = m·m^{-s₀}`, plus the exact Gaussian rational
`(5(1−s₀))⁻¹ = −2/185 + (12/185)i`: the template for the oracle-point
offline run. -/

/-- The `K = 2` block box: `Σ_j c_j (10+j)^{-s₀}`, `j = 1 … 4`. -/
def demoBlock : ComplexInterval :=
  ((((ComplexInterval.exact 1 0).mul (demoTerm 4 11)).add
    (kappaC.mul (demoTerm 4 12))).add
    (kappaC.neg.mul (demoTerm 4 13))).add
    ((ComplexInterval.exact (-1) 0).mul (demoTerm 4 14))

/-- The antiderivative box: `Σ_j c_j (10+j)·(10+j)^{-s₀}` times the exact
`(5(1−s₀))⁻¹`. -/
def demoAnti : ComplexInterval :=
  (((((ComplexInterval.exact 11 0).mul (demoTerm 4 11)).add
    ((ComplexInterval.exact 12 0).mul (kappaC.mul (demoTerm 4 12)))).add
    ((ComplexInterval.exact 13 0).mul (kappaC.neg.mul (demoTerm 4 13)))).add
    ((ComplexInterval.exact (-14) 0).mul (demoTerm 4 14))).mul
    (ComplexInterval.exact (-2 / 185) (12 / 185))

/-- The order-2 corrected centre box: `S + block/2 − anti`. -/
def demoB2 : ComplexInterval :=
  (demoB.add (demoBlock.mul (ComplexInterval.exact (1 / 2) 0))).add demoAnti.neg

private lemma coeff11 : dh_coeff 11 = 1 := rfl
private lemma coeff12 : dh_coeff 12 = dh_kappa := rfl
private lemma coeff13 : dh_coeff 13 = -dh_kappa := rfl
private lemma coeff14 : dh_coeff 14 = -1 := rfl

private lemma term11 : (demoTerm 4 11).contains (((11 : ℕ) : ℂ) ^ (-demoPt)) :=
  term_contains (kL := 4) (m := 11) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
      ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
      ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
      ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
      ZetaLean.Interval.sub, Finset.sum_range_succ])

private lemma term12 : (demoTerm 4 12).contains (((12 : ℕ) : ℂ) ^ (-demoPt)) :=
  term_contains (kL := 4) (m := 12) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
      ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
      ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
      ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
      ZetaLean.Interval.sub, Finset.sum_range_succ])

private lemma term13 : (demoTerm 4 13).contains (((13 : ℕ) : ℂ) ^ (-demoPt)) :=
  term_contains (kL := 4) (m := 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
      ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
      ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
      ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
      ZetaLean.Interval.sub, Finset.sum_range_succ])

private lemma term14 : (demoTerm 4 14).contains (((14 : ℕ) : ℂ) ^ (-demoPt)) :=
  term_contains (kL := 4) (m := 14) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [demoS, normBound, mul, neg, ComplexInterval.exact,
      ZetaLean.Interval.logQ, ZetaLean.Interval.log2I, ZetaLean.Interval.log1,
      ZetaLean.Interval.logSum, ZetaLean.Interval.logRem, ZetaLean.Interval.exact,
      ZetaLean.Interval.mul, ZetaLean.Interval.add, ZetaLean.Interval.neg,
      ZetaLean.Interval.sub, Finset.sum_range_succ])

/-- The block value at `K = 2`, in the shape the boxes certify. -/
private lemma dhBlock_demo_eq : dhBlock demoPt 2
    = ((1 : ℝ) : ℂ) * ((11 : ℕ) : ℂ) ^ (-demoPt)
      + ((dh_kappa : ℝ) : ℂ) * ((12 : ℕ) : ℂ) ^ (-demoPt)
      + ((-dh_kappa : ℝ) : ℂ) * ((13 : ℕ) : ℂ) ^ (-demoPt)
      + ((-1 : ℝ) : ℂ) * ((14 : ℕ) : ℂ) ^ (-demoPt) := by
  rw [dhBlock]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [coeff11, coeff12, coeff13, coeff14,
    show dh_coeff 10 = 0 from rfl]

private lemma demoBlock_contains : demoBlock.contains (dhBlock demoPt 2) := by
  rw [dhBlock_demo_eq, demoBlock]
  exact ComplexInterval.contains_add (ComplexInterval.contains_add
    (ComplexInterval.contains_add
      (ComplexInterval.contains_mul contains_one term11)
      (ComplexInterval.contains_mul contains_kappaC term12))
    (ComplexInterval.contains_mul contains_negKappa term13))
    (ComplexInterval.contains_mul contains_negOne term14)

/-- `(5(1 − s₀))⁻¹` is the exact Gaussian rational `−2/185 + (12/185)i`. -/
private lemma inv_demo_eq : (5 * (1 - demoPt))⁻¹
    = (⟨((-2 / 185 : ℚ) : ℝ), ((12 / 185 : ℚ) : ℝ)⟩ : ℂ) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Complex.ext <;>
    simp [demoPt, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;>
    norm_num

/-- Splitting `m^{1-s} = m · m^{-s}` for a positive natural base. -/
private lemma cpow_one_sub {m : ℕ} (hm : 0 < m) :
    ((m : ℕ) : ℂ) ^ ((1 : ℂ) - demoPt) = ((m : ℕ) : ℂ) * ((m : ℕ) : ℂ) ^ (-demoPt) := by
  rw [show (1 : ℂ) - demoPt = 1 + -demoPt by ring,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hm.ne'), Complex.cpow_one]

private lemma demoAnti_contains : demoAnti.contains (dhAnti demoPt ((2 : ℕ) : ℝ)) := by
  have hval : dhAnti demoPt ((2 : ℕ) : ℝ)
      = (((11 : ℕ) : ℂ) * ((11 : ℕ) : ℂ) ^ (-demoPt)
          + ((12 : ℕ) : ℂ) * (((dh_kappa : ℝ) : ℂ) * ((12 : ℕ) : ℂ) ^ (-demoPt))
          + ((13 : ℕ) : ℂ) * (((-dh_kappa : ℝ) : ℂ) * ((13 : ℕ) : ℂ) ^ (-demoPt))
          + (-(14 : ℕ) : ℂ) * ((14 : ℕ) : ℂ) ^ (-demoPt))
        * (5 * (1 - demoPt))⁻¹ := by
    rw [dhAnti, dhPair, div_eq_mul_inv]
    congr 1
    have h11 : ((5 * ((2 : ℕ) : ℝ) + 1 : ℝ) : ℂ) = ((11 : ℕ) : ℂ) := by push_cast; norm_num
    have h12 : ((5 * ((2 : ℕ) : ℝ) + 2 : ℝ) : ℂ) = ((12 : ℕ) : ℂ) := by push_cast; norm_num
    have h13 : ((5 * ((2 : ℕ) : ℝ) + 3 : ℝ) : ℂ) = ((13 : ℕ) : ℂ) := by push_cast; norm_num
    have h14 : ((5 * ((2 : ℕ) : ℝ) + 4 : ℝ) : ℂ) = ((14 : ℕ) : ℂ) := by push_cast; norm_num
    rw [h11, h12, h13, h14, cpow_one_sub (by norm_num : 0 < 11),
      cpow_one_sub (by norm_num : 0 < 12), cpow_one_sub (by norm_num : 0 < 13),
      cpow_one_sub (by norm_num : 0 < 14)]
    push_cast
    ring
  rw [hval, inv_demo_eq, demoAnti]
  refine ComplexInterval.contains_mul ?_ (ComplexInterval.contains_exact _ _)
  have e11 : (ComplexInterval.exact 11 0).contains ((11 : ℕ) : ℂ) := by
    have h := ComplexInterval.contains_exact 11 0
    rwa [show (⟨((11 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = ((11 : ℕ) : ℂ) by
      apply Complex.ext <;> push_cast <;> simp] at h
  have e12 : (ComplexInterval.exact 12 0).contains ((12 : ℕ) : ℂ) := by
    have h := ComplexInterval.contains_exact 12 0
    rwa [show (⟨((12 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = ((12 : ℕ) : ℂ) by
      apply Complex.ext <;> push_cast <;> simp] at h
  have e13 : (ComplexInterval.exact 13 0).contains ((13 : ℕ) : ℂ) := by
    have h := ComplexInterval.contains_exact 13 0
    rwa [show (⟨((13 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = ((13 : ℕ) : ℂ) by
      apply Complex.ext <;> push_cast <;> simp] at h
  have e14 : (ComplexInterval.exact (-14) 0).contains (-(14 : ℕ) : ℂ) := by
    have h := ComplexInterval.contains_exact (-14) 0
    rwa [show (⟨((-14 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = (-(14 : ℕ) : ℂ) by
      apply Complex.ext <;> push_cast <;> simp] at h
  exact ComplexInterval.contains_add (ComplexInterval.contains_add
    (ComplexInterval.contains_add
      (ComplexInterval.contains_mul e11 term11)
      (ComplexInterval.contains_mul e12
        (ComplexInterval.contains_mul contains_kappaC term12)))
    (ComplexInterval.contains_mul e13
      (ComplexInterval.contains_mul contains_negKappa term13)))
    (ComplexInterval.contains_mul e14 term14)

set_option maxRecDepth 100000 in
/-- **The order-2 pipeline, end to end at the demo point.**  The corrected
centre box, inflated by `1/10` (versus `2/5` at order 0 with the same
`K = 2`), contains `DH (3/2 + 3i)`: every correction term kernel-checked,
no oracle input anywhere.  This is the exact template of the oracle-point
offline run priced in `HANDOFF.md`. -/
theorem DH_demo2_enclosure : (demoB2.inflate (1 / 10)).contains (DH demoPt) := by
  refine DH_mem_of_partial_enclosure_order2 (by norm_num) (by norm_num)
    (K := 2) (by norm_num) ?_ ?_
  · -- the corrected centre: `S + dhBlock/2 − dhAnti` lands in `demoB2`
    have hhalf : (demoBlock.mul (ComplexInterval.exact (1 / 2) 0)).contains
        (dhBlock demoPt 2 / 2) := by
      have h := ComplexInterval.contains_mul demoBlock_contains
        (ComplexInterval.contains_exact (1 / 2) 0)
      rwa [show dhBlock demoPt 2 * (⟨((1 / 2 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ)
          = dhBlock demoPt 2 / 2 by
        rw [show (⟨((1 / 2 : ℚ) : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = (2⁻¹ : ℂ) by
          apply Complex.ext <;> push_cast <;> simp]
        ring] at h
    have hneg := ComplexInterval.contains_neg demoAnti_contains
    have h := ComplexInterval.contains_add
      (ComplexInterval.contains_add demoB_contains hhalf) hneg
    rwa [show ∑ n ∈ range (2 * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-demoPt)
          + dhBlock demoPt 2 / 2 + -dhAnti demoPt ((2 : ℕ) : ℝ)
        = ∑ n ∈ range (2 * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-demoPt)
          + dhBlock demoPt 2 / 2 - dhAnti demoPt ((2 : ℕ) : ℝ) by ring] at h
  · -- the order-2 radius at `K = 2` is below `1/10`
    have hκ : dh_kappa ≤ ((2840794 / 10000000 : ℚ) : ℝ) := contains_kappaI.2
    have hκ0 : (0 : ℝ) ≤ dh_kappa := by exact_mod_cast dh_kappa_nonneg
    have hs : ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ)‖ ≤ 4.5 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      show |((3 / 2 : ℚ) : ℝ)| + |((3 : ℚ) : ℝ)| ≤ _
      rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
      norm_num
    have hs1 : ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ) + 1‖ ≤ 5.5 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      show |((3 / 2 : ℚ) : ℝ) + 1| + |((3 : ℚ) : ℝ) + 0| ≤ _
      rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
      norm_num
    have hs2 : ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ) + 2‖ ≤ 6.5 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.add_re, Complex.add_im]
      show |((3 / 2 : ℚ) : ℝ) + (2 : ℂ).re| + |((3 : ℚ) : ℝ) + (2 : ℂ).im| ≤ _
      norm_num
    have hP : (5 * ((2 : ℕ) : ℝ) + 1) ^ (-((3 / 2 : ℚ) : ℝ) - 2) ≤ 1 / 1331 := by
      have he : -((3 / 2 : ℚ) : ℝ) - 2 ≤ ((-3 : ℤ) : ℝ) := by push_cast; norm_num
      have hb : (1 : ℝ) ≤ 5 * ((2 : ℕ) : ℝ) + 1 := by push_cast; norm_num
      calc (5 * ((2 : ℕ) : ℝ) + 1) ^ (-((3 / 2 : ℚ) : ℝ) - 2)
          ≤ (5 * ((2 : ℕ) : ℝ) + 1) ^ ((-3 : ℤ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hb he
        _ = 1 / 1331 := by
            rw [Real.rpow_intCast]
            push_cast
            norm_num
    have hP0 : (0 : ℝ) ≤ (5 * ((2 : ℕ) : ℝ) + 1) ^ (-((3 / 2 : ℚ) : ℝ) - 2) :=
      Real.rpow_nonneg (by push_cast; norm_num) _
    have hden : ((3 / 2 : ℚ) : ℝ) + 2 = 7 / 2 := by push_cast; norm_num
    rw [hden]
    have h1 : (3 : ℝ) + dh_kappa ≤ 3.2840794 := by push_cast at hκ; linarith
    calc 5 / 8 * ((3 + dh_kappa) * ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ)‖
          * ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ) + 1‖
          * ‖(⟨((3 / 2 : ℚ) : ℝ), ((3 : ℚ) : ℝ)⟩ : ℂ) + 2‖)
          * (5 * ((2 : ℕ) : ℝ) + 1) ^ (-((3 / 2 : ℚ) : ℝ) - 2) / (7 / 2)
        ≤ 5 / 8 * (3.2840794 * 4.5 * 5.5 * 6.5) * (1 / 1331) / (7 / 2) := by
          gcongr
      _ ≤ ((1 / 10 : ℚ) : ℝ) := by push_cast; norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`DH (3/2 + 3i) ≠ 0`, kernel-checked**, the enclosure stays away from
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
