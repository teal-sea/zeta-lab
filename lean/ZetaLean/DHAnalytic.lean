/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.DavenportHeilbronn

/-!
# The analytic half of the Davenport-Heilbronn theorem

This file constructs the Davenport-Heilbronn function as a concrete linear
combination of Mathlib Dirichlet L-functions and kernel-checks everything the
`davenport_heilbronn_statement` asserts about it *except* the off-line zero:

* `DH`: the function itself, `a·L(s,χ) + b·L(s,χ⁻¹)` where `χ` is the
  quartic character mod 5 with `χ(2) = i`, `a = (1 - iκ)/2`, `b = (1 + iκ)/2`
  and `κ = dh_kappa`;
* `DH_differentiable`: it is entire;
* `DH_series_rep`: for `Re(z) > 1` it is the sum of the Dirichlet series
  with the real coefficients `dh_coeff` (the lab's `zeta/epstein.py`
  coefficients: `1, κ, -κ, -1, 0` repeating);
* `DH_functional_eq`: the completed function
  `(π/5)^(-(s+1)/2)·Γ((s+1)/2)·DH(s)` is symmetric under `s ↦ 1-s`, away
  from the Gamma-factor poles;
* `dh_analytic_half`: the three bundled as an existence statement, matching
  conjuncts 0-2 of `davenport_heilbronn_statement`.

The mathematical content of the functional equation is the root-number
identity `a·W(χ) = b`: the constant `κ` is *exactly* the value that rotates
the two conjugate root numbers onto each other, which reduces (via the Gauss
sum `τ(χ) = -2·sin(π/5) + 2·sin(2π/5)·i`) to two real identities proved here
from Mathlib's `Real.cos_pi_div_five` by radical algebra:

* `κ·(2·sin(2π/5) + √5) = 2·sin(π/5)`
* `2·sin(2π/5) + 2·κ·sin(π/5) = √5`

Every convention-sensitive step (the sign of `stdAddChar`, the direction of
the root-number identity, the radical forms of `sin(π/5)` and `sin(2π/5)`)
was first pinned numerically at 40 digits against `zeta/epstein.py`'s
`KAPPA_REF` before being formalized; the kernel now carries the proof.

What remains for the full theorem is only the numeric half: a certified
evaluation showing `DH` vanishes at the off-line point (see
`ZetaLean/OracleDH.lean` for the oracle data and what is still uncertified).
-/

open Complex DirichletCharacter

namespace ZetaLean.DH

/-! ### The character -/

/-- The quartic Dirichlet character mod 5 with `χ(2) = i`, taking values in
`ℤ[i]` so that multiplicativity is a `decide`-able finite check. -/
def dhCharAux : MulChar (ZMod 5) GaussianInt where
  toFun a :=
    match a with
    | 0 => 0
    | 1 => 1
    | 2 => ⟨0, 1⟩
    | 3 => ⟨0, -1⟩
    | 4 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- The Davenport-Heilbronn character: `dhCharAux` pushed into `ℂ`. -/
noncomputable def dhChar : DirichletCharacter ℂ 5 :=
  dhCharAux.ringHomComp GaussianInt.toComplex

lemma dhChar_zero : dhChar 0 = 0 := by
  rw [dhChar, MulChar.ringHomComp_apply, show dhCharAux 0 = 0 from rfl, map_zero]

lemma dhChar_one' : dhChar 1 = 1 := map_one dhChar

lemma dhChar_two : dhChar 2 = I := by
  rw [dhChar, MulChar.ringHomComp_apply, show dhCharAux 2 = ⟨0, 1⟩ from rfl,
    GaussianInt.toComplex_def']
  simp

lemma dhChar_three : dhChar 3 = -I := by
  rw [dhChar, MulChar.ringHomComp_apply, show dhCharAux 3 = ⟨0, -1⟩ from rfl,
    GaussianInt.toComplex_def']
  simp

lemma dhChar_four : dhChar 4 = -1 := by
  rw [dhChar, MulChar.ringHomComp_apply, show dhCharAux 4 = -1 from rfl, map_neg, map_one]

lemma dhChar_inv_apply (a : ZMod 5) : dhChar⁻¹ a = (dhChar a)⁻¹ :=
  MulChar.inv_apply_eq_inv' dhChar a

lemma dhChar_inv_zero : dhChar⁻¹ 0 = 0 := by rw [dhChar_inv_apply, dhChar_zero, inv_zero]

lemma dhChar_inv_one : dhChar⁻¹ 1 = 1 := map_one dhChar⁻¹

lemma dhChar_inv_two : dhChar⁻¹ 2 = -I := by rw [dhChar_inv_apply, dhChar_two, inv_I]

lemma dhChar_inv_three : dhChar⁻¹ 3 = I := by
  rw [dhChar_inv_apply, dhChar_three, inv_neg, inv_I, neg_neg]

lemma dhChar_inv_four : dhChar⁻¹ 4 = -1 := by
  rw [dhChar_inv_apply, dhChar_four]
  norm_num

lemma dhChar_ne_one : dhChar ≠ 1 := by
  intro h
  have h2 : (1 : DirichletCharacter ℂ 5) 2 = I := by rw [← h]; exact dhChar_two
  have h2' : (1 : DirichletCharacter ℂ 5) 2 = 1 :=
    MulChar.one_apply (by decide : IsUnit (2 : ZMod 5))
  rw [h2'] at h2
  simp [Complex.ext_iff] at h2

lemma dhChar_inv_ne_one : dhChar⁻¹ ≠ 1 := by
  intro h
  have h2 : (1 : DirichletCharacter ℂ 5) 2 = -I := by rw [← h]; exact dhChar_inv_two
  have h2' : (1 : DirichletCharacter ℂ 5) 2 = 1 :=
    MulChar.one_apply (by decide : IsUnit (2 : ZMod 5))
  rw [h2'] at h2
  simp [Complex.ext_iff] at h2

lemma dhChar_isPrimitive : dhChar.IsPrimitive := by
  rw [isPrimitive_def]
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ (conductor_dvd_level dhChar) with h | h
  · exact absurd (dhChar.eq_one_iff_conductor_eq_one.mpr h) dhChar_ne_one
  · exact h

lemma dhChar_inv_isPrimitive : dhChar⁻¹.IsPrimitive := by
  rw [isPrimitive_def]
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ (conductor_dvd_level dhChar⁻¹) with h | h
  · exact absurd (dhChar⁻¹.eq_one_iff_conductor_eq_one.mpr h) dhChar_inv_ne_one
  · exact h

lemma dhChar_odd : dhChar.Odd := by
  unfold DirichletCharacter.Odd
  rw [show (-1 : ZMod 5) = 4 from by decide, dhChar_four]

lemma dhChar_inv_odd : dhChar⁻¹.Odd := by
  unfold DirichletCharacter.Odd
  rw [show (-1 : ZMod 5) = 4 from by decide, dhChar_inv_four]

lemma dhChar_not_even : ¬dhChar.Even := by
  intro h
  have h' : (-1 : ℂ) = 1 := dhChar_odd ▸ h
  norm_num at h'

lemma dhChar_inv_not_even : ¬dhChar⁻¹.Even := by
  intro h
  have h' : (-1 : ℂ) = 1 := dhChar_inv_odd ▸ h
  norm_num at h'

/-! ### The coefficients -/

/-- The first rotation constant `a = (1 - iκ)/2`. -/
noncomputable def dhA : ℂ := (1 - I * (dh_kappa : ℂ)) / 2

/-- The second rotation constant `b = (1 + iκ)/2`. -/
noncomputable def dhB : ℂ := (1 + I * (dh_kappa : ℂ)) / 2

/-- The real DH coefficients are the character combination `a·χ(n) + b·χ⁻¹(n)`. -/
lemma dh_coeff_eq_char (n : ℕ) :
    (dh_coeff n : ℂ) = dhA * dhChar (n : ZMod 5) + dhB * dhChar⁻¹ (n : ZMod 5) := by
  have hcast : ((n : ZMod 5)) = ((n % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod n 5).symm
  have hcases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hcases with h | h | h | h | h
  · have hc : dh_coeff n = 0 := by unfold dh_coeff; rw [h]; rfl
    have hz : ((n : ZMod 5)) = 0 := by rw [hcast, h]; norm_num
    rw [hc, hz, dhChar_zero, dhChar_inv_zero]
    norm_num
  · have hc : dh_coeff n = 1 := by unfold dh_coeff; rw [h]; rfl
    have hz : ((n : ZMod 5)) = 1 := by rw [hcast, h]; norm_num
    rw [hc, hz, dhChar_one', dhChar_inv_one]
    unfold dhA dhB
    push_cast
    ring
  · have hc : dh_coeff n = dh_kappa := by unfold dh_coeff; rw [h]; rfl
    have hz : ((n : ZMod 5)) = 2 := by rw [hcast, h]; norm_num
    rw [hc, hz, dhChar_two, dhChar_inv_two]
    unfold dhA dhB
    linear_combination (dh_kappa : ℂ) * Complex.I_sq
  · have hc : dh_coeff n = -dh_kappa := by unfold dh_coeff; rw [h]; rfl
    have hz : ((n : ZMod 5)) = 3 := by rw [hcast, h]; norm_num
    rw [hc, hz, dhChar_three, dhChar_inv_three]
    push_cast
    unfold dhA dhB
    linear_combination (-(dh_kappa : ℂ)) * Complex.I_sq
  · have hc : dh_coeff n = -1 := by unfold dh_coeff; rw [h]; rfl
    have hz : ((n : ZMod 5)) = 4 := by rw [hcast, h]; norm_num
    rw [hc, hz, dhChar_four, dhChar_inv_four]
    push_cast
    unfold dhA dhB
    ring

/-! ### The function -/

set_option linter.dupNamespace false in
/-- The Davenport-Heilbronn function: the entire linear combination of the
two conjugate quartic L-functions mod 5 whose Dirichlet coefficients are the
real sequence `dh_coeff`. -/
noncomputable def DH (s : ℂ) : ℂ :=
  dhA * LFunction dhChar s + dhB * LFunction dhChar⁻¹ s

/-- Condition 0 of `davenport_heilbronn_statement`, for `DH`. -/
theorem DH_differentiable : Differentiable ℂ DH :=
  ((differentiable_LFunction dhChar_ne_one).const_mul dhA).add
    ((differentiable_LFunction dhChar_inv_ne_one).const_mul dhB)

/-- Condition 1 of `davenport_heilbronn_statement`, for `DH`. -/
theorem DH_series_rep : dh_series_rep DH := by
  intro z hz
  have h1 : HasSum (fun n : ℕ => LSeries.term (fun k : ℕ => dhChar k) z n)
      (LFunction dhChar z) := by
    rw [LFunction_eq_LSeries dhChar hz]
    exact (LSeriesSummable_of_one_lt_re dhChar hz).LSeriesHasSum
  have h2 : HasSum (fun n : ℕ => LSeries.term (fun k : ℕ => dhChar⁻¹ k) z n)
      (LFunction dhChar⁻¹ z) := by
    rw [LFunction_eq_LSeries dhChar⁻¹ hz]
    exact (LSeriesSummable_of_one_lt_re dhChar⁻¹ hz).LSeriesHasSum
  have h : HasSum (fun n : ℕ =>
      dhA * LSeries.term (fun k : ℕ => dhChar k) z n +
        dhB * LSeries.term (fun k : ℕ => dhChar⁻¹ k) z n)
      (dhA * LFunction dhChar z + dhB * LFunction dhChar⁻¹ z) :=
    (h1.mul_left dhA).add (h2.mul_left dhB)
  have hfe : (fun n : ℕ => (dh_coeff n : ℂ) * (n : ℂ) ^ (-z))
      = fun n : ℕ =>
        dhA * LSeries.term (fun k : ℕ => dhChar k) z n +
          dhB * LSeries.term (fun k : ℕ => dhChar⁻¹ k) z n := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero, show dh_coeff 0 = 0 from rfl]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, dh_coeff_eq_char n,
        cpow_neg, div_eq_mul_inv, div_eq_mul_inv]
      ring
  rw [hfe]
  exact h

/-! ### The two real κ-identities

The radical algebra behind the root number.  Abbreviate
`R = √(10 - 2√5)`, `P = √(10 + 2√5)`, `F = √5`; then `sin(π/5) = R/4`,
`sin(2π/5) = P/4`, and everything reduces to `R·(F + 1) = 2·P` and
`P·(F - 1) = 2·R`: both checked by squaring. -/

private lemma sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
  Real.mul_self_sqrt (by norm_num)

private lemma sqrt5_pos : 0 < Real.sqrt 5 :=
  Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt5_lt : Real.sqrt 5 < 5 := by
  nlinarith [sqrt5_sq, sqrt5_pos]

private lemma radicand_lo_pos : (0 : ℝ) < 10 - 2 * Real.sqrt 5 := by
  nlinarith [sqrt5_lt]

private lemma radicand_hi_pos : (0 : ℝ) < 10 + 2 * Real.sqrt 5 := by
  nlinarith [sqrt5_pos]

private lemma R_sq : Real.sqrt (10 - 2 * Real.sqrt 5) * Real.sqrt (10 - 2 * Real.sqrt 5)
    = 10 - 2 * Real.sqrt 5 :=
  Real.mul_self_sqrt radicand_lo_pos.le

private lemma P_sq : Real.sqrt (10 + 2 * Real.sqrt 5) * Real.sqrt (10 + 2 * Real.sqrt 5)
    = 10 + 2 * Real.sqrt 5 :=
  Real.mul_self_sqrt radicand_hi_pos.le

private lemma R_pos : 0 < Real.sqrt (10 - 2 * Real.sqrt 5) :=
  Real.sqrt_pos.mpr radicand_lo_pos

private lemma P_pos : 0 < Real.sqrt (10 + 2 * Real.sqrt 5) :=
  Real.sqrt_pos.mpr radicand_hi_pos

/-- `√(10-2√5)·(√5 + 1) = 2·√(10+2√5)` (both sides square to `40 + 8√5`). -/
private lemma R_mul_sqrt5_add_one :
    Real.sqrt (10 - 2 * Real.sqrt 5) * (Real.sqrt 5 + 1)
      = 2 * Real.sqrt (10 + 2 * Real.sqrt 5) := by
  have hl : 0 ≤ Real.sqrt (10 - 2 * Real.sqrt 5) * (Real.sqrt 5 + 1) := by positivity
  have hr : 0 ≤ 2 * Real.sqrt (10 + 2 * Real.sqrt 5) := by positivity
  have hsq : (Real.sqrt (10 - 2 * Real.sqrt 5) * (Real.sqrt 5 + 1)) ^ 2
      = (2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 := by
    nlinarith [R_sq, P_sq, sqrt5_sq]
  calc Real.sqrt (10 - 2 * Real.sqrt 5) * (Real.sqrt 5 + 1)
      = Real.sqrt ((Real.sqrt (10 - 2 * Real.sqrt 5) * (Real.sqrt 5 + 1)) ^ 2) :=
        (Real.sqrt_sq hl).symm
    _ = Real.sqrt ((2 * Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2) := by rw [hsq]
    _ = 2 * Real.sqrt (10 + 2 * Real.sqrt 5) := Real.sqrt_sq hr

/-- `√(10+2√5)·(√5 - 1) = 2·√(10-2√5)` (both sides square to `40 - 8√5`). -/
private lemma P_mul_sqrt5_sub_one :
    Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)
      = 2 * Real.sqrt (10 - 2 * Real.sqrt 5) := by
  have h1 : (0:ℝ) ≤ Real.sqrt 5 - 1 := by nlinarith [sqrt5_sq, sqrt5_pos]
  have hl : 0 ≤ Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1) := by positivity
  have hr : 0 ≤ 2 * Real.sqrt (10 - 2 * Real.sqrt 5) := by positivity
  have hsq : (Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) ^ 2
      = (2 * Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 := by
    nlinarith [R_sq, P_sq, sqrt5_sq]
  calc Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)
      = Real.sqrt ((Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) ^ 2) :=
        (Real.sqrt_sq hl).symm
    _ = Real.sqrt ((2 * Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2) := by rw [hsq]
    _ = 2 * Real.sqrt (10 - 2 * Real.sqrt 5) := Real.sqrt_sq hr

/-- `sin(π/5) = √(10 - 2√5)/4`, from Mathlib's `cos(π/5) = (1+√5)/4`. -/
lemma sin_pi_div_five : Real.sin (Real.pi / 5) = Real.sqrt (10 - 2 * Real.sqrt 5) / 4 := by
  have h := Real.sin_eq_sqrt_one_sub_cos_sq
    (le_of_lt (by positivity : (0:ℝ) < Real.pi / 5))
    (by linarith [Real.pi_pos] : Real.pi / 5 ≤ Real.pi)
  rw [h, Real.cos_pi_div_five,
    show 1 - ((1 + Real.sqrt 5) / 4) ^ 2 = (10 - 2 * Real.sqrt 5) * (1 / 4) ^ 2 by
      linear_combination (-(1 : ℝ) / 16) * sqrt5_sq,
    Real.sqrt_mul radicand_lo_pos.le, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 4)]
  ring

/-- `cos(2π/5) = (√5 - 1)/4`, by the double-angle formula. -/
lemma cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul,
    Real.cos_pi_div_five]
  linear_combination (1 / 8 : ℝ) * sqrt5_sq

/-- `sin(2π/5) = √(10 + 2√5)/4`. -/
lemma sin_two_pi_div_five :
    Real.sin (2 * Real.pi / 5) = Real.sqrt (10 + 2 * Real.sqrt 5) / 4 := by
  have h := Real.sin_eq_sqrt_one_sub_cos_sq
    (le_of_lt (by positivity : (0:ℝ) < 2 * Real.pi / 5))
    (by linarith [Real.pi_pos] : 2 * Real.pi / 5 ≤ Real.pi)
  rw [h, cos_two_pi_div_five,
    show 1 - ((Real.sqrt 5 - 1) / 4) ^ 2 = (10 + 2 * Real.sqrt 5) * (1 / 4) ^ 2 by
      linear_combination (-(1 : ℝ) / 16) * sqrt5_sq,
    Real.sqrt_mul radicand_hi_pos.le, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 4)]
  ring

/-- The first κ-identity: `κ·(2·sin(2π/5) + √5) = 2·sin(π/5)`.
This is one real component of the root-number identity `a·W(χ) = b`. -/
lemma kappa_identity_one :
    dh_kappa * (2 * Real.sin (2 * Real.pi / 5) + Real.sqrt 5) = 2 * Real.sin (Real.pi / 5) := by
  rw [sin_pi_div_five, sin_two_pi_div_five]
  unfold dh_kappa
  have h1 : Real.sqrt 5 - 1 ≠ 0 := by nlinarith [sqrt5_sq, sqrt5_pos]
  field_simp
  nlinarith [R_mul_sqrt5_add_one, P_mul_sqrt5_sub_one, sqrt5_sq, R_sq, P_sq,
    R_pos, P_pos, sqrt5_pos]

/-- The second κ-identity: `2·sin(2π/5) + 2·κ·sin(π/5) = √5`.
This is the other real component of the root-number identity. -/
lemma kappa_identity_two :
    2 * Real.sin (2 * Real.pi / 5) + 2 * dh_kappa * Real.sin (Real.pi / 5) = Real.sqrt 5 := by
  rw [sin_pi_div_five, sin_two_pi_div_five]
  unfold dh_kappa
  have h1 : Real.sqrt 5 - 1 ≠ 0 := by nlinarith [sqrt5_sq, sqrt5_pos]
  field_simp
  nlinarith [R_mul_sqrt5_add_one, P_mul_sqrt5_sub_one, sqrt5_sq, R_sq, P_sq,
    R_pos, P_pos, sqrt5_pos]

/-! ### The Gauss sums -/

private lemma stdAddChar_val (j : ℕ) :
    ZMod.stdAddChar ((j : ℕ) : ZMod 5) =
      (Real.cos (2 * Real.pi * j / 5) : ℂ) + (Real.sin (2 * Real.pi * j / 5) : ℂ) * I := by
  have h : ((j : ℤ) : ZMod 5) = ((j : ℕ) : ZMod 5) := by push_cast; rfl
  rw [← h, ZMod.stdAddChar_coe]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * I * (j : ℂ) / 5 = 2 * (Real.pi : ℂ) * (j : ℂ) / 5 * I by ring,
    exp_mul_I]

private lemma cos_val_four :
    Real.cos (2 * Real.pi * 4 / 5) = Real.cos (2 * Real.pi * 1 / 5) := by
  rw [show 2 * Real.pi * 4 / 5 = 2 * Real.pi - 2 * Real.pi * 1 / 5 by ring,
    Real.cos_two_pi_sub]

private lemma sin_val_four :
    Real.sin (2 * Real.pi * 4 / 5) = -Real.sin (2 * Real.pi * 1 / 5) := by
  rw [show 2 * Real.pi * 4 / 5 = 2 * Real.pi - 2 * Real.pi * 1 / 5 by ring,
    Real.sin_two_pi_sub]

private lemma cos_val_three :
    Real.cos (2 * Real.pi * 3 / 5) = Real.cos (2 * Real.pi * 2 / 5) := by
  rw [show 2 * Real.pi * 3 / 5 = 2 * Real.pi - 2 * Real.pi * 2 / 5 by ring,
    Real.cos_two_pi_sub]

private lemma sin_val_three :
    Real.sin (2 * Real.pi * 3 / 5) = -Real.sin (2 * Real.pi * 2 / 5) := by
  rw [show 2 * Real.pi * 3 / 5 = 2 * Real.pi - 2 * Real.pi * 2 / 5 by ring,
    Real.sin_two_pi_sub]

private lemma sin_val_two :
    Real.sin (2 * Real.pi * 2 / 5) = Real.sin (Real.pi / 5) := by
  rw [show 2 * Real.pi * 2 / 5 = Real.pi - Real.pi / 5 by ring, Real.sin_pi_sub]

private lemma sin_val_one :
    Real.sin (2 * Real.pi * 1 / 5) = Real.sin (2 * Real.pi / 5) := by norm_num

/-- The Gauss sum of `χ`: `τ(χ) = -2·sin(π/5) + 2·sin(2π/5)·i`. -/
lemma gaussSum_dhChar :
    gaussSum dhChar ZMod.stdAddChar =
      -2 * (Real.sin (Real.pi / 5) : ℂ) + 2 * (Real.sin (2 * Real.pi / 5) : ℂ) * I := by
  have hexp : gaussSum dhChar ZMod.stdAddChar =
      dhChar ((0 : ℕ) : ZMod 5) * ZMod.stdAddChar ((0 : ℕ) : ZMod 5) +
      dhChar ((1 : ℕ) : ZMod 5) * ZMod.stdAddChar ((1 : ℕ) : ZMod 5) +
      dhChar ((2 : ℕ) : ZMod 5) * ZMod.stdAddChar ((2 : ℕ) : ZMod 5) +
      dhChar ((3 : ℕ) : ZMod 5) * ZMod.stdAddChar ((3 : ℕ) : ZMod 5) +
      dhChar ((4 : ℕ) : ZMod 5) * ZMod.stdAddChar ((4 : ℕ) : ZMod 5) :=
    Fin.sum_univ_five _
  rw [hexp, stdAddChar_val, stdAddChar_val, stdAddChar_val, stdAddChar_val, stdAddChar_val,
    show ((0 : ℕ) : ZMod 5) = (0 : ZMod 5) from by decide,
    show ((1 : ℕ) : ZMod 5) = (1 : ZMod 5) from by decide,
    show ((2 : ℕ) : ZMod 5) = (2 : ZMod 5) from by decide,
    show ((3 : ℕ) : ZMod 5) = (3 : ZMod 5) from by decide,
    show ((4 : ℕ) : ZMod 5) = (4 : ZMod 5) from by decide,
    dhChar_zero, dhChar_one', dhChar_two, dhChar_three, dhChar_four]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [cos_val_four, sin_val_four, cos_val_three, sin_val_three, sin_val_two, sin_val_one]
  push_cast
  linear_combination (2 * Complex.sin ((Real.pi : ℂ) / 5)) * Complex.I_sq

/-- The Gauss sum of `χ⁻¹`: `τ(χ⁻¹) = 2·sin(π/5) + 2·sin(2π/5)·i`. -/
lemma gaussSum_dhChar_inv :
    gaussSum dhChar⁻¹ ZMod.stdAddChar =
      2 * (Real.sin (Real.pi / 5) : ℂ) + 2 * (Real.sin (2 * Real.pi / 5) : ℂ) * I := by
  have hexp : gaussSum dhChar⁻¹ ZMod.stdAddChar =
      dhChar⁻¹ ((0 : ℕ) : ZMod 5) * ZMod.stdAddChar ((0 : ℕ) : ZMod 5) +
      dhChar⁻¹ ((1 : ℕ) : ZMod 5) * ZMod.stdAddChar ((1 : ℕ) : ZMod 5) +
      dhChar⁻¹ ((2 : ℕ) : ZMod 5) * ZMod.stdAddChar ((2 : ℕ) : ZMod 5) +
      dhChar⁻¹ ((3 : ℕ) : ZMod 5) * ZMod.stdAddChar ((3 : ℕ) : ZMod 5) +
      dhChar⁻¹ ((4 : ℕ) : ZMod 5) * ZMod.stdAddChar ((4 : ℕ) : ZMod 5) :=
    Fin.sum_univ_five _
  rw [hexp, stdAddChar_val, stdAddChar_val, stdAddChar_val, stdAddChar_val, stdAddChar_val,
    show ((0 : ℕ) : ZMod 5) = (0 : ZMod 5) from by decide,
    show ((1 : ℕ) : ZMod 5) = (1 : ZMod 5) from by decide,
    show ((2 : ℕ) : ZMod 5) = (2 : ZMod 5) from by decide,
    show ((3 : ℕ) : ZMod 5) = (3 : ZMod 5) from by decide,
    show ((4 : ℕ) : ZMod 5) = (4 : ZMod 5) from by decide,
    dhChar_inv_zero, dhChar_inv_one, dhChar_inv_two, dhChar_inv_three, dhChar_inv_four]
  push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [cos_val_four, sin_val_four, cos_val_three, sin_val_three, sin_val_two, sin_val_one]
  push_cast
  linear_combination (-2 * Complex.sin ((Real.pi : ℂ) / 5)) * Complex.I_sq

/-! ### The root-number identities -/

private lemma five_cpow_half : ((5 : ℕ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt 5 : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow,
    show ((5 : ℕ) : ℂ) = ((5 : ℝ) : ℂ) by norm_num,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← ofReal_cpow (by norm_num : (0:ℝ) ≤ (5:ℝ))]

private lemma sqrt5_ne_zero_c : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := by
  simp only [ne_eq, ofReal_eq_zero]
  exact sqrt5_pos.ne'

private lemma I_mul_sqrt5_ne_zero : I * ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 :=
  mul_ne_zero I_ne_zero sqrt5_ne_zero_c

set_option linter.unusedSimpArgs false in
/-- The cleared-denominator form of the root-number identity `a·W(χ) = b`:
its real part is `kappa_identity_one`, its imaginary part `kappa_identity_two`. -/
private lemma root_key_one :
    (1 - I * (dh_kappa : ℂ)) *
      (-2 * (Real.sin (Real.pi / 5) : ℂ) + 2 * (Real.sin (2 * Real.pi / 5) : ℂ) * I) =
    (1 + I * (dh_kappa : ℂ)) * (I * (Real.sqrt 5 : ℂ)) := by
  have h1 := kappa_identity_one
  have h2 := kappa_identity_two
  apply Complex.ext <;>
  · simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, one_re, one_im, I_re, I_im,
      ofReal_re, ofReal_im, re_ofNat, im_ofNat, neg_mul, neg_re, neg_im, mul_one, mul_zero,
      one_mul, zero_mul, zero_sub, sub_zero, zero_add, add_zero, neg_zero, neg_neg]
    ring_nf
    ring_nf at h1 h2
    linarith [h1, h2]

set_option linter.unusedSimpArgs false in
/-- The mirror identity `b·W(χ⁻¹) = a`, cleared of denominators. -/
private lemma root_key_two :
    (1 + I * (dh_kappa : ℂ)) *
      (2 * (Real.sin (Real.pi / 5) : ℂ) + 2 * (Real.sin (2 * Real.pi / 5) : ℂ) * I) =
    (1 - I * (dh_kappa : ℂ)) * (I * (Real.sqrt 5 : ℂ)) := by
  have h1 := kappa_identity_one
  have h2 := kappa_identity_two
  apply Complex.ext <;>
  · simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, one_re, one_im, I_re, I_im,
      ofReal_re, ofReal_im, re_ofNat, im_ofNat, neg_mul, neg_re, neg_im, mul_one, mul_zero,
      one_mul, zero_mul, zero_sub, sub_zero, zero_add, add_zero, neg_zero, neg_neg]
    ring_nf
    ring_nf at h1 h2
    linarith [h1, h2]

/-- The root-number identity `a·W(χ) = b`: `κ` is exactly the constant that
makes the completed DH function symmetric. -/
lemma dhA_mul_rootNumber : dhA * rootNumber dhChar = dhB := by
  unfold rootNumber dhA dhB
  rw [if_neg dhChar_not_even, gaussSum_dhChar, five_cpow_half, pow_one,
    div_div, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero two_ne_zero I_mul_sqrt5_ne_zero) two_ne_zero]
  linear_combination (2 : ℂ) * root_key_one

/-- The mirror root-number identity `b·W(χ⁻¹) = a`. -/
lemma dhB_mul_rootNumber : dhB * rootNumber dhChar⁻¹ = dhA := by
  unfold rootNumber dhA dhB
  rw [if_neg dhChar_inv_not_even, gaussSum_dhChar_inv, five_cpow_half, pow_one,
    div_div, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero two_ne_zero I_mul_sqrt5_ne_zero) two_ne_zero]
  linear_combination (2 : ℂ) * root_key_two

/-! ### The completed function and the functional equation -/

private lemma pi_cpow_ne_zero (w : ℂ) : ((Real.pi : ℝ) : ℂ) ^ w ≠ 0 := by
  intro h0
  exact absurd ((cpow_eq_zero_iff _ _).mp h0).1 (ofReal_ne_zero.mpr Real.pi_ne_zero)

private lemma five_cpow_ne_zero (w : ℂ) : (5 : ℂ) ^ w ≠ 0 := by
  intro h0
  exact absurd ((cpow_eq_zero_iff _ _).mp h0).1 (by norm_num)

/-- Away from the Gamma poles, the abstract completed function of the
statement is the `5^((z+1)/2)`-weighted combination of Mathlib's completed
L-functions.  This is where the junk-value guard earns its keep: the
identity is *false* at `z = -1, -3, …`. -/
private lemma dh_completed_DH_eq (z : ℂ) (h : Complex.Gamma ((z + 1) / 2) ≠ 0) :
    dh_completed DH z = (5 : ℂ) ^ ((z + 1) / 2) *
      (dhA * completedLFunction dhChar z + dhB * completedLFunction dhChar⁻¹ z) := by
  have hA : ((Real.pi : ℝ) : ℂ) ^ ((z + 1) / 2) ≠ 0 := pi_cpow_ne_zero _
  have hB : (5 : ℂ) ^ ((z + 1) / 2) ≠ 0 := five_cpow_ne_zero _
  have hγ : Gammaℝ (z + 1)
      = (((Real.pi : ℝ) : ℂ) ^ ((z + 1) / 2))⁻¹ * Complex.Gamma ((z + 1) / 2) := by
    rw [Gammaℝ_def, show -(z + 1) / 2 = -((z + 1) / 2) by ring, cpow_neg]
  have hγne : Gammaℝ (z + 1) ≠ 0 := by
    rw [hγ]
    exact mul_ne_zero (inv_ne_zero hA) h
  have hL1 : LFunction dhChar z = completedLFunction dhChar z / Gammaℝ (z + 1) := by
    rw [LFunction_eq_completed_div_gammaFactor dhChar z (Or.inr (by norm_num)),
      dhChar_odd.gammaFactor_def]
  have hL2 : LFunction dhChar⁻¹ z = completedLFunction dhChar⁻¹ z / Gammaℝ (z + 1) := by
    rw [LFunction_eq_completed_div_gammaFactor dhChar⁻¹ z (Or.inr (by norm_num)),
      dhChar_inv_odd.gammaFactor_def]
  have hbase : (Real.pi / 5 : ℂ) ^ (-(z + 1) / 2)
      = (((Real.pi : ℝ) : ℂ) ^ ((z + 1) / 2))⁻¹ * (5 : ℂ) ^ ((z + 1) / 2) := by
    rw [show (Real.pi / 5 : ℂ) = ((Real.pi : ℝ) : ℂ) / ((5 : ℝ) : ℂ) by push_cast; ring,
      div_cpow_ofReal_nonneg Real.pi_pos.le (by norm_num : (0:ℝ) ≤ (5:ℝ)),
      show -(z + 1) / 2 = -((z + 1) / 2) by ring, cpow_neg, cpow_neg,
      show ((5 : ℝ) : ℂ) = (5 : ℂ) by norm_num]
    field_simp
  unfold dh_completed DH
  rw [hbase, hL1, hL2, hγ]
  field_simp

/-- Condition 2 of `davenport_heilbronn_statement`, for `DH`: the completed
function is symmetric under `z ↦ 1 - z` away from the Gamma-factor poles. -/
theorem DH_functional_eq : dh_functional_eq DH := by
  intro z hz hz'
  rw [dh_completed_DH_eq z hz, dh_completed_DH_eq (1 - z) hz']
  have hFE1 := dhChar_isPrimitive.completedLFunction_one_sub z
  have hFE2 := dhChar_inv_isPrimitive.completedLFunction_one_sub z
  rw [inv_inv] at hFE2
  have hN : ((5 : ℕ) : ℂ) = (5 : ℂ) := by norm_num
  rw [hN] at hFE1 hFE2
  rw [hFE1, hFE2]
  have hpow : (5 : ℂ) ^ ((1 - z + 1) / 2) * (5 : ℂ) ^ (z - 1 / 2)
      = (5 : ℂ) ^ ((z + 1) / 2) := by
    rw [← cpow_add _ _ (by norm_num : (5:ℂ) ≠ 0)]
    congr 1
    ring
  linear_combination
    (-(dhA * rootNumber dhChar * completedLFunction dhChar⁻¹ z
        + dhB * rootNumber dhChar⁻¹ * completedLFunction dhChar z)) * hpow
    - (5 : ℂ) ^ ((z + 1) / 2) * completedLFunction dhChar⁻¹ z * dhA_mul_rootNumber
    - (5 : ℂ) ^ ((z + 1) / 2) * completedLFunction dhChar z * dhB_mul_rootNumber

/-! ### The packaged analytic half -/

/-- **The analytic half of the Davenport-Heilbronn theorem** (Rung 3
Phase B, first face): there is an entire function which is the sum of the
Davenport-Heilbronn Dirichlet series on `Re(z) > 1` and whose completion
`(π/5)^(-(s+1)/2)·Γ((s+1)/2)·f(s)` is symmetric under `s ↦ 1-s`.  What is
*not* yet certified is only the off-line zero (conditions 3-4 of
`davenport_heilbronn_statement`). -/
theorem dh_analytic_half :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f :=
  ⟨DH, DH_differentiable, DH_series_rep, DH_functional_eq⟩

end ZetaLean.DH
