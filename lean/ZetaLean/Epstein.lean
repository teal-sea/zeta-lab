import Mathlib

/-!
# Davenport-Heilbronn κ derivation

This file formalizes the linear-solve derivation of Davenport-Heilbronn's κ
(the coefficient making the combination self-dual with real coefficients).
This is finite linear algebra over explicit constants, satisfying the
"derive conventions, never remember them" requirement.
-/

open Complex

/--
The defect `F(s) - F(1-s)` is linear in `κ`.
If `F(s) = c * L1 + c_bar * L2` with `c = (1 - I * κ) / 2` and `c_bar = (1 + I * κ) / 2`,
then `F(s) - F(1-s) = (A - I * κ * B) / 2` where `A` and `B` are the sum and difference
combinations of the evaluations.
-/
theorem davenport_heilbronn_defect (L1 L2 L3 L4 κ : ℂ) :
    (((1 - I * κ) / 2) * L1 + ((1 + I * κ) / 2) * L2) -
    (((1 - I * κ) / 2) * L3 + ((1 + I * κ) / 2) * L4) =
    ((L1 + L2 - L3 - L4) - I * κ * (L1 - L2 - L3 + L4)) / 2 := by
  ring

/--
Therefore, setting the defect to zero is equivalent to `A = I * κ * B`.
-/
theorem davenport_heilbronn_zero_defect (L1 L2 L3 L4 κ : ℂ)
    (h_defect : (((1 - I * κ) / 2) * L1 + ((1 + I * κ) / 2) * L2) =
                (((1 - I * κ) / 2) * L3 + ((1 + I * κ) / 2) * L4)) :
    L1 + L2 - L3 - L4 = I * κ * (L1 - L2 - L3 + L4) := by
  have h1 : (((1 - I * κ) / 2) * L1 + ((1 + I * κ) / 2) * L2) -
            (((1 - I * κ) / 2) * L3 + ((1 + I * κ) / 2) * L4) = 0 := sub_eq_zero.mpr h_defect
  have h2 := davenport_heilbronn_defect L1 L2 L3 L4 κ
  rw [h1] at h2
  have h3 : ((L1 + L2 - L3 - L4) - I * κ * (L1 - L2 - L3 + L4)) / 2 = 0 := h2.symm
  have h4 : (L1 + L2 - L3 - L4) - I * κ * (L1 - L2 - L3 + L4) = 0 := by
    calc (L1 + L2 - L3 - L4) - I * κ * (L1 - L2 - L3 + L4)
      _ = (((L1 + L2 - L3 - L4) - I * κ * (L1 - L2 - L3 + L4)) / 2) * 2 := by ring
      _ = 0 * 2 := by rw [h3]
      _ = 0 := MulZeroClass.zero_mul 2
  exact sub_eq_zero.mp h4

/--
Solving for `κ` at a point where `B ≠ 0`.
-/
theorem davenport_heilbronn_kappa (L1 L2 L3 L4 κ : ℂ)
    (h_defect : (((1 - I * κ) / 2) * L1 + ((1 + I * κ) / 2) * L2) =
                (((1 - I * κ) / 2) * L3 + ((1 + I * κ) / 2) * L4))
    (hB : L1 - L2 - L3 + L4 ≠ 0) :
    κ = (L1 + L2 - L3 - L4) / (I * (L1 - L2 - L3 + L4)) := by
  have h := davenport_heilbronn_zero_defect L1 L2 L3 L4 κ h_defect
  -- We have A = I * κ * B.
  -- Thus κ = A / (I * B)
  have hI : I ≠ 0 := I_ne_zero
  have denom_ne_zero : I * (L1 - L2 - L3 + L4) ≠ 0 := mul_ne_zero hI hB
  calc κ
    _ = κ * (I * (L1 - L2 - L3 + L4)) / (I * (L1 - L2 - L3 + L4)) := (mul_div_cancel_right₀ κ denom_ne_zero).symm
    _ = (I * κ * (L1 - L2 - L3 + L4)) / (I * (L1 - L2 - L3 + L4)) := by ring_nf
    _ = (L1 + L2 - L3 - L4) / (I * (L1 - L2 - L3 + L4)) := by rw [←h]

/-!
## The root-number form of the same solve

`zeta/epstein.py` derives κ numerically from the linear system above.  The
classical explanation of *why* that system has a real solution is Gauss-sum
theory: writing `w` for the root number in `Λ(s, χ) = w · Λ(1-s, χ̄)`, the
self-duality of `F = c·Λ(s,χ) + c̄·Λ(s,χ̄)` with `c = (1 - iκ)/2` reduces to
the scalar constraint `1 + iκ = w · (1 - iκ)`.  The two theorems below are
the finite algebra of that reduction, kernel-checked: the constraint forces
`κ = -i(w-1)/(w+1)` (uniqueness), and for any unimodular `w ≠ -1` that value
is real (existence of a *real* κ, which is what makes the Davenport-Heilbronn
coefficients real).  What is **not** formalized here is the analytic input —
the functional equation itself and the value of `w` for the character mod 5;
those remain the oracle side of the boundary.
-/

/-- Self-duality forces κ: the constraint `1 + iκ = w(1 - iκ)` with `w ≠ -1`
has the unique solution `κ = -i(w-1)/(w+1)`. -/
theorem kappa_of_root_number {w κ : ℂ} (hw : w ≠ -1)
    (h : 1 + I * κ = w * (1 - I * κ)) :
    κ = -I * (w - 1) / (w + 1) := by
  have hw' : w + 1 ≠ 0 := fun h0 => hw (by linear_combination h0)
  rw [eq_div_iff hw']
  -- `ring` treats `I` as an atom, so the relation `I * I = -1` must be
  -- supplied explicitly alongside the constraint.
  linear_combination (-I) * h + κ * (w + 1) * Complex.I_mul_I

/-- For unimodular `w ≠ -1` the forced κ is real: it equals its own
conjugate.  This is why the linear solve in `zeta/epstein.py` lands on a real
constant (checked there numerically; here it is a theorem about the algebra). -/
theorem kappa_real_of_unimodular {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ -1) :
    (starRingEnd ℂ) (-I * (w - 1) / (w + 1)) = -I * (w - 1) / (w + 1) := by
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    exact one_ne_zero hw.symm
  have hconj : (starRingEnd ℂ) w = w⁻¹ := (Complex.inv_eq_conj hw).symm
  have hw' : w + 1 ≠ 0 := fun h0 => hw1 (by linear_combination h0)
  have hwinv : w⁻¹ + 1 ≠ 0 := by
    intro h0
    apply hw'
    have hmul : w * (w⁻¹ + 1) = 0 := by rw [h0, mul_zero]
    rw [mul_add, mul_inv_cancel₀ hw0, mul_one] at hmul
    linear_combination hmul
  simp only [map_div₀, map_mul, map_neg, map_sub, map_add, map_one,
    Complex.conj_I, neg_neg, hconj]
  rw [div_eq_div_iff hwinv hw']
  linear_combination (2 * I) * inv_mul_cancel₀ hw0
