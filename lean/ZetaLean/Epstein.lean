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
