module

/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
public import Mathlib
public import FourPointCand.Main

@[expose] public section

/-!
# Solution interface for the stronger four-point bound

The definitions below match `StrongerChallenge` and are tied to the proof
development by definitional equalities, except for `H`, which uses `HD_one`.
This module does not import the statement-only Challenge.
The upstream zeta formalization and Ainta's analytic argument retain their
attribution in `hunts/four_point_pressure/PALOMAR-READINESS.md`.
-/

open scoped BigOperators
noncomputable section
namespace Zeta23Ext.PalomarFourPoint

/-- A zero of Mathlib's zeta function in the open critical strip. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- Multiplicity, defined by the analytic order of vanishing. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- Nontrivial zeros with ordinate in the half-open interval `(T₁,T₂]`. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- The zero count in that interval, with multiplicity. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- The number of simple zeros on the critical line in that interval. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- The upstream Theorem D constant, expressed without importing its proof. -/
def H : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)

theorem Ncount_eq : Ncount = _root_.Zeta23.Ncount := rfl

theorem N0simple_eq : N0simple = _root_.Zeta23.N0simple := rfl

theorem H_eq : H = _root_.Zeta23.ThmD.HD 1 := _root_.Zeta23.ThmD.HD_one.symm

theorem four_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((14400000 * H - 17240) / 14366681 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.FourPoint.four_point_bound

theorem four_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (14400000 * H - 17240) / 14366681 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.FourPoint.four_point_bound_ratio

#print axioms four_point_bound
#print axioms four_point_bound_ratio

end Zeta23Ext.PalomarFourPoint
