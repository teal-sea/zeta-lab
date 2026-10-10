/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import OAI.NumberTheory.DirichletL.Nonvanishing
import OAI.NumberTheory.SiegelZeros.Estimates.ConstantCancellation
import OAI.NumberTheory.DirichletL.LogarithmicControl
import QRH125

/-!
This bridge is compiled in OpenAI's own patched Lake environment by
scripts/namespace-build.sh. It introduces no zero-free hypothesis as an axiom.
The character bound itself is not yet proved.
-/

namespace QRH125

/-- The requested target, kept as a proposition until its analytic inputs
are proved. There is deliberately no theorem claiming this proposition. -/
def LeastNonresidueBound : Prop :=
  ∀ (q : ℕ) [NeZero q], 3 ≤ q →
    ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ (Real.log q) ^ 8 ∧
        χ (n : ZMod q) ≠ 0 ∧ χ (n : ZMod q) ≠ 1

/-- Restate the upstream theorem without changing its pole exception. -/
theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

open OAI.SiegelZeros
open OAI.SiegelZeros.SiegelZerosAwei.W51

/-- A canonical choice of the complex Hadamard constant, independent of any
choice of affine factorization. Its real part cancellation remains to prove. -/
noncomputable def hadamardB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  logDeriv (normalizedCompletion χ) 0

/-- Remove the existential affine constants from OpenAI's log derivative
identity. This works for complex primitive characters as well as real ones. -/
theorem logDeriv_eq_hadamardB_add_zero_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    {z : ℂ} (hz : normalizedCompletion χ z ≠ 0) :
    logDeriv (normalizedCompletion χ) z = hadamardB χ +
      ∑' i : ZeroIndex χ, ((z - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹) := by
  obtain ⟨A, B, haffine⟩ :=
    SiegelZerosAwei.Workers.W01.normalizedCompletion_affine_factorization χ hχ hprimitive
  have hB : hadamardB χ = B :=
    logDeriv_normalizedCompletion_zero_of_affine χ hχ hprimitive A B haffine
  rw [hB]
  exact logDeriv_normalizedCompletion_of_affine χ hχ hprimitive A B haffine hz

end QRH125
