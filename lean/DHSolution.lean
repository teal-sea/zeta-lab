/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.DHZeroCriterion

/-!
# Proved solution

This module imports the Davenport-Heilbronn development and proves the three
statements advertised in `DHChallenge.lean`.

Following the Palomar layout this module does **not** import `DHChallenge`:
the two modules independently declare the same names, and Comparator checks
that each compared declaration has the same statement in both.  The
definitions below are therefore verbatim copies of the ones in
`DHChallenge.lean`, which are themselves verbatim copies of the
development's own root-level definitions.

Each copy is definitionally equal to its original.  `dh_coeff` is defined by
a `match`, and two `match` definitions generate two distinct auxiliary
matchers, so its bridge is proved by case analysis on `n % 5` rather than by
`rfl`; the remaining bridges are `rfl`.
-/

namespace ZetaLean.PalomarDH

/-! ### The Davenport-Heilbronn data -/

/-- The Davenport-Heilbronn constant `κ`, the value making the coefficients real. -/
noncomputable def dh_kappa : ℝ :=
  (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)

/-- The Dirichlet coefficients of the Davenport-Heilbronn function: the real
sequence `1, κ, -κ, -1, 0` repeating with period 5. -/
noncomputable def dh_coeff (n : ℕ) : ℝ :=
  match n % 5 with
  | 1 => 1
  | 2 => dh_kappa
  | 3 => -dh_kappa
  | 4 => -1
  | _ => 0

/-- The completed Davenport-Heilbronn function factor. -/
noncomputable def dh_completed (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Real.pi / 5 : ℂ) ^ (-(s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * f s

/-- `f` is represented by the Davenport-Heilbronn Dirichlet series (which has
real coefficients) on the half-plane `Re z > 1`. -/
def dh_series_rep (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 1 < z.re → HasSum (fun (n : ℕ) => (dh_coeff n : ℂ) * (n : ℂ) ^ (-z)) (f z)

/-- `f` satisfies the Davenport-Heilbronn functional equation, away from the
poles of the two Gamma factors.  The `Complex.Gamma _ ≠ 0` guards exclude
exactly the points where Mathlib's junk value `Gamma = 0` would make the
unrestricted equation false; everywhere else both sides are the honest
completed function. -/
def dh_functional_eq (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Complex.Gamma ((z + 1) / 2) ≠ 0 → Complex.Gamma ((1 - z + 1) / 2) ≠ 0 →
    dh_completed f z = dh_completed f (1 - z)

/-! ### Bridges to the development's own definitions -/

theorem dh_kappa_eq : dh_kappa = _root_.dh_kappa := rfl

theorem dh_coeff_eq : dh_coeff = _root_.dh_coeff := by
  funext n
  have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases h with h | h | h | h | h <;>
    simp only [dh_coeff, _root_.dh_coeff, h, dh_kappa, _root_.dh_kappa]

theorem dh_completed_eq : dh_completed = _root_.dh_completed := rfl

theorem dh_series_rep_eq : dh_series_rep = _root_.dh_series_rep := by
  funext f
  simp only [dh_series_rep, _root_.dh_series_rep, dh_coeff_eq]

theorem dh_functional_eq_eq : dh_functional_eq = _root_.dh_functional_eq := by
  funext f
  simp only [dh_functional_eq, _root_.dh_functional_eq, dh_completed_eq]

/-! ### The advertised theorems -/

/-- **Minimum-modulus criterion.** -/
theorem exists_zero_of_norm_lt_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h1 : ‖f c‖ < ε) (h2 : ∀ z ∈ Metric.sphere c r, ε ≤ ‖f z‖) :
    ∃ z ∈ Metric.closedBall c r, f z = 0 :=
  ZetaLean.DH.exists_zero_of_norm_lt_on_sphere hf hr h1 h2

/-- **Minimum-modulus criterion, general boundary version.** -/
theorem exists_zero_of_norm_lt_on_frontier {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : Set ℂ} (hUb : Bornology.IsBounded U) (hUo : IsOpen U)
    {c : ℂ} (hc : c ∈ U) {ε : ℝ}
    (h1 : ‖f c‖ < ε) (h2 : ∀ z ∈ frontier U, ε ≤ ‖f z‖) :
    ∃ z ∈ closure U, f z = 0 :=
  ZetaLean.DH.exists_zero_of_norm_lt_on_frontier hf hUb hUo hc h1 h2

/-- **The analytic half of the Davenport-Heilbronn theorem.** -/
theorem dh_analytic_half :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f := by
  rw [dh_series_rep_eq, dh_functional_eq_eq]
  exact ZetaLean.DH.dh_analytic_half

end ZetaLean.PalomarDH
