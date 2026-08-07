import Mathlib
import ZetaLean.Rigor

/-!
# The Davenport-Heilbronn Theorem

This file states and eventually proves the Davenport-Heilbronn theorem:
there exists a Dirichlet series with real coefficients and a functional equation
that has a zero off the critical line `Re(s) = 1/2`.

The function used is the Davenport-Heilbronn function:
`DH(s) = (1 - iκ)/2 * L(s, χ_1) + (1 + iκ)/2 * L(s, χ_2)`
where `χ_1` and `χ_2` are Dirichlet characters modulo 5, and `κ` is a specific real constant.

**Status (Rung 3).** Phase A formalizes the *statement*
(`davenport_heilbronn_statement`, a named `Prop`) — deliberately a `def`, not
a sorried `theorem`: the lab's rule is that the Lean arm counts nothing with
a `sorry`, and a statement asserts nothing, so it needs none.  Phase B — the
open mountain — is the proof, which will certify the off-line zero by
interval evaluation (the Oracle Boundary Pattern; see
`ZetaLean/DirichletEval.lean` for what is and is not yet kernel-checked).
-/

open Complex

/-- The constant κ = (sqrt (10 - 2 * sqrt 5) - 2) / (sqrt 5 - 1), the value
`zeta/epstein.py` derives by linear solve (`KAPPA_REF`). -/
noncomputable def dh_kappa : ℝ :=
  (Real.sqrt (10 - 2 * Real.sqrt 5) - 2) / (Real.sqrt 5 - 1)

/-- The Dirichlet coefficients of the Davenport-Heilbronn function -/
noncomputable def dh_coeff (n : ℕ) : ℝ :=
  match n % 5 with
  | 1 => 1
  | 2 => dh_kappa
  | 3 => -dh_kappa
  | 4 => -1
  | _ => 0

/-- The completed Davenport-Heilbronn function factor -/
noncomputable def dh_completed (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Real.pi / 5 : ℂ) ^ (-(s + 1) / 2) * Complex.Gamma ((s + 1) / 2) * f s

/-- The Davenport-Heilbronn theorem, as a statement:
    there exists a function matching the DH Dirichlet series (which has real
    coefficients) for Re(s) > 1, satisfying the functional equation, and
    having a zero off the critical line `Re(s) = 1/2`.

    Rung 3 Phase B is the (currently open) proof:
    `theorem davenport_heilbronn : davenport_heilbronn_statement`. -/
def davenport_heilbronn_statement : Prop :=
  ∃ (f : ℂ → ℂ) (s : ℂ),
    -- 1. f is represented by the Davenport-Heilbronn Dirichlet series for Re(s) > 1
    (∀ z : ℂ, 1 < z.re → HasSum (fun (n : ℕ) => (dh_coeff n : ℂ) * (n : ℂ) ^ (-z)) (f z)) ∧
    -- 2. f satisfies the functional equation
    (∀ z : ℂ, dh_completed f z = dh_completed f (1 - z)) ∧
    -- 3. f has a zero at s
    f s = 0 ∧
    -- 4. s is off the critical line
    s.re ≠ 1/2

