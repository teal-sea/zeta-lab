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
open mountain — is the proof.  Its *analytic half* (a concrete entire
function with the DH series and the functional equation) is now
kernel-checked in `ZetaLean/DHAnalytic.lean`; the *numeric half* (certifying
the off-line zero by interval evaluation, the Oracle Boundary Pattern; see
`ZetaLean/DirichletEval.lean`) remains open.

**Two defects found and fixed in the original Phase A statement.**  The first
draft of `davenport_heilbronn_statement` quantified the functional equation
over *all* of `ℂ` and did not require `f` to be differentiable.  Both choices
were wrong, in opposite directions:

1. *The unrestricted functional equation was falsifiable.*  Mathlib's
   `Complex.Gamma` takes the junk value `0` at its poles
   (`Complex.Gamma_zero`), so at `z = -1` the left side of
   `dh_completed f z = dh_completed f (1 - z)` is `0` while the right side is
   a nonzero multiple of `f 2` — and condition 1 pins `f 2` to a positive
   sum.  The old statement was therefore *false for every admissible `f`*,
   hence unprovable.  The functional equation is now guarded by
   `Complex.Gamma _ ≠ 0` hypotheses, its maximal honest domain.

2. *Without differentiability the statement did not encode the theorem.*
   Nothing tied `f` inside the critical strip to its Dirichlet series outside
   it, so a discontinuous patchwork `f` could smuggle in an off-line "zero"
   with no Davenport–Heilbronn content.  `Differentiable ℂ f` restores the
   identity-theorem rigidity: conditions 1 and 2 now pin `f` uniquely.
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

/-- `f` is represented by the Davenport-Heilbronn Dirichlet series (which has
    real coefficients) on the half-plane `Re(z) > 1`. -/
def dh_series_rep (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 1 < z.re → HasSum (fun (n : ℕ) => (dh_coeff n : ℂ) * (n : ℂ) ^ (-z)) (f z)

/-- `f` satisfies the Davenport-Heilbronn functional equation, away from the
    poles of the two Gamma factors.  The `Complex.Gamma _ ≠ 0` guards exclude
    exactly the points where Mathlib's junk value `Gamma = 0` would make the
    unrestricted equation false (see the module docstring); everywhere else
    both sides are the honest completed function. -/
def dh_functional_eq (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, Complex.Gamma ((z + 1) / 2) ≠ 0 → Complex.Gamma ((1 - z + 1) / 2) ≠ 0 →
    dh_completed f z = dh_completed f (1 - z)

/-- The Davenport-Heilbronn theorem, as a statement:
    there exists an entire function matching the DH Dirichlet series (which
    has real coefficients) for Re(s) > 1, satisfying the functional equation,
    and having a zero off the critical line `Re(s) = 1/2`.

    Rung 3 Phase B is the (currently open) proof:
    `theorem davenport_heilbronn : davenport_heilbronn_statement`.
    Its analytic half — everything except the off-line zero — is
    kernel-checked as `dh_analytic_half` in `ZetaLean/DHAnalytic.lean`. -/
def davenport_heilbronn_statement : Prop :=
  ∃ (f : ℂ → ℂ) (s : ℂ),
    -- 0. f is entire (without this, conditions 1-2 would not pin f inside
    --    the critical strip and the off-line zero would carry no content)
    Differentiable ℂ f ∧
    -- 1. f is represented by the Davenport-Heilbronn Dirichlet series for Re(s) > 1
    dh_series_rep f ∧
    -- 2. f satisfies the functional equation
    dh_functional_eq f ∧
    -- 3. f has a zero at s
    f s = 0 ∧
    -- 4. s is off the critical line
    s.re ≠ 1/2

