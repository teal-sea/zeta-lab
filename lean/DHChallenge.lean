/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Advertised statements: certified zero-existence, and the analytic half of Davenport-Heilbronn

This module is the small, trusted surface a mathematical reader should audit.
It restates, self-containedly and over Mathlib alone, three results of the
Zeta Lab Davenport-Heilbronn development.

## Background

Davenport and Heilbronn (1936) exhibited a Dirichlet series with **real**
coefficients satisfying a Riemann-type functional equation which nevertheless
has zeros off the critical line.  It is the standard demonstration that a
functional equation of Riemann type, on its own, does not force the Riemann
Hypothesis.  The function is

```
DH(s) = (1 - iκ)/2 · L(s, χ) + (1 + iκ)/2 · L(s, χ⁻¹)
```

for a quartic Dirichlet character `χ` mod 5 and the constant `κ` below, which
is exactly the value that rotates the two conjugate root numbers onto each
other and so makes the Dirichlet coefficients real.

## The three advertised statements

**1. `exists_zero_of_norm_lt_on_sphere` — the minimum-modulus criterion.**
If an entire `f` has strictly smaller norm at the centre of a disk than the
bound it satisfies on the boundary sphere, then `f` has a zero in the closed
disk.  This is the bridge from *finite computation* to *existence*: the exact
location of a zero of an entire function cannot be certified by evaluating the
function anywhere, however precisely, but a strict inequality between one
central value and a boundary bound does certify that a zero is enclosed.  The
proof applies Mathlib's maximum-modulus principle to `1/f`; no argument
principle and no winding numbers are involved.

**2. `exists_zero_of_norm_lt_on_frontier` — the same, on any bounded open set.**
The disk is never needed.  For an axis-aligned open rectangle the frontier is
four segments, which is the shape interval arithmetic can actually discharge,
so this is the form a certified numerical search consumes.

**3. `dh_analytic_half` — the analytic half of the Davenport-Heilbronn theorem.**
There exists an entire function represented by the Davenport-Heilbronn
Dirichlet series on `Re z > 1` whose completion `(π/5)^(-(s+1)/2)·Γ((s+1)/2)·f(s)`
is symmetric under `s ↦ 1-s`.  The statement is existential in `f`, so it
carries its own non-vacuity and needs none of the character theory used to
build the witness.

## Scope: what is *not* claimed

**The Davenport-Heilbronn theorem itself is not proved here.**  Its full
statement additionally requires a zero `s` with `s.re ≠ 1/2`, and that
conjunct is absent from every statement below.  What is offered is the
analytic half together with a general criterion under which a finite,
certified evaluation would supply the missing half.  Discharging that
criterion for this function is a numerical obligation that this submission
does not carry, and no numerical enclosure for any zero of `DH` is asserted.

Every definition below is a verbatim copy of the corresponding definition in
the development, re-declared in the namespace `ZetaLean.PalomarDH` so that
this file depends on Mathlib alone.
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

/-! ### The advertised theorems -/

/-- **Minimum-modulus criterion.**  If an entire `f` has smaller norm at the
centre of a disk than anywhere on the boundary sphere, it has a zero in the
closed disk. -/
theorem exists_zero_of_norm_lt_on_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h1 : ‖f c‖ < ε) (h2 : ∀ z ∈ Metric.sphere c r, ε ≤ ‖f z‖) :
    ∃ z ∈ Metric.closedBall c r, f z = 0 := by
  sorry

/-- **Minimum-modulus criterion, general boundary version.**  If entire `f`
has smaller norm at a point of a bounded open `U` than anywhere on
`frontier U`, it has a zero in `closure U`. -/
theorem exists_zero_of_norm_lt_on_frontier {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {U : Set ℂ} (hUb : Bornology.IsBounded U) (hUo : IsOpen U)
    {c : ℂ} (hc : c ∈ U) {ε : ℝ}
    (h1 : ‖f c‖ < ε) (h2 : ∀ z ∈ frontier U, ε ≤ ‖f z‖) :
    ∃ z ∈ closure U, f z = 0 := by
  sorry

/-- **The analytic half of the Davenport-Heilbronn theorem.**  There is an
entire function represented by the Davenport-Heilbronn Dirichlet series on
`Re z > 1` and satisfying the functional equation.  The off-line zero, which
is the remaining conjunct of the full theorem, is **not** asserted. -/
theorem dh_analytic_half :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ dh_series_rep f ∧ dh_functional_eq f := by
  sorry

end ZetaLean.PalomarDH
