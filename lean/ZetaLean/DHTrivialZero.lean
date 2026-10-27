module

/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
public import Mathlib
public import ZetaLean.DHAnalytic

@[expose] public section

/-!
# `davenport_heilbronn_statement` is met by a trivial zero

`davenport_heilbronn_statement` (`ZetaLean/DavenportHeilbronn.lean`) asks for
an entire `f` with the Davenport-Heilbronn series on `Re z > 1`, the
functional equation, and a zero `s` with `s.re ≠ 1/2`.  It bounds `s` away
from the critical line and nowhere else, so a *trivial* zero satisfies it.
`DH = a·L(s, χ) + b·L(s, χ⁻¹)` combines the L-functions of two odd primitive
characters mod 5, and each vanishes at `s = -1, -3, -5, …` (Mathlib's
`DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one`).  So `DH (-1) = 0`,
`(-1 : ℂ).re = -1 ≠ 1/2`, and the statement follows from the analytic half
(`dh_analytic_half`) and this one lemma, with no numerical site at all.

The statement therefore does not separate `DH` from `ζ`: the analogous
statement for `riemannZeta` holds at its trivial zero `s = -2`
(`riemannZeta_neg_two_mul_nat_add_one`).  It is the third defect of the same
kind in this statement: the module docstring of `DavenportHeilbronn.lean`
records the first two.  It was found by the adversarial review of PR #353 on
2026-10-26.

**Where the content lives.**  The theorems that carry Davenport and
Heilbronn's point, a zero off the line *inside the critical strip* for a
function with zeta's kind of series and functional equation, are, in
`ZetaLean.DH.Rung3Assembly.Plan2` (hunt #145,
`hunts/rung3_ball_production/RESULTS.md`, outside this package because its
215 site oleans total about 15 GB):

* `dh_separation_hundred`: below height 100, `DH` has a zero with
  `0 < s.re < 1`, `0 < s.im ≤ 100` and `s.re ≠ 1/2`, while every zero of
  Mathlib's `riemannZeta` there has real part `1/2` (hunt #137);
* `dh_zero_located`: a zero of `DH` in the closed square of half-width `3/64`
  about `808517/10^6 + (21424837/250000)·i`, so with real part at least
  `0.761642`;

read together with `dh_analytic_half` (`ZetaLean/DHAnalytic.lean`), which
says that this `DH` is entire, has the series and satisfies the functional
equation.  Their grade is kernel-checked, pending external verification.

`davenport_heilbronn_statement` itself is left unchanged: it is in the import
closure of those 215 site oleans, which were compiled against it.
-/

open Complex DirichletCharacter

namespace ZetaLean.DH

/-- `DH` vanishes at the trivial zero `s = -1`, since both of its characters
are odd. -/
theorem DH_neg_one : DH (-1) = 0 := by
  have h1 := dhChar_odd.LFunction_neg_two_mul_nat_sub_one 0
  have h2 := dhChar_inv_odd.LFunction_neg_two_mul_nat_sub_one 0
  simp only [Nat.cast_zero, mul_zero, neg_zero, zero_sub] at h1 h2
  simp [DH, h1, h2]

/-- Every conjunct of `davenport_heilbronn_statement`, for `f = DH` and the
trivial zero `s = -1`. -/
theorem dh_trivial_zero_witness :
    Differentiable ℂ DH ∧ dh_series_rep DH ∧ dh_functional_eq DH ∧
      DH (-1) = 0 ∧ (-1 : ℂ).re ≠ 1 / 2 :=
  ⟨DH_differentiable, DH_series_rep, DH_functional_eq, DH_neg_one, by norm_num⟩

/-- `davenport_heilbronn_statement` holds with the witness `s = -1`, a trivial
zero; this is why the statement is weak.  See the module docstring for the
theorems that carry the content. -/
theorem davenport_heilbronn_statement_of_trivial_zero :
    davenport_heilbronn_statement :=
  ⟨DH, -1, dh_trivial_zero_witness⟩

end ZetaLean.DH
