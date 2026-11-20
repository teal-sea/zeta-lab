module

/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
public import Mathlib
public import ZetaLean.HardyZ

@[expose] public section

/-!
# A socket for the 2026-11-20 claim of RH and GRH

On 2026-11-20 Levent Alpoge posted, at alpo.ge, a Lean archive that claims a proof of
the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
L-functions.  Its top file `lean/src/Main.lean` states five theorems: Mathlib's
`RiemannHypothesis`, and the four propositions defined in its
`lean/src/Statements.lean` (16 lines, importing only Mathlib; sha256
`79ef7ca776e42abe1f46caee13ea09bd19f1e2d0b1620d8d5d200258f33b47bf`).

This module is a socket for that claim.  It is not part of the claim and it is not an
endorsement of it.

* **Restated, not imported.**  The four `def`s below copy the four definitions of
  `Statements.lean` character for character into the namespace
  `ZetaLean.RiemannClaim`, where they are elaborated against this arm's own pinned
  Mathlib.  No file of the archive is imported, vendored or built here.
* **Their truth is not asserted here.**  This module postulates nothing.  Two helpers
  are unconditional and rest on Mathlib alone.  Every other theorem below takes the
  proposition it needs as an explicit hypothesis and derives a form that other work in
  this repository consumes: it is a theorem about an implication, and it says nothing
  about whether its hypothesis holds.  When this module was written the lab had seen
  no kernel accept the archive.
* **Written without a compiler.**  The proofs below were checked by reading Mathlib's
  and Lean's source at this arm's pin, not by running Lean.  Until a root build that
  includes this module has passed (`lake build` in `lean/`), its theorems are stated,
  not kernel-checked.
* **Discharge.**  If the five statements become theorems at this arm's pin, each
  conditional theorem below is discharged by one application:

  | hypothesis here                     | theorem of the archive's `Main.lean`  |
  |-------------------------------------|---------------------------------------|
  | `RiemannHypothesis`                 | `riemannHypothesis`                   |
  | `RiemannZetaZerosOnLine`            | `riemannZeta_eq_zero_re`              |
  | `DirichletLNonvanishingRightOfHalf` | `LFunction_ne_zero_of_half_lt_re`     |
  | `DirichletLZerosOnLine`             | `LFunction_eq_zero_re`                |
  | `PrimitiveDirichletLZerosOnLine`    | `LFunction_eq_zero_re_of_isPrimitive` |

  The archive states its propositions in the root namespace.  Elaborated against one
  Mathlib they and the restatements here unfold to the same terms, which is what lets
  the application type-check.  The archive pins Lean `v4.33.1` and Mathlib
  `0df444a360ea`; this arm pins Lean `v4.35.0-rc2` and Mathlib `065356127b1d`.  A
  verdict on the archive at its own pin is a statement about Mathlib's definitions at
  that pin, so the one-application discharge needs the five theorems transported to
  this arm's pin first.

## What is derived

* `riemannHypothesis_iff_riemannZetaZerosOnLine`: the archive's zeta statement is
  Mathlib's `RiemannHypothesis`, by unfolding.
* `dirichlet_nonvanishing`: the nonvanishing statement gives the `7/8` zero-free
  half-plane in the shape of `QRH125.dirichlet_nonvanishing`
  (`lean/qrh/QRHOpenAI.lean`); `dirichlet_nonvanishing_of_lt_re` is the same for every
  `θ ≥ 1/2`.
* `riemannZeta_ne_zero_of_dirichletLNonvanishing` and
  `riemannZeta_ne_zero_of_riemannHypothesis`: `riemannZeta s ≠ 0` for `1/2 < Re s`, from
  the modulus-one case and from `RiemannHypothesis` respectively.
* `hardyZ_eq_zero_of_riemannHypothesis`: under `RiemannHypothesis` every zero of
  `riemannZeta` with positive real part is `1/2 + i t` with `t` a zero of the lab's
  Hardy function `hardyZ` (`ZetaLean/HardyZ.lean`).
* `primitiveDirichletLZerosOnLine_of_dirichletLZerosOnLine`: the statement for all
  characters contains the statement for primitive ones.

The three zeta theorems carry no hypothesis `s ≠ 1`.  The zeta function has a pole at
`1`; Mathlib's `riemannZeta 1` is a value assigned there, and Mathlib's
`riemannZeta_one_ne_zero` shows that value is not zero.  So no zero of `riemannZeta` is
the point `1`, and at `s = 1` the two nonvanishing theorems restate that fact about the
assigned value: they say nothing there about the zeta function.

Two unconditional helpers serve them.  `ne_one_of_riemannZeta_eq_zero` is the remark
just made.  `not_trivialZero_of_re_pos` says that a point with positive real part is
not a trivial zero; the two theorems that start from `RiemannHypothesis` use it.
-/

namespace ZetaLean.RiemannClaim

/-! ### The four propositions of `Statements.lean`, restated -/

/-- `RiemannZetaZerosOnLine` of the archive's `Statements.lean`, restated: every zero of
`riemannZeta` other than the trivial zeros `-2 (n + 1)` and the point `1` has real part
`1/2`.  A proposition, not a theorem. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- `DirichletLNonvanishingRightOfHalf` of the archive's `Statements.lean`, restated: no
Dirichlet L-function vanishes at a point with real part above `1/2`, the pole of the
trivial character at `1` excepted.  A proposition, not a theorem. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- `DirichletLZerosOnLine` of the archive's `Statements.lean`, restated: every zero of a
Dirichlet L-function in the open critical strip has real part `1/2`.  A proposition, not
a theorem. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- `PrimitiveDirichletLZerosOnLine` of the archive's `Statements.lean`, restated:
`DirichletLZerosOnLine` for primitive characters only.  A proposition, not a theorem. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-! ### Two unconditional helpers -/

/-- A zero of `riemannZeta` is not the point `1`.  The zeta function has a pole at `1`;
Mathlib's `riemannZeta 1` is a value assigned there, and Mathlib's
`riemannZeta_one_ne_zero` shows that value is not zero.  Consumed by the three zeta
theorems below, which for this reason carry no hypothesis `s ≠ 1`. -/
theorem ne_one_of_riemannZeta_eq_zero {s : ℂ} (hz : riemannZeta s = 0) : s ≠ 1 :=
  fun h1 => riemannZeta_one_ne_zero ((congrArg riemannZeta h1).symm.trans hz)

/-- A point with positive real part is not a trivial zero `-2 (n + 1)`, whose real part
is negative.  Consumed by the two theorems below that start from `RiemannHypothesis`,
which use it to meet the second hypothesis of that proposition. -/
theorem not_trivialZero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  rintro ⟨n, hn⟩
  have hre : s.re = (-2 * ((n : ℂ) + 1)).re := congrArg Complex.re hn
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat] at hre
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith only [hs, hre, hn0]

/-! ### Conditional consequences -/

/-- The archive's `RiemannZetaZerosOnLine` is Mathlib's `RiemannHypothesis` at this arm's
pin: the two definitions unfold to the same proposition. -/
theorem riemannHypothesis_iff_riemannZetaZerosOnLine :
    RiemannHypothesis ↔ RiemannZetaZerosOnLine :=
  Iff.rfl

/-- If no Dirichlet L-function vanishes to the right of `1/2`, none vanishes to the right
of any `θ ≥ 1/2`.  The pole exception is written `¬ (χ = 1 ∧ s = 1)`, the convention of
`QRH125.dirichlet_nonvanishing` in `lean/qrh/QRHOpenAI.lean`. -/
theorem dirichlet_nonvanishing_of_lt_re (h : DirichletLNonvanishingRightOfHalf)
    {θ : ℝ} (hθ : 1 / 2 ≤ θ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : θ < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  h q χ s (lt_of_le_of_lt hθ hs) (not_and_or.mp hpole)

/-- The `7/8` zero-free half-plane, as a consequence of the claimed nonvanishing to the
right of `1/2`.  After the hypothesis `h` the signature is that of
`QRH125.dirichlet_nonvanishing` in `lean/qrh/QRHOpenAI.lean`, the form in which this lab
consumes OpenAI's quasi-Riemann theorem.  That package has its own toolchain pin, so the
match is one of shape: the same binders, the same pole exception, the same conclusion. -/
theorem dirichlet_nonvanishing (h : DirichletLNonvanishingRightOfHalf)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_nonvanishing_of_lt_re h (by norm_num : (1 / 2 : ℝ) ≤ 7 / 8) χ hs hpole

/-- The modulus-one case of the claimed nonvanishing: `riemannZeta` has no zero with real
part above `1/2`.  Mathlib's `DirichletCharacter.LFunction_modOne_eq` identifies the
L-function of the character modulo `1` with `riemannZeta`.  The hypothesis `h` is silent
at `s = 1`, which its pole exception leaves out; there the conclusion is Mathlib's
`riemannZeta_one_ne_zero`, reached through `ne_one_of_riemannZeta_eq_zero`. -/
theorem riemannZeta_ne_zero_of_dirichletLNonvanishing
    (h : DirichletLNonvanishingRightOfHalf) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := ne_one_of_riemannZeta_eq_zero hz
  have key : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 :=
    h 1 1 s hs (Or.inr hs1)
  have e : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s :=
    congrFun (DirichletCharacter.LFunction_modOne_eq (χ := 1)) s
  exact key (e.trans hz)

/-- Under `RiemannHypothesis`, `riemannZeta` has no zero with real part above `1/2`.  At
`s = 1` the conclusion is Mathlib's `riemannZeta_one_ne_zero`, a fact about the value
Mathlib assigns at the pole, reached through `ne_one_of_riemannZeta_eq_zero`. -/
theorem riemannZeta_ne_zero_of_riemannHypothesis (h : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := by linarith only [hs]
  have hs1 : s ≠ 1 := ne_one_of_riemannZeta_eq_zero hz
  have hre : s.re = 1 / 2 := h s hz (not_trivialZero_of_re_pos hpos) hs1
  linarith only [hs, hre]

/-- Under `RiemannHypothesis`, every zero `s` of `riemannZeta` with positive real part is
`1/2 + i t` with `t = s.im`, and `t` is a zero of the lab's Hardy function `hardyZ`
(`ZetaLean/HardyZ.lean`, through `hardyZ_zero_iff`).  So every nontrivial zero is a real
zero of `Z`.  The point `1` needs no exception: it is not a zero of `riemannZeta`, by
`ne_one_of_riemannZeta_eq_zero`. -/
theorem hardyZ_eq_zero_of_riemannHypothesis (h : RiemannHypothesis) {s : ℂ}
    (hz : riemannZeta s = 0) (hpos : 0 < s.re) :
    s = 1 / 2 + (s.im : ℂ) * Complex.I ∧ hardyZ s.im = 0 := by
  have hs1 : s ≠ 1 := ne_one_of_riemannZeta_eq_zero hz
  have hre : s.re = 1 / 2 := h s hz (not_trivialZero_of_re_pos hpos) hs1
  have hcast : ((s.re : ℝ) : ℂ) = 1 / 2 := by
    rewrite [hre, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rfl
  have hs_eq : s = 1 / 2 + (s.im : ℂ) * Complex.I := by
    calc s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
      _ = 1 / 2 + (s.im : ℂ) * Complex.I := by rw [hcast]
  exact ⟨hs_eq, (hardyZ_zero_iff s.im).mpr ((congrArg riemannZeta hs_eq).symm.trans hz)⟩

/-- The claimed statement for all Dirichlet characters contains the claimed statement for
primitive characters: the primitivity hypothesis is dropped. -/
theorem primitiveDirichletLZerosOnLine_of_dirichletLZerosOnLine
    (h : DirichletLZerosOnLine) : PrimitiveDirichletLZerosOnLine := by
  intro N inst χ _ s h0 h1 hz
  exact @h N inst χ s h0 h1 hz

end ZetaLean.RiemannClaim
