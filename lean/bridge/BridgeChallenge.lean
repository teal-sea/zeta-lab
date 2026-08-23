/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Mathlib

/-!
# Advertised statement: the seven-point simple-zero bound, conditional on its certificate

This module is the small, trusted surface a mathematical reader should audit.
It restates, self-containedly and over Mathlib alone, the principal theorems of
the Zeta Lab bridge development.  All four declarations advertised below are
compared by Comparator against the proof development.

## What the theorems say

Let `N(T₁,T₂)` count the nontrivial zeros of `riemannZeta` with ordinate in
`(T₁,T₂]`, with multiplicity, and `N₀ˢ(T₁,T₂)` the *simple* zeros among them
that lie on the critical line.  The Lean development accompanying
arXiv:2608.13637 proves, unconditionally, that for every `ε > 0` and all large
`T`,

```
(H − ε) · N(T,2T) ≤ N₀ˢ(T,2T),      H = 3/2 − (1/√2) cot(1/√2) = 0.6725007036…
```

Ainta refines `H` by carrying a spectral defect through that argument and
bounding it, block by block, through a local inequality on seven points.  The
refinement is what is advertised here, in the parametric form the Lean proof
actually establishes:

```
(Φ(c,m,p) − ε) · N(T,2T) ≤ N₀ˢ(T,2T),
Φ(c,m,p) = (H − 6(m−1)/(pm)) / (1 − c(m−6)/m).
```

The refinement is **conditional**.  Its hypothesis `hCert` says that the
seven-point functional `F6` below is at least `c` at every vector of six
nonnegative gaps.  That inequality is not proved here and is not a theorem of
Lean; see the docstring of `seven_point_bound`.  Two rational side conditions,
`c(m−6) ≤ 1` and `7 ≤ m`, `0 < p`, `0 < c`, are hypotheses too, and are
discharged by `norm_num` in the three instantiated statements.

## Scope: what is *not* claimed

**Nothing here bears on the Riemann Hypothesis.**  The conclusion is a lower
bound on a proportion of zeros, valid whether or not RH holds.

**The base constant `H` is not this work.**  It is the theorem of the
development this one extends, and it appears here only inside `Φ`.

**The seven-point inequality is assumed, not proved.**  Every instantiated
statement below carries it as a named hypothesis with the numbers written out,
so no reading of these statements can take them as unconditional.

## The four advertised declarations

`seven_point_bound` is the parametric theorem.  `seven_point_bound_paper`
instantiates it at Ainta's published `(c,m,p) = (19/5000, 269, 3000)` and
recovers the paper's constant `(1345000 H − 2680)/1340003` exactly.
`seven_point_bound_lab` and `seven_point_bound_lab_ratio` instantiate it at
this laboratory's own verified parameters `(34697/10⁷, 294, 3400)`, where the
constant is `(520625000 H − 915625)/518855453 = 0.673029553…`; the second of
the two states the same conclusion as a bound on the ratio `N₀ˢ/N`, which is
the form the result is usually quoted in.

Every definition below is a verbatim copy of the corresponding definition in
the proof development — the five counting definitions from the dependency
`anthropics/zeta-23-lean`, the kernel and functional definitions from
`Zeta23Ext/Bridge/Defs.lean` — re-declared here in the namespace
`Zeta23Ext.Palomar` so that this file depends on Mathlib alone.  The one
exception is `H`, which the development takes from the dependency as `HD 1`
and which is written here in the closed form the dependency proves equal to it
(`HD_one`), so that the constant can be read off this file without trusting
any other project.

## The four `sorry`s below are deliberate

The Palomar format requires the Challenge module to *state* its claims without
proving them.  `BridgeSolution.lean` proves the same four statements from the
development, and Comparator checks that the two match.  The proof development
is sorry-free; these placeholders are not uncertified steps in it.
-/

open scoped BigOperators

noncomputable section

namespace Zeta23Ext.Palomar

/-! ### Counting the zeros of ζ

Verbatim from the dependency's `Zeta23/Statement.lean`, which defines them
directly against Mathlib. -/

/-- `ρ` is a nontrivial zero of `ζ`: a zero in the open critical strip. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- `m_ρ`, the multiplicity of `ρ`: the order of vanishing of `ζ` at `ρ`, via
Mathlib's `analyticOrderAt`. -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- `{ρ nontrivial zero : T₁ < γ ≤ T₂}`, with `γ = Im ρ`. -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- `N(T₁,T₂)`: the number of nontrivial zeros with `T₁ < γ ≤ T₂`, counted with
multiplicity. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- `N₀ˢ(T₁,T₂)`: the number of `ρ` with `T₁ < γ ≤ T₂`, `β = 1/2` and `m_ρ = 1`,
that is the simple zeros on the critical line in the window. -/
def N0simple (T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-! ### The Montgomery-Taylor overlap kernel -/

/-- `K(x) := ∫_{-1/2}^{1/2} cos(√2 t) cos(2π x t) dt`. -/
def Kfun (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)

/-- `k(x) := K(x)/K(0)`, the normalised overlap kernel. -/
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

/-- `w(x) := k(x)²`, the overlap weight. -/
def wfun (x : ℝ) : ℝ := kfun x ^ 2

/-! ### The seven-point functional -/

/-- The seven ordered points `y₀ = 0`, `yᵢ = g₀ + ⋯ + g_{i−1}` determined by six
nonnegative gaps `g`. -/
def pts (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ j : Fin 6, if (j : ℕ) < (i : ℕ) then g j else 0

/-- `F6(g) := (1/p) Σ gᵢ + Σ_{i<j} (2/(7 − (j−i))) w(y_j − y_i)`: the pressure
term at denominator `p` plus the twenty-one pairwise overlap weights of the
seven points `y` determined by `g`.  This is the functional whose lower bound is
the computer-assisted input of the whole argument. -/
def F6 (p : ℕ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin 7, ∑ j : Fin 7,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((7 : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (pts g j - pts g i)
        else 0

/-! ### The two constants -/

/-- `H = 3/2 − (1/√2) cot(1/√2) = 0.6725007036794116…`, the constant of the base
theorem this work refines.  In the development it is the dependency's `HD 1`;
the closed form written here is what the dependency's `HD_one` proves it equals,
and it is written out so that this file needs no other project to be read. -/
def H : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)

/-- `Φ(c,m,p) := (H − 6(m−1)/(pm)) / (1 − c(m−6)/m)`, the constant the refinement
produces from a certificate constant `c`, a block length `m` and a pressure
denominator `p`. -/
def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (H - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)

/-! ### The advertised theorems -/

/-- **The seven-point simple-zero bound, conditional on its certificate.**  For
every `c > 0`, `m ≥ 7`, `p > 0` with `c(m−6) ≤ 1`: if the seven-point functional
`F6 p` is bounded below by `c` at every vector of six nonnegative gaps, then for
every `ε > 0` and all large `T`,

`(Φ(c,m,p) − ε) · N(T,2T) ≤ N₀ˢ(T,2T)`.

**`hCert` is a hypothesis, and is not a Lean fact.**  It is the seven-point
inequality of Ainta's Proposition 4.1.  What is known about it is that an
interval-arithmetic program written in Arb accepts it — at `(c, p) = (19/5000,
3000)` in the published run at `github.com/ainta/zeta-simple-zeros`, and at
`(34697/10⁷, 3400)` in this laboratory's own run, both reproduced and recorded
under `hunts/ainta_seven_point` in the submitted repository.  A verifier's
acceptance is not a kernel-checked proof, and no claim is made here that it is.
The hypothesis is stated in the theorem rather than assumed as an axiom exactly
so that this distinction survives every way of quoting the result.

`hA0 : c(m−6) ≤ 1` is a rational side condition on the parameters, not a
numerical input; `7 ≤ m`, `0 < p`, `0 < c` likewise.  All four are discharged by
`norm_num` in the instantiated statements below.

Nothing here bears on the Riemann Hypothesis. -/
theorem seven_point_bound (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **At Ainta's published parameters.**  With `c = 19/5000`, `m = 269`,
`p = 3000` the side conditions hold and the constant is the paper's
`(1345000 H − 2680)/1340003 = 0.6730085279277797…`.

`hCert` is the same hypothesis as in `seven_point_bound`, with the published
numbers written out; it is the inequality the Arb verifier accepts, not a
theorem of Lean. -/
theorem seven_point_bound_paper
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * H - 2680) / 1340003 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **At this laboratory's own parameters.**  A finer pressure sweep puts the
seven-point peak at `p = 3400`, where the verifier accepts `c = 34697/10⁷` and
refuses `34701/10⁷`; the cap `c(m−6) ≤ 1` then gives `m = 294`.  The constant is
`(520625000 H − 915625)/518855453 = 0.6730295534796928…`.

`hCert` is again the seven-point inequality, at those numbers, and again is an
assumption: what changes between this statement and `seven_point_bound_paper`
is which certificate is assumed, not what has been proved about ζ. -/
theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * H - 915625) / 518855453 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  sorry

/-- **The same bound as a proportion.**  Under the same hypothesis, for every
`ε > 0` and all large `T`,

`N₀ˢ(T,2T) / N(T,2T) ≥ 0.6730295534796928… − ε`,

which is the form the result is usually quoted in.  There is no positivity
guard on the denominator: `N(T,2T) → ∞`, so the inequality is asserted at every
sufficiently large `T` outright. -/
theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * H - 915625) / 518855453 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  sorry

end Zeta23Ext.Palomar
