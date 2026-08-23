/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Mathlib

/-!
# Advertised statement: the `n`-point simple-zero bound, and its eight-point instance

This module is the small, trusted surface a mathematical reader should audit.
It restates, self-containedly and over Mathlib alone, the principal theorems of
the `n`-point layer of the Zeta Lab bridge development.  All three declarations
advertised below are compared by Comparator against the proof development.

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
bounding it, block by block, through a local inequality on **seven** points.
What is advertised here is that refinement carried out for **`n` points**, for
every `n ≥ 2` at once:

```
(Φₙ(c,m,p) − ε) · N(T,2T) ≤ N₀ˢ(T,2T),
Φₙ(c,m,p) = (H − (n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m).
```

The two numerals of the seven-point argument are the two the generalisation
resolves: the `6` in the numerator is the number of times a single gap is
charged when the pressure term is summed over the windows of a block, which is
`n−1`; and the `m−6` in the denominator is the number of windows of `n`
consecutive points in a block of `m`, which is `m−(n−1)`.  At `n = 7` the
statement is Ainta's, with `Φ₇ = Φ` and the `n`-point functional `F 7 p` equal
to his `F6 p` definitionally.

## Scope: what is *not* claimed

**Nothing here bears on the Riemann Hypothesis.**  The conclusion is a lower
bound on a proportion of zeros, valid whether or not RH holds.

**The base constant `H` is not this work.**  It is the theorem of the
development this one extends, and it appears here only inside `Φₙ`.

**The `n`-point inequality is assumed, not proved.**  Every statement below
carries it as a named hypothesis `hCert`, and the two instantiated statements
write its numbers out, so no reading of these statements can take them as
unconditional.

**The mathematics of the seven-point case is Ainta's, not this laboratory's.**
The generalisation in `n`, its Lean proof and the eight-point certificate are
this laboratory's.

## The three advertised declarations

`n_point_bound` is the parametric theorem: `n` points, a certificate constant
`c`, a block length `m` and a pressure denominator `p`, with the side
conditions `2 ≤ n`, `n ≤ m`, `0 < p`, `0 < c` and the block cap
`c(m−(n−1)) ≤ 1`.

`eight_point_bound` and `eight_point_bound_ratio` instantiate it at `n = 8` and
at the eight-point certificate this laboratory's own interval-arithmetic run
accepts, `c = 41763/10⁷` at `p = 3200`.  The cap `c(m−7) ≤ 1` gives
`m ≤ 7 + ⌊10⁷/41763⌋ = 246`, and at `m = 246` the constant is
`(2460000000 H − 5359375)/2450018643 = 0.67305298298962888…`, against
`0.67302955347969271…` at this laboratory's best seven-point parameters and
`0.67300852792777976…` at Ainta's published ones.  The second of the two states
the same conclusion as a bound on the ratio `N₀ˢ/N`, which is the form the
result is usually quoted in.

Every definition below is a verbatim copy of the corresponding definition in
the proof development — the five counting definitions from the dependency
`anthropics/zeta-23-lean`, the kernel and `n`-point definitions from
`Zeta23Ext/Bridge/Defs.lean` — re-declared here in the namespace
`Zeta23Ext.PalomarEight` so that this file depends on Mathlib alone.  The one
exception is `H`, which the development takes from the dependency as `HD 1`
and which is written here in the closed form the dependency proves equal to it
(`HD_one`), so that the constant can be read off this file without trusting
any other project.

## The three `sorry`s below are deliberate

The Palomar format requires the Challenge module to *state* its claims without
proving them.  `EightSolution.lean` proves the same three statements from the
development, and Comparator checks that the two match.  The proof development
is sorry-free; these placeholders are not uncertified steps in it.
-/

open scoped BigOperators

noncomputable section

namespace Zeta23Ext.PalomarEight

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

/-! ### The `n`-point functional -/

/-- The `n` ordered points `y₀ = 0`, `yᵢ = g₀ + ⋯ + g_{i−1}` determined by `n−1`
nonnegative gaps `g`. -/
def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0

/-- `F n p (g) := (1/p) Σ gᵢ + Σ_{s=1}^{n−1} (2/(n−s)) Σ_{i=1}^{n−s} w(gᵢ + ⋯ + g_{i+s−1})`,
the `n`-point functional at pressure denominator `p`, written as a sum over the
`n(n−1)/2` pairs `i < j` of the `n` points with coefficient `2/(n − (j−i))`.
This is the functional whose lower bound is the computer-assisted input of the
whole argument; `F 7 p` is Ainta's `F6 p`, definitionally. -/
def F (n p : ℕ) (g : Fin (n - 1) → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((n : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (ptsN n g j - ptsN n g i)
        else 0

/-! ### The two constants -/

/-- `H = 3/2 − (1/√2) cot(1/√2) = 0.6725007036794116…`, the constant of the base
theorem this work refines.  In the development it is the dependency's `HD 1`;
the closed form written here is what the dependency's `HD_one` proves it equals,
and it is written out so that this file needs no other project to be read. -/
def H : ℝ := 3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)

/-- `Φₙ(n,c,m,p) := (H − (n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m)`, the constant the
refinement produces from a point count `n`, a certificate constant `c`, a block
length `m` and a pressure denominator `p`. -/
def Phi_n (n : ℕ) (c : ℝ) (m p : ℕ) : ℝ :=
  (H - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m))
    / (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m)

/-! ### The advertised theorems -/

/-- **The `n`-point simple-zero bound, conditional on its certificate.**  For
every `n ≥ 2`, `c > 0`, `m ≥ n`, `p > 0` with `c(m−(n−1)) ≤ 1`: if the `n`-point
functional `F n p` is bounded below by `c` at every vector of `n−1` nonnegative
gaps, then for every `ε > 0` and all large `T`,

`(Φₙ(n,c,m,p) − ε) · N(T,2T) ≤ N₀ˢ(T,2T)`.

**`hCert` is a hypothesis, and is not a Lean fact.**  At `n = 7` it is the
seven-point inequality of Ainta's Proposition 4.1.  What is known about it is
that an interval-arithmetic program written in Arb accepts it — at
`(c, p) = (19/5000, 3000)` in the published run at
`github.com/ainta/zeta-simple-zeros`, at `(34697/10⁷, 3400)` in this
laboratory's own seven-point run, and at `(41763/10⁷, 3200)` for `n = 8` in
this laboratory's eight-point run, all recorded under
`hunts/ainta_seven_point` in the submitted repository.  A verifier's acceptance
is not a kernel-checked proof, and no claim is made here that it is.  The
hypothesis is stated in the theorem rather than assumed as an axiom exactly so
that this distinction survives every way of quoting the result.

`hA0 : c(m−(n−1)) ≤ 1` is a rational side condition on the parameters, not a
numerical input; `2 ≤ n`, `n ≤ m`, `0 < p`, `0 < c` likewise.  All five are
discharged by `norm_num` in the instantiated statements below.

Nothing here bears on the Riemann Hypothesis. -/
theorem n_point_bound (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_n n c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-- **At eight points, and at this laboratory's accepted eight-point
certificate.**  A generalisation of Ainta's published verifier to `n` points,
validated first by reproducing his seven-point run bit for bit, accepts
`41763/10⁷ ≤ F 8 3200 g` at every vector of seven nonnegative gaps: 64 of 64
shards, 6 504 134 nodes, with the minimiser the palindrome
`(1.046, 1.989, 1.987, 1.042, 1.987, 1.989, 1.046)` and Arb at the argmin giving
`0.0041763 ≤ inf F 8 3200 ≤ 0.0041773221`.  The cap `c(m−7) ≤ 1` gives
`m ≤ 7 + ⌊10⁷/41763⌋ = 246`, and at `m = 246` the constant is

`(2460000000 H − 5359375)/2450018643 = 0.67305298298962888…`,

against `0.67302955347969271…` at this laboratory's best seven-point parameters.

`hCert` is again an assumption and not a theorem of Lean: what changes between
this statement and the seven-point one is which certificate is assumed and at
how many points, not what has been proved about ζ. -/
theorem eight_point_bound
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * H - 5359375) / 2450018643 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  sorry

/-- **The eight-point bound as a proportion.**  Under the same hypothesis, for
every `ε > 0` and all large `T`,

`N₀ˢ(T,2T) / N(T,2T) ≥ 0.67305298298962888… − ε`,

which is the form the result is usually quoted in.  There is no positivity
guard on the denominator: `N(T,2T) → ∞`, so the inequality is asserted at every
sufficiently large `T` outright. -/
theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * H - 5359375) / 2450018643 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  sorry

end Zeta23Ext.PalomarEight
