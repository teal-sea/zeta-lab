/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Mathlib

/-!
# Advertised statements: the `n`-point simple-zero bound and three instances of it

Let `N(T₁,T₂)` count the nontrivial zeros of `riemannZeta` with ordinate in
`(T₁,T₂]`, with multiplicity, and `N₀ˢ(T₁,T₂)` the *simple* zeros among them on
the critical line.  The Lean development accompanying arXiv:2608.13637 proves,
unconditionally, that for every `ε > 0` and all large `T`,

```
(H − ε) · N(T,2T) ≤ N₀ˢ(T,2T),      H = 3/2 − (1/√2) cot(1/√2) = 0.6725007036…
```

Ainta refines `H` by carrying a spectral defect through that argument and
bounding it block by block through a local inequality on seven points.  What is
advertised here is that refinement carried out for `n` points, for every `n ≥ 2`
at once, together with three instances of it:

```
(Φₙ(c,m,p) − ε) · N(T,2T) ≤ N₀ˢ(T,2T),
Φₙ(c,m,p) = (H − (n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m).
```

The two numerals of the seven-point argument are the two the generalisation
resolves: the `6` in the numerator is the number of times a single gap is
charged when the pressure term is summed over the windows of a block, which is
`n−1`; and the `m−6` in the denominator is the number of windows of `n`
consecutive points in a block of `m`, which is `m−(n−1)`.  At `n = 7` the
statement is Ainta's.

## Which statements are conditional, and which are not

`n_point_bound` and the two eight-point statements carry the finite inequality
as a named hypothesis `hCert`.  It is not a theorem of Lean; what is known about
it at `n = 8` is that an interval-arithmetic program accepts it.

The two three-point statements and the four-point statement carry **no
hypothesis**.  Their certificates are proved inside Lean.  At three points,
`1345/10⁶ ≤ F 3 3000 g` at every pair of nonnegative gaps is proved inside Lean
from an explicit enclosure of the kernel, so the `n = 3` instance of
`n_point_bound` is unconditional.  Its constant

```
Φ₃ = (149000000 H − 99200)/148800133 = 0.67273733450380945032…
```

exceeds `H = 0.67250070367941164573…` by `2.3663·10⁻⁴`, so those two statements are
an unconditional improvement, for Mathlib's `riemannZeta`, of the Theorem D the
pinned dependency proves.

At four points, `2310/10⁶ ≤ F 4 2500 g` at every triple of nonnegative gaps is
also proved inside Lean.  The resulting unconditional constant is

```
Φ₄ = (906250 H − 1085)/904171 = 0.67284701976668882760…
```

## Scope: what is *not* claimed

**Nothing here bears on the Riemann Hypothesis.**  The conclusion is a lower
bound on a proportion of zeros, valid whether or not RH holds.

**The base constant `H` is not this work.**  It is the theorem of the
development this one extends, and appears here only inside `Φₙ`.

**The mathematics of the seven-point case is Ainta's.**  The generalisation in
`n`, its Lean proof, the eight-point certificate and the three- and four-point
enclosures are this laboratory's.

## The definitions

Every definition below is a verbatim copy of the corresponding definition in the
proof development — the five counting definitions from the dependency
`anthropics/zeta-23-lean`, the kernel and `n`-point definitions from
`Zeta23Ext/Bridge/Defs.lean` — re-declared in the namespace
`Zeta23Ext.PalomarV2` so that this file depends on Mathlib alone.  The one
exception is `H`, which the development takes from the dependency as `HD 1` and
which is written here in the closed form the dependency's `HD_one` proves it
equals.

## The seven `sorry`s below are deliberate

The Palomar format requires the Challenge module to *state* its claims without
proving them.  `V2Solution.lean` proves the same seven statements from the
development, and Comparator checks that the two match.  The proof development is
sorry-free; these placeholders are not uncertified steps in it.
-/

open scoped BigOperators

noncomputable section

namespace Zeta23Ext.PalomarV2

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
This is the functional whose lower bound is the finite input of the whole
argument; `F 7 p` is Ainta's `F6 p`, definitionally. -/
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

/-! ### The parametric theorem, conditional on its certificate -/

/-- **The `n`-point simple-zero bound, conditional on its certificate.**  For
every `n ≥ 2`, `c > 0`, `m ≥ n`, `p > 0` with `c(m−(n−1)) ≤ 1`: if the `n`-point
functional `F n p` is bounded below by `c` at every vector of `n−1` nonnegative
gaps, then for every `ε > 0` and all large `T`,

`(Φₙ(n,c,m,p) − ε) · N(T,2T) ≤ N₀ˢ(T,2T)`.

**`hCert` is a hypothesis, and is not a Lean fact.**  At `n = 7` it is the
seven-point inequality of Ainta's Proposition 4.1.  What is known about it in
general is that an interval-arithmetic program written in Arb accepts it: at
`(c, p) = (19/5000, 3000)` in the published run at
`github.com/ainta/zeta-simple-zeros`, at `(34697/10⁷, 3400)` in this
laboratory's own seven-point run, and at `(41763/10⁷, 3200)` for `n = 8`.  A
verifier's acceptance is not a kernel-checked proof and no claim is made here
that it is.  The hypothesis is stated in the theorem rather than assumed as an
axiom exactly so that this distinction survives every way of quoting the result.
At `n = 3` it is not assumed at all: see `three_point_bound`.

`hA0 : c(m−(n−1)) ≤ 1` is a rational side condition on the parameters, not a
numerical input; `2 ≤ n`, `n ≤ m`, `0 < p`, `0 < c` likewise.  All five are
discharged by `norm_num` in the instances below.

Nothing here bears on the Riemann Hypothesis. -/
theorem n_point_bound (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_n n c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  sorry

/-! ### The eight-point instance, still conditional -/

/-- **At eight points, and at this laboratory's accepted eight-point
certificate.**  A generalisation of Ainta's published verifier to `n` points,
validated first by reproducing his seven-point run node for node without
finding a defect, accepts
`41763/10⁷ ≤ F 8 3200 g` at every vector of seven nonnegative gaps: 64 of 64
shards, 6 504 134 nodes, with the minimiser the palindrome
`(1.046, 1.989, 1.987, 1.042, 1.987, 1.989, 1.046)`.  The cap `c(m−7) ≤ 1` gives
`m ≤ 7 + ⌊10⁷/41763⌋ = 246`, and at `m = 246` the constant is

`(2460000000 H − 5359375)/2450018643 = 0.67305298298962888…`.

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

which is the form the result is usually quoted in.  There is no positivity guard
on the denominator: `N(T,2T) → ∞`, so the inequality is asserted at every
sufficiently large `T` outright. -/
theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * H - 5359375) / 2450018643 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  sorry

/-! ### The three-point instance, unconditional -/

/-- **At three points, with the certificate proved rather than assumed.**  The
`n = 3` instance of `n_point_bound` at `c = 1345/10⁶`, `p = 3000`, `m = 745`.
Its hypothesis `hCert` reads `1345/10⁶ ≤ F 3 3000 g` at every pair of
nonnegative gaps, and that inequality is a theorem of Lean in the development:
`w` is enclosed from a twelve-term Taylor bound on `cos` and `sin` and the
closed form of `K`, and the quarter-plane of the two gaps is covered by 368
interval cell lemmas applied 1515 times over 487 leaves.  **Nothing is assumed
here**, so this statement carries no hypothesis at all.

The cap `c(m−2) ≤ 1` gives `m ≤ 2 + ⌊10⁶/1345⌋ = 745`, and at `m = 745` the
constant is

`(149000000 H − 99200)/148800133 = 0.67273733450380945032…`,

which exceeds `H = 0.67250070367941164573…` by `2.3663·10⁻⁴`.  For Mathlib's
`riemannZeta` this is an unconditional improvement of the Theorem D of the
development this one extends.

Nothing here bears on the Riemann Hypothesis: the conclusion is a lower bound on
a proportion of zeros and holds whether or not RH does. -/
theorem three_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((149000000 * H - 99200) / 148800133 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  sorry

/-- **The three-point bound as a proportion, unconditional.**  For every `ε > 0`
and all large `T`,

`N₀ˢ(T,2T) / N(T,2T) ≥ 0.67273733450380945032… − ε`,

with no hypothesis and no positivity guard on the denominator. -/
theorem three_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (149000000 * H - 99200) / 148800133 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  sorry

/-! ### The four-point instance, unconditional -/

/-- **At four points, with the certificate proved rather than assumed.**  The
certificate `2310/10⁶ ≤ F 4 2500 g` at every triple of nonnegative gaps is a
theorem of Lean in the development.  Thus this statement has no hypothesis.

For every `ε > 0` and all large `T`,

`((906250 H − 1085)/904171 − ε) · N(T,2T) ≤ N₀ˢ(T,2T)`,

with constant `0.67284701976668882760…`. -/
theorem four_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((906250 * H - 1085) / 904171 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  sorry

/-- **The four-point bound as a proportion, unconditional.**  For every
`ε > 0` and all large `T`,

`N₀ˢ(T,2T) / N(T,2T) ≥ 0.67284701976668882760… − ε`,

with no hypothesis and no positivity guard on the denominator. -/
theorem four_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (906250 * H - 1085) / 904171 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  sorry

end Zeta23Ext.PalomarV2
