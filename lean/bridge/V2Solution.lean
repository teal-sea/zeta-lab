/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Mathlib
import Zeta23Ext.Bridge.Main
import ThreePoint.Main

/-!
# Proved solution

This module imports the bridge development and the three-point certificate, and
proves the five statements advertised in `V2Challenge.lean`.

Following the Palomar layout this module does **not** import `V2Challenge`:
the two modules independently declare the same names, and Comparator checks
that each compared declaration has the same statement in both.  The definitions
below are therefore verbatim copies of the ones in `V2Challenge.lean`,
which are themselves verbatim copies of the definitions the development uses —
five from the pinned dependency `anthropics/zeta-23-lean`
(`Zeta23/Statement.lean`) and five from `Zeta23Ext/Bridge/Defs.lean`.

Each copy is definitionally equal to its original and its bridge below is
`rfl`.  The one exception is `H`: the development takes the constant from the
dependency as `HD 1 = 2 − 1/c₁*`, and the closed form `3/2 − (1/√2)cot(1/√2)`
written in the Challenge is a *theorem* about it (`Zeta23.ThmD.HD_one`), not a
definitional unfolding.  `H_eq` is that theorem, and `Phi_n_eq` carries it into
the constant.

The namespace is `Zeta23Ext.PalomarV2`, distinct from the `Zeta23Ext.Palomar`
of the surface this entry's first version advertises (`BridgeChallenge.lean`,
`BridgeSolution.lean`), which this module neither imports nor changes.

If a definition the advertised statements mention is edited in
`Zeta23Ext/Bridge/Defs.lean`, or upstream in `Zeta23/Statement.lean`, the `rfl`
bridges below will break.  That is the intended alarm: the registry entry pins
a commit, and the statements it advertises must keep matching the development.
-/

open scoped BigOperators

noncomputable section

namespace Zeta23Ext.PalomarV2

/-! ### Counting the zeros of ζ -/

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

/-! ### Bridges to the development's own definitions -/

theorem IsNontrivialZero_eq : IsNontrivialZero = _root_.Zeta23.IsNontrivialZero := rfl

theorem zeroMult_eq : zeroMult = _root_.Zeta23.zeroMult := rfl

theorem zerosIn_eq : zerosIn = _root_.Zeta23.zerosIn := rfl

theorem Ncount_eq : Ncount = _root_.Zeta23.Ncount := rfl

theorem N0simple_eq : N0simple = _root_.Zeta23.N0simple := rfl

theorem Kfun_eq : Kfun = _root_.Zeta23Ext.Bridge.Kfun := rfl

theorem kfun_eq : kfun = _root_.Zeta23Ext.Bridge.kfun := rfl

theorem wfun_eq : wfun = _root_.Zeta23Ext.Bridge.wfun := rfl

theorem ptsN_eq : ptsN = _root_.Zeta23Ext.Bridge.ptsN := rfl

theorem F_eq : F = _root_.Zeta23Ext.Bridge.F := rfl

/-- Not `rfl`: the development's constant is the dependency's `HD 1 = 2 − 1/c₁*`,
and the closed form is the dependency's theorem `HD_one` about it. -/
theorem H_eq : H = _root_.Zeta23.ThmD.HD 1 := _root_.Zeta23.ThmD.HD_one.symm

theorem Phi_n_eq (n : ℕ) (c : ℝ) (m p : ℕ) :
    Phi_n n c m p = _root_.Zeta23Ext.Bridge.Phi_n n c m p := by
  unfold Phi_n _root_.Zeta23Ext.Bridge.Phi_n
  rw [H_eq]

/-! ### The advertised theorems -/

/-- **The `n`-point simple-zero bound, conditional on its certificate.** -/
theorem n_point_bound (n : ℕ) (c : ℝ) (m p : ℕ) (hn : 2 ≤ n) (hm : n ≤ m) (hp : 0 < p)
    (hc : 0 < c)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ F n p g)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi_n n c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simp only [F_eq] at hCert
  simp only [Phi_n_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.n_point_bound n c m p hn hm hp hc hCert hA0

/-- **At eight points, at the accepted certificate** `(41763/10⁷, 3200)` with
`m = 246`. -/
theorem eight_point_bound
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2460000000 * H - 5359375) / 2450018643 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simp only [F_eq] at hCert
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.eight_point_bound hCert

/-- **The eight-point bound as a proportion.** -/
theorem eight_point_bound_ratio
    (hCert : ∀ g : Fin 7 → ℝ, (∀ i, 0 ≤ g i) → 41763 / 10000000 ≤ F 8 3200 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2460000000 * H - 5359375) / 2450018643 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  simp only [F_eq] at hCert
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.eight_point_bound_ratio hCert

/-- **At three points, with the certificate proved rather than assumed.**  No
hypothesis: `Zeta23Ext.Bridge.ThreePoint.three_point_cert` is the `n = 3`
instance of `hCert` at `c = 1345/10⁶`, `p = 3000`, proved in this package from
368 interval cell lemmas applied 1515 times over 487 leaves. -/
theorem three_point_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((149000000 * H - 99200) / 148800133 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.ThreePoint.three_point_bound

/-- **The three-point bound as a proportion, unconditional.** -/
theorem three_point_bound_ratio :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (149000000 * H - 99200) / 148800133 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.ThreePoint.three_point_bound_ratio

/-! ### Standing axiom audit

Every line below must report exactly `[propext, Classical.choice, Quot.sound]`;
`permitted_axioms` in `lean/bridge/comparator-v2.json` names those three and
no others, and a `sorryAx` here would mean the Challenge's deliberate holes had
leaked into the proved surface. -/

#print axioms n_point_bound
#print axioms eight_point_bound
#print axioms eight_point_bound_ratio
#print axioms three_point_bound
#print axioms three_point_bound_ratio

end Zeta23Ext.PalomarV2
