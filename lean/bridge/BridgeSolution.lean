/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Mathlib
import Zeta23Ext.Bridge.Main

/-!
# Proved solution

This module imports the bridge development and proves the four statements
advertised in `BridgeChallenge.lean`.

Following the Palomar layout this module does **not** import `BridgeChallenge`:
the two modules independently declare the same names, and Comparator checks
that each compared declaration has the same statement in both.  The definitions
below are therefore verbatim copies of the ones in `BridgeChallenge.lean`,
which are themselves verbatim copies of the definitions the development uses —
five from the pinned dependency `anthropics/zeta-23-lean`
(`Zeta23/Statement.lean`) and five from `Zeta23Ext/Bridge/Defs.lean`.

Each copy is definitionally equal to its original and its bridge below is
`rfl`.  The one exception is `H`: the development takes the constant from the
dependency as `HD 1 = 2 − 1/c₁*`, and the closed form `3/2 − (1/√2)cot(1/√2)`
written in the Challenge is a *theorem* about it (`Zeta23.ThmD.HD_one`), not a
definitional unfolding.  `H_eq` is that theorem, and `Phi_eq` carries it into
the constant.

If a definition the advertised statements mention is edited in
`Zeta23Ext/Bridge/Defs.lean`, or upstream in `Zeta23/Statement.lean`, the `rfl`
bridges below will break.  That is the intended alarm: the registry entry pins
a commit, and the statements it advertises must keep matching the development.
-/

open scoped BigOperators

noncomputable section

namespace Zeta23Ext.Palomar

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

/-! ### Bridges to the development's own definitions -/

theorem IsNontrivialZero_eq : IsNontrivialZero = _root_.Zeta23.IsNontrivialZero := rfl

theorem zeroMult_eq : zeroMult = _root_.Zeta23.zeroMult := rfl

theorem zerosIn_eq : zerosIn = _root_.Zeta23.zerosIn := rfl

theorem Ncount_eq : Ncount = _root_.Zeta23.Ncount := rfl

theorem N0simple_eq : N0simple = _root_.Zeta23.N0simple := rfl

theorem Kfun_eq : Kfun = _root_.Zeta23Ext.Bridge.Kfun := rfl

theorem kfun_eq : kfun = _root_.Zeta23Ext.Bridge.kfun := rfl

theorem wfun_eq : wfun = _root_.Zeta23Ext.Bridge.wfun := rfl

theorem pts_eq : pts = _root_.Zeta23Ext.Bridge.pts := rfl

theorem F6_eq : F6 = _root_.Zeta23Ext.Bridge.F6 := rfl

/-- Not `rfl`: the development's constant is the dependency's `HD 1 = 2 − 1/c₁*`,
and the closed form is the dependency's theorem `HD_one` about it. -/
theorem H_eq : H = _root_.Zeta23.ThmD.HD 1 := _root_.Zeta23.ThmD.HD_one.symm

theorem Phi_eq (c : ℝ) (m p : ℕ) : Phi c m p = _root_.Zeta23Ext.Bridge.Phi c m p := by
  unfold Phi _root_.Zeta23Ext.Bridge.Phi
  rw [H_eq]

/-! ### The advertised theorems -/

/-- **The seven-point simple-zero bound, conditional on its certificate.** -/
theorem seven_point_bound (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simp only [F6_eq] at hCert
  simp only [Phi_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.seven_point_bound c m p hm hp hc hCert hA0

/-- **At Ainta's published parameters** `(19/5000, 269, 3000)`. -/
theorem seven_point_bound_paper
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * H - 2680) / 1340003 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  simp only [F6_eq] at hCert
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.seven_point_bound_paper hCert

/-- **At this laboratory's own parameters** `(34697/10⁷, 294, 3400)`. -/
theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * H - 915625) / 518855453 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  simp only [F6_eq] at hCert
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.seven_point_bound_lab hCert

/-- **The same bound as a proportion.** -/
theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * H - 915625) / 518855453 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  simp only [F6_eq] at hCert
  simp only [H_eq, Ncount_eq, N0simple_eq]
  exact _root_.Zeta23Ext.Bridge.seven_point_bound_lab_ratio hCert

/-! ### Standing axiom audit

Every line below must report exactly `[propext, Classical.choice, Quot.sound]`;
`permitted_axioms` in `lean/comparator-bridge.json` names those three and no
others, and a `sorryAx` here would mean the Challenge's deliberate holes had
leaked into the proved surface. -/

#print axioms seven_point_bound
#print axioms seven_point_bound_paper
#print axioms seven_point_bound_lab
#print axioms seven_point_bound_lab_ratio

end Zeta23Ext.Palomar
