/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Zeta23.ThmD.Mult
import Zeta23Ext.StableRankTrace

/-!
# Bridge definitions: the seven-point simple-zero bound (Ainta, `riemann.tex`)

The objects of `hunts/ainta_seven_point/TRUST-MAP.md` steps S6–S16, written in the vocabulary of
the vendored `anthropics/zeta-23-lean` (`[L23]`) wherever that vocabulary exists:

* `RHLinalg.rtrace / frobSq / posIndex / specMap` (`Zeta23/LinAlg/`),
* `Zeta23.ZeroSide.ZeroBlockData` with its `S₁, s₁, s₂, Ncount, blockP, blockQ, PairReps`
  (`Zeta23/ZeroSide.lean`), instantiated at height `T` by `Zeta23.ZeroSide.blockData`,
* the window parameters `Zeta23.Params` (`L, d, tau, a, phiHat, hat`) and the Montgomery–Taylor
  window-realizing family `Params.atD` (`Zeta23/ThmD/ParamsD.lean`),
* the counting functions `ZeroConfig.N / N0s / NIprime / s1` and the constant `ThmD.HD 1`
  (`= 3/2 − (1/√2)cot(1/√2)`, `Zeta23/ThmD/Functional.lean`, `HD_one`),
* Ainta's profile `Psi` from `Zeta23Ext/StableRankTrace.lean` (`= gc 2 + 1`, kernel-checked there).

What is new here and has no upstream counterpart: the overlap kernel `k`, `w = k²`, the seven-point
functional `F6` with pressure denominator `p`, the block objects (defect `D = tr Psi`, energy, span,
off-diagonal mass), the retained central simple zeros and their Gram matrix `M°`, the simple-zero
factor `P₁ = V Vᴴ` with its complement `Q' = Â − P₁`, and the bound constant `Phi c m p`.

Nothing in this file is a theorem about ζ; the only proofs are bookkeeping (Hermitian-ness,
positivity, injectivity) that the step files and `Bridge/Main.lean` consume.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

/-! ### 1. The Montgomery–Taylor overlap kernel  ([A] §3, eq:kdef, eq:Kexplicit) -/

/-- `K(x) := ∫_{-1/2}^{1/2} cos(√2 t) cos(2π x t) dt`  ([A] eq:Kexplicit, the integral that defines
it; the closed sinc form printed there is a consequence and is what the Arb verifier evaluates). -/
def Kfun (x : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)

/-- `k(x) := K(x)/K(0)`  ([A] eq:kdef). -/
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0

/-- `w(x) := k(x)²`  ([A] end of §3). -/
def wfun (x : ℝ) : ℝ := kfun x ^ 2

/-! ### 2. The seven-point functional  ([A] §4, eq:F6) -/

/-- The seven ordered points `y₀ = 0, yᵢ = g₀ + ⋯ + g_{i−1}` determined by six gaps. -/
def pts (g : Fin 6 → ℝ) (i : Fin 7) : ℝ := ∑ j : Fin 6, if (j : ℕ) < (i : ℕ) then g j else 0

/-- `F6(g) := (1/p) Σ gᵢ + Σ_{r=1}^{6} (2/(7−r)) Σ_{i=1}^{7−r} w(gᵢ + ⋯ + g_{i+r−1})`  ([A] eq:F6),
written as a sum over the 21 pairs `i < j` of the seven points with coefficient `2/(7 − (j−i))`.
`p` is the pressure denominator (`p = 3000` in both published runs). -/
def F6 (p : ℕ) (g : Fin 6 → ℝ) : ℝ :=
  (1 / (p : ℝ)) * ∑ i, g i
    + ∑ i : Fin 7, ∑ j : Fin 7,
        if (i : ℕ) < (j : ℕ) then
          (2 / ((7 : ℝ) - (((j : ℕ) - (i : ℕ) : ℕ) : ℝ))) * wfun (pts g j - pts g i)
        else 0

/-! ### 3. Block quantities on an abstract finite index set -/

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `E := Σ_{i ≠ j ∈ B} w(xᵢ − xⱼ) = 2 Σ_{i<j} w(yⱼ − yᵢ)`  ([A] Lemma 4.2, `E_m`; `w` is even). -/
def energyOn (x : ι → ℝ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else wfun (x i - x j)

/-- `Σ_{i ≠ j ∈ B} |G_{ij}|² = 2 Σ_{i<j} |G_{ij}|²`  ([A] Lemma 4.3, for Hermitian `G`). -/
def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
  ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2

/-- `span(B) := max_B x − min_B x`  ([A] §4 after eq:mA; `0` for the empty block). -/
def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
  if h : B.Nonempty then B.sup' h x - B.inf' h x else 0

/-- `B` is a set of *consecutive* points in the order given by `x`. -/
def IsInterval (x : ι → ℝ) (B : Finset ι) : Prop :=
  ∀ i ∈ B, ∀ j ∈ B, ∀ k, x i ≤ x k → x k ≤ x j → k ∈ B

lemma abs_sub_le_spanOf (x : ι → ℝ) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B) :
    |x i - x j| ≤ spanOf x B := by
  have hne : B.Nonempty := ⟨i, hi⟩
  unfold spanOf
  rw [dif_pos hne, abs_le]
  constructor
  · linarith [Finset.le_sup' x hj, Finset.inf'_le x hi]
  · linarith [Finset.le_sup' x hi, Finset.inf'_le x hj]

lemma spanOf_nonneg (x : ι → ℝ) (B : Finset ι) : 0 ≤ spanOf x B := by
  unfold spanOf
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    linarith [Finset.le_sup' x hi, Finset.inf'_le x hi]
  · exact le_rfl

/-! ### 4. The spectral defect `D(M) := tr Psi(M)`  ([A] §2, eq:Psi and the line after it) -/

/-- `D(M) := tr Psi(M)` for Hermitian `M`, through `[L23]`'s `specMap` (S5). -/
def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)

lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
  unfold defect
  rw [rtrace_specMap]
  exact Finset.sum_nonneg fun _ _ => Psi_nonneg _

/-- `D(G_B)`: the defect of the principal submatrix of `M` on the block `B`. -/
def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
  defect (hM.submatrix (Subtype.val : B → ι))

lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
    0 ≤ blockDefect hM B :=
  defect_nonneg _

end Blocks

/-! ### 5. The bound constant  ([A] §5, TRUST-MAP §1.1) -/

/-- `Phi(c, m, p) := (H − 6(m−1)/(pm)) / (1 − c(m−6)/m)` with `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`. -/
def Phi (c : ℝ) (m p : ℕ) : ℝ :=
  (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / (1 - c * ((m : ℝ) - 6) / m)

/-! ### 6. The simple-zero factor at the block level  ([A] §1: `P₁ = V Vᵀ`, `Q' = Â − P₁`) -/

section BlockLevel

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

/-- `V`: the `d × s₁` matrix whose columns are `v_ρ = u_ρ/√c`, `ρ ∈ 𝒮₁` (`c = aL²`). -/
def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)

/-- `P₁ := V Vᴴ = Σ_{ρ ∈ 𝒮₁} v_ρ v_ρ*`. -/
def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ

/-- `Q' := Â − P₁` with `Â = blockP + blockQ` (`[L23]` prop:block (ii)). -/
def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c

/-- `M := Vᴴ V`, the Gram matrix of the simple on-line zeros of `𝒵(I′)`. -/
def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Vsimple D c)ᴴ * Vsimple D c

lemma P₁_posSemidef (c : ℝ) : (P₁ D c).PosSemidef := posSemidef_self_mul_conjTranspose _

lemma gramS₁_isHermitian (c : ℝ) : (gramS₁ D c).IsHermitian :=
  isHermitian_conjTranspose_mul_self _

lemma gramS₁_posSemidef (c : ℝ) : (gramS₁ D c).PosSemidef :=
  posSemidef_conjTranspose_mul_self _

lemma blockP_isHermitian (c : ℝ) : (D.blockP c).IsHermitian :=
  ZeroBlockData.isHermitian_real_smul D.onPart_posSemidef.isHermitian _

lemma Q'_isHermitian (c : ℝ) : (Q' D c).IsHermitian :=
  ((blockP_isHermitian D c).add (D.blockQ_isHermitian c)).sub (P₁_posSemidef D c).1

lemma P₁_add_Q' (c : ℝ) : P₁ D c + Q' D c = D.blockP c + D.blockQ c := by
  unfold Q'; abel

end BlockLevel

/-! ### 7. The concrete objects at height `T`  ([A] §§1, 3, 5) -/

section Concrete

open Classical

/-- The Montgomery–Taylor window of height `T` at `λ = 1`: `[L23]`'s window-realizing family
`Params.atD` of the §6 parameters `paramsOf stdProfile 1` (`w = 1`, `L = ℓ`).  This is the
"optimised test family of Theorem D, `L = ℓ`" of [A] §1. -/
def mtParams (T : ℝ) : Params := (paramsOf stdProfile 1).atD T

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- The normalised ordinate `x_ρ := L(γ_ρ − T)/(2π)`  ([A] §3). -/
def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)

/-- `c := aL²`, the normalisation of the hat units ([L23] eq:hatunits). -/
def aL2 : ℝ := P.a T * P.L T ^ 2

/-- The block data of `𝒵(I′)` for the window `P` at height `T`: `[L23]`'s `blockData` with its
conjugation input discharged by `[L23]`'s `phiHatConj`. -/
def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj

/-- The retained central simple zeros ([A] Lemma 3.1, §5): `𝒮₁` minus the two strips of normalised
width `L²` at the ends of the grid.  (`L² ≤ x_ρ ≤ d − L²` already forces `T < γ_ρ < 2T`.) -/
def retained : Finset (ZI Z T) :=
  (bdata Z P T).S₁.filter fun z =>
    P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2

lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
  (Finset.mem_filter.mp hz).1

/-- The inclusion of the retained zeros into `𝒮₁`. -/
def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
  fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩

lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
  fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)

/-- `M°`: the Gram matrix of the retained central simple zeros, the principal submatrix of the
full Gram matrix `M = Vᴴ V` of `𝒮₁` ([A] Corollary 2.2 and §5). -/
def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
  (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)

lemma gram_isHermitian : (gram Z P T).IsHermitian :=
  (gramS₁_isHermitian _ _).submatrix _

lemma gram_posSemidef : (gram Z P T).PosSemidef :=
  (gramS₁_posSemidef _ _).submatrix _

/-- `D(M°)`. -/
def Dcirc : ℝ := defect (gram_isHermitian Z P T)

/-- The normalised ordinates of the retained zeros. -/
def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)

lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (bdata Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
  have h : (bdata Z P T).σ z = z := by
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    exact hz.1
  exact (mkData_σ_eq_iff Z T _ _ z).mp h

/-- Distinct retained zeros have distinct normalised ordinates (they share `β = 1/2`). -/
lemma xret_injective (hL : 0 < P.L T) : Function.Injective (xret Z P T) := by
  intro z z' h
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  unfold xret xnorm at h
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have him : (z.1 : ℂ).im = (z'.1 : ℂ).im := by
    have h1 := (div_left_inj' hpi.ne').mp h
    have h2 := mul_left_cancel₀ hL.ne' h1
    linarith
  apply Subtype.ext; apply Subtype.ext
  exact Complex.ext (by rw [hz, hz']) him

end Concrete

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms abs_sub_le_spanOf
#print axioms spanOf_nonneg
#print axioms defect_nonneg
#print axioms blockDefect_nonneg
#print axioms Q'_isHermitian
#print axioms P₁_add_Q'
#print axioms gram_isHermitian
#print axioms gram_posSemidef
#print axioms toS₁_injective
#print axioms xret_injective

end Zeta23Ext.Bridge
