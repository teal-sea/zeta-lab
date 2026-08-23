/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.S11
import Zeta23Ext.Bridge.S12

/-!
# S13: the per-block bound  ([A] eq:269block)

`D(G_B) + (6/p)·span(B) ≥ A₀ − o(1)` for a block `B` of `m` retained zeros, `A₀ = c(m − 6) ≤ 1`.
Stated here *deterministically at one height*: the `o(1)` is an explicit tolerance `δ` on the
Gram entries (S9's conclusion at that height), and the error is `2m²δ`.  `Bridge/Main.lean`
combines this with S9 into the uniform-in-`T` form the paper displays.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **S13** ([A] eq:269block, fixed height).  If the Gram entries on a block `B` of `m` points are
within `δ` of the kernel, `c(m − 6) − 2m²δ ≤ D(G_B) + (6/p)·span(B)`.

Residual goal (HANDWRITTEN, medium): from `|G_{ij} − k(xᵢ−xⱼ)| ≤ δ` and `|k| ≤ 1` (`|K(x)| ≤ K(0)`
since `cos(√2 t) ≥ 0` on `[−1/2, 1/2]`) get `|G_{ij}|² ≥ w(xᵢ−xⱼ) − 2δ` termwise, hence
`offDiagSqOn G_B ≥ energyOn x B − 2m(m−1)δ`; S12 on the principal submatrix `G_B ⪰ 0`
(`PosSemidef.submatrix`) gives `D(G_B) ≥ min{1, offDiagSqOn}`; S11 on `B` gives
`energyOn + (6/p) span ≥ c(m−6)`; finally `min{1, c(m−6) − (6/p)span − 2m²δ} = c(m−6) − (6/p)span − 2m²δ`
because `c(m−6) ≤ 1` (`hA0`; this is where TRUST-MAP §1.2's cap `m ≤ 6 + ⌊1/c⌋` enters). -/
theorem block_bound {c : ℝ} {m p : ℕ} (hm : 7 ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g) (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    (x : ι → ℝ) {G : Matrix ι ι ℂ} (hG : G.PosSemidef) (B : Finset ι) (hB : B.card = m)
    (hx : Set.InjOn x B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    c * ((m : ℝ) - 6) - 2 * (m : ℝ) ^ 2 * δ ≤ blockDefect hG.1 B + (6 / (p : ℝ)) * spanOf x B := by
  sorry

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms block_bound

end Zeta23Ext.Bridge
