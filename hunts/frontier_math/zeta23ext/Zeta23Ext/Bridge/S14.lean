/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs
import Zeta23Ext.Bridge.Helpers_pinching

/-!
# S14: block pinching  ([A] eq:pinching and Corollary 2.2's `D(M) ≥ D(M°)`)

`D(M) ≥ Σ_B D(G_B)` for any partition of the index set into blocks, "because pinching is an
average of unitary conjugations and `X ↦ tr Psi(X)` is convex and unitarily invariant".

**Status: PROVED, zero `sorry`.**  Both lemmas are instances of
`Zeta23Ext/Bridge/Helpers_pinching.lean`, which proves the pinching inequality for every convex
`f : ℝ → ℝ` (partition form) and every convex `f ≥ 0` (one-block form) from a single mechanism,
the sub-stochastic mixture `μ_j(M|_B) = Σ_i S_{ji} λ_i(M)` of the eigenvalues of a principal
submatrix, followed by Jensen.  Neither half of the paper's sentence is used: the block-diagonal
compression is never written as an average of unitary conjugations, and the convexity of the
*matrix* functional `X ↦ tr Psi(X)` is never invoked (it is a consequence of what is proved, not
an input).  General pinching remains absent from Mathlib at the pinned revision; what is supplied
here is the finite-dimensional convex-trace case that S14 needs, in `[L23]`'s `specMap` vocabulary.

The only property of `Psi` that enters is its convexity on `ℝ` (`Psi_convexOn`, from the affine
minorants `affine_le_Psi`, the same device as upstream's `affine_le_gc`), plus `Psi_nonneg` for the
one-block form.  The statement for general Hermitian `M` (not only PSD) is proved as stated.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **S14, partition form** ([A] eq:pinching).  For Hermitian `M` and any labelling `β : ι → κ`,
`Σ_b D(M|_{β⁻¹ b}) ≤ D(M)`.

Proof: `rtrace_specMap_pinching_le` at `f = Psi`, which is convex on `ℝ` (`Psi_convexOn`).  No
sign condition on `Psi` is needed in this form: in every eigen-direction of `M` the block weights
sum to exactly `1` (`sum_compressWeight_fiberwise`). -/
theorem pinching_partition {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ) :
    ∑ b, blockDefect hM (univ.filter fun i => β i = b) ≤ defect hM := by
  unfold blockDefect defect
  exact rtrace_specMap_pinching_le hM Psi_convexOn β

/-- **S14, two-block form** ([A] Corollary 2.2, "pinching the full Gram matrix into the retained
central block and its complement gives `D(M) ≥ D(M°)`").  `D(M.submatrix f f) ≤ D(M)` for an
injective `f`.

Proof: `rtrace_specMap_submatrix_le` at `f = Psi`, using `Psi_convexOn` and `Psi_nonneg`.  This is
proved directly from the one-block mixture (weights `≤ 1`, `compressWeight_le_one`), not through
the partition form with `κ := Bool`; the latter route would need the defect to be invariant under
reindexing a principal submatrix by `{i // i ∈ range f} ≃ κ'`, which is a second eigenvalue
bookkeeping fact that is not needed when the weights are tracked explicitly. -/
theorem pinching_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : κ → ι) (hf : Function.Injective f) :
    defect (hM.submatrix f) ≤ defect hM := by
  unfold defect
  exact rtrace_specMap_submatrix_le hM hf Psi_convexOn Zeta23Ext.StableRankTrace.Psi_nonneg

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms pinching_partition
#print axioms pinching_submatrix

end Zeta23Ext.Bridge
