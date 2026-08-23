/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

/-!
# S15: averaging over the `m` offsets  ([A] §5, eq:defect-global)

Two statements.  `offset_average` is the combinatorial core, ζ-free: for a finite set of points
with distinct ordinates, a block functional satisfying the per-block bound (S13's conclusion) and
the pinching bound (S14's conclusion) satisfies the averaged inequality.  `span_retained_le` is
the one analytic input of this step, `x_{S°} − x_1 ≤ T/h = LT/2π = d + O(1) = N + o(N)` by
Riemann–von Mangoldt (`[L23]` `PaperInputs.RvM`, which is S0).
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **S15, combinatorial core** ([A] §5: "For each offset, sum eq:269block over the full blocks and
use eq:pinching; then average over the `m` offsets").

Residual goal (HANDWRITTEN, small–medium): sort the points by `x`; for each offset `j < m`
partition the indices into the full consecutive blocks `{j + im + 1, …, j + (i+1)m}` and the
leftover points (`β_j`); `hpinch` at `β_j` plus `hD0` on the leftover classes gives
`Σ_{B full} Dblk B ≤ Dtot`; `hblock` on each full block gives
`A · n_j ≤ Dtot + q · Σ_{B full} span B`; sum over `j`: the number of full blocks satisfies
`Σ_j n_j ≥ card ι − m + 1`, and every gap `x_{k+1} − x_k` lies inside a full block span for at
most `m − 1` offsets, so `Σ_j Σ_B span B ≤ (m − 1)(x_max − x_min)`. -/
theorem offset_average (x : ι → ℝ) (hx : Function.Injective x) {m : ℕ} (hm : 1 ≤ m)
    (Dblk : Finset ι → ℝ) (Dtot A q : ℝ) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hD0 : ∀ B, 0 ≤ Dblk B)
    (hblock : ∀ B : Finset ι, B.card = m → IsInterval x B → A ≤ Dblk B + q * spanOf x B)
    (hpinch : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ),
      ∑ b, Dblk (univ.filter fun i => β i = b) ≤ Dtot) :
    A * ((Fintype.card ι : ℝ) - m) - q * ((m : ℝ) - 1) * spanOf x univ ≤ m * Dtot := by
  sorry

end Abstract

section Analytic

open Classical

/-- **S15, the Riemann–von Mangoldt input** ([A] §5: `x_{S°} − x_1 ≤ T/h = LT/2π = d + O(1)
= N(T,2T) + o(N(T,2T))`).

Residual goal (HANDWRITTEN, small; RvM itself is `H.RvM.main`, S0): every retained zero has
`T < γ ≤ 2T`, so `0 < x_ρ ≤ LT/2π`; at `λ = 1`, `L = l(T) = ℓ₁(T) − 2 log 2 + 1`, so
`LT/2π = T ℓ₁/2π + (1 − 2 log 2) T/2π ≤ N(T,2T) + C log T` by `RvM.main`, and `C log T ≤ ε N`
eventually (`tendsto_N_atTop`). -/
theorem span_retained_le (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      spanOf (xret Z (mtParams T) T) univ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by
  sorry

end Analytic

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms offset_average
#print axioms span_retained_le

end Zeta23Ext.Bridge
