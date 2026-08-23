/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

/-!
# S8: the tail passage  ([A] Corollary 2.2, eq:global-defect)

From the fixed-height counting inequality with defect (S7, instantiated at the Montgomery–Taylor
window) to `N₀ˢ(T,2T) ≥ H N(T,2T) + D(M°) − o(N)`.  This is `[L23]`'s chain
`hatAz_mult2 → seamA_mult2 → thmD_mult2_abstract → thmD₀_simple_mult`
(`Zeta23/Assembly/SeamMult.lean`, `Zeta23/ThmD/Mult.lean`) carried through with one extra
nonnegative term, which `[L23]`'s seam files do not carry (TRUST-MAP S8, LARGE).
-/

noncomputable section

open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

/-- **S8** ([A] eq:global-defect).  Given the counting inequality with defect at every large
height (S7 at the window `mtParams T`), `(H − ε) N + D(M°) ≤ N₀ˢ` eventually, for every `ε > 0`.

Residual goal (HANDWRITTEN, LARGE): (i) `seamA_mult2`'s perturbation `Â → Ĝ = Â + Ê` with the
tail bounds `TailInputs` (`ctr_sub_frobSq_perturb` is `c`-generic and does not touch the defect
term, so it goes through verbatim); (ii) `s₁(I′) ≤ N₀ˢ(T,2T) + N(I′∖I)` and
`N(I′) = N(T,2T) + N(I′∖I)` (`s1_le`, `NIprime_eq`); (iii) the trace asymptotics
`tr Ĝ = N(1 + o(1))`, `‖Ĝ‖_F² = (1/c₁* + o(1)) N` with `2 − 1/c₁* = HD 1` — in `[L23]` these are
`TracesBoundsD` / `tendsto_cRatio_concrete` for `λ < 1` followed by the `λ → 1⁻` passage
`eps_form_HD`, whereas [A] works at `λ = 1` outright; carrying the defect through that passage
requires either the trace asymptotics at `λ = 1` (where `[L23]`'s `calE` does not tend to `0`)
or a `λ`-dependent kernel `k_λ` with continuity in `λ` — this is the gap the trust map grades
LARGE, and it is the residual of this lemma, not of the skeleton. -/
theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
    (h7 : ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by
  sorry

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms tail_passage

end Zeta23Ext.Bridge
