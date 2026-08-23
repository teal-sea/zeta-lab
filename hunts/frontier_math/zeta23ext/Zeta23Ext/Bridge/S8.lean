/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs
import Zeta23Ext.Bridge.Helpers_S8

/-!
# S8: the tail passage  ([A] Corollary 2.2, eq:global-defect)

From the fixed-height counting inequality with defect (S7, instantiated at the Montgomery–Taylor
window) to `N₀ˢ(T,2T) ≥ H N(T,2T) + D(M°) − o(N)`.  This is `[L23]`'s chain
`hatAz_mult2 → seamA_mult2 → thmD_mult2_abstract → thmD_mult_lam_abstract → thmD₀_simple_mult`
(`Zeta23/Assembly/SeamMult.lean`, `Zeta23/ThmD/Mult.lean`) carried through with one extra
nonnegative term, which `[L23]`'s seam files do not carry (TRUST-MAP S8, graded LARGE).

**Proved.**  The two `[L23]` theorems are re-stated with the defect term in
`Bridge/Helpers_S8.lean` (`seamA_mult2_defect`, `endgame_defect`); this file instantiates them at
`P = paramsOf stdProfile 1`, i.e. at `λ = 1`, exactly as `[L23]`'s `thmD_mult_lam_abstract` does at
`λ < 1`.  What the formal state showed: the `λ → 1⁻` passage `eps_form_HD`, which the trust map and
the skeleton's residual note both took to be the LARGE obstacle (the defect `D(M°)` lives at the
`λ = 1` window and would not survive a limit over windows), is **not needed**.  Every analytic input
of `thmD_mult2_abstract` is stated for `P.Valid`, i.e. `0 < λ ≤ 1` (`calE_tendsto_zero`,
`tracesBoundsD_concrete`, `tendsto_cRatio_concrete`, `eventually_tailPackageD`,
`isLittleO_sqrtX_Tl`, `tendsto_theta_over_L`), and `thmD_mult2_abstract`'s own hypothesis
`hlam : P.lam < 1` is used only as `hlam.le`.  The skeleton's residual note was wrong on one point:
`[L23]`'s `calE` **does** tend to `0` at `λ = 1` (`Zeta23/Assembly.lean`, `calE_tendsto_zero`,
hypothesis `P.lam ≤ 1`; the paper's `𝓔_T ≪ w/L + log l / l` at `λ = 1`).
-/

noncomputable section

open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

/-- **S8** ([A] eq:global-defect).  Given the counting inequality with defect at every large
height (S7 at the window `mtParams T`), `(H − ε) N + D(M°) ≤ N₀ˢ` eventually, for every `ε > 0`.

Proof: `[L23]`'s `thmD_mult_lam_abstract` at `P = paramsOf stdProfile 1` (`λ = 1`, `w = 1`), with
its `thmD_mult2_abstract` replaced by `endgame_defect` and the seam core supplied by `h7`.  The
constant is `HD 1 = 2 − 1/cStar 1` by definition (`two_sub_inv_cStar`), and `cStar 1` is the limit
of the concrete window ratio (`tendsto_cRatio_concrete`, valid for `λ ≤ 1`). -/
theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
    (h7 : ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by
  -- the §6 parameters at λ = 1; `mtParams T = P.atD T` by definition
  set P : Params := paramsOf stdProfile 1 with hPdef
  have hP : P.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : P.lam = 1 := rfl
  -- the inputs of `[L23]`'s `thmD_mult_lam_abstract`, none of which needs `λ < 1`
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)
  -- the endgame with the defect carried through
  have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
    (fun T => Dcirc Z (mtParams T) T) h7
  intro ε hε
  have h' := h ε hε
  -- `HD 1 = 2 − 1/cStar 1` and `P.lam = 1`
  have hHD : HD 1 = 2 - (cStar P.lam)⁻¹ := by rw [hlam, HD, one_div]
  rw [hHD]
  exact h'

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms tail_passage

end Zeta23Ext.Bridge
