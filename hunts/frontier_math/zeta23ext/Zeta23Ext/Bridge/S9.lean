/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs
import Zeta23Ext.Bridge.Helpers_S9

/-!
# S9: the uniform kernel limit  ([A] Lemma 3.1, eq:kernel-limit)

`⟨v_ρ, v_ρ′⟩ = k(x_ρ − x_ρ′) + o(1)` uniformly in `T` over retained pairs at bounded normalised
separation, and the two deleted strips contain `o(N)` zeros.  `[L23]` has the full-grid Poisson
identity (`Zeta23/Poisson.lean`, `hasSum_phiHatR_mul`), the window profile
`vStar lam s = cos(√2 λ s)` (`Zeta23/ThmD/Functional.lean`) and the cosine window's
autocorrelation (`Zeta23/ThmD/Window.lean`, `Cfun`, `integral_cos_overlap`), but no `k`, no
`L → ∞` limit of `Φ(hx)/(aL)`, and no uniformity statement (TRUST-MAP S9, LARGE).
-/

noncomputable section

open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

/-- **S9** ([A] eq:kernel-limit).  For every `R₀` and `δ > 0`, eventually in `T`, every pair of
retained zeros at normalised separation `≤ R₀` has Gram entry within `δ` of `k(x_ρ − x_ρ′)`.

**Proved** (`Zeta23Ext/Bridge/Helpers_S9.lean`, `gram_close_of`): at every height `T` with `8w ≤ L`,
`4πw ≤ L` and the §5 local hypotheses of the D-data, every retained pair satisfies
`|⟨v_ρ, v_ρ′⟩ − k(x_ρ − x_ρ′)| ≤ 10 (c_DT/w)²/L⁴ + 12w/L`.  The three ingredients are all `[L23]`:
(i) the full-grid identity `AdmWindow.hasSum_vHatR_mul` for the Montgomery–Taylor window
(`ThmD.admWindow_params`); (ii) the tail `|K_∞ − K| ≤ (ρ(γ) + ρ(γ′))/2` (`PrimeSide.abs_Kinf_sub_Kfun_le`)
with `ρ ≤ W(γ−T) + W(2T−γ) + ψ(τ_d−γ)²` (`PrimeSide.rho_le_majorant`, the `r⁻²` decay of [C26] §5.3) and
`W(Δ) ≤ 2(c/w)²/L²` for `Δ ≥ L`; (iii) `|Φ_D(hx) − L·K(x)| ≤ 2w` from the `L¹` comparison
`ThmD.integral_abs_phiDsq_sub_sharp`, and `|aL − L·K(0)| ≤ 4w` from `ThmD.aD_close`.

The hypotheses `H : PaperInputs Z` and `|x_ρ − x_ρ′| ≤ R₀` are **not used**: the bound is uniform over
all retained pairs, at every separation, and involves the zeros only through the strip condition
`L² ≤ x_ρ ≤ d − L²`. -/
set_option linter.unusedVariables false in
theorem kernel_limit (Z : ZeroConfig) (H : PaperInputs Z) (R₀ : ℝ) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      |xret Z (mtParams T) T z - xret Z (mtParams T) T z'| ≤ R₀ →
      ‖gram Z (mtParams T) T z z'
          - (kfun (xret Z (mtParams T) T z - xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  have hlam : (paramsOf stdProfile 1).lam = 1 := rfl
  obtain ⟨T₀, hT₀⟩ := localHypsCoreD_eventually hP
  set K : ℝ := (cDT (paramsOf stdProfile 1).ϱ (paramsOf stdProfile 1).lam
    / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP, eventually_w4pi hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 h4π hTT₀ hL1 hLδ
  intro z z' _
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hlam hT h8 h4π hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T with hLdef
  have hL : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hL 2, pow_pos hL 3]
  have h1 : 10 * K / L ^ 4 ≤ 10 * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc 10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
      ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
    _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
    _ ≤ δ := h2

/-- **S9, the strip count** ([A] Lemma 3.1: "The number deleted is `o(N(T,2T))`"; eq:Scentral
`S° = N₀ˢ(T,2T) − o(N(T,2T))`).

Residual goal (HANDWRITTEN, small): the two strips have ordinate length `2π L²/L = 2πL = O(L)`
and contain `O(L²) = O(log² T)` zeros by the local count `H.RvM.local_count`
(`N(t+1) − N(t) ≤ A₀ log(t+3)`), and `log² T = o(N)` (`tendsto_N_atTop`); the zeros of
`𝒮₁ ∩ (T, 2T]` not in either strip are exactly `retained`. -/
theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
        ≤ ((retained Z (mtParams T) T).card : ℝ) := by
  sorry

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms kernel_limit
#print axioms deleted_strips

end Zeta23Ext.Bridge
