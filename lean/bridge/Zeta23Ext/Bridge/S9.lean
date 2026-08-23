/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Zeta23Ext.Bridge.Defs
import Zeta23Ext.Bridge.Helpers_S9

/-!
# S9: the uniform kernel limit  ([A] Lemma 3.1, eq:kernel-limit)

`⟨v_ρ, v_ρ′⟩ = k(x_ρ − x_ρ′) + o(1)` uniformly in `T` over retained pairs, and the two deleted
strips contain `o(N)` zeros.  **Both are proved here, sorry-free**, from `[L23]` material that the
trust map recorded as absent: the full-grid identity is `AdmWindow.hasSum_vHatR_mul` *for the
Montgomery–Taylor window* (`ThmD.admWindow_params`, not only the flat taper's `hasSum_phiHatR_mul`);
the tail outside `[0, d)` is `PrimeSide.rho` with the `r⁻²` majorant `PrimeSide.rho_le_majorant`
of [C26] §5.3; and the `L → ∞` limit `Φ_D(hx)/(aL) → K(x)/K(0)` is the `L¹` comparison
`ThmD.integral_abs_phiDsq_sub_sharp` (window vs sharp cutoff, `≤ 2w`) plus `ThmD.aD_close`.
`k` itself (`Kfun`, `kfun` in `Bridge/Defs.lean`) is the only genuinely new object.

The proofs are in `Zeta23Ext/Bridge/Helpers_S9.lean`.  What the formal statement exposed: the
error is `10 (c_DT/w)²/L⁴ + 12w/L` at every height, for **every** pair of retained zeros at
**every** separation; the paper's restriction `|x_ρ − x_ρ′| ≤ R₀` and the analytic inputs
`H : PaperInputs Z` play no role in eq:kernel-limit (they are needed downstream and for the strip
count respectively).
-/

noncomputable section

open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

set_option linter.unusedVariables false in
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

**Proved** (`Zeta23Ext/Bridge/Helpers_S9.lean`, sections 6–8): a simple on-line zero of `(T, 2T]` is
retained unless its ordinate lies in `(T, T + 2πL]` or in `(2T − 2πL − 2π/L, 2T]`
(`N0s_le_card_retained_add`); by the local count `H.RvM.local_count` and window additivity of
`Z.N` these strips hold at most `1600 A₀ L²` zeros (`strips_le`); and `N(T,2T) ≥ TL/2π − |C| log T`
by `H.RvM.main`, so `1600 A₀ L² ≤ ε N(T,2T)` as soon as `log T ≤ c T` (`Real.isLittleO_log_id_atTop`). -/
theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
        ≤ ((retained Z (mtParams T) T).card : ℝ) := by
  intro ε hε
  have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
  have hA0 : 0 < A₀ := by linarith
  have hπ := Real.pi_pos
  set c : ℝ := ε / (4 * Real.pi * (1600 * A₀)) with hc
  have hcpos : 0 < c := by positivity
  have hlittle : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
    Real.isLittleO_log_id_atTop.def hcpos
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop T₀,
    (tendsto_L hP).eventually_ge_atTop 1, hlittle,
    eventually_ge_atTop (4 * Real.pi * |C| * (1 + 2 * Real.pi))] with T hT1 hTT₀ hL1 hlog hTC
  have hT0 : 0 < T := by linarith
  set L : ℝ := (paramsOf stdProfile 1).L T with hLdef
  -- `L = log T − log 2π`
  have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
    rw [hLdef]
    show 1 * Real.log (T / (2 * Real.pi)) = _
    rw [one_mul, Real.log_div hT0.ne' (by positivity)]
  have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
  have hLlogT : L ≤ Real.log T := by linarith
  have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
  have hLT : L ≤ T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlogc : Real.log T ≤ c * T := by
    have h := hlog
    simp only [id, Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlogT0] at h
    exact h
  -- the inclusion and the strip count
  have hLpos : 0 < (mtParams T).L T := by show 0 < L; linarith
  have hincl := N0s_le_card_retained_add Z (mtParams T) T hLpos
  have hstrips := strips_le Z hA₀ hloc hT1 hL1 hLT hlogT
  have hincl' : (Z.N0s T (2 * T) : ℝ) ≤ (retained Z (mtParams T) T).card + 1600 * A₀ * L ^ 2 := by
    have e1 : (mtParams T).L T = L := rfl
    rw [e1] at hincl
    linarith
  -- the lower bound on `N(T,2T)` from Riemann–von Mangoldt
  have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
    have h := hRvM T hTT₀
    have hℓ₁ : L ≤ ell1 T := by
      show 1 * l T ≤ l T + 2 * Real.log 2 - 1
      have := Real.log_two_gt_d9
      linarith
    have h1 := (abs_le.mp h).1
    have h2 : C * Real.log T ≤ |C| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
    have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
    linarith
  -- the strips are `o(N)`: `1600 A₀ L² + ε |C| log T ≤ ε T L / 2π`
  have hkey : 1600 * A₀ * L ^ 2 + ε * |C| * Real.log T ≤ ε * (T * L / (2 * Real.pi)) := by
    have hA : 1600 * A₀ * L ^ 2 ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : 1600 * A₀ * L ^ 2 ≤ 1600 * A₀ * L * (c * T) := by
        have : L * L ≤ L * (c * T) := by
          have : L ≤ c * T := hLlogT.trans hlogc
          exact mul_le_mul_of_nonneg_left this (by linarith)
        nlinarith
      have h2 : 1600 * A₀ * L * (c * T) = ε * T * L / (4 * Real.pi) := by
        rw [hc]; field_simp
      linarith
    have hB : ε * |C| * Real.log T ≤ ε * T * L / (4 * Real.pi) := by
      have h1 : |C| * Real.log T ≤ |C| * ((1 + 2 * Real.pi) * L) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        nlinarith
      have h2 : |C| * (1 + 2 * Real.pi) * (4 * Real.pi) ≤ T := by linarith
      have h3 : |C| * ((1 + 2 * Real.pi) * L) ≤ T * L / (4 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]
        have hL0 : 0 ≤ L := by linarith
        nlinarith
      calc ε * |C| * Real.log T = ε * (|C| * Real.log T) := by ring
        _ ≤ ε * (|C| * ((1 + 2 * Real.pi) * L)) := mul_le_mul_of_nonneg_left h1 hε.le
        _ ≤ ε * (T * L / (4 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hε.le
        _ = ε * T * L / (4 * Real.pi) := by ring
    have : ε * T * L / (4 * Real.pi) + ε * T * L / (4 * Real.pi) = ε * (T * L / (2 * Real.pi)) := by
      field_simp
      ring
    linarith
  have hεN : 1600 * A₀ * L ^ 2 ≤ ε * (Z.N T (2 * T) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hN hε.le
    nlinarith [hkey]
  linarith

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms kernel_limit
#print axioms deleted_strips

end Zeta23Ext.Bridge
