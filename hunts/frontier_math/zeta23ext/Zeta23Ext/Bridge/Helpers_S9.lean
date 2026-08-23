/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs
import Zeta23.ThmD.ZeroSideD
import Zeta23.PrimeSideA.EndsE1

/-!
# Helpers for S9: the uniform kernel limit  ([A] Lemma 3.1, eq:kernel-limit)

The Gram entry `⟨v_ρ, v_ρ′⟩ = (aL²)⁻¹ Σ_{0≤k<d} φ̂(γ−τ_k) φ̂(γ′−τ_k)` is the *finite* part of the
full-grid Poisson sum `Σ_{k∈ℤ} φ̂(γ−τ_k) φ̂(γ′−τ_k) = L Φ(γ−γ′)` (`[L23]` `AdmWindow.hasSum_vHatR_mul`,
the Montgomery–Taylor window at height `T` being an `AdmWindow` by `ThmD.admWindow_params`).
Two estimates close the lemma:

* **(ii) the tail.**  `[L23]`'s `PrimeSide.abs_Kinf_sub_Kfun_le` (weighted AM–GM) bounds the missing
  terms by `(ρ(γ) + ρ(γ′))/2` with `ρ(τ) = Σ_{k∉[0,d)} φ̂(τ−τ_k)²`, and `PrimeSide.rho_le_majorant`
  is exactly the `r⁻²` decay of [C26] §5.3 the paper cites: `ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d−τ)²`.
  On the retained zeros (`L² ≤ x ≤ d − L²`) all three arguments are `≥ 2πL`, where `W = O(L⁻²)`.
* **(iii) the limit.**  `Φ(hx) = ∫ φ_D(u)² e^{ihxu} du` is within `2w` of the same transform of the
  sharp window `1_{[−L/2,L/2]} cos(√2 u/L)` (`[L23]` `ThmD.integral_abs_phiDsq_sub_sharp`), whose real
  part is `L·K(x)` by the substitution `u = Lt`; `aL = ∫ φ_D²` is within `4w` of `L·K(0)`
  (`[L23]` `ThmD.aD_close`).  So `Φ(hx)/(aL) = k(x) + O(1/L)` **for every real `x`**, not only on
  compacts: the `L¹` argument needs no bound on `x`.

Both errors are `O(1/L)` with explicit constants and no dependence on `x_ρ − x_ρ′` at all: the
paper's `|x_ρ − x_ρ′| ≤ R₀` is not used anywhere in this file.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

/-! ### 1. The Gram entry as the finite Poisson sum -/

section GramEntry

variable (Z : ZeroConfig) (P : Params) (T : ℝ)

/-- The evaluation vector of an on-line zero is real: `v_ρ(k) = φ̂(γ_ρ − τ_k)` with `γ_ρ = Im ρ`. -/
lemma bdata_v_eq (hreal : PhiHatReal T P) {y : ZI Z T} (hy : (y : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
    (bdata Z P T).v y k = (P.phiHatR T ((y : ℂ).im - P.tau T k) : ℂ) := by
  simp only [bdata, blockData, mkData_v, evalVec]
  rw [gammaOf_of_re_eq_half hy, ← Complex.ofReal_sub, hreal]

/-- `⟨v_ρ, v_ρ′⟩ = (aL²)⁻¹ Σ_{0≤k<d} φ̂(γ_ρ − τ_k) φ̂(γ_ρ′ − τ_k)` for retained (hence on-line) zeros. -/
lemma gram_apply (hreal : PhiHatReal T P) (hc : 0 ≤ aL2 P T) (z z' : retained Z P T) :
    gram Z P T z z' =
      (((aL2 P T)⁻¹ * ∑ k : Fin (P.d T),
        P.phiHatR T ((z.1 : ℂ).im - P.tau T k) * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℝ) : ℂ) := by
  have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
  have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
  have hsq : (Real.sqrt (aL2 P T) : ℂ) * (Real.sqrt (aL2 P T) : ℂ) = (aL2 P T : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hentry : ∀ a b : (bdata Z P T).S₁, gramS₁ (bdata Z P T) (aL2 P T) a b
      = ∑ k, star (Vsimple (bdata Z P T) (aL2 P T) k a) * Vsimple (bdata Z P T) (aL2 P T) k b := by
    intro a b
    simp only [gramS₁, Matrix.mul_apply, Matrix.conjTranspose_apply]
  unfold gram
  rw [Matrix.submatrix_apply, hentry]
  have e : ∀ k : Fin (P.d T),
      star (Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z))
        * Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z')
      = (((aL2 P T)⁻¹ * (P.phiHatR T ((z.1 : ℂ).im - P.tau T k)
          * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k)) : ℝ) : ℂ) := by
    intro k
    have h1 : (bdata Z P T).v (toS₁ Z P T z) k = (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz k
    have h2 : (bdata Z P T).v (toS₁ Z P T z') k = (P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℂ) :=
      bdata_v_eq Z P T hreal hz' k
    simp only [Vsimple]
    rw [h1, h2]
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq]
    push_cast
    ring
  simp_rw [e]
  rw [← Complex.ofReal_sum, Finset.mul_sum]

end GramEntry

/-! ### 2. The Montgomery–Taylor window at height `T` -/

section Window

variable {P : Params} (hP : P.Valid) (T : ℝ)
include hP

/-- `φ̂` of the height-`T` window, as a real function: it is `AdmWindow.vHatR (P.phiD T)`. -/
lemma atD_phiHatR_eq : (P.atD T).phiHatR T = AdmWindow.vHatR (P.phiD T) := atD_phiHatR hP T

/-- `φ̂` of the height-`T` window is real on `ℝ` (the shape `PhiHatReal`). -/
lemma phiHatReal_atD : PhiHatReal T (P.atD T) := fun r => GzGp.phiHat_ofReal _ T r

/-- The quadratic decay `|φ̂(r)| r² ≤ c_DT/w`, uniform in `T` (`[L23]` `AdmWindow.abs_vHatR_mul_sq_le`). -/
lemma abs_phiHatR_atD_mul_sq_le (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    |(P.atD T).phiHatR T r| * r ^ 2 ≤ cDT P.ϱ P.lam / P.w := by
  rw [atD_phiHatR_eq hP T]
  exact (admWindow_params hP h8).abs_vHatR_mul_sq_le r

/-- The full-grid Poisson identity for the height-`T` window, for every pair of real ordinates
(`[L23]` `AdmWindow.hasSum_vHatR_mul`): `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ′−τ_k) = L·Φ_D(τ−τ′)`. -/
lemma hasSum_phiHatR_atD_mul (h8 : 8 * P.w ≤ P.L T) (τ τ' : ℝ) :
    HasSum (fun k : ℤ => (P.atD T).phiHatR T (τ - (P.atD T).tau T k)
        * (P.atD T).phiHatR T (τ' - (P.atD T).tau T k))
      (P.L T * AdmWindow.VPhiR (P.phiD T) (τ - τ')) := by
  have h := (admWindow_params hP h8).hasSum_vHatR_mul T τ τ'
  simp only [atD_phiHatR_eq hP T, atD_tau_eq]
  exact h

end Window

/-! ### 3. The tail (ii): the Poisson sum outside `[0, d)`  ([C26] §5.3, `[L23]` `PrimeSide.rho`) -/

section Tail

/-- `W(Δ) ≤ 2 (c/w)² / L²` for `Δ ≥ L` (`ψ(Δ)² ≤ (c/w)²/Δ⁴`, `∫_{(Δ,∞)} ψ² ≤ (c/w)²/(3Δ³)`,
`h⁻¹ = L/2π`). -/
lemma Wfun_le_of_L_le {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) {Δ : ℝ} (hΔ : p.L ≤ Δ) :
    PrimeSide.Wfun c p Δ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h8 := hF.eight_le_L
  have hL : 0 < p.L := hF.L_pos
  have hΔ0 : 0 < Δ := lt_of_lt_of_le hL hΔ
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
  set K : ℝ := (c / p.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hπ := Real.pi_pos
  -- ψ(Δ)² ≤ K/Δ⁴
  have hψ : PrimeSide.psiA c p Δ ^ 2 ≤ K / Δ ^ 4 := by
    have h1 : PrimeSide.psiA c p Δ ≤ c / (p.w * Δ ^ 2) := PrimeSide.psiA_le_div_sq hΔ0.ne'
    calc PrimeSide.psiA c p Δ ^ 2 ≤ (c / (p.w * Δ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF Δ) h1 2
      _ = K / Δ ^ 4 := by rw [hK]; field_simp
  -- ∫_{(Δ,∞)} ψ² ≤ K/(3Δ³)
  have hint : ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2 ≤ K / (3 * Δ ^ 3) :=
    PrimeSide.setIntegral_psiA_sq_Ioi_le_div hF hΔ0
  have hh : (p.h)⁻¹ = p.L / (2 * Real.pi) := by
    unfold PrimeSide.Setting.h; rw [inv_div]
  have hhpos : 0 ≤ (p.h)⁻¹ := by rw [hh]; positivity
  -- the two pieces against K/L²
  have hΔ4 : p.L ^ 2 ≤ Δ ^ 4 := by
    have : p.L ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hL.le hΔ 2
    have h2 : (1 : ℝ) ≤ Δ ^ 2 := by nlinarith
    calc p.L ^ 2 ≤ Δ ^ 2 := this
      _ = Δ ^ 2 * 1 := (mul_one _).symm
      _ ≤ Δ ^ 2 * Δ ^ 2 := by gcongr
      _ = Δ ^ 4 := by ring
  have hA : K / Δ ^ 4 ≤ K / p.L ^ 2 :=
    div_le_div_of_nonneg_left hK0 (by positivity) hΔ4
  have hB : (p.h)⁻¹ * (K / (3 * Δ ^ 3)) ≤ K / p.L ^ 2 := by
    rw [hh]
    have e : p.L / (2 * Real.pi) * (K / (3 * Δ ^ 3)) = K * (p.L / (6 * Real.pi * Δ ^ 3)) := by
      field_simp; ring
    rw [e]
    have hΔ3 : p.L ^ 3 ≤ Δ ^ 3 := pow_le_pow_left₀ hL.le hΔ 3
    have h3 : p.L / (6 * Real.pi * Δ ^ 3) ≤ 1 / p.L ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : p.L * p.L ^ 2 = p.L ^ 3 := by ring
      rw [this]
      nlinarith [Real.pi_gt_three, pow_pos hΔ0 3]
    calc K * (p.L / (6 * Real.pi * Δ ^ 3)) ≤ K * (1 / p.L ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hK0
      _ = K / p.L ^ 2 := by ring
  unfold PrimeSide.Wfun
  calc PrimeSide.psiA c p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2
      ≤ K / Δ ^ 4 + (p.h)⁻¹ * (K / (3 * Δ ^ 3)) := by
        gcongr
    _ ≤ K / p.L ^ 2 + K / p.L ^ 2 := add_le_add hA hB
    _ = 2 * K / p.L ^ 2 := by ring

/-- `ρ(τ) ≤ 5 (c/w)² / L²` once `τ − T`, `2T − τ` and `τ_d − τ` are all `≥ L`
(`[L23]` `PrimeSide.rho_le_majorant`, the `r⁻²` decay of [C26] §5.3). -/
lemma rho_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ) :
    PrimeSide.rho p F τ ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have hL : 0 < p.L := hF.L_pos
  have hτ : τ ∈ Set.Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
  have hmaj := PrimeSide.rho_le_majorant hF hT hτ
  have hW1 := Wfun_le_of_L_le hF h1
  have hW2 := Wfun_le_of_L_le hF h2
  have hψ : PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / p.w) ^ 2 / p.L ^ 2 := by
    have hΔ0 : 0 < p.tau p.d - τ := lt_of_lt_of_le hL h3
    have hw : 0 < p.w := by linarith [hF.one_le_w]
    have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
    have hb : PrimeSide.psiA c p (p.tau p.d - τ) ≤ c / (p.w * (p.tau p.d - τ) ^ 2) :=
      PrimeSide.psiA_le_div_sq hΔ0.ne'
    have hΔ4 : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 4 := by
      have h8 := hF.eight_le_L
      have : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := pow_le_pow_left₀ hL.le h3 2
      have h2' : (1 : ℝ) ≤ (p.tau p.d - τ) ^ 2 := by nlinarith
      calc p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := this
        _ = (p.tau p.d - τ) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (p.tau p.d - τ) ^ 2 * (p.tau p.d - τ) ^ 2 := by gcongr
        _ = (p.tau p.d - τ) ^ 4 := by ring
    calc PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / (p.w * (p.tau p.d - τ) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF _) hb 2
      _ = (c / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by field_simp
      _ ≤ (c / p.w) ^ 2 / p.L ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΔ4
  calc PrimeSide.rho p F τ
      ≤ PrimeSide.Wfun c p (τ - p.T) + PrimeSide.Wfun c p (2 * p.T - τ)
          + PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 := hmaj
    _ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 + 2 * (c / p.w) ^ 2 / p.L ^ 2 + (c / p.w) ^ 2 / p.L ^ 2 :=
        add_le_add (add_le_add hW1 hW2) hψ
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

/-- **The tail bound.**  `|K_∞(τ,τ′) − K(τ,τ′)| ≤ 5 (c/w)² / L²` for two ordinates both at distance
`≥ L` from `T`, `2T` and `τ_d`  (`[L23]` `PrimeSide.abs_Kinf_sub_Kfun_le` at `s = 1`). -/
lemma abs_Kinf_sub_Kfun_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
    (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ τ' : ℝ}
    (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ)
    (h1' : p.L ≤ τ' - p.T) (h2' : p.L ≤ 2 * p.T - τ') (h3' : p.L ≤ p.tau p.d - τ') :
    |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'| ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
  have h := PrimeSide.abs_Kinf_sub_Kfun_le hF τ τ' one_pos
  have hρ := rho_le_of_far hF hT h1 h2 h3
  have hρ' := rho_le_of_far hF hT h1' h2' h3'
  calc |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'|
      ≤ (1 * PrimeSide.rho p F τ + PrimeSide.rho p F τ' / 1) / 2 := h
    _ ≤ (1 * (5 * (c / p.w) ^ 2 / p.L ^ 2) + 5 * (c / p.w) ^ 2 / p.L ^ 2 / 1) / 2 := by
        gcongr
    _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring

end Tail

/-! ### 4. The limit (iii): `Φ(hx)/(aL) → K(x)/K(0)`, uniformly in `x` -/

section Limit

/-- `K(0) = a*₁ = ∫_{−1/2}^{1/2} cos(√2 t) dt`. -/
lemma Kfun_zero_eq_aStar : Kfun 0 = aStar 1 := by
  simp [Kfun, aStar, vStar]

lemma cos_sqrt_two_mul_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) :
    0 ≤ Real.cos (Real.sqrt 2 * t) := by
  apply Real.cos_nonneg_of_mem_Icc
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 := Real.sqrt_nonneg 2
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith [mul_nonneg h0 (by linarith [ht.1] : (0:ℝ) ≤ t + 1 / 2),
    mul_nonneg h0 (by linarith [ht.2] : (0:ℝ) ≤ 1 / 2 - t)]

lemma cos_sqrt_two_mul_pos {t : ℝ} (ht : t ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2)) :
    0 < Real.cos (Real.sqrt 2 * t) := by
  apply Real.cos_pos_of_mem_Ioo
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 := Real.sqrt_nonneg 2
  have hπ := Real.pi_gt_three
  constructor <;> nlinarith [mul_nonneg h0 (by linarith [ht.1] : (0:ℝ) ≤ t + 1 / 2),
    mul_nonneg h0 (by linarith [ht.2] : (0:ℝ) ≤ 1 / 2 - t)]

/-- `K(0) > 0`  (`= √2 sin(1/√2)`; here only positivity of the integrand is used). -/
lemma Kfun_zero_pos : 0 < Kfun 0 := by
  unfold Kfun
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
  · intro t ht
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
    exact cos_sqrt_two_mul_pos ht
  · norm_num

/-- `|K(x)| ≤ K(0)`: the cosine factor `cos(√2 t)` is nonnegative on `[−1/2, 1/2]`. -/
lemma abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 := by
  unfold Kfun
  have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
  calc |∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)|
      ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), |Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t) := by
        apply intervalIntegral.integral_mono_on hab
        · exact ((by fun_prop : Continuous fun t : ℝ =>
            Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)).abs).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun t : ℝ =>
            Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * 0 * t)).intervalIntegrable _ _
        · intro t ht
          simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
          rw [abs_mul, abs_of_nonneg (cos_sqrt_two_mul_nonneg ht)]
          exact mul_le_of_le_one_right (cos_sqrt_two_mul_nonneg ht) (Real.abs_cos_le_one _)

/-- The real part of the paper transform of a real integrable function is its cosine transform. -/
lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
  unfold paperFT
  have hexp : Continuous fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) := by fun_prop
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine hg.ofReal.mul_bdd (c := 1) hexp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Complex.norm_exp]
    simp
  rw [← integral_re_C hint]
  congr 1 with u
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The sharp window `1_{[−L/2,L/2]} cos(√2 u/L)` is integrable. -/
lemma sharpW_integrable {L : ℝ} : Integrable (sharpW 1 L) := by
  unfold sharpW
  rw [integrable_indicator_iff measurableSet_Icc]
  have hc : Continuous fun u : ℝ => vStar 1 (u / L) := by unfold vStar; fun_prop
  exact hc.integrableOn_Icc

/-- The cosine transform of the sharp window at frequency `hx = 2πx/L` is `L·K(x)`
(substitution `u = Lt`). -/
lemma integral_sharpW_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ u, sharpW 1 L u * Real.cos (2 * Real.pi * x / L * u) = L * Kfun x := by
  set f : ℝ → ℝ := fun t => Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t) with hf
  have hind : ∀ u, sharpW 1 L u * Real.cos (2 * Real.pi * x / L * u)
      = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
    intro u
    unfold sharpW vStar
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
      simp only [mul_one]
      congr 2
      field_simp
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_div (f := f) hL.ne',
    smul_eq_mul, show -(L / 2) / L = -(1 : ℝ) / 2 by field_simp; try ring,
    show L / 2 / L = (1 : ℝ) / 2 by field_simp; try ring]
  rfl

/-- `|∫ f cos(r·) − ∫ g cos(r·)| ≤ ‖f − g‖₁`. -/
lemma abs_integral_mul_cos_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
    |(∫ u, f u * Real.cos (r * u)) - ∫ u, g u * Real.cos (r * u)| ≤ ∫ u, |f u - g u| := by
  have hcos : Continuous fun u : ℝ => Real.cos (r * u) := by fun_prop
  have hbd : ∀ u : ℝ, ‖Real.cos (r * u)‖ ≤ 1 := fun u => by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  have hfi : Integrable fun u => f u * Real.cos (r * u) :=
    hf.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hgi : Integrable fun u => g u * Real.cos (r * u) :=
    hg.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  rw [← integral_sub hfi hgi]
  calc |∫ u, (f u * Real.cos (r * u) - g u * Real.cos (r * u))|
      ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u - g u| := by
        refine integral_mono (hfi.sub hgi).abs (hf.sub hg).abs fun u => ?_
        rw [← sub_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

variable {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP hlam h8

/-- `|Φ_D(hx) − L·K(x)| ≤ 2w`: the window and the sharp cutoff differ by `≤ 2w` in `L¹`
(`[L23]` `ThmD.integral_abs_phiDsq_sub_sharp`), and a cosine transform is `1`-Lipschitz in `L¹`. -/
lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) - P.L T * Kfun x| ≤ 2 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  set r := 2 * Real.pi * x / P.L T with hr
  have hV : AdmWindow.VPhiR (P.phiD T) r = ∫ u, P.phiD T u ^ 2 * Real.cos (r * u) :=
    re_paperFT_ofReal (hW.integrable_pow two_pos) r
  have hS : ∫ u, sharpW 1 (P.L T) u * Real.cos (r * u) = P.L T * Kfun x :=
    integral_sharpW_mul_cos hL x
  have hL1 : ∫ u, |P.phiD T u ^ 2 - sharpW P.lam (P.L T) u| ≤ 2 * P.w :=
    integral_abs_phiDsq_sub_sharp hP.taper hP.lam_pos hP.lam_le_one hw (by linarith)
  rw [hlam] at hL1
  rw [hV, ← hS]
  exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) sharpW_integrable r).trans hL1

/-- `|aL − L·K(0)| ≤ 4w`  (`[L23]` `ThmD.aD_close`: `|a_D − a*| ≤ 4w/L`). -/
lemma abs_aL_sub_L_mul_Kfun_zero_le :
    |(P.atD T).a T * P.L T - P.L T * Kfun 0| ≤ 4 * P.w := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have h : |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - aStar P.lam| ≤ 4 * P.w / P.L T :=
    aD_close hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8
  rw [hlam, ← Kfun_zero_eq_aStar] at h
  have ha : (P.atD T).a T = (P.L T)⁻¹ * ∫ u, P.phiD T u ^ 2 := by rw [atD_a_eq_av hP]; rfl
  rw [ha]
  have e : (P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) * P.L T - P.L T * Kfun 0
      = ((P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0) * P.L T := by ring
  rw [e, abs_mul, abs_of_pos hL]
  calc |(P.L T)⁻¹ * (∫ u, P.phiD T u ^ 2) - Kfun 0| * P.L T ≤ 4 * P.w / P.L T * P.L T :=
        mul_le_mul_of_nonneg_right h hL.le
    _ = 4 * P.w := by field_simp

/-- **The normalised full-grid overlap converges to `k`, uniformly in `x`:**
`|Φ_D(hx)/(aL) − k(x)| ≤ 12w/L` for every real `x`. -/
lemma abs_VPhiR_div_sub_kfun_le (h4π : 4 * Real.pi * P.w ≤ P.L T) (x : ℝ) :
    |AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) / ((P.atD T).a T * P.L T) - kfun x|
      ≤ 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have hw : 0 < P.w := hW.w_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP hlam h8 x
  have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP hlam h8
  have hK0 : 0 < Kfun 0 := Kfun_zero_pos
  have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
  set V := AdmWindow.VPhiR (P.phiD T) (2 * Real.pi * x / P.L T) with hV
  set A := (P.atD T).a T * P.L T with hA
  set K := Kfun x with hK'
  set K0 := Kfun 0 with hK0'
  have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
  have hApos : 0 < A := by linarith
  have e : V / A - K / K0 = (V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0) := by
    field_simp
    ring
  unfold kfun
  rw [e]
  have h2' : |P.L T * K0 - A| ≤ 4 * P.w := by rw [abs_sub_comm]; exact h2
  calc |(V - P.L T * K) / A + K * (P.L T * K0 - A) / (A * K0)|
      ≤ |(V - P.L T * K) / A| + |K * (P.L T * K0 - A) / (A * K0)| := abs_add_le _ _
    _ = |V - P.L T * K| / A + |K| * |P.L T * K0 - A| / (A * K0) := by
        rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
    _ ≤ 2 * P.w / A + K0 * (4 * P.w) / (A * K0) := by gcongr
    _ = 6 * P.w / A := by field_simp; ring
    _ ≤ 12 * P.w / P.L T := by
        rw [div_le_div_iff₀ hApos hL]
        nlinarith

end Limit

/-! ### 5. Assembly: one height `T` -/

section Assembly

/-- A retained zero is at ordinate distance `≥ L` from `T`, from `2T` and from the last grid point
`τ_d` (the strips of normalised width `L²` are `2πL ≥ L` wide in the ordinate). -/
lemma retained_far {Z : ZeroConfig} {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
    {z : ZI Z T} (hz : z ∈ retained Z P T) :
    P.L T ≤ (z : ℂ).im - T ∧ P.L T ≤ 2 * T - (z : ℂ).im ∧ P.L T ≤ P.tau T (P.d T) - (z : ℂ).im := by
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hz
  unfold xnorm at h1 h2
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hd : ((P.d T : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
  have h1' : 2 * Real.pi * P.L T ^ 2 ≤ P.L T * ((z : ℂ).im - T) := by
    have := (le_div_iff₀ hπ).mp h1; linarith
  have h2' : P.L T * ((z : ℂ).im - T) ≤ 2 * Real.pi * ((P.d T : ℝ) - P.L T ^ 2) := by
    have := (div_le_iff₀ hπ).mp h2; linarith
  have hd' : 2 * Real.pi * (P.d T : ℝ) ≤ P.L T * T := by
    have := (le_div_iff₀ hπ).mp hd; linarith
  have g1 : 2 * Real.pi * P.L T ≤ (z : ℂ).im - T := by
    have : P.L T * (2 * Real.pi * P.L T) ≤ P.L T * ((z : ℂ).im - T) := by nlinarith
    exact le_of_mul_le_mul_left this hL
  have g2 : 2 * Real.pi * P.L T ≤ 2 * T - (z : ℂ).im := by
    have : P.L T * ((z : ℂ).im - T) ≤ P.L T * (T - 2 * Real.pi * P.L T) := by nlinarith
    have := le_of_mul_le_mul_left this hL
    linarith
  have hL2 : P.L T ≤ 2 * Real.pi * P.L T := by nlinarith
  refine ⟨by linarith, by linarith, ?_⟩
  -- τ_d − γ = T + d·(2π/L) − γ
  have htau : P.tau T (P.d T) = T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
    simp only [Params.tau, Params.hgrid, Int.cast_natCast]
  rw [htau]
  have e : T + (P.d T : ℝ) * (2 * Real.pi / P.L T) - (z : ℂ).im
      = (2 * Real.pi * (P.d T : ℝ) - P.L T * ((z : ℂ).im - T)) / P.L T := by
    field_simp
    ring
  rw [e, le_div_iff₀ hL]
  nlinarith

/-- The finite Poisson sum of the height-`T` window is `[L23]`'s `PrimeSide.Kfun` of the D-data. -/
lemma Kfun_eq_sum {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
    PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'
      = ∑ k : Fin ((P.atD T).d T), (P.atD T).phiHatR T (γ - (P.atD T).tau T k)
          * (P.atD T).phiHatR T (γ' - (P.atD T).tau T k) := by
  rw [atD_phiHatR_eq hP T]; rfl

/-- `K_∞(γ,γ′) = L·Φ_D(γ−γ′)` for the D-data. -/
lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
    PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      = P.L T * AdmWindow.VPhiR (P.phiD T) (γ - γ') := rfl

/-- **One height.**  Under the side conditions at height `T` (`8w ≤ L`, `4πw ≤ L`, the §5 local
hypotheses of the D-data), every pair of retained zeros satisfies
`|⟨v_ρ, v_ρ′⟩ − k(x_ρ − x_ρ′)| ≤ 10 (c_DT/w)²/L⁴ + 12w/L`, with no condition on `x_ρ − x_ρ′`. -/
theorem gram_close_of {P : Params} (hP : P.Valid) (hlam : P.lam = 1) {T : ℝ} (hT : 0 < T)
    (h8 : 8 * P.w ≤ P.L T) (h4π : 4 * Real.pi * P.w ≤ P.L T)
    (hF : PrimeSide.LocalHypsCoreW (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T))
    (Z : ZeroConfig) (z z' : retained Z (P.atD T) T) :
    ‖gram Z (P.atD T) T z z'
        - (kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z') : ℂ)‖
      ≤ 10 * (cDT P.ϱ P.lam / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
  have hW := admWindow_params hP h8
  have hL := hW.L_pos
  have ha : 1 / 2 ≤ (P.atD T).a T := (aD_range_of hP h8 h4π).1
  have hc : 0 < aL2 (P.atD T) T := by
    unfold aL2; rw [Params.atD_L]; positivity
  set K : ℝ := (cDT P.ϱ P.lam / P.w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  rw [gram_apply Z (P.atD T) T (phiHatReal_atD hP T) hc.le z z', ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
  set γ : ℝ := (z.1 : ℂ).im with hγ
  set γ' : ℝ := (z'.1 : ℂ).im with hγ'
  -- the tail
  obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := P.atD T) hL hT.le z.2
  obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := P.atD T) hL hT.le z'.2
  have htail : |PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ'
      - PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
    abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'
  -- the limit
  have hx : 2 * Real.pi * (xret Z (P.atD T) T z - xret Z (P.atD T) T z') / P.L T = γ - γ' := by
    unfold xret xnorm
    rw [Params.atD_L]
    field_simp
    ring
  have hlim := abs_VPhiR_div_sub_kfun_le hP hlam h8 h4π (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
  rw [hx] at hlim
  -- algebra
  set A : ℝ := (P.atD T).a T with hA
  set V : ℝ := AdmWindow.VPhiR (P.phiD T) (γ - γ') with hV
  set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (P.localFunD T) γ γ' with hKf
  have hKinf : PrimeSide.Kinf (P.toSetting T) (P.localFunD T) γ γ' = P.L T * V := Kinf_eq T γ γ'
  rw [hKinf] at htail
  have haL2 : aL2 (P.atD T) T = A * P.L T ^ 2 := by unfold aL2; rw [Params.atD_L]
  rw [haL2]
  have hApos : 0 < A := by linarith
  have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')
      = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')) := by
    field_simp
    ring
  rw [hsplit]
  have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hL 2]
  calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
        + (V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z'))|
      ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
        + |V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')| := abs_add_le _ _
    _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
        + |V / (A * P.L T) - kfun (xret Z (P.atD T) T z - xret Z (P.atD T) T z')| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
    _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
        gcongr
    _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
        field_simp
        ring

end Assembly

/-! ### 6. The strip count ([A] Lemma 3.1, "the number deleted is `o(N(T,2T))`") -/

section Strips

variable (Z : ZeroConfig)

/-- Windows split: `(a, c] = (a, b] ∪ (b, c]`. -/
lemma window_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Z.window a c = Z.window a b ∪ Z.window b c := by
  ext ρ
  simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hc⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hc⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, hb, hc⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 hb, hc⟩

/-- Window additivity of the abstract count: `N(a,c] = N(a,b] + N(b,c]`. -/
lemma N_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : Z.N a c = Z.N a b + Z.N b c := by
  unfold ZeroConfig.N
  rw [window_union Z h1 h2]
  refine finsum_mem_union ?_ (Z.finite_window a b) (Z.finite_window b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, hb', _⟩
  exact absurd hb (not_le.2 hb')

/-- Window monotonicity of the abstract count: `(a,b] ⊆ (c,d] ⇒ N(a,b] ≤ N(c,d]`. -/
lemma N_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Z.N a b ≤ Z.N c d := by
  unfold ZeroConfig.N
  have hsub : Z.window a b ⊆ Z.window c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  have hfab : (Z.window a b).Finite := Z.finite_window a b
  have hfcd : (Z.window c d).Finite := Z.finite_window c d
  rw [finsum_mem_eq_finite_toFinset_sum _ hfab, finsum_mem_eq_finite_toFinset_sum _ hfcd]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

/-- Distinct points are at most the count with multiplicity: `#window ≤ N`. -/
lemma ncard_window_le_N (a b : ℝ) : (Z.window a b).ncard ≤ Z.N a b := by
  unfold ZeroConfig.N
  have hfin : (Z.window a b).Finite := Z.finite_window a b
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  exact Z.one_le_mult ρ hρ.1

/-- The local count over `n` consecutive unit windows: `N(a, a+n] ≤ n A₀ log(|a| + n + 3)`. -/
lemma N_le_of_local_count {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (n : ℕ) :
    (Z.N a (a + n) : ℝ) ≤ n * A₀ * Real.log (|a| + n + 3) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_mul]
    have : Z.N a a = 0 := by
      unfold ZeroConfig.N
      have : Z.window a a = ∅ := by
        ext ρ
        simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨_, h1, h2⟩; linarith
      rw [this, finsum_mem_empty]
    rw [this]; simp
  | succ n ih =>
    have hsplit : Z.N a (a + (n + 1 : ℕ)) = Z.N a (a + n) + Z.N (a + n) (a + n + 1) := by
      push_cast
      rw [← add_assoc]
      exact N_add Z (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) (by linarith)
    rw [hsplit]
    push_cast
    have h1 := hloc (a + n)
    have hlogmono : Real.log (|a| + n + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlogmono' : Real.log (|a + n| + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
      Real.log_le_log (by positivity) (by linarith [abs_add_le a (n : ℝ), abs_of_nonneg (n.cast_nonneg : (0:ℝ) ≤ n)])
    have hA : 0 ≤ A₀ := by linarith
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    calc ((Z.N a (a + n) : ℕ) : ℝ) + ((Z.N (a + n) (a + n + 1) : ℕ) : ℝ)
        ≤ n * A₀ * Real.log (|a| + n + 3) + A₀ * Real.log (|a + n| + 3) := add_le_add ih h1
      _ ≤ n * A₀ * Real.log (|a| + (n + 1) + 3) + A₀ * Real.log (|a| + (n + 1) + 3) := by
          gcongr
      _ = (n + 1) * A₀ * Real.log (|a| + (n + 1) + 3) := by ring

/-- The local count over a window of real length `ℓ ≥ 0`: `N(a, a+ℓ] ≤ (ℓ+1) A₀ log(|a| + ℓ + 4)`. -/
lemma N_le_of_local_count_real {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (Z.N a (a + ℓ) : ℝ) ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by
  set n : ℕ := ⌈ℓ⌉₊ with hn
  have hn1 : ℓ ≤ n := Nat.le_ceil ℓ
  have hn2 : (n : ℝ) < ℓ + 1 := Nat.ceil_lt_add_one hℓ
  have hA : 0 ≤ A₀ := by linarith
  have hmono : (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := by
    exact_mod_cast N_mono Z le_rfl (by linarith)
  have hlog : Real.log (|a| + n + 3) ≤ Real.log (|a| + ℓ + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (|a| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg a, (n.cast_nonneg : (0:ℝ) ≤ n)])
  calc (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := hmono
    _ ≤ n * A₀ * Real.log (|a| + n + 3) := N_le_of_local_count Z hA₀ hloc a n
    _ ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by gcongr

end Strips

/-! ### 7. The simple on-line zeros of `(T, 2T]` not retained lie in the two strips -/

section StripInclusion

/-- `N₀ˢ(T,2T) ≤ #retained + N(T, T+2πL] + N(2T − 2πL − 2π/L, 2T]`: a simple on-line zero of
`(T, 2T]` is retained unless its normalised ordinate `x` has `x < L²` (the lower strip, ordinate
width `2πL`) or `x > d − L²` (the upper strip, ordinate width `< 2πL + 2π/L` since
`d > LT/2π − 1`). -/
lemma N0s_le_card_retained_add (Z : ZeroConfig) (P : Params) (T : ℝ) (hL : 0 < P.L T) :
    (Z.N0s T (2 * T) : ℝ) ≤ (retained Z P T).card
      + Z.N T (T + 2 * Real.pi * P.L T)
      + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T) := by
  classical
  set ℓ : ℝ := 2 * Real.pi * P.L T with hℓ
  set ℓ' : ℝ := 2 * Real.pi * P.L T + 2 * Real.pi / P.L T with hℓ'
  set A : Set ℂ := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple with hA
  set R : Finset ℂ := (retained Z P T).map (Function.Embedding.subtype _) with hR
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
  have hsub : A ⊆ (↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T) := by
    rintro ρ ⟨⟨⟨hρc, hT1, hT2⟩, hre⟩, hm⟩
    have hre' : ρ.re = 1 / 2 := hre
    have hm' : Z.mult ρ = 1 := hm
    have hρZ : ρ ∈ ZI Z T := by
      rw [mem_ZI, mem_ZIprime_iff]
      exact ⟨hρc, by linarith, by linarith⟩
    set z : ZI Z T := ⟨ρ, hρZ⟩ with hz
    have hzS : z ∈ (bdata Z P T).S₁ := by
      simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(mkData_σ_eq_iff Z T _ _ z).mpr hre', hm'⟩
    by_cases hx : P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
    · left; left
      rw [Finset.mem_coe, hR, Finset.mem_map]
      exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hx⟩, rfl⟩
    · rw [not_and_or] at hx
      rcases hx with hx | hx
      · left; right
        refine ⟨hρc, hT1, ?_⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (div_lt_iff₀ hπ).mp hx
        have : P.L T * (ρ.im - T) < P.L T * ℓ := by rw [hℓ]; nlinarith
        have := lt_of_mul_lt_mul_left this hL.le
        show ρ.im ≤ T + ℓ
        linarith
      · right
        refine ⟨hρc, ?_, hT2⟩
        push Not at hx
        unfold xnorm at hx
        have h1 := (lt_div_iff₀ hπ).mp hx
        have hd : P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := Nat.lt_floor_add_one _
        have hd' := (div_lt_iff₀ hπ).mp hd
        have hLℓ' : P.L T * ℓ' = 2 * Real.pi * P.L T ^ 2 + 2 * Real.pi := by
          rw [hℓ']; field_simp
        have : P.L T * (2 * T - ℓ') < P.L T * ρ.im := by nlinarith
        exact lt_of_mul_lt_mul_left this hL.le
  have hfin : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).Finite :=
    ((R.finite_toSet).union (Z.finite_window _ _)).union (Z.finite_window _ _)
  have hN0s : Z.N0s T (2 * T) = A.ncard := rfl
  have hcard : ((↑R : Set ℂ).ncard : ℝ) = (retained Z P T).card := by
    rw [Set.ncard_coe_finset, hR, Finset.card_map]
  have hlo := ncard_window_le_N Z T (T + ℓ)
  have hhi := ncard_window_le_N Z (2 * T - ℓ') (2 * T)
  have hu : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).ncard
      ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_union_le _ _).trans (by gcongr; exact Set.ncard_union_le _ _)
  have hle : A.ncard ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard
      + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
    (Set.ncard_le_ncard hsub hfin).trans hu
  rw [hN0s]
  calc (A.ncard : ℝ) ≤ ((↑R : Set ℂ).ncard : ℝ) + (Z.window T (T + ℓ)).ncard
        + (Z.window (2 * T - ℓ') (2 * T)).ncard := by exact_mod_cast hle
    _ ≤ (retained Z P T).card + Z.N T (T + ℓ) + Z.N (2 * T - ℓ') (2 * T) := by
        rw [hcard]
        have hlo' : ((Z.window T (T + ℓ)).ncard : ℝ) ≤ Z.N T (T + ℓ) := by exact_mod_cast hlo
        have hhi' : ((Z.window (2 * T - ℓ') (2 * T)).ncard : ℝ) ≤ Z.N (2 * T - ℓ') (2 * T) := by
          exact_mod_cast hhi
        linarith

end StripInclusion

/-! ### 8. The two strips hold `O(L²)` zeros -/

section StripCount

/-- At heights with `1 ≤ T`, `1 ≤ L ≤ T` and `log T ≤ L + 2π`, the two strips of ordinate width
`2πL` and `2πL + 2π/L` hold at most `1600 A₀ L²` zeros (local count `N(t+1) − N(t) ≤ A₀ log(t+3)`). -/
lemma strips_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {T L : ℝ} (hT : 1 ≤ T)
    (hL1 : 1 ≤ L) (hLT : L ≤ T) (hlogT : Real.log T ≤ L + 2 * Real.pi) :
    (Z.N T (T + 2 * Real.pi * L) : ℝ) + Z.N (2 * T - (2 * Real.pi * L + 2 * Real.pi / L)) (2 * T)
      ≤ 1600 * A₀ * L ^ 2 := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_four
  have hπ3 := Real.pi_gt_three
  have hA : 0 ≤ A₀ := by linarith
  set ℓ : ℝ := 2 * Real.pi * L with hℓ
  set ℓ' : ℝ := 2 * Real.pi * L + 2 * Real.pi / L with hℓ'
  have hLpos : 0 < L := by linarith
  have hℓ0 : 0 ≤ ℓ := by positivity
  have h2πL : 2 * Real.pi / L ≤ 2 * Real.pi * L := by
    rw [div_le_iff₀ hLpos]; nlinarith
  have hℓ'0 : 0 ≤ ℓ' := by positivity
  have hℓ'le : ℓ' ≤ 4 * Real.pi * L := by rw [hℓ']; linarith
  have hℓle : ℓ ≤ ℓ' := by
    have : 0 ≤ 2 * Real.pi / L := by positivity
    rw [hℓ, hℓ']; linarith
  have h1 := N_le_of_local_count_real Z hA₀ hloc T hℓ0
  have h2 := N_le_of_local_count_real Z hA₀ hloc (2 * T - ℓ') hℓ'0
  rw [sub_add_cancel] at h2
  -- both log arguments are ≤ M := (6 + 8π) T
  set M : ℝ := (6 + 8 * Real.pi) * T with hM
  have hM1 : |T| + ℓ + 4 ≤ M := by
    rw [abs_of_pos (by linarith), hM]; nlinarith
  have hM2 : |2 * T - ℓ'| + ℓ' + 4 ≤ M := by
    have : |2 * T - ℓ'| ≤ 2 * T + ℓ' := by
      rw [abs_le]; constructor <;> linarith
    rw [hM]; nlinarith
  have hlogM : Real.log M ≤ (6 + 10 * Real.pi) * L := by
    have hT0 : 0 < T := by linarith
    rw [hM, Real.log_mul (by positivity) hT0.ne']
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
    nlinarith
  have hlog1 : Real.log (|T| + ℓ + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM1).trans hlogM
  have hlog2 : Real.log (|2 * T - ℓ'| + ℓ' + 4) ≤ (6 + 10 * Real.pi) * L :=
    (Real.log_le_log (by positivity) hM2).trans hlogM
  have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by nlinarith
  have hcoef' : ℓ + 1 ≤ (4 * Real.pi + 1) * L := by linarith
  have hb1 : (Z.N T (T + ℓ) : ℝ) ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h1.trans ?_
    have h0 : 0 ≤ Real.log (|T| + ℓ + 4) := Real.log_nonneg (by linarith [abs_nonneg T])
    gcongr
  have hb2 : (Z.N (2 * T - ℓ') (2 * T) : ℝ)
      ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
    refine h2.trans ?_
    have h0 : 0 ≤ Real.log (|2 * T - ℓ'| + ℓ' + 4) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * T - ℓ')])
    gcongr
  have hL2 : 0 ≤ A₀ * L ^ 2 := by positivity
  have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by nlinarith
  calc (Z.N T (T + ℓ) : ℝ) + Z.N (2 * T - ℓ') (2 * T)
      ≤ 2 * ((4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L)) := by linarith
    _ = 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) * (A₀ * L ^ 2) := by ring
    _ ≤ 1600 * (A₀ * L ^ 2) := by
        gcongr
    _ = 1600 * A₀ * L ^ 2 := by ring

end StripCount

end Zeta23Ext.Bridge
