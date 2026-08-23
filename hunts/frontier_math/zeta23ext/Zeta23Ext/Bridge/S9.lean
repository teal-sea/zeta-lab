/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

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
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

open Classical

/-- **S9** ([A] eq:kernel-limit).  For every `R₀` and `δ > 0`, eventually in `T`, every pair of
retained zeros at normalised separation `≤ R₀` has Gram entry within `δ` of `k(x_ρ − x_ρ′)`.

Residual goal (HANDWRITTEN, LARGE): (i) the full-grid identity
`(aL²)⁻¹ Σ_{j∈ℤ} φ̂(γ−τ_j) φ̂(γ′−τ_j) = Φ(γ−γ′)/(aL)` (`[L23]` `hasSum_phiHatR_mul`);
(ii) the terms with `j ∉ [0, d)` contribute `O(L⁻²)` uniformly for retained pairs at bounded
separation (the `r⁻²` decay of [C26] §5.3; this is what the strips of width `L²` buy);
(iii) `Φ(hx)/(aL) → K(x)/K(0)` uniformly on compacts, because `φ_D(Lt)² → cos(√2 t) 1_{[−1/2,1/2]}`
in `L¹` as the fixed-width taper has rescaled length `O(L⁻¹)`. -/
theorem kernel_limit (Z : ZeroConfig) (H : PaperInputs Z) (R₀ : ℝ) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      |xret Z (mtParams T) T z - xret Z (mtParams T) T z'| ≤ R₀ →
      ‖gram Z (mtParams T) T z z'
          - (kfun (xret Z (mtParams T) T z - xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  sorry

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
