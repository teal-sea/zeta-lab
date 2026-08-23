/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

/-!
# S16: solving the linear inequality for `N₀ˢ`  ([A] §5, lines 437–457)

From `(1 − A₀/m) N₀ˢ ≥ (H − 6(m−1)/(pm)) N − o(N)` divide by `1 − A₀/m > 0` and let `T → ∞`.
Proved outright: it is algebra.  Also the paper's closed form at the published parameters.
-/

noncomputable section

open Filter
open Zeta23.ThmD

namespace Zeta23Ext.Bridge

/-- `1 − c(m−6)/m > 0` when `c(m − 6) ≤ 1 < m`. -/
lemma one_sub_div_pos {c : ℝ} {m : ℕ} (hm : 7 ≤ m) (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    0 < 1 - c * ((m : ℝ) - 6) / m := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith

/-- **S16.**  The ε-form division: if eventually
`(H − 6(m−1)/(pm) − ε) N ≤ (1 − c(m−6)/m) N₀ˢ` for every `ε > 0`, then eventually
`(Phi c m p − ε) N ≤ N₀ˢ` for every `ε > 0`. -/
theorem solve_linear {N N0 : ℝ → ℝ} {c : ℝ} {m p : ℕ} (hm : 7 ≤ m)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N T ≤ (1 - c * ((m : ℝ) - 6) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop, (Phi c m p - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - 6) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have hPhi : Phi c m p = (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn := rfl
  rw [hPhi]
  have : (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn - ε
      = (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε * Dn) / Dn := by
    field_simp
  rw [this, div_mul_eq_mul_div, div_le_iff₀ hD]
  linarith

/-- **Non-vacuity.**  At the published parameters `c = 19/5000`, `m = 269`, `p = 3000` the constant
is the paper's `(1 345 000 H − 2 680) / 1 340 003` ([A] Theorem 1.1, line 111). -/
theorem Phi_paper : Phi (19 / 5000) 269 3000 = (1345000 * HD 1 - 2680) / 1340003 := by
  unfold Phi
  norm_num
  field_simp
  ring

/-- `H = 3/2 − (1/√2) cot(1/√2)` is `[L23]`'s `HD 1` (`HD_one`). -/
theorem Phi_paper' :
    Phi (19 / 5000) 269 3000
      = (1345000 * (3 / 2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹))
          - 2680) / 1340003 := by
  rw [Phi_paper, HD_one]

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms one_sub_div_pos
#print axioms solve_linear
#print axioms Phi_paper
#print axioms Phi_paper'

end Zeta23Ext.Bridge
