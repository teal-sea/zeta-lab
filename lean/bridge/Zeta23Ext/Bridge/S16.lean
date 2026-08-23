/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Zeta23Ext.Bridge.Defs

/-!
# S16: solving the linear inequality for `N₀ˢ`  ([A] §5, lines 437–457)

From `(1 − A₀/m) N₀ˢ ≥ (H − (n−1)(m−1)/(pm)) N − o(N)` divide by `1 − A₀/m > 0` and let `T → ∞`.
Proved outright: it is algebra.  Also the closed forms at the published and laboratory
parameters, seven-point and eight-point.
-/

noncomputable section

open Filter
open Zeta23.ThmD

namespace Zeta23Ext.Bridge

/-- `1 − c(m−(n−1))/m > 0` when `c(m − (n−1)) ≤ 1 < m`. -/
lemma one_sub_div_pos {c : ℝ} {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1) :
    0 < 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
  have hmpos : (0 : ℝ) < m := by linarith
  rw [sub_pos, div_lt_one hmpos]
  linarith

/-- **S16**, `n`-point form.  The ε-form division: if eventually
`(H − (n−1)(m−1)/(pm) − ε) N ≤ (1 − c(m−(n−1))/m) N₀ˢ` for every `ε > 0`, then eventually
`(Phi_n n c m p − ε) N ≤ N₀ˢ` for every `ε > 0`.  Pure algebra; the only `n` in it is the
numeral that the paper writes as `6`. -/
theorem solve_linear {N N0 : ℝ → ℝ} {c : ℝ} {n m p : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (hA0 : c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ 1)
    (h : ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N T
        ≤ (1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m) * N0 T) :
    ∀ ε > 0, ∀ᶠ T in atTop, (Phi_n n c m p - ε) * N T ≤ N0 T := by
  intro ε hε
  have hD := one_sub_div_pos hn hm hA0
  set Dn : ℝ := 1 - c * ((m : ℝ) - ((n : ℝ) - 1)) / m with hDn
  filter_upwards [h (ε * Dn) (mul_pos hε hD)] with T hT
  have hPhi : Phi_n n c m p
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn := rfl
  rw [hPhi]
  have : (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m)) / Dn - ε
      = (HD 1 - ((n : ℝ) - 1) * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε * Dn) / Dn := by
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

/-- **This laboratory's own parameters.**  The seven-point pressure sweep of
`hunts/ainta_seven_point` puts the peak at `p = 3400`, where the verifier accepts
`c = 34697/10⁷` and refuses `34701/10⁷`; the cap `c(m − 6) ≤ 1` then gives `m = 294`.  At those
values the constant is `(520 625 000 H − 915 625) / 518 855 453 = 0.673029553…`, against the
paper's `0.673008527…` at `(19/5000, 269, 3000)`.  This is arithmetic in `Phi`, not a new
theorem about ζ: what changes is which certificate is assumed, and that assumption is the
hypothesis `hCert` of `seven_point_bound`. -/
theorem Phi_lab : Phi (34697 / 10000000) 294 3400
    = (520625000 * HD 1 - 915625) / 518855453 := by
  unfold Phi
  norm_num
  field_simp
  ring

/-- **The eight-point instance.**  `hunts/ainta_seven_point`'s eight-point run accepts
`F 8 3200 ≥ 41763/10⁷` (all 64 shards; floor bracketed `0.0041763 ≤ inf F₇ ≤ 0.0041773221`), and
the cap `c(m − 7) ≤ 1` gives `m ≤ 7 + ⌊10⁷/41763⌋ = 246`.  At those values
`Phi₈ = (2 460 000 000 H − 5 359 375)/2 450 018 643 = 0.673052982…`, against the seven-point
laboratory value `0.673029553…`.  Arithmetic in `Phi_n`, not a new theorem about ζ. -/
theorem Phi_lab8 : Phi_n 8 (41763 / 10000000) 246 3200
    = (2460000000 * HD 1 - 5359375) / 2450018643 := by
  unfold Phi_n
  norm_num
  field_simp
  ring

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms one_sub_div_pos
#print axioms solve_linear
#print axioms Phi_paper
#print axioms Phi_paper'
#print axioms Phi_lab
#print axioms Phi_lab8

end Zeta23Ext.Bridge
