/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Zeta23Ext.Bridge.S7
import Zeta23Ext.Bridge.S8
import Zeta23Ext.Bridge.S9
import Zeta23Ext.Bridge.S13
import Zeta23Ext.Bridge.S14
import Zeta23Ext.Bridge.S15
import Zeta23Ext.Bridge.S16

/-!
# The seven-point simple-zero bound, assembled  ([A] Theorem 1.1)

`seven_point_bound` mirrors `[L23]`'s `thmD₀_simple_mult` (`Zeta23/ThmD/Mult.lean`):

  `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (Phi c m p − ε) · N(T,2T) ≤ N₀ˢ(T,2T)`

for Mathlib's `riemannZeta` (`Ncount`, `N0simple` of `Zeta23/Statement.lean`), from the
certificate hypothesis `hCert : ∀ g ≥ 0, c ≤ F6 p g` (S10, the Arb certificate, taken as a
hypothesis the way `[L23]` takes `EnclOK`) and the block cap `hA0 : c(m − 6) ≤ 1`.

**The whole Bridge tree is sorry-free** (integrated 2026-08-23 from the five attack branches
`bridge/{skeleton,finite,pinching,S8,S9}`).  Every step lemma S6–S9, S11–S16 is proved, and
`#print axioms seven_point_bound` reports `[propext, Classical.choice, Quot.sound]`.  The only
hypotheses of the theorem are the two the paper itself takes as inputs, `hCert` (S10) and `hA0`
([A] eq:mA); nothing else is assumed.  The assembly below is the paper's deduction ([A] §§2, 5)
written as filter arithmetic:

  S7 ⟶ (S14) ⟶ S8 ⟶ `(H − η)N + D(M°) ≤ N₀ˢ`
  S9 + S13 ⟶ uniform per-block bound ⟶ S15 (with S14) ⟶ `D(M°) ≥ (A₀/m) N₀ˢ − (6(m−1)/pm) N − o(N)`
  S16 ⟶ the bound.

Side conditions `7 ≤ m`, `0 < p`, `0 < c`: blocks need seven points, the pressure term needs a
positive denominator, and a certificate constant `c ≤ 0` is vacuous (`F6 ≥ 0`); the published
parameters `(19/5000, 269, 3000)` satisfy all three.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD

namespace Zeta23Ext.Bridge

open Classical

/-- The §6 parameters at `λ = 1`; `mtParams T = P₀.atD T` is the height-`T` window. -/
def P₀ : Params := paramsOf stdProfile 1

lemma P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl

lemma eventually_L_pos : ∀ᶠ T in atTop, 0 < (mtParams T).L T :=
  (tendsto_L P₀_valid).eventually_gt_atTop 0

/-! ### S7 at the Montgomery–Taylor window, with `D(M) ≥ D(M°)` (S14) -/

/-- The counting inequality with defect, at the concrete window, in the form S8 consumes.
Instantiates S7 at `blockData Z T (mtParams T)` exactly as `[L23]`'s `hatAz_mult2` instantiates
`mult_two`, and pinches `D(M)` down to `D(M°)` by S14. -/
theorem eventually_h7 (Z : ZeroConfig) :
    ∀ᶠ T in atTop,
      4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
        - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
        - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
  filter_upwards [eventually_w8 P₀_valid, eventually_w4pi P₀_valid] with T h8 h4π
  set P := mtParams T with hP
  have hconj : PhiHatConj T P := phiHatConj
  have hL : 0 < P.L T := by
    change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
  have ha : 1 / 2 ≤ P.a T := (aD_range_of P₀_valid h8 h4π).1
  have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
  have hPois : PoissonSq T P := poissonSqD P₀_valid h8
  have h7 := count_defect (bdata Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
    (sum_normSq_v_le Z T P hconj phiHatReal hPois)
  have hD : Dcirc Z P T ≤ defect (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) :=
    pinching_submatrix (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) (toS₁ Z P T)
      (toS₁_injective Z P T)
  have hA : P.hat T (Z.Az P T) = (bdata Z P T).blockP (aL2 P T) + (bdata Z P T).blockQ (aL2 P T) :=
    hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hN : (Z.NIprime T : ℝ) = ((bdata Z P T).Ncount : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  have hs : (Z.s1 T : ℝ) = ((bdata Z P T).s₁ : ℝ) := by
    rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  rw [hA, hN, hs]
  linarith [h7, hD]

/-! ### S9 + S13: the per-block bound, uniform in `T`  ([A] eq:269block) -/

/-- Every block of `m` retained zeros satisfies `D(G_B) + (6/p) span(B) ≥ A₀ − η`, eventually
in `T`.  [A] §4 after eq:mA: "If `span(B)/500 ≥ A₀` then eq:269block is immediate. Otherwise
`span(B) < 500`, so Lemma 3.1 applies uniformly to every pair in `B`." -/
theorem block_bound_eventually (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {m p : ℕ}
    (hm : 7 ≤ m) (hp : 0 < p)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g) (hA0 : c * ((m : ℝ) - 6) ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ B : Finset (retained Z (mtParams T) T), B.card = m →
      c * ((m : ℝ) - 6) - η ≤ blockDefect (gram_isHermitian Z (mtParams T) T) B
        + (6 / (p : ℝ)) * spanOf (xret Z (mtParams T) T) B := by
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmsq : 0 < 2 * (m : ℝ) ^ 2 := by positivity
  set δ : ℝ := η / (2 * (m : ℝ) ^ 2) with hδ
  have hδpos : 0 < δ := div_pos hη hmsq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [kernel_limit Z H ((p : ℝ) / 6) δ hδpos, eventually_L_pos] with T hclose hL
  intro B hB
  set x := xret Z (mtParams T) T with hx
  set q : ℝ := 6 / (p : ℝ) with hq
  have hq0 : 0 < q := by positivity
  by_cases hsp : c * ((m : ℝ) - 6) ≤ q * spanOf x B
  · linarith [blockDefect_nonneg (gram_isHermitian Z (mtParams T) T) B]
  · rw [not_le] at hsp
    have hR : spanOf x B ≤ (p : ℝ) / 6 := by
      have h1 : spanOf x B < 1 / q := by
        rw [lt_div_iff₀ hq0]; linarith
      have h1q : 1 / q = (p : ℝ) / 6 := one_div_div 6 (p : ℝ)
      linarith
    have hcl : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        ‖gram Z (mtParams T) T i j - (kfun (x i - x j) : ℂ)‖ ≤ δ := by
      intro i hi j hj _
      exact hclose i j ((abs_sub_le_spanOf x hi hj).trans hR)
    have h13 := block_bound hm hp hCert hA0 x (gram_posSemidef Z (mtParams T) T) B hB
      (xret_injective Z (mtParams T) T hL).injOn hδpos.le hcl
    have hη' : 2 * (m : ℝ) ^ 2 * δ = η := by rw [hδ]; field_simp
    rw [hη'] at h13
    exact h13

/-! ### S8 + S9 + S13 + S14 + S15: the pre-S16 inequality  ([A] §5, lines 437–443) -/

/-- `(H − 6(m−1)/(pm) − ε) N ≤ (1 − A₀/m) N₀ˢ` eventually, for every `ε > 0`.  This is [A]'s
display after "Substitute eq:defect-numbers into eq:global-defect", with every `o(N)` made an
explicit `η N`. -/
theorem pre_solve (Z : ZeroConfig) (H : PaperInputs Z) {c : ℝ} {m p : ℕ}
    (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g) (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (1 - c * ((m : ℝ) - 6) / m) * (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  have hm' : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hA₀pos : 0 < c * ((m : ℝ) - 6) := mul_pos hc (by linarith)
  have hq0 : (0 : ℝ) ≤ 6 / (p : ℝ) := div_nonneg (by norm_num) hp'.le
  have hq6 : (6 : ℝ) / (p : ℝ) ≤ 6 := by
    rw [div_le_iff₀ hp']; nlinarith
  have hηpos : 0 < min (ε / 10) (c * ((m : ℝ) - 6)) := lt_min (by positivity) hA₀pos
  have hηε : min (ε / 10) (c * ((m : ℝ) - 6)) ≤ ε / 10 := min_le_left _ _
  have hηA : min (ε / 10) (c * ((m : ℝ) - 6)) ≤ c * ((m : ℝ) - 6) := min_le_right _ _
  have hA' : 0 ≤ c * ((m : ℝ) - 6) - min (ε / 10) (c * ((m : ℝ) - 6)) := by linarith
  filter_upwards [block_bound_eventually Z H hm hp hCert hA0 hηpos,
    deleted_strips Z H _ hηpos, span_retained_le Z H _ hηpos,
    tail_passage Z H (eventually_h7 Z) _ hηpos,
    (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop ((m : ℝ) / min (ε / 10) (c * ((m : ℝ) - 6))),
    eventually_L_pos] with T hblk hstrip hspan h8 hNbig hL
  -- S15 (with S13's uniform block bound and S14's pinching as inputs)
  have h15 := offset_average (xret Z (mtParams T) T) (xret_injective Z (mtParams T) T hL)
    (show 1 ≤ m by omega) (blockDefect (gram_isHermitian Z (mtParams T) T))
    (Dcirc Z (mtParams T) T) (c * ((m : ℝ) - 6) - min (ε / 10) (c * ((m : ℝ) - 6))) (6 / (p : ℝ))
    hA' hq0 (blockDefect_nonneg _) (fun B hB _ => hblk B hB)
    (fun κ _ _ β => pinching_partition (gram_isHermitian Z (mtParams T) T) κ β)
  rw [Fintype.card_coe] at h15
  have hN0 : (0 : ℝ) ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hn0N : (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ) := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    exact_mod_cast h
  have hmN : (m : ℝ) ≤ min (ε / 10) (c * ((m : ℝ) - 6)) * (Z.N T (2 * T) : ℝ) := by
    have := (div_le_iff₀ hηpos).mp hNbig; linarith
  -- the real numbers at height T
  set A₀ : ℝ := c * ((m : ℝ) - 6) with hA₀
  set q : ℝ := 6 / (p : ℝ) with hq
  set η : ℝ := min (ε / 10) A₀ with hη
  set N : ℝ := (Z.N T (2 * T) : ℝ) with hNdef
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ) with hn0def
  set S : ℝ := ((retained Z (mtParams T) T).card : ℝ) with hSdef
  set D : ℝ := Dcirc Z (mtParams T) T with hDdef
  set sp : ℝ := spanOf (xret Z (mtParams T) T) univ with hspdef
  clear_value A₀ q η N n0 S D sp
  -- arithmetic, [A] lines 411–457 with explicit errors
  have step1 : (A₀ - η) * (n0 - 2 * η * N) ≤ (A₀ - η) * (S - m) :=
    mul_le_mul_of_nonneg_left (by linarith) hA'
  have step2 : q * ((m : ℝ) - 1) * sp ≤ q * ((m : ℝ) - 1) * ((1 + η) * N) :=
    mul_le_mul_of_nonneg_left hspan (mul_nonneg hq0 (by linarith))
  have hηN : 0 ≤ η * N := mul_nonneg hηpos.le hN0
  have e1 : A₀ * (η * N) ≤ 1 * (η * N) := mul_le_mul_of_nonneg_right hA0 hηN
  have e2 : η * n0 ≤ η * N := mul_le_mul_of_nonneg_left hn0N hηpos.le
  have e3 : 0 ≤ η * η * N := mul_nonneg (mul_nonneg hηpos.le hηpos.le) hN0
  have step3 : A₀ * n0 - 3 * η * N ≤ (A₀ - η) * (n0 - 2 * η * N) := by linarith [e1, e2, e3]
  have hmD : (m : ℝ) * D ≤ m * (n0 - (HD 1 - η) * N) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  have hq' : q * ((m : ℝ) - 1) ≤ 6 * ((m : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hq6 (by linarith)
  have hcoef1 : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ η * (7 * (m : ℝ) - 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hηpos.le
  have hcoef2 : η * (7 * (m : ℝ) - 3) ≤ ε / 10 * (7 * (m : ℝ) - 3) :=
    mul_le_mul_of_nonneg_right hηε (by linarith)
  have hεm : 0 ≤ ε * m := mul_nonneg hε.le hmpos.le
  have hcoef : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) ≤ m * ε := by linarith [hcoef1, hcoef2, hεm]
  have hηN' : η * ((m : ℝ) + 3 + q * ((m : ℝ) - 1)) * N ≤ m * ε * N :=
    mul_le_mul_of_nonneg_right hcoef hN0
  have key : ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N ≤ ((m : ℝ) - A₀) * n0 := by
    linarith [h15, step1, step2, step3, hmD, hηN']
  have hL1 : (HD 1 - 6 * ((m : ℝ) - 1) / ((p : ℝ) * m) - ε) * N
      = ((m : ℝ) * HD 1 - q * ((m : ℝ) - 1) - m * ε) * N / m := by
    rw [hq]; field_simp
  have hR1 : (1 - A₀ / m) * n0 = ((m : ℝ) - A₀) * n0 / m := by
    field_simp
  rw [hL1, hR1]
  exact div_le_div_of_nonneg_right key hmpos.le

/-! ### The theorem -/

/-- **Ainta's seven-point bound, conditional on the certificate** ([A] Theorem 1.1, in the form of
`[L23]`'s `thmD₀_simple_mult`): for Mathlib's `riemannZeta`,

  `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (Phi c m p − ε) · N(T,2T) ≤ N₀ˢ(T,2T)`,

where `Phi c m p = (H − 6(m−1)/(pm)) / (1 − c(m−6)/m)` and `H = HD 1 = 3/2 − (1/√2)cot(1/√2)`.
Hypotheses: the seven-point certificate `hCert` (S10, an Arb enclosure; enters as a hypothesis the
way `[L23]` takes `EnclOK`), the block cap `hA0 : c(m − 6) ≤ 1` (TRUST-MAP §1.2), and the side
conditions `7 ≤ m`, `0 < p`, `0 < c`.

**Hypotheses, by name, and why each is believed.**
* `hCert : ∀ g ≥ 0, c ≤ F6 p g` (S10).  Ainta's Proposition 4.1 ([A] eq:F6bound): the seven-point
  functional is bounded below by `c = 19/5000` at pressure `p = 3000`.  Believed because the Arb
  interval-arithmetic verifier at `github.com/ainta/zeta-simple-zeros` accepts it (707 901 nodes,
  depth 37, grid 1/4000, 128 bits) and this laboratory reproduced that run field for field
  (`hunts/ainta_seven_point/RESULTS.md`).  Not a Lean fact; it enters as a hypothesis the way
  `[L23]` takes `EnclOK` for its own numerical inputs.
* `hA0 : c (m − 6) ≤ 1` (S13's cap, [A] eq:mA).  A rational side condition on the parameters,
  `4997/5000 ≤ 1` at the published values; discharged by `norm_num` in `seven_point_bound_paper`.
* `7 ≤ m`, `0 < p`, `0 < c`: side conditions, discharged by `norm_num` at the published values.

Everything else is proved: the proof is sorry-free and depends on the step lemmas S6–S9, S11–S16,
each of which is proved in its own file with standard axioms only. -/
theorem seven_point_bound (c : ℝ) (m p : ℕ) (hm : 7 ≤ m) (hp : 0 < p) (hc : 0 < c)
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → c ≤ F6 p g)
    (hA0 : c * ((m : ℝ) - 6) ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Phi c m p - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have h := solve_linear (N := fun T => (Ncount T (2 * T) : ℝ))
    (N0 := fun T => (N0simple T (2 * T) : ℝ)) hm hA0 (by
      have := pre_solve zetaZeroConfig paperInputs_zeta hm hp hc hCert hA0
      simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using this)
  intro ε hε
  exact eventually_atTop.mp (h ε hε)

/-- **Non-vacuity at the published parameters.**  With `c = 19/5000`, `m = 269`, `p = 3000` the
conclusion's constant is the paper's `(1 345 000 H − 2 680)/1 340 003` ([A] Theorem 1.1), and the
side conditions hold. -/
theorem seven_point_bound_paper
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 19 / 5000 ≤ F6 3000 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((1345000 * HD 1 - 2680) / 1340003 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  rw [← Phi_paper]
  exact seven_point_bound (19 / 5000) 269 3000 (by norm_num) (by norm_num) (by norm_num) hCert
    (by norm_num)

/-- `N(T,2T) → ∞`, so the ratio `N₀ˢ/N` below is eventually a ratio of positive numbers.  This
is `[L23]`'s Riemann-von Mangoldt consequence `Assembly.tendsto_N_atTop`, at ζ. -/
lemma eventually_Ncount_pos : ∀ᶠ T in atTop, 0 < (Ncount T (2 * T) : ℝ) := by
  have h := Zeta23.Assembly.tendsto_N_atTop zetaZeroConfig paperInputs_zeta.RvM
  simpa only [zetaZeroConfig_N] using h.eventually_gt_atTop 0

/-- **At this laboratory's own certificate parameters.**  The seven-point pressure sweep of
`hunts/ainta_seven_point` puts the peak at `p = 3400`, where the interval-arithmetic verifier
accepts `c = 34697/10⁷` (grid 4000 and 8000; `34701/10⁷` is refused) and the cap `c(m − 6) ≤ 1`
gives `m = 294`.  The constant is then `(520 625 000 H − 915 625)/518 855 453 = 0.673029553…`,
against `[A]` Theorem 1.1's `0.673008527…`.

The improvement is in the hypothesis, not in the mathematics of this file: `hCert` is assumed at
different parameters, and `Phi` is evaluated there.  The certificate is still not a Lean fact. -/
theorem seven_point_bound_lab
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((520625000 * HD 1 - 915625) / 518855453 - ε) * (Ncount T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  rw [← Phi_lab]
  exact seven_point_bound (34697 / 10000000) 294 3400 (by norm_num) (by norm_num) (by norm_num)
    hCert (by norm_num)

/-- **The same bound as a proportion.**  `N₀ˢ(T,2T)/N(T,2T) ≥ 0.673029553… − ε` for all large `T`,
which is the form the statement is usually quoted in ("more than 67.3% of the zeros are simple
and on the critical line").  No positivity guard is needed: `N(T,2T) → ∞` by
`eventually_Ncount_pos`. -/
theorem seven_point_bound_lab_ratio
    (hCert : ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → 34697 / 10000000 ≤ F6 3400 g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (520625000 * HD 1 - 915625) / 518855453 - ε
        ≤ (N0simple T (2 * T) : ℝ) / (Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := seven_point_bound_lab hCert ε hε
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp eventually_Ncount_pos
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have h1 := hT₁ T (le_trans (le_max_left _ _) hT)
  have h2 := hT₂ T (le_trans (le_max_right _ _) hT)
  rw [le_div_iff₀ h2]
  exact h1

/-! ### Standing axiom audit

Same idiom as `Zeta23Ext/StableRankTrace.lean`.  Expected, and observed on 2026-08-23: every line
below reports exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `native_decide`,
no new axiom anywhere in the import closure. -/

#print axioms solve_linear
#print axioms Phi_paper
#print axioms Phi_paper'
#print axioms eventually_L_pos
#print axioms count_defect
#print axioms eventually_h7
#print axioms block_bound_eventually
#print axioms pre_solve
#print axioms seven_point_bound
#print axioms seven_point_bound_paper
#print axioms eventually_Ncount_pos
#print axioms seven_point_bound_lab
#print axioms seven_point_bound_lab_ratio

end Zeta23Ext.Bridge
