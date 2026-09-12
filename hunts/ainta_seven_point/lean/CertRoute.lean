/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Zeta23Ext.Bridge.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The certificate route: the first slice

`Zeta23Ext.Bridge.n_point_bound` is proved for every `n`, conditional on the finite inequality
`hCert`.  This file is the feasibility slice of proving `hCert` itself, and it works with the
same `Kfun`, `kfun`, `wfun`, `F` that `Zeta23Ext/Bridge/Defs.lean` defines: nothing is
transcribed.  See `hunts/ainta_seven_point/CERTIFICATE-ROUTE.md`.

What is here:

* `certGoal`, the exact Lean statement a proof of the seven-point inequality at this
  laboratory's parameters would have to establish, and `certGoal_eq_hypothesis`, which says it
  is *definitionally* the hypothesis `Zeta23Ext.Bridge.seven_point_bound_lab` consumes.
* `Kfun_eq_sinc`: the integral that defines the kernel equals the sinc form the Arb verifier
  evaluates.  `Defs.lean` states this in a docstring ("the closed sinc form printed there is a
  consequence"); it was not a theorem anywhere until now, and every route to `hCert` needs it,
  because no interval arithmetic can be run on an integral.
* `cos_sin_taylor12`: a twelve-term Taylor enclosure of `cos` and `sin` on `[-1,1]`.  Mathlib
  at the pinned revision has no numerical evaluator for `sin`/`cos` and no interval-arithmetic
  tactic; its best bound is the four-term `Real.cos_bound`, whose error at `θ = 0.79` is about
  `2 · 10⁻²`, six orders of magnitude too coarse for a kernel table.
* `kfun_closed`: `k(x) = (cos b − 2γ b sin b)/(1 − 2b²)` with `b = πx` and one transcendental
  constant `γ = (1/√2) cot(1/√2) = 3/2 − H`.
* `wfun_cell_4160_lower`: one closed cell of the verifier's `1/4000` grid, enclosed.  This is
  the atomic unit of the 45 608-entry table, and the thing whose cost the note projects.

No `sorry`, no `native_decide`, no `axiom`.  The axiom audit is at the bottom.
-/

noncomputable section
open Real intervalIntegral

namespace Zeta23Ext.Bridge.CertRoute

/-! ## The obligation, stated exactly -/

/-- **The goal.**  What a proof of the seven-point inequality at this laboratory's parameters
`(n, c, p) = (7, 34697/10⁷, 3400)` would have to establish, in the vocabulary of
`Zeta23Ext/Bridge/Defs.lean`. -/
def certGoal : Prop :=
  ∀ g : Fin (7 - 1) → ℝ, (∀ i, 0 ≤ g i) → (34697/10000000 : ℝ) ≤ F 7 3400 g

/-- `certGoal` is, definitionally, the hypothesis `hCert` of
`Zeta23Ext.Bridge.seven_point_bound_lab`: discharging it would turn that theorem
unconditional. -/
theorem certGoal_eq_hypothesis :
    certGoal ↔ ∀ g : Fin 6 → ℝ, (∀ i, 0 ≤ g i) → (34697/10000000 : ℝ) ≤ F6 3400 g :=
  Iff.rfl

/-! ## The kernel in closed form -/

/-- `∫_{-1/2}^{1/2} cos (c t) dt = sinc (c/2)`, with no case split needed at `c = 0`. -/
theorem integral_cos_mul_eq_sinc (c : ℝ) :
    (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) = Real.sinc (c / 2) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; norm_num
  · have hc2 : c / 2 ≠ 0 := by simpa using hc
    rw [integral_comp_mul_left _ hc, integral_cos, Real.sinc_of_ne_zero hc2,
      show c * ((1:ℝ)/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring,
      Real.sin_neg, smul_eq_mul]
    field_simp
    ring

private lemma cos_mul_intervalIntegrable (c a b : ℝ) :
    IntervalIntegrable (fun t => Real.cos (c * t)) MeasureTheory.volume a b :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- **The sinc form of the Montgomery–Taylor overlap kernel.**  The integral that *defines* `K`
equals the closed form the Arb verifier evaluates, at every real `x`, including the two points
where the naive quotient form has a removable singularity. -/
theorem Kfun_eq_sinc (x : ℝ) :
    Kfun x =
      (Real.sinc ((Real.sqrt 2 - 2 * Real.pi * x) / 2)
        + Real.sinc ((Real.sqrt 2 + 2 * Real.pi * x) / 2)) / 2 := by
  have key : ∀ t : ℝ, Real.cos (Real.sqrt 2 * t) * Real.cos (2 * Real.pi * x * t)
      = (Real.cos ((Real.sqrt 2 - 2 * Real.pi * x) * t)
          + Real.cos ((Real.sqrt 2 + 2 * Real.pi * x) * t)) / 2 := by
    intro t
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  unfold Kfun
  simp_rw [key]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (cos_mul_intervalIntegrable _ _ _)
      (cos_mul_intervalIntegrable _ _ _),
    integral_cos_mul_eq_sinc, integral_cos_mul_eq_sinc]

/-! ## Numerical enclosure machinery -/

/-- Degree-10 Taylor polynomial of `cos`. -/
def taylorCos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800

/-- Degree-11 Taylor polynomial of `sin`. -/
def taylorSin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800

/-- The remainder bound `13 / (12! * 12)` that `Complex.exp_bound` supplies at `n = 12`. -/
def taylorErr : ℝ := 13/5748019200

/-- Twelve-term Taylor bound for `cos` and `sin` on `|θ| ≤ 1`, from `Complex.exp_bound`.
Mathlib at this revision has only the four-term `Real.cos_bound` (error `5/96 · θ⁴`), which is
about `10⁻²` at `θ = 0.79` and useless for a kernel table. -/
theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
    |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
        ≤ |θ|^12 * (13/5748019200) ∧
    |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
        ≤ |θ|^12 * (13/5748019200) := by
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using hθ
  have hb := Complex.exp_bound hx (n := 12) (by norm_num)
  have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    apply Complex.ext <;> · simp [pow_succ]; ring
  rw [hsum, hnx] at hb
  have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
    refine hb.trans (le_of_eq ?_)
    norm_num
  constructor
  · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
  · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
      - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
        + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
          * Complex.I))
    refine le_trans (le_of_eq ?_) (this.trans hE)
    simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]

private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]

private lemma err_scale {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t| ^ 12 * (13 / 5748019200) ≤ taylorErr := by
  rw [abs_of_nonneg h0]
  have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
  unfold taylorErr; nlinarith

theorem cos_lower {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    taylorCos u - taylorErr ≤ Real.cos θ := by
  have h0u : 0 ≤ u := h0.trans hu
  have hmono : Real.cos u ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hu1.trans one_le_pi) hu
  have ht := (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).1
  have he := err_scale h0u hu1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

theorem cos_upper {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos θ ≤ taylorCos l + taylorErr := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hmono : Real.cos θ ≤ Real.cos l :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans one_le_pi) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).1
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorCos
  linarith [this.1, this.2]

theorem sin_lower {θ l : ℝ} (h0 : 0 ≤ l) (hl : l ≤ θ) (hθ1 : θ ≤ 1) :
    taylorSin l - taylorErr ≤ Real.sin θ := by
  have hl1 : l ≤ 1 := hl.trans hθ1
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin l ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
  have ht := (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).2
  have he := err_scale h0 hl1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

theorem sin_upper {θ u : ℝ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : u ≤ 1) :
    Real.sin θ ≤ taylorSin u + taylorErr := by
  have h0u : 0 ≤ u := h0.trans hu
  have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : Real.sin θ ≤ Real.sin u :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hu1.trans hpi2) hu
  have ht := (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).2
  have he := err_scale h0u hu1
  have := abs_le.mp ht
  unfold taylorSin
  linarith [this.1, this.2]

/-! ## The kernel in closed form -/

/-- `γ := (1/√2) cot (1/√2)`, the single transcendental constant of the closed form.
It is `3/2 - H` for the constant `H` of the upstream Theorem D. -/
def gam : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)

private lemma sqrt2_half_bounds :
    (70710678/100000000 : ℝ) ≤ Real.sqrt 2 / 2 ∧ Real.sqrt 2 / 2 ≤ 70710679/100000000 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor <;> nlinarith [h2, hnn]

private lemma sin_sqrt2_half_pos : 0 < Real.sin (Real.sqrt 2 / 2) := by
  have hb := sqrt2_half_bounds
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hb.1]) ?_
  linarith [hb.2, Real.pi_gt_three]

theorem gam_bounds : (827499/1000000 : ℝ) ≤ gam ∧ gam ≤ 827500/1000000 := by
  have hb := sqrt2_half_bounds
  have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
  have h1 : Real.sqrt 2 / 2 ≤ 1 := by linarith [hb.2]
  have hcl : (7602445/10000000 : ℝ) ≤ Real.cos (Real.sqrt 2 / 2) := by
    have := cos_lower h0 hb.2 (by norm_num)
    have h : (7602445/10000000 : ℝ) ≤ taylorCos (70710679/100000000) - taylorErr := by
      unfold taylorCos taylorErr; norm_num
    linarith
  have hcu : Real.cos (Real.sqrt 2 / 2) ≤ 7602447/10000000 := by
    have := cos_upper (by norm_num) hb.1 h1
    have h : taylorCos (70710678/100000000 : ℝ) + taylorErr ≤ 7602447/10000000 := by
      unfold taylorCos taylorErr; norm_num
    linarith
  have hsl : (6496369/10000000 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) := by
    have := sin_lower (by norm_num) hb.1 h1
    have h : (6496369/10000000 : ℝ) ≤ taylorSin (70710678/100000000) - taylorErr := by
      unfold taylorSin taylorErr; norm_num
    linarith
  have hsu : Real.sin (Real.sqrt 2 / 2) ≤ 6496370/10000000 := by
    have := sin_upper h0 hb.2 (by norm_num)
    have h : taylorSin (70710679/100000000 : ℝ) + taylorErr ≤ 6496370/10000000 := by
      unfold taylorSin taylorErr; norm_num
    linarith
  have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith
  have hprodl : (70710678/100000000 : ℝ) * (7602445/10000000)
      ≤ (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) :=
    mul_le_mul hb.1 hcl (by norm_num) h0
  have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2)
      ≤ (70710679/100000000 : ℝ) * (7602447/10000000) :=
    mul_le_mul hb.2 hcu (by linarith) (by norm_num)
  constructor
  · rw [gam, le_div_iff₀ hspos]; nlinarith [hprodl, hsu]
  · rw [gam, div_le_iff₀ hspos]; nlinarith [hprodu, hsl]

private lemma kfun_aux (a b : ℝ) (ha : a ≠ 0) (hsa : Real.sin a ≠ 0)
    (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ((Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b)) / 2) / (Real.sin a / a)
      = (a^2 * Real.cos b - a * b * (Real.cos a / Real.sin a) * Real.sin b) / (a^2 - b^2) := by
  have hab : a^2 - b^2 ≠ 0 := by
    have hfac : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [hfac]; exact mul_ne_zero h1 h2
  rw [Real.sin_sub, Real.sin_add]
  field_simp
  ring

/-- **The closed form of the normalised kernel.**  `k(x) = (cos b − 2γ b sin b)/(1 − 2b²)`,
`b = πx`, valid off the two removable singularities `b² = 1/2`. -/
theorem kfun_closed (x : ℝ) (h : 1 - 2*(Real.pi*x)^2 ≠ 0) :
    kfun x = (Real.cos (Real.pi*x) - 2*gam*(Real.pi*x)*Real.sin (Real.pi*x))
      / (1 - 2*(Real.pi*x)^2) := by
  have hb := sqrt2_half_bounds
  set a : ℝ := Real.sqrt 2 / 2 with ha_def
  set b : ℝ := Real.pi * x with hb_def
  have ha2 : a^2 = 1/2 := by
    rw [ha_def, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have ha : a ≠ 0 := by positivity
  have hsa : Real.sin a ≠ 0 := ne_of_gt sin_sqrt2_half_pos
  have h1 : a - b ≠ 0 := by
    intro hz
    apply h
    have : b = a := by linarith [sub_eq_zero.mp hz]
    rw [this]; nlinarith [ha2]
  have h2 : a + b ≠ 0 := by
    intro hz
    apply h
    have : b = -a := by linarith
    rw [this]; nlinarith [ha2]
  have hK : Kfun x = (Real.sin (a - b)/(a - b) + Real.sin (a + b)/(a + b))/2 := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*x)/2 = a - b by rw [ha_def, hb_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*x)/2 = a + b by rw [ha_def, hb_def]; ring,
      Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2]
  have hK0 : Kfun 0 = Real.sin a / a := by
    rw [Kfun_eq_sinc, show (Real.sqrt 2 - 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      show (Real.sqrt 2 + 2*Real.pi*0)/2 = a by rw [ha_def]; ring,
      Real.sinc_of_ne_zero ha]
    ring
  have hgam : gam = a * (Real.cos a / Real.sin a) := by
    rw [gam, ← ha_def]; field_simp
  have hne1 : (1/2 : ℝ) - b^2 ≠ 0 := by
    intro hz; apply h; linarith
  rw [kfun, hK, hK0, kfun_aux a b ha hsa h1 h2, hgam, ha2,
    div_eq_div_iff hne1 h]
  ring

/-! ## One cell of the kernel table -/

/-- **A rigorous Lean lower bound for `w = k²` on one closed cell of the verifier's `1/4000`
grid**: cell index 4160, `x ∈ [1.04, 1.04025]`, inside the first surviving gap component
`[3809, 4778]`, so a cell the search actually queries.  An interval evaluation of `kfun_closed`
in exact rationals at 20 digits gives `2.3164e-4` for this cell and the true minimum is
`2.3171e-4`; this proof gets `2.3e-4`, kernel-checked. -/
theorem wfun_cell_4160_lower (x : ℝ) (hx : 104/100 ≤ x) (hx' : x ≤ 104025/100000) :
    (23/100000 : ℝ) ≤ wfun x := by
  have hpl : (3.14159265358979323846 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_d20
  have hph : Real.pi ≤ 3.14159265358979323847 := le_of_lt Real.pi_lt_d20
  have hbl : (3267256/1000000 : ℝ) ≤ Real.pi * x := by nlinarith
  have hbu : Real.pi * x ≤ 3268042/1000000 := by nlinarith
  set θ : ℝ := Real.pi * (x - 1) with hθ_def
  have hθl : (1256637/10000000 : ℝ) ≤ θ := by rw [hθ_def]; nlinarith
  have hθu : θ ≤ 1264492/10000000 := by rw [hθ_def]; nlinarith
  have hθ0 : (0:ℝ) ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hcosl : (992015/1000000 : ℝ) ≤ Real.cos θ := by
    have := cos_lower hθ0 hθu (by norm_num)
    have h : (992015/1000000 : ℝ) ≤ taylorCos (1264492/10000000) - taylorErr := by
      unfold taylorCos taylorErr; norm_num
    linarith
  have hcosu : Real.cos θ ≤ 992115/1000000 := by
    have := cos_upper (by norm_num) hθl hθ1
    have h : taylorCos (1256637/10000000 : ℝ) + taylorErr ≤ 992115/1000000 := by
      unfold taylorCos taylorErr; norm_num
    linarith
  have hsinl : (125333/1000000 : ℝ) ≤ Real.sin θ := by
    have := sin_lower (by norm_num) hθl hθ1
    have h : (125333/1000000 : ℝ) ≤ taylorSin (1256637/10000000) - taylorErr := by
      unfold taylorSin taylorErr; norm_num
    linarith
  have hsinu : Real.sin θ ≤ 126113/1000000 := by
    have := sin_upper hθ0 hθu (by norm_num)
    have h : taylorSin (1264492/10000000 : ℝ) + taylorErr ≤ 126113/1000000 := by
      unfold taylorSin taylorErr; norm_num
    linarith
  -- reduce `cos (π x)` and `sin (π x)` to the first period
  have hcosb : Real.cos (Real.pi * x) = - Real.cos θ := by
    rw [hθ_def, show Real.pi * x = Real.pi + Real.pi * (x - 1) by ring, Real.cos_add,
      Real.cos_pi, Real.sin_pi]; ring
  have hsinb : Real.sin (Real.pi * x) = - Real.sin θ := by
    rw [hθ_def, show Real.pi * x = Real.pi + Real.pi * (x - 1) by ring, Real.sin_add,
      Real.cos_pi, Real.sin_pi]; ring
  have hg := gam_bounds
  have hD : 1 - 2*(Real.pi*x)^2 ≤ -20349923/1000000 := by nlinarith
  have hDl : (-20360198/1000000 : ℝ) ≤ 1 - 2*(Real.pi*x)^2 := by nlinarith
  have hDne : 1 - 2*(Real.pi*x)^2 ≠ 0 := by intro hz; rw [hz] at hD; norm_num at hD
  have hDneg : 1 - 2*(Real.pi*x)^2 < 0 := by linarith
  -- the numerator, built one factor at a time so that no product is left to `nlinarith`
  have hgb1 : (827499/1000000 : ℝ) * (3267256/1000000) ≤ gam * (Real.pi*x) :=
    mul_le_mul hg.1 hbl (by norm_num) (by linarith [hg.1])
  have hgb2 : gam * (Real.pi*x) ≤ (827500/1000000 : ℝ) * (3268042/1000000) :=
    mul_le_mul hg.2 hbu (by linarith [hbl]) (by norm_num)
  have hgbs1 : (827499/1000000 : ℝ) * (3267256/1000000) * (125333/1000000)
      ≤ gam * (Real.pi*x) * Real.sin θ :=
    mul_le_mul hgb1 hsinl (by norm_num) (by nlinarith [hgb1])
  have hgbs2 : gam * (Real.pi*x) * Real.sin θ
      ≤ (827500/1000000 : ℝ) * (3268042/1000000) * (126113/1000000) :=
    mul_le_mul hgb2 hsinu (by linarith [hsinl]) (by norm_num)
  have hk : (1522/100000 : ℝ) ≤ kfun x := by
    rw [kfun_closed x hDne, le_div_iff_of_neg hDneg, hcosb, hsinb]
    nlinarith [hcosl, hgbs2, hDl]
  have hw : wfun x = kfun x ^ 2 := rfl
  rw [hw]
  nlinarith [hk]

/-! ### Standing axiom audit (idiom of `Zeta23Ext/Bridge/Defs.lean`) -/

#print axioms certGoal_eq_hypothesis
#print axioms integral_cos_mul_eq_sinc
#print axioms Kfun_eq_sinc
#print axioms cos_sin_taylor12
#print axioms cos_lower
#print axioms cos_upper
#print axioms sin_lower
#print axioms sin_upper
#print axioms gam_bounds
#print axioms kfun_closed
#print axioms wfun_cell_4160_lower

end Zeta23Ext.Bridge.CertRoute

end
