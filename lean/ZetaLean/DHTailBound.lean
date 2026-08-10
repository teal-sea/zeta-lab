/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.DavenportHeilbronn
import ZetaLean.DHAnalytic

/-!
# The certified tail bound: `DH` beyond absolute convergence

The Dirichlet series of `DH` does not converge absolutely at the off-line
zero (`Re s ≈ 0.808`), which is why `ZetaLean/OracleDH.lean` could bound only
individual terms.  This file closes that gap with a kernel-checked
representation of `DH` on the whole half-plane `Re s > 0`:

* `norm_cpow_sub_cpow_le` — the mean-value two-point bound
  `‖b^{-s} − a^{-s}‖ ≤ ‖s‖·a^{-Re s − 1}·(b − a)`: Mathlib's convex mean
  value inequality applied to `t ↦ (t : ℂ)^{-s}`; no integrals.
* `dhBlock` — the series grouped into five-term blocks `n = 5k … 5k+4`.  The
  coefficient pattern `(0, 1, κ, −κ, −1)` pairs into two differences, so each
  block obeys `‖dhBlock s k‖ ≤ (3 + κ)·‖s‖·(5k+1)^{-Re s − 1}`
  (`norm_dhBlock_le`) and the grouped series converges *absolutely* for
  `Re s > 0` (`summable_dhBlock`) — the analytic continuation made
  computable.
* `hasSum_dhBlock_DH` — for `Re s > 1` the blocks sum to `DH s`, by
  regrouping the absolutely convergent series along `Nat.divModEquiv 5`.
* `dhBlockSum_eq_DH` — the same holds on all of `Re s > 0`: the block sum is
  differentiable there (Weierstrass, via
  `differentiableOn_tsum_of_summable_norm`), `DH` is entire, the two agree
  on `Re s > 1`, and the identity theorem finishes.  This is the
  kernel-checked analytic continuation of the DH series.
* `DH_tail_bound` — the payoff: for `Re s > 0` and `K ≥ 2`,
  `‖DH s − ∑_{n < 5K} dh_coeff n · n^{-s}‖
     ≤ (3 + κ)·‖s‖·5^{-Re s − 1}·(K−1)^{-Re s}/Re s`,
  the tail of the block bounds summed by the integral test
  (`AntitoneOn.tsum_comp_add_le_integral` + `integral_Ioi_rpow_of_lt`).

Together with `ZetaLean/IntervalCExp.lean` (which encloses each partial-sum
term `n^{-s}` in a computed rational box), evaluating `DH` anywhere in
`Re s > 0` is now a finite computation plus this theorem's explicit error
term.  What remains of rung 3 Phase B is assembly: enclosing the finite sum
tightly enough, at the centre and on the sphere, to discharge the two
hypotheses of `davenport_heilbronn_of_certified_disk` — a compute problem,
no longer a mathematics gap.
-/

open Complex Finset

namespace ZetaLean.DH

/-! ### The two-point mean-value bound -/

/-- `‖b^{-s} − a^{-s}‖ ≤ ‖s‖·a^{-Re s−1}·(b−a)` for `0 < a ≤ b`: the convex
mean value inequality for `t ↦ (t : ℂ)^{-s}` on `[a, b]`, whose derivative
norm `‖s‖·t^{-Re s−1}` is largest at the left endpoint. -/
theorem norm_cpow_sub_cpow_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hderiv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1))
        (Set.Icc a b) t := fun t ht =>
    (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le ha ht.1).ne'
      (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc a b,
      ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      show (-s - 1).re = -s.re - 1 by simp]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)) (norm_nonneg s)
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    hbound (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h

/-- The two-point bound with natural-number endpoints, as the block estimates
use it. -/
private lemma norm_natCast_cpow_sub_le {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {s : ℂ} (hs : 0 < s.re) :
    ‖(n : ℂ) ^ (-s) - (m : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ((m : ℝ)) ^ (-s.re - 1) * ((n : ℝ) - (m : ℝ)) := by
  have h := norm_cpow_sub_cpow_le (a := (m : ℝ)) (b := (n : ℝ))
    (by exact_mod_cast hm) (by exact_mod_cast hmn) hs
  simpa using h

/-! ### κ is nonnegative -/

private lemma sqrt5_sq' : Real.sqrt 5 * Real.sqrt 5 = 5 :=
  Real.mul_self_sqrt (by norm_num)

private lemma sqrt5_gt_one : 1 < Real.sqrt 5 := by
  nlinarith [sqrt5_sq', Real.sqrt_nonneg 5]

private lemma sqrt5_le_three : Real.sqrt 5 ≤ 3 := by
  nlinarith [sqrt5_sq', Real.sqrt_nonneg 5]

lemma dh_kappa_nonneg : 0 ≤ dh_kappa := by
  unfold dh_kappa
  apply div_nonneg _ (by linarith [sqrt5_gt_one])
  have h4 : (0 : ℝ) ≤ 10 - 2 * Real.sqrt 5 := by linarith [sqrt5_le_three]
  have h2 : (2 : ℝ) ≤ Real.sqrt (10 - 2 * Real.sqrt 5) := by
    nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (10 - 2 * Real.sqrt 5),
      sqrt5_le_three]
  linarith

/-! ### The blocks -/

/-- One five-term block of the DH series, `n = 5k … 5k+4`. -/
noncomputable def dhBlock (s : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range 5, (dh_coeff (k * 5 + j) : ℂ) * ((k * 5 + j : ℕ) : ℂ) ^ (-s)

private lemma coeff_at (k j : ℕ) (hj : j < 5) :
    dh_coeff (k * 5 + j) = dh_coeff j := by
  unfold dh_coeff
  rw [show k * 5 + j = 5 * k + j from by ring, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- The coefficient pattern `(0, 1, κ, −κ, −1)` pairs into two differences. -/
private lemma dhBlock_eq_pair (s : ℂ) (k : ℕ) :
    dhBlock s k =
      (((k * 5 + 1 : ℕ) : ℂ) ^ (-s) - ((k * 5 + 4 : ℕ) : ℂ) ^ (-s))
        + (dh_kappa : ℂ) *
          (((k * 5 + 2 : ℕ) : ℂ) ^ (-s) - ((k * 5 + 3 : ℕ) : ℂ) ^ (-s)) := by
  have h0 : dh_coeff (k * 5) = 0 := by
    have h := coeff_at k 0 (by norm_num)
    rw [add_zero] at h
    exact h.trans rfl
  have h1 : dh_coeff (k * 5 + 1) = 1 := (coeff_at k 1 (by norm_num)).trans rfl
  have h2 : dh_coeff (k * 5 + 2) = dh_kappa := (coeff_at k 2 (by norm_num)).trans rfl
  have h3 : dh_coeff (k * 5 + 3) = -dh_kappa := (coeff_at k 3 (by norm_num)).trans rfl
  have h4 : dh_coeff (k * 5 + 4) = -1 := (coeff_at k 4 (by norm_num)).trans rfl
  rw [dhBlock]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero,
    h0, h1, h2, h3, h4]
  push_cast
  ring

/-- The block bound, `k ≥ 1`: two applications of the two-point bound, one
per coefficient pair. -/
theorem norm_dhBlock_le {s : ℂ} (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖dhBlock s k‖ ≤ (3 + dh_kappa) * ‖s‖ * ((k * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  have hb : (0 : ℝ) < ((k * 5 + 1 : ℕ) : ℝ) := by positivity
  have hpair1 : ‖((k * 5 + 1 : ℕ) : ℂ) ^ (-s) - ((k * 5 + 4 : ℕ) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ((k * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) * 3 := by
    rw [norm_sub_rev]
    have h := norm_natCast_cpow_sub_le (m := k * 5 + 1) (n := k * 5 + 4)
      (by omega) (by omega) hs
    refine h.trans (le_of_eq ?_)
    push_cast
    ring
  have hpair2 : ‖((k * 5 + 2 : ℕ) : ℂ) ^ (-s) - ((k * 5 + 3 : ℕ) : ℂ) ^ (-s)‖
      ≤ ‖s‖ * ((k * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
    rw [norm_sub_rev]
    have h := norm_natCast_cpow_sub_le (m := k * 5 + 2) (n := k * 5 + 3)
      (by omega) (by omega) hs
    have he : ‖s‖ * ((k * 5 + 2 : ℕ) : ℝ) ^ (-s.re - 1)
        * (((k * 5 + 3 : ℕ) : ℝ) - ((k * 5 + 2 : ℕ) : ℝ))
        = ‖s‖ * ((k * 5 + 2 : ℕ) : ℝ) ^ (-s.re - 1) := by push_cast; ring
    rw [he] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hb (by push_cast; linarith) (by linarith))
      (norm_nonneg s)
  calc ‖dhBlock s k‖
      ≤ ‖((k * 5 + 1 : ℕ) : ℂ) ^ (-s) - ((k * 5 + 4 : ℕ) : ℂ) ^ (-s)‖
        + ‖(dh_kappa : ℂ) *
            (((k * 5 + 2 : ℕ) : ℂ) ^ (-s) - ((k * 5 + 3 : ℕ) : ℂ) ^ (-s))‖ := by
        rw [dhBlock_eq_pair]; exact norm_add_le _ _
    _ ≤ ‖s‖ * ((k * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) * 3
        + dh_kappa * (‖s‖ * ((k * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
        refine add_le_add hpair1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg dh_kappa_nonneg]
        exact mul_le_mul_of_nonneg_left hpair2 dh_kappa_nonneg
    _ = (3 + dh_kappa) * ‖s‖ * ((k * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by ring

/-! ### Absolute summability of the blocks for `Re s > 0` -/

private lemma summable_shifted_rpow {p : ℝ} (hp : 0 < p) (c : ℕ) :
    Summable (fun k : ℕ => (((k + 1 + c) * 5 + 1 : ℕ) : ℝ) ^ (-p - 1)) := by
  have hbase : Summable (fun k : ℕ => ((k : ℝ)) ^ (-p - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ (-p - 1)) := by
    have := (summable_nat_add_iff
      (f := fun k : ℕ => ((k : ℝ)) ^ (-p - 1)) 1).mpr hbase
    simpa using this
  refine hshift.of_nonneg_of_le
    (fun k => Real.rpow_nonneg (by positivity) _) fun k => ?_
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) c]

theorem summable_dhBlock {s : ℂ} (hs : 0 < s.re) : Summable (dhBlock s) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_norm_bounded
    (g := fun k : ℕ =>
      (3 + dh_kappa) * ‖s‖ * (((k + 1) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1))
    ?_ fun k => norm_dhBlock_le hs (by omega)
  have := (summable_shifted_rpow hs 0).mul_left ((3 + dh_kappa) * ‖s‖)
  simpa using this

/-! ### The blocks sum to `DH` for `Re s > 1` -/

theorem hasSum_dhBlock_DH {s : ℂ} (hs : 1 < s.re) : HasSum (dhBlock s) (DH s) := by
  have h := DH_series_rep s hs
  have h2 : HasSum ((fun n : ℕ => (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)) ∘
      ⇑(Nat.divModEquiv 5).symm) (DH s) := ((Nat.divModEquiv 5).symm.hasSum_iff).mpr h
  refine HasSum.prod_fiberwise h2 fun k => ?_
  have hfin := hasSum_fintype
    (fun j : Fin 5 => (dh_coeff (k * 5 + (j : ℕ)) : ℂ)
      * ((k * 5 + (j : ℕ) : ℕ) : ℂ) ^ (-s))
  have hval : ∑ j : Fin 5, (dh_coeff (k * 5 + (j : ℕ)) : ℂ)
      * ((k * 5 + (j : ℕ) : ℕ) : ℂ) ^ (-s) = dhBlock s k := by
    rw [dhBlock, ← Fin.sum_univ_eq_sum_range
      (fun j => (dh_coeff (k * 5 + j) : ℂ) * ((k * 5 + j : ℕ) : ℂ) ^ (-s)) 5]
  rw [hval] at hfin
  convert hfin using 2 with j
  simp [Function.comp, Nat.divModEquiv]

/-! ### The block sum, differentiable on `Re s > 0` -/

/-- The block sum — for `Re s > 0` this *is* `DH` (`dhBlockSum_eq_DH`), but
that is a theorem, not the definition. -/
noncomputable def dhBlockSum (s : ℂ) : ℂ := ∑' k, dhBlock s k

private lemma differentiable_block (k : ℕ) :
    Differentiable ℂ fun s => dhBlock s k := by
  refine Differentiable.fun_sum fun j hj => ?_
  rcases Nat.eq_zero_or_pos (k * 5 + j) with h | h
  · have hc : dh_coeff (k * 5 + j) = 0 := by rw [h]; rfl
    have hfun : (fun s : ℂ =>
        (dh_coeff (k * 5 + j) : ℂ) * ((k * 5 + j : ℕ) : ℂ) ^ (-s)) = fun _ => 0 := by
      funext s
      rw [hc]
      simp
    rw [hfun]
    exact differentiable_const 0
  · exact (differentiable_neg.const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr h.ne'))).const_mul _

theorem differentiableOn_dhBlockSum :
    DifferentiableOn ℂ dhBlockSum {z : ℂ | 0 < z.re} := by
  intro s₀ hs₀
  have hs₀' : (0 : ℝ) < s₀.re := hs₀
  set δ : ℝ := s₀.re / 2 with hδdef
  have hδ0 : 0 < δ := half_pos hs₀'
  have hre : ∀ z ∈ Metric.ball s₀ δ, δ ≤ z.re := by
    intro z hz
    have h1 : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - s₀)
    have h2 : ‖z - s₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h3 := (abs_le.mp h1).1
    have : s₀.re - δ ≤ z.re := by linarith
    rw [hδdef] at this ⊢
    linarith
  have hsub : Metric.ball s₀ δ ⊆ {z : ℂ | 0 < z.re} := fun z hz =>
    lt_of_lt_of_le hδ0 (hre z hz)
  have hM : ∀ z ∈ Metric.ball s₀ δ, ‖z‖ ≤ ‖s₀‖ + δ := by
    intro z hz
    have h2 : ‖z - s₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    calc ‖z‖ = ‖s₀ + (z - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖z - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + δ := by linarith
  have hnn : (0 : ℝ) ≤ 3 + dh_kappa := by linarith [dh_kappa_nonneg]
  have hu : Summable (fun k : ℕ =>
      (3 + dh_kappa) * (‖s₀‖ + δ) * (((k + 1) * 5 + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
    have := (summable_shifted_rpow hδ0 0).mul_left ((3 + dh_kappa) * (‖s₀‖ + δ))
    simpa using this
  have hF_le : ∀ (k : ℕ), ∀ w ∈ Metric.ball s₀ δ, ‖dhBlock w (k + 1)‖
      ≤ (3 + dh_kappa) * (‖s₀‖ + δ) * (((k + 1) * 5 + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
    intro k w hw
    have hw0 : 0 < w.re := hsub hw
    refine (norm_dhBlock_le hw0 (k := k + 1) (by omega)).trans ?_
    have hbase : (1 : ℝ) ≤ (((k + 1) * 5 + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hexp : (((k + 1) * 5 + 1 : ℕ) : ℝ) ^ (-w.re - 1)
        ≤ (((k + 1) * 5 + 1 : ℕ) : ℝ) ^ (-δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hre w hw])
    have h1 : (3 + dh_kappa) * ‖w‖ ≤ (3 + dh_kappa) * (‖s₀‖ + δ) :=
      mul_le_mul_of_nonneg_left (hM w hw) hnn
    exact mul_le_mul h1 hexp (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg hnn (add_nonneg (norm_nonneg _) hδ0.le))
  have hshift : DifferentiableOn ℂ
      (fun w => ∑' k, dhBlock w (k + 1)) (Metric.ball s₀ δ) :=
    differentiableOn_tsum_of_summable_norm hu
      (fun k => (differentiable_block (k + 1)).differentiableOn)
      Metric.isOpen_ball hF_le
  have hd : DifferentiableOn ℂ
      (fun w => dhBlock w 0 + ∑' k, dhBlock w (k + 1)) (Metric.ball s₀ δ) :=
    ((differentiable_block 0).differentiableOn).add hshift
  have heq : Set.EqOn dhBlockSum
      (fun w => dhBlock w 0 + ∑' k, dhBlock w (k + 1)) (Metric.ball s₀ δ) := by
    intro w hw
    simpa [dhBlockSum] using
      tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr (summable_dhBlock (hsub hw)))
  exact ((hd.congr heq).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ0))).differentiableWithinAt

/-! ### The identity: the block sum *is* `DH` on `Re s > 0` -/

theorem dhBlockSum_eq_DH {s : ℂ} (hs : 0 < s.re) : dhBlockSum s = DH s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => Complex.add_re x y, fun c x => by
      simp [Complex.real_smul, Complex.mul_re]⟩
  have hconv : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_gt hlin 0
  have hDH : AnalyticOnNhd ℂ DH {z : ℂ | 0 < z.re} :=
    DH_differentiable.differentiableOn.analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ dhBlockSum {z : ℂ | 0 < z.re} :=
    differentiableOn_dhBlockSum.analyticOnNhd hU
  have h2mem : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simp
  have hev : dhBlockSum =ᶠ[nhds (2 : ℂ)] DH := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen1.mem_nhds ?_) fun z hz => ?_
    · simp
    · simpa [dhBlockSum] using (hasSum_dhBlock_DH hz).tsum_eq
  exact hG.eqOn_of_preconnected_of_eventuallyEq hDH hconv.isPreconnected
    h2mem hev hs

/-! ### Regrouping the finite partial sums -/

private lemma sum_range_mul_five (f : ℕ → ℂ) (K : ℕ) :
    ∑ n ∈ range (K * 5), f n
      = ∑ k ∈ range K, ∑ j ∈ range 5, f (k * 5 + j) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, show (K + 1) * 5 = K * 5 + 5 by ring]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    ring

/-! ### The tail bound -/

/-- **The certified tail bound.**  For `Re s > 0` and `K ≥ 2`, the distance
from `DH s` to the `5K`-term partial sum of its Dirichlet series is at most
`(3 + κ)·‖s‖·5^{-Re s − 1}·(K−1)^{-Re s}/Re s`.  Every ingredient is
kernel-checked: the analytic continuation is `dhBlockSum_eq_DH`, the
per-block bounds are mean-value inequalities, and the tail of block bounds
is summed by the integral test.  This turns `DH` at any strip point into a
finite computation plus an explicit error term — the statement whose absence
`OracleDH.lean` records. -/
theorem DH_tail_bound {s : ℂ} (hs : 0 < s.re) {K : ℕ} (hK : 2 ≤ K) :
    ‖DH s - ∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)‖
      ≤ (3 + dh_kappa) * ‖s‖ * (5 : ℝ) ^ (-s.re - 1)
        * (((K : ℝ) - 1) ^ (-s.re) / s.re) := by
  have hsummable := summable_dhBlock hs
  have hnn : (0 : ℝ) ≤ 3 + dh_kappa := by linarith [dh_kappa_nonneg]
  -- the partial sum over `n < 5K` is the partial sum of the first `K` blocks
  have hsplit := Summable.sum_add_tsum_nat_add' (f := dhBlock s) (k := K)
    ((summable_nat_add_iff K).mpr hsummable)
  have key : DH s - ∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
      = ∑' k, dhBlock s (k + K) := by
    rw [← dhBlockSum_eq_DH hs, dhBlockSum, ← hsplit,
      sum_range_mul_five (fun n => (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)) K]
    simp only [dhBlock]
    ring
  -- summability of the three comparison series
  have hplain : Summable (fun k : ℕ =>
      (((k + K) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    refine (summable_shifted_rpow hs (K - 1)).congr fun k => ?_
    rw [show k + 1 + (K - 1) = k + K from by omega]
  have hg : Summable (fun k : ℕ =>
      (3 + dh_kappa) * ‖s‖ * (((k + K) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
    hplain.mul_left ((3 + dh_kappa) * ‖s‖)
  have hnorm : Summable (fun k : ℕ => ‖dhBlock s (k + K)‖) :=
    hg.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_dhBlock_le hs (by omega))
  have hKR : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hshifted : Summable (fun k : ℕ => ((k + K : ℕ) : ℝ) ^ (-s.re - 1)) := by
    have hbase : Summable (fun k : ℕ => ((k : ℝ)) ^ (-s.re - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have := (summable_nat_add_iff
      (f := fun k : ℕ => ((k : ℝ)) ^ (-s.re - 1)) K).mpr hbase
    simpa using this
  have hcmp : Summable (fun k : ℕ =>
      ((k + K : ℕ) : ℝ) ^ (-s.re - 1) * (5 : ℝ) ^ (-s.re - 1)) :=
    hshifted.mul_right _
  -- pointwise comparison of block bases with `5·(k+K)`
  have hpoint : ∀ k : ℕ, (((k + K) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1)
      ≤ ((k + K : ℕ) : ℝ) ^ (-s.re - 1) * (5 : ℝ) ^ (-s.re - 1) := by
    intro k
    have hkK : (0 : ℝ) < ((k + K : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have h5 : (0 : ℝ) < (((k + K) * 5 : ℕ) : ℝ) := by positivity
    have h1 : (((k + K) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1)
        ≤ (((k + K) * 5 : ℕ) : ℝ) ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos h5 (by push_cast; linarith) (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [show (((k + K) * 5 : ℕ) : ℝ) = ((k + K : ℕ) : ℝ) * 5 by push_cast; ring,
      Real.mul_rpow hkK.le (by norm_num)]
  -- the integral test for the shifted rpow tail
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s.re - 1))
      (Set.Ici ((K - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hKR hx) hxy (by linarith)
  have hintg : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-s.re - 1))
      (Set.Ioi ((K - 1 : ℕ) : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hKR
  have hnonneg : ∀ t ∈ Set.Ioi ((K - 1 : ℕ) : ℝ),
      0 ≤ (fun t : ℝ => t ^ (-s.re - 1)) t := fun t ht =>
    Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt hKR.le ht)) _
  have htail := AntitoneOn.tsum_comp_add_le_integral (K - 1) hanti hintg hnonneg
  have hidx : ∀ n : ℕ, n + (K - 1) + 1 = n + K := fun n => by omega
  simp only [hidx] at htail
  have hint : ∫ t in Set.Ioi ((K - 1 : ℕ) : ℝ), t ^ (-s.re - 1)
      = (((K : ℝ) - 1) ^ (-s.re) / s.re) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hKR,
      show -s.re - 1 + 1 = -s.re by ring,
      Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one, neg_div_neg_eq]
  rw [hint] at htail
  -- assemble
  calc ‖DH s - ∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)‖
      = ‖∑' k, dhBlock s (k + K)‖ := by rw [key]
    _ ≤ ∑' k, ‖dhBlock s (k + K)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, (3 + dh_kappa) * ‖s‖
          * (((k + K) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
        hnorm.tsum_le_tsum (fun k => norm_dhBlock_le hs (by omega)) hg
    _ = (3 + dh_kappa) * ‖s‖
          * ∑' k, (((k + K) * 5 + 1 : ℕ) : ℝ) ^ (-s.re - 1) := tsum_mul_left
    _ ≤ (3 + dh_kappa) * ‖s‖
          * ∑' k, ((k + K : ℕ) : ℝ) ^ (-s.re - 1) * (5 : ℝ) ^ (-s.re - 1) := by
        exact mul_le_mul_of_nonneg_left
          (hplain.tsum_le_tsum hpoint hcmp) (mul_nonneg hnn (norm_nonneg s))
    _ = (3 + dh_kappa) * ‖s‖ * (5 : ℝ) ^ (-s.re - 1)
          * ∑' k, ((k + K : ℕ) : ℝ) ^ (-s.re - 1) := by
        rw [tsum_mul_right]
        ring
    _ ≤ (3 + dh_kappa) * ‖s‖ * (5 : ℝ) ^ (-s.re - 1)
          * (((K : ℝ) - 1) ^ (-s.re) / s.re) := by
        refine mul_le_mul_of_nonneg_left htail ?_
        exact mul_nonneg (mul_nonneg hnn (norm_nonneg s)) (Real.rpow_nonneg (by norm_num) _)

end ZetaLean.DH
