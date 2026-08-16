import Mathlib

namespace AristotleT

open Filter Set Topology MeasureTheory

noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

/-! ### The one–dimensional ramp and its two derivatives -/

private noncomputable def rampPoly1 (x : ℝ) : ℝ :=
  140 * x ^ 3 - 420 * x ^ 4 + 420 * x ^ 5 - 140 * x ^ 6

private noncomputable def rampPoly2 (x : ℝ) : ℝ :=
  420 * x ^ 2 - 1680 * x ^ 3 + 2100 * x ^ 4 - 840 * x ^ 5

private noncomputable def eta1 (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 0 else rampPoly1 x

private noncomputable def eta2 (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 0 else rampPoly2 x

private theorem hasDerivAt_rampPoly (x : ℝ) : HasDerivAt rampPoly (rampPoly1 x) x := by
  unfold rampPoly rampPoly1
  exact (((((hasDerivAt_pow 4 x).const_mul 35).sub ((hasDerivAt_pow 5 x).const_mul 84)).add
      ((hasDerivAt_pow 6 x).const_mul 70)).sub
      ((hasDerivAt_pow 7 x).const_mul 20)).congr_deriv (by push_cast; ring)

private theorem hasDerivAt_rampPoly1 (x : ℝ) : HasDerivAt rampPoly1 (rampPoly2 x) x := by
  unfold rampPoly1 rampPoly2
  exact (((((hasDerivAt_pow 3 x).const_mul 140).sub ((hasDerivAt_pow 4 x).const_mul 420)).add
      ((hasDerivAt_pow 5 x).const_mul 420)).sub
      ((hasDerivAt_pow 6 x).const_mul 140)).congr_deriv (by push_cast; ring)

private theorem continuous_rampPoly2 : Continuous rampPoly2 := by
  unfold rampPoly2; fun_prop

private theorem hasDerivAt_of_left_right {f g h : ℝ → ℝ} {c a : ℝ}
    (hl : ∀ᶠ y in 𝓝[≤] a, f y = g y) (hg : HasDerivAt g c a)
    (hr : ∀ᶠ y in 𝓝[≥] a, f y = h y) (hh : HasDerivAt h c a) :
    HasDerivAt f c a := by
  have h1 : HasDerivWithinAt f c (Set.Iic a) a :=
    hg.hasDerivWithinAt.congr_of_eventuallyEq hl (hl.self_of_nhdsWithin Set.self_mem_Iic)
  have h2 : HasDerivWithinAt f c (Set.Ici a) a :=
    hh.hasDerivWithinAt.congr_of_eventuallyEq hr (hr.self_of_nhdsWithin Set.self_mem_Ici)
  have := h1.union h2
  rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
  exact this

private theorem hasDerivAt_eta (x : ℝ) : HasDerivAt eta (eta1 x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have he : eta1 x = 0 := by simp [eta1, hx.le]
    rw [he]
    refine (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    have : y ≤ 0 := le_of_lt hy
    simp [eta, this]
  · subst hx
    have h0 : eta1 (0:ℝ) = 0 := by simp [eta1]
    rw [h0]
    refine hasDerivAt_of_left_right (g := fun _ => (0:ℝ)) ?_ (hasDerivAt_const _ _)
      (h := rampPoly) ?_ ((hasDerivAt_rampPoly 0).congr_deriv (by norm_num [rampPoly1]))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have : y ≤ 0 := hy
      simp [eta, this]
    · filter_upwards [Ico_mem_nhdsGE (by norm_num : (0:ℝ) < 1)] with y hy
      rcases le_or_gt y 0 with h | h
      · have hy0 : y = 0 := le_antisymm h hy.1
        simp [eta, hy0, rampPoly]
      · simp [eta, not_le.2 h, not_le.2 hy.2]
  · rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
    · have he : eta1 x = rampPoly1 x := by simp [eta1, not_le.2 hx, not_le.2 hx1]
      rw [he]
      refine (hasDerivAt_rampPoly x).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx hx1] with y hy
      simp [eta, not_le.2 hy.1, not_le.2 hy.2]
    · subst hx1
      have h0 : eta1 (1:ℝ) = 0 := by simp [eta1]
      rw [h0]
      refine hasDerivAt_of_left_right (g := rampPoly) ?_
        ((hasDerivAt_rampPoly 1).congr_deriv (by norm_num [rampPoly1]))
        (h := fun _ => (1:ℝ)) ?_ (hasDerivAt_const _ _)
      · filter_upwards [Ioc_mem_nhdsLE (by norm_num : (0:ℝ) < 1)] with y hy
        rcases lt_or_ge y 1 with h | h
        · simp [eta, not_le.2 hy.1, not_le.2 h]
        · have hy1 : y = 1 := le_antisymm hy.2 h
          rw [hy1]; norm_num [eta, rampPoly]
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hy1 : (1:ℝ) ≤ y := hy
        have : ¬ y ≤ 0 := by linarith
        simp [eta, this, hy1]
    · have he : eta1 x = 0 := by simp [eta1, hx1.le, not_le.2 hx]
      rw [he]
      refine (hasDerivAt_const x (1:ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      have hy1 : (1:ℝ) < y := hy
      have : ¬ y ≤ 0 := by linarith
      simp [eta, this, hy1.le]

private theorem hasDerivAt_eta1 (x : ℝ) : HasDerivAt eta1 (eta2 x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have he : eta2 x = 0 := by simp [eta2, hx.le]
    rw [he]
    refine (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    have : y ≤ 0 := le_of_lt hy
    simp [eta1, this]
  · subst hx
    have h0 : eta2 (0:ℝ) = 0 := by simp [eta2]
    rw [h0]
    refine hasDerivAt_of_left_right (g := fun _ => (0:ℝ)) ?_ (hasDerivAt_const _ _)
      (h := rampPoly1) ?_ ((hasDerivAt_rampPoly1 0).congr_deriv (by norm_num [rampPoly2]))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have : y ≤ 0 := hy
      simp [eta1, this]
    · filter_upwards [Ico_mem_nhdsGE (by norm_num : (0:ℝ) < 1)] with y hy
      rcases le_or_gt y 0 with h | h
      · have hy0 : y = 0 := le_antisymm h hy.1
        simp [eta1, hy0, rampPoly1]
      · simp [eta1, not_le.2 h, not_le.2 hy.2]
  · rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
    · have he : eta2 x = rampPoly2 x := by simp [eta2, not_le.2 hx, not_le.2 hx1]
      rw [he]
      refine (hasDerivAt_rampPoly1 x).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hx hx1] with y hy
      simp [eta1, not_le.2 hy.1, not_le.2 hy.2]
    · subst hx1
      have h0 : eta2 (1:ℝ) = 0 := by simp [eta2]
      rw [h0]
      refine hasDerivAt_of_left_right (g := rampPoly1) ?_
        ((hasDerivAt_rampPoly1 1).congr_deriv (by norm_num [rampPoly2]))
        (h := fun _ => (0:ℝ)) ?_ (hasDerivAt_const _ _)
      · filter_upwards [Ioc_mem_nhdsLE (by norm_num : (0:ℝ) < 1)] with y hy
        rcases lt_or_ge y 1 with h | h
        · simp [eta1, not_le.2 hy.1, not_le.2 h]
        · have hy1 : y = 1 := le_antisymm hy.2 h
          rw [hy1]; norm_num [eta1, rampPoly1]
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hy1 : (1:ℝ) ≤ y := hy
        have : ¬ y ≤ 0 := by linarith
        simp [eta1, this, hy1]
    · have he : eta2 x = 0 := by simp [eta2, hx1.le, not_le.2 hx]
      rw [he]
      refine (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      have hy1 : (1:ℝ) < y := hy
      have : ¬ y ≤ 0 := by linarith
      simp [eta1, this, hy1.le]

private theorem continuous_eta : Continuous eta :=
  Differentiable.continuous (fun x => (hasDerivAt_eta x).differentiableAt)

private theorem continuous_eta1 : Continuous eta1 :=
  Differentiable.continuous (fun x => (hasDerivAt_eta1 x).differentiableAt)

private theorem continuous_eta2 : Continuous eta2 := by
  have h1 : Continuous (fun x : ℝ => if 1 ≤ x then (0:ℝ) else rampPoly2 x) :=
    Continuous.if_le continuous_const continuous_rampPoly2 continuous_const continuous_id
      (by intro x hx; rw [← hx]; norm_num [rampPoly2])
  unfold eta2
  exact Continuous.if_le continuous_const h1 continuous_id continuous_const
      (by intro x hx; rw [hx]; norm_num [rampPoly2])

/-! ### Elementary values and signs -/

private theorem rampPoly_factor (x : ℝ) :
    rampPoly x = x ^ 4 * (1 + 4 * (1 - x) + 10 * (1 - x) ^ 2 + 20 * (1 - x) ^ 3) := by
  unfold rampPoly; ring

private theorem one_sub_rampPoly_factor (x : ℝ) :
    1 - rampPoly x = (1 - x) ^ 4 * (1 + 4 * x + 10 * x ^ 2 + 20 * x ^ 3) := by
  unfold rampPoly; ring

private theorem rampPoly1_factor (x : ℝ) : rampPoly1 x = 140 * x ^ 3 * (1 - x) ^ 3 := by
  unfold rampPoly1; ring

private theorem rampPoly2_factor (x : ℝ) :
    rampPoly2 x = 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x) := by
  unfold rampPoly2; ring

private theorem eta_nonneg (x : ℝ) : 0 ≤ eta x := by
  unfold eta
  split_ifs with h1 h2
  · exact le_refl 0
  · norm_num
  · rw [rampPoly_factor]
    have hx : 0 < x := not_le.1 h1
    have hx1 : x < 1 := not_le.1 h2
    have ht : (0:ℝ) ≤ 1 - x := by linarith
    refine mul_nonneg (by positivity) ?_
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3]

private theorem eta_le_one (x : ℝ) : eta x ≤ 1 := by
  unfold eta
  split_ifs with h1 h2
  · norm_num
  · exact le_refl 1
  · have hx : 0 < x := not_le.1 h1
    have hx1 : x < 1 := not_le.1 h2
    have ht : (0:ℝ) ≤ 1 - x := by linarith
    have key : 0 ≤ 1 - rampPoly x := by
      rw [one_sub_rampPoly_factor]
      refine mul_nonneg (by positivity) ?_
      nlinarith [pow_nonneg hx.le 2, pow_nonneg hx.le 3]
    linarith

private theorem abs_eta_le_one (x : ℝ) : |eta x| ≤ 1 :=
  abs_le.2 ⟨by linarith [eta_nonneg x], eta_le_one x⟩

private theorem eta_of_nonpos {x : ℝ} (h : x ≤ 0) : eta x = 0 := by simp [eta, h]

private theorem eta_of_one_le {x : ℝ} (h : 1 ≤ x) : eta x = 1 := by
  have : ¬ x ≤ 0 := by linarith
  simp [eta, this, h]

private theorem eta1_of_nonpos {x : ℝ} (h : x ≤ 0) : eta1 x = 0 := by simp [eta1, h]

private theorem eta1_of_one_le {x : ℝ} (h : 1 ≤ x) : eta1 x = 0 := by
  have : ¬ x ≤ 0 := by linarith
  simp [eta1, this, h]

private theorem eta2_of_nonpos {x : ℝ} (h : x ≤ 0) : eta2 x = 0 := by simp [eta2, h]

private theorem eta2_of_one_le {x : ℝ} (h : 1 ≤ x) : eta2 x = 0 := by
  have : ¬ x ≤ 0 := by linarith
  simp [eta2, this, h]

private theorem eta1_nonneg (x : ℝ) : 0 ≤ eta1 x := by
  unfold eta1
  split_ifs with h1 h2
  · exact le_refl 0
  · exact le_refl 0
  · rw [rampPoly1_factor]
    have hx : 0 < x := not_le.1 h1
    have hx1 : x < 1 := not_le.1 h2
    have ht : (0:ℝ) ≤ 1 - x := by linarith
    positivity

private theorem eta1_half : eta1 (1/2 : ℝ) = 35/16 := by
  norm_num [eta1, rampPoly1]

private theorem eta2_nonneg_of_le_half {x : ℝ} (h1 : x ≤ 1/2) : 0 ≤ eta2 x := by
  unfold eta2
  split_ifs with ha hb
  · exact le_refl 0
  · exact le_refl 0
  · rw [rampPoly2_factor]
    have hx : 0 < x := not_le.1 ha
    have hnn : (0:ℝ) ≤ 1 - 2 * x := by linarith
    have h2 : (0:ℝ) ≤ 420 * x ^ 2 * (1 - x) ^ 2 := by positivity
    exact mul_nonneg h2 hnn

private theorem eta2_nonpos_of_half_le {x : ℝ} (h0 : 1/2 ≤ x) : eta2 x ≤ 0 := by
  unfold eta2
  split_ifs with ha hb
  · exact le_refl 0
  · exact le_refl 0
  · rw [rampPoly2_factor]
    have hx : 0 < x := not_le.1 ha
    have hnn : (1 - 2 * x) ≤ 0 := by linarith
    have h2 : (0:ℝ) ≤ 420 * x ^ 2 * (1 - x) ^ 2 := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos h2 hnn

/-! ### The tapering factor `ψ(u) = η(L/2 - |u|)` and its two derivatives -/

private noncomputable def psi (L u : ℝ) : ℝ := eta (L / 2 - |u|)

private noncomputable def psi1 (L u : ℝ) : ℝ :=
  if 0 ≤ u then -eta1 (L / 2 - u) else eta1 (L / 2 + u)

private noncomputable def psi2 (L u : ℝ) : ℝ := eta2 (L / 2 - |u|)

private theorem hasDerivAt_psi {L : ℝ} (hL : 8 ≤ L) (u : ℝ) :
    HasDerivAt (psi L) (psi1 L u) u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hps : psi1 L u = eta1 (L / 2 + u) * 1 := by
      rw [psi1, if_neg (not_le.2 hu)]; ring
    rw [hps]
    have hbase : HasDerivAt (fun y : ℝ => eta (L / 2 + y)) (eta1 (L / 2 + u) * 1) u :=
      HasDerivAt.comp u (hasDerivAt_eta (L / 2 + u)) ((hasDerivAt_id u).const_add (L / 2))
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hu] with y hy
    have hy' : y < 0 := hy
    rw [psi, abs_of_neg hy', sub_neg_eq_add]
  · subst hu
    have hps : psi1 L 0 = 0 := by
      rw [psi1, if_pos le_rfl, eta1_of_one_le (by linarith), neg_zero]
    rw [hps]
    refine (hasDerivAt_const (0:ℝ) (1:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)] with y hy
    have hy1 : |y| < 1 := abs_lt.2 ⟨hy.1, hy.2⟩
    rw [psi, eta_of_one_le (by linarith)]
  · have hps : psi1 L u = eta1 (L / 2 - u) * (-1) := by
      rw [psi1, if_pos hu.le]; ring
    rw [hps]
    have hbase : HasDerivAt (fun y : ℝ => eta (L / 2 - y)) (eta1 (L / 2 - u) * (-1)) u :=
      HasDerivAt.comp u (hasDerivAt_eta (L / 2 - u)) ((hasDerivAt_id u).const_sub (L / 2))
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hu] with y hy
    have hy' : 0 < y := hy
    rw [psi, abs_of_pos hy']

private theorem hasDerivAt_psi1 {L : ℝ} (hL : 8 ≤ L) (u : ℝ) :
    HasDerivAt (psi1 L) (psi2 L u) u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hps : psi2 L u = eta2 (L / 2 + u) * 1 := by
      rw [psi2, abs_of_neg hu, sub_neg_eq_add, mul_one]
    rw [hps]
    have hbase : HasDerivAt (fun y : ℝ => eta1 (L / 2 + y)) (eta2 (L / 2 + u) * 1) u :=
      HasDerivAt.comp u (hasDerivAt_eta1 (L / 2 + u)) ((hasDerivAt_id u).const_add (L / 2))
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hu] with y hy
    have hy' : y < 0 := hy
    rw [psi1, if_neg (not_le.2 hy')]
  · subst hu
    have hps : psi2 L 0 = 0 := by
      rw [psi2, abs_zero, sub_zero, eta2_of_one_le (by linarith)]
    rw [hps]
    refine (hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)] with y hy
    rcases le_or_gt 0 y with h | h
    · rw [psi1, if_pos h, eta1_of_one_le (by linarith [hy.2]), neg_zero]
    · rw [psi1, if_neg (not_le.2 h), eta1_of_one_le (by linarith [hy.1])]
  · have hps : psi2 L u = -(eta2 (L / 2 - u) * (-1)) := by
      rw [psi2, abs_of_pos hu]; ring
    rw [hps]
    have hbase : HasDerivAt (fun y : ℝ => -eta1 (L / 2 - y)) (-(eta2 (L / 2 - u) * (-1))) u :=
      (HasDerivAt.comp u (hasDerivAt_eta1 (L / 2 - u))
        ((hasDerivAt_id u).const_sub (L / 2))).neg
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hu] with y hy
    have hy' : 0 < y := hy
    rw [psi1, if_pos hy'.le]

private theorem continuous_psi (L : ℝ) : Continuous (psi L) :=
  continuous_eta.comp (by fun_prop)

private theorem continuous_psi1 {L : ℝ} (hL : 8 ≤ L) : Continuous (psi1 L) :=
  Differentiable.continuous (fun u => (hasDerivAt_psi1 hL u).differentiableAt)

private theorem continuous_psi2 (L : ℝ) : Continuous (psi2 L) :=
  continuous_eta2.comp (by fun_prop)

private theorem psi_eq_zero {L u : ℝ} (h : L / 2 ≤ |u|) : psi L u = 0 :=
  eta_of_nonpos (by linarith)

private theorem psi1_eq_zero {L u : ℝ} (h : L / 2 ≤ |u|) : psi1 L u = 0 := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu] at h
    rw [psi1, if_pos hu, eta1_of_nonpos (by linarith), neg_zero]
  · rw [abs_of_neg hu] at h
    rw [psi1, if_neg (not_le.2 hu), eta1_of_nonpos (by linarith)]

private theorem psi2_eq_zero {L u : ℝ} (h : L / 2 ≤ |u|) : psi2 L u = 0 :=
  eta2_of_nonpos (by linarith)

/-! ### Integrals -/

private theorem le_abs_of_notMem_Ioc {L x : ℝ} (hx : x ∉ Set.Ioc (-(L / 2)) (L / 2)) :
    L / 2 ≤ |x| := by
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  rcases hx with h | h
  · exact le_abs.2 (Or.inr (by linarith))
  · exact le_abs.2 (Or.inl h.le)

private theorem integrable_of_support {L : ℝ} {f : ℝ → ℝ} (hc : Continuous f)
    (hf : ∀ u, L / 2 ≤ |u| → f u = 0) : Integrable f := by
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (K := Set.Icc (-(L / 2)) (L / 2)) isCompact_Icc ?_)
  intro x hx
  refine hf x ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact le_abs.2 (Or.inr (by linarith))
  · exact le_abs.2 (Or.inl h.le)

private theorem integral_eq_intervalIntegral {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ∀ u, L / 2 ≤ |u| → f u = 0) :
    ∫ u : ℝ, f u = ∫ u in (-(L / 2))..(L / 2), f u := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hf x (le_abs_of_notMem_Ioc hx))).symm

private theorem intervalIntegral_eta1 {L : ℝ} (hL : 8 ≤ L) :
    ∫ x in (0:ℝ)..(L / 2), eta1 x = 1 := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := eta) (f' := eta1) (a := 0) (b := L / 2)
    (fun x _ => hasDerivAt_eta x) (continuous_eta1.intervalIntegrable _ _)
  rw [this, eta_of_one_le (by linarith : (1:ℝ) ≤ L / 2), eta_of_nonpos (le_refl 0)]
  ring

private theorem intervalIntegral_abs_eta2 {L : ℝ} (hL : 8 ≤ L) :
    ∫ x in (0:ℝ)..(L / 2), |eta2 x| = 35 / 8 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => |eta2 x|) volume a b := fun a b =>
    (continuous_eta2.abs).intervalIntegrable _ _
  have h1 : ∫ x in (0:ℝ)..(1/2 : ℝ), |eta2 x| = 35 / 16 := by
    have hcongr : ∫ x in (0:ℝ)..(1/2 : ℝ), |eta2 x| = ∫ x in (0:ℝ)..(1/2 : ℝ), eta2 x := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
      exact abs_of_nonneg (eta2_nonneg_of_le_half hx.2)
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := eta1) (f' := eta2) (fun x _ => hasDerivAt_eta1 x)
      (continuous_eta2.intervalIntegrable _ _), eta1_half, eta1_of_nonpos (le_refl 0)]
    ring
  have h2 : ∫ x in (1/2 : ℝ)..(1:ℝ), |eta2 x| = 35 / 16 := by
    have hcongr : ∫ x in (1/2 : ℝ)..(1:ℝ), |eta2 x| = ∫ x in (1/2 : ℝ)..(1:ℝ), -eta2 x := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at hx
      exact abs_of_nonpos (eta2_nonpos_of_half_le hx.1)
    rw [hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := eta1) (f' := eta2) (fun x _ => hasDerivAt_eta1 x)
      (continuous_eta2.intervalIntegrable _ _), eta1_half, eta1_of_one_le (le_refl 1)]
    ring
  have h3 : ∫ x in (1:ℝ)..(L / 2), |eta2 x| = 0 := by
    have hcongr : ∫ x in (1:ℝ)..(L / 2), |eta2 x| = ∫ _x in (1:ℝ)..(L / 2), (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (1:ℝ) ≤ L / 2)] at hx
      simp only [eta2_of_one_le hx.1, abs_zero]
    rw [hcongr, intervalIntegral.integral_const]
    simp
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun x => |eta2 x|) (a := (0:ℝ)) (b := (1/2:ℝ)) (c := (1:ℝ)) (hint _ _) (hint _ _)
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun x => |eta2 x|) (a := (0:ℝ)) (b := (1:ℝ)) (c := L / 2) (hint _ _) (hint _ _)
  rw [← e2, ← e1, h1, h2, h3]
  norm_num

private theorem integral_abs_psi_le {L : ℝ} (hL : 8 ≤ L) : ∫ u : ℝ, |psi L u| ≤ L := by
  rw [integral_eq_intervalIntegral (by linarith : (0:ℝ) < L)
    (fun u hu => by rw [psi_eq_zero hu, abs_zero])]
  have hmono := intervalIntegral.integral_mono_on (a := -(L / 2)) (b := L / 2)
    (f := fun u => |psi L u|) (g := fun _ => (1:ℝ)) (by linarith)
    ((continuous_psi L).abs.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume))
    (fun x _ => abs_eta_le_one (L / 2 - |x|))
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hmono
  linarith

private theorem integral_abs_psi1 {L : ℝ} (hL : 8 ≤ L) : ∫ u : ℝ, |psi1 L u| = 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => |psi1 L u|) volume a b := fun a b =>
    ((continuous_psi1 hL).abs).intervalIntegrable _ _
  rw [integral_eq_intervalIntegral (by linarith : (0:ℝ) < L)
    (fun u hu => by rw [psi1_eq_zero hu, abs_zero])]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun u => |psi1 L u|) (a := -(L / 2)) (b := (0:ℝ)) (c := L / 2) (hint _ _) (hint _ _)
  have hright : ∫ u in (0:ℝ)..(L / 2), |psi1 L u| = 1 := by
    have hc : ∫ u in (0:ℝ)..(L / 2), |psi1 L u| = ∫ u in (0:ℝ)..(L / 2), eta1 (L / 2 - u) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ L / 2)] at hx
      show |psi1 L x| = eta1 (L / 2 - x)
      rw [psi1, if_pos hx.1, abs_neg, abs_of_nonneg (eta1_nonneg _)]
    rw [hc, intervalIntegral.integral_comp_sub_left (fun x => eta1 x) (L / 2), sub_self, sub_zero]
    exact intervalIntegral_eta1 hL
  have hleft : ∫ u in (-(L / 2))..(0:ℝ), |psi1 L u| = 1 := by
    have hc : ∫ u in (-(L / 2))..(0:ℝ), |psi1 L u|
        = ∫ u in (-(L / 2))..(0:ℝ), eta1 (L / 2 + u) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith : -(L / 2) ≤ (0:ℝ))] at hx
      show |psi1 L x| = eta1 (L / 2 + x)
      rcases lt_or_ge x 0 with h | h
      · rw [psi1, if_neg (not_le.2 h), abs_of_nonneg (eta1_nonneg _)]
      · have hx0 : x = 0 := le_antisymm hx.2 h
        subst hx0
        rw [psi1, if_pos le_rfl, add_zero, sub_zero,
          eta1_of_one_le (by linarith : (1:ℝ) ≤ L / 2), neg_zero, abs_zero]
    have hz : L / 2 + -(L / 2) = 0 := by ring
    rw [hc, intervalIntegral.integral_comp_add_left (fun x => eta1 x) (L / 2), hz, add_zero]
    exact intervalIntegral_eta1 hL
  rw [← hsplit, hright, hleft]
  norm_num

private theorem integral_abs_psi2 {L : ℝ} (hL : 8 ≤ L) : ∫ u : ℝ, |psi2 L u| = 35 / 4 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => |psi2 L u|) volume a b := fun a b =>
    ((continuous_psi2 L).abs).intervalIntegrable _ _
  rw [integral_eq_intervalIntegral (by linarith : (0:ℝ) < L)
    (fun u hu => by rw [psi2_eq_zero hu, abs_zero])]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun u => |psi2 L u|) (a := -(L / 2)) (b := (0:ℝ)) (c := L / 2) (hint _ _) (hint _ _)
  have hright : ∫ u in (0:ℝ)..(L / 2), |psi2 L u| = 35 / 8 := by
    have hc : ∫ u in (0:ℝ)..(L / 2), |psi2 L u| = ∫ u in (0:ℝ)..(L / 2), |eta2 (L / 2 - u)| := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ L / 2)] at hx
      show |psi2 L x| = |eta2 (L / 2 - x)|
      rw [psi2, abs_of_nonneg hx.1]
    rw [hc, intervalIntegral.integral_comp_sub_left (fun x => |eta2 x|) (L / 2), sub_self, sub_zero]
    exact intervalIntegral_abs_eta2 hL
  have hleft : ∫ u in (-(L / 2))..(0:ℝ), |psi2 L u| = 35 / 8 := by
    have hc : ∫ u in (-(L / 2))..(0:ℝ), |psi2 L u|
        = ∫ u in (-(L / 2))..(0:ℝ), |eta2 (L / 2 + u)| := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith : -(L / 2) ≤ (0:ℝ))] at hx
      show |psi2 L x| = |eta2 (L / 2 + x)|
      rw [psi2, abs_of_nonpos hx.2, sub_neg_eq_add]
    have hz : L / 2 + -(L / 2) = 0 := by ring
    rw [hc, intervalIntegral.integral_comp_add_left (fun x => |eta2 x|) (L / 2), hz, add_zero]
    exact intervalIntegral_abs_eta2 hL
  rw [← hsplit, hright, hleft]
  norm_num

/-! ### The main bound -/

theorem taper_second_deriv_L1_bound
    (P : ℝ → ℝ) (L B0 B1 B2 : ℝ) (hL : 8 ≤ L) (hP : ContDiff ℝ 2 P)
    (hB0 : ∀ y : ℝ, |y| ≤ 1/2 → |P y| ≤ B0)
    (hB1 : ∀ y : ℝ, |y| ≤ 1/2 → |deriv P y| ≤ B1)
    (hB2 : ∀ y : ℝ, |y| ≤ 1/2 → |deriv (deriv P) y| ≤ B2) :
    (∫ u : ℝ, |iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|)) u|)
      ≤ B2 / L + 4 * B1 / L + (35 / 4) * B0 := by
  have hLpos : (0:ℝ) < L := by linarith
  -- smoothness of `P`
  have hPd : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hPd1 : Differentiable ℝ (deriv P) := by
    have h := hP.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  have hPcont : Continuous P := hPd.continuous
  have hP1cont : Continuous (deriv P) := hPd1.continuous
  have hP2cont : Continuous (deriv (deriv P)) := by
    have h := hP.continuous_iteratedDeriv 2 (by norm_num)
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at h
  -- nonnegativity of the constants
  have hB0nn : 0 ≤ B0 := le_trans (abs_nonneg _) (hB0 0 (by norm_num))
  have hB1nn : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 0 (by norm_num))
  have hB2nn : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 0 (by norm_num))
  -- derivatives of the rescaled profile
  have hQ : ∀ u : ℝ, HasDerivAt (fun u : ℝ => P (u / L)) (deriv P (u / L) / L) u := by
    intro u
    exact (HasDerivAt.comp u (hPd (u / L)).hasDerivAt
      ((hasDerivAt_id u).div_const L)).congr_deriv (by field_simp)
  have hQ1 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => deriv P (u / L) / L)
      (deriv (deriv P) (u / L) / L ^ 2) u := by
    intro u
    refine HasDerivAt.congr_deriv (f' := deriv (deriv P) (u / L) * (1 / L) / L) ?_ (by ring)
    exact (HasDerivAt.comp u (hPd1 (u / L)).hasDerivAt
      ((hasDerivAt_id u).div_const L)).div_const L
  -- first and second derivative of the window
  have hphi : ∀ u : ℝ, HasDerivAt (fun u : ℝ => P (u / L) * eta (L / 2 - |u|))
      (deriv P (u / L) / L * psi L u + P (u / L) * psi1 L u) u :=
    fun u => (hQ u).mul (hasDerivAt_psi hL u)
  have hF1 : ∀ u : ℝ,
      HasDerivAt (fun u : ℝ => deriv P (u / L) / L * psi L u + P (u / L) * psi1 L u)
        (deriv (deriv P) (u / L) / L ^ 2 * psi L u
          + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u) u := by
    intro u
    exact (((hQ1 u).mul (hasDerivAt_psi hL u)).add
      ((hQ u).mul (hasDerivAt_psi1 hL u))).congr_deriv (by ring)
  have hiter : iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|))
      = fun u : ℝ => deriv (deriv P) (u / L) / L ^ 2 * psi L u
          + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u := by
    rw [iteratedDeriv_succ, iteratedDeriv_one,
      (funext fun u => (hphi u).deriv :
        deriv (fun u : ℝ => P (u / L) * eta (L / 2 - |u|))
          = fun u : ℝ => deriv P (u / L) / L * psi L u + P (u / L) * psi1 L u)]
    exact funext fun u => (hF1 u).deriv
  rw [hiter]
  -- continuity and integrability
  have hcQ : Continuous (fun u : ℝ => P (u / L)) := hPcont.comp (by fun_prop)
  have hcQ1 : Continuous (fun u : ℝ => deriv P (u / L) / L) :=
    (hP1cont.comp (by fun_prop)).div_const L
  have hcQ2 : Continuous (fun u : ℝ => deriv (deriv P) (u / L) / L ^ 2) :=
    (hP2cont.comp (by fun_prop)).div_const _
  have hcF2 : Continuous (fun u : ℝ => deriv (deriv P) (u / L) / L ^ 2 * psi L u
      + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u) :=
    ((hcQ2.mul (continuous_psi L)).add
      (continuous_const.mul (hcQ1.mul (continuous_psi1 hL)))).add (hcQ.mul (continuous_psi2 L))
  have hF2zero : ∀ u : ℝ, L / 2 ≤ |u| →
      deriv (deriv P) (u / L) / L ^ 2 * psi L u
        + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u = 0 := by
    intro u hu
    rw [psi_eq_zero hu, psi1_eq_zero hu, psi2_eq_zero hu]
    ring
  have iF2 : Integrable (fun u : ℝ => |deriv (deriv P) (u / L) / L ^ 2 * psi L u
      + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u|) :=
    integrable_of_support (L := L) hcF2.abs (fun u hu => by rw [hF2zero u hu, abs_zero])
  have i1 : Integrable (fun u : ℝ => |psi L u|) :=
    integrable_of_support (L := L) (continuous_psi L).abs
      (fun u hu => by rw [psi_eq_zero hu, abs_zero])
  have i2 : Integrable (fun u : ℝ => |psi1 L u|) :=
    integrable_of_support (L := L) (continuous_psi1 hL).abs
      (fun u hu => by rw [psi1_eq_zero hu, abs_zero])
  have i3 : Integrable (fun u : ℝ => |psi2 L u|) :=
    integrable_of_support (L := L) (continuous_psi2 L).abs
      (fun u hu => by rw [psi2_eq_zero hu, abs_zero])
  have ih : Integrable (fun u : ℝ => B2 / L ^ 2 * |psi L u| + 2 * (B1 / L) * |psi1 L u|
      + B0 * |psi2 L u|) := ((i1.const_mul _).add (i2.const_mul _)).add (i3.const_mul _)
  -- the pointwise bound
  have hpt : ∀ u : ℝ, |deriv (deriv P) (u / L) / L ^ 2 * psi L u
      + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u|
      ≤ B2 / L ^ 2 * |psi L u| + 2 * (B1 / L) * |psi1 L u| + B0 * |psi2 L u| := by
    intro u
    rcases le_or_gt (L / 2) |u| with hu | hu
    · rw [hF2zero u hu, abs_zero, psi_eq_zero hu, psi1_eq_zero hu, psi2_eq_zero hu]
      simp
    · have habs : |u / L| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
        linarith
      have e0 : |P (u / L)| ≤ B0 := hB0 _ habs
      have e1 : |deriv P (u / L) / L| ≤ B1 / L := by
        rw [abs_div, abs_of_pos hLpos]
        gcongr
        exact hB1 _ habs
      have e2 : |deriv (deriv P) (u / L) / L ^ 2| ≤ B2 / L ^ 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < L ^ 2)]
        gcongr
        exact hB2 _ habs
      have bA : |deriv (deriv P) (u / L) / L ^ 2 * psi L u| ≤ B2 / L ^ 2 * |psi L u| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right e2 (abs_nonneg _)
      have bB : |2 * (deriv P (u / L) / L * psi1 L u)| ≤ 2 * (B1 / L) * |psi1 L u| := by
        calc |2 * (deriv P (u / L) / L * psi1 L u)|
            = 2 * (|deriv P (u / L) / L| * |psi1 L u|) := by
              rw [abs_mul, abs_mul]; norm_num
          _ ≤ 2 * (B1 / L * |psi1 L u|) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right e1 (abs_nonneg _)) (by norm_num)
          _ = 2 * (B1 / L) * |psi1 L u| := by ring
      have bC : |P (u / L) * psi2 L u| ≤ B0 * |psi2 L u| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right e0 (abs_nonneg _)
      exact (abs_add_three _ _ _).trans (by linarith)
  -- put everything together
  calc (∫ u : ℝ, |deriv (deriv P) (u / L) / L ^ 2 * psi L u
          + 2 * (deriv P (u / L) / L * psi1 L u) + P (u / L) * psi2 L u|)
      ≤ ∫ u : ℝ, (B2 / L ^ 2 * |psi L u| + 2 * (B1 / L) * |psi1 L u| + B0 * |psi2 L u|) :=
        integral_mono iF2 ih hpt
    _ = B2 / L ^ 2 * (∫ u : ℝ, |psi L u|) + 2 * (B1 / L) * (∫ u : ℝ, |psi1 L u|)
          + B0 * (∫ u : ℝ, |psi2 L u|) := by
        have ic1 : Integrable (fun u : ℝ => B2 / L ^ 2 * |psi L u|) := i1.const_mul _
        have ic2 : Integrable (fun u : ℝ => 2 * (B1 / L) * |psi1 L u|) := i2.const_mul _
        have ic3 : Integrable (fun u : ℝ => B0 * |psi2 L u|) := i3.const_mul _
        have iab : Integrable
            (fun u : ℝ => B2 / L ^ 2 * |psi L u| + 2 * (B1 / L) * |psi1 L u|) := ic1.add ic2
        rw [integral_add iab ic3, integral_add ic1 ic2, integral_const_mul,
          integral_const_mul, integral_const_mul]
    _ ≤ B2 / L ^ 2 * L + 2 * (B1 / L) * 2 + B0 * (35 / 4) := by
        rw [integral_abs_psi1 hL, integral_abs_psi2 hL]
        have := integral_abs_psi_le hL
        have hc : (0:ℝ) ≤ B2 / L ^ 2 := by positivity
        nlinarith
    _ = B2 / L + 4 * B1 / L + (35 / 4) * B0 := by
        field_simp
        ring


end AristotleT