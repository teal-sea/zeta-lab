import Mathlib

namespace AristotleTU2

noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

namespace TaperAux

/-! ### The ramp polynomial and its derivatives -/

noncomputable def rampD (x : ℝ) : ℝ := 140 * x ^ 3 * (1 - x) ^ 3
noncomputable def rampDD (x : ℝ) : ℝ := 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)

noncomputable def etaD (x : ℝ) : ℝ := if x ≤ 0 then 0 else if 1 ≤ x then 0 else rampD x
noncomputable def etaDD (x : ℝ) : ℝ := if x ≤ 0 then 0 else if 1 ≤ x then 0 else rampDD x

lemma hasDerivAt_rampPoly (x : ℝ) : HasDerivAt rampPoly (rampD x) x := by
  have h4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
  have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by simpa using hasDerivAt_pow 5 x
  have h6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * x ^ 5) x := by simpa using hasDerivAt_pow 6 x
  have h7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * x ^ 6) x := by simpa using hasDerivAt_pow 7 x
  exact ((((h4.const_mul 35).sub (h5.const_mul 84)).add (h6.const_mul 70)).sub
    (h7.const_mul 20)).congr_deriv (by simp [rampD]; ring)

lemma hasDerivAt_rampD (x : ℝ) : HasDerivAt rampD (rampDD x) x := by
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
  have h3' : HasDerivAt (fun y : ℝ => (1 - y) ^ 3) (3 * (1 - x) ^ 2 * (-1)) x := by
    have h : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
    simpa using h.fun_pow 3
  exact ((h3.const_mul 140).mul h3').congr_deriv (by simp [rampDD]; ring)

/-! ### Basic identities for `eta` and its derivatives -/

lemma eta_eq_zero {y : ℝ} (h : y ≤ 0) : eta y = 0 := if_pos h

lemma eta_eq_one {y : ℝ} (h : 1 ≤ y) : eta y = 1 := by
  have h0 : ¬ (y ≤ 0) := by linarith
  simp [eta, h0, h]

lemma eta_eq_ramp {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : eta y = rampPoly y := by
  rcases eq_or_lt_of_le h0 with rfl | h0'
  · simp [eta, rampPoly]
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · rw [eta_eq_one le_rfl]; norm_num [rampPoly]
  · have ha : ¬ (y ≤ 0) := by linarith
    have hb : ¬ (1 ≤ y) := by linarith
    simp [eta, ha, hb]

lemma etaD_eq_zero {y : ℝ} (h : y ≤ 0) : etaD y = 0 := if_pos h

lemma etaD_eq_zero' {y : ℝ} (h : 1 ≤ y) : etaD y = 0 := by
  have h0 : ¬ (y ≤ 0) := by linarith
  simp [etaD, h0, h]

lemma etaD_eq_ramp {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : etaD y = rampD y := by
  rcases eq_or_lt_of_le h0 with rfl | h0'
  · simp [etaD, rampD]
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · rw [etaD_eq_zero' le_rfl]; norm_num [rampD]
  · have ha : ¬ (y ≤ 0) := by linarith
    have hb : ¬ (1 ≤ y) := by linarith
    simp [etaD, ha, hb]

lemma etaDD_eq_zero {y : ℝ} (h : y ≤ 0) : etaDD y = 0 := if_pos h

lemma etaDD_eq_zero' {y : ℝ} (h : 1 ≤ y) : etaDD y = 0 := by
  have h0 : ¬ (y ≤ 0) := by linarith
  simp [etaDD, h0, h]

lemma etaDD_eq_ramp {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : etaDD y = rampDD y := by
  rcases eq_or_lt_of_le h0 with rfl | h0'
  · simp [etaDD, rampDD]
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · rw [etaDD_eq_zero' le_rfl]; norm_num [rampDD]
  · have ha : ¬ (y ≤ 0) := by linarith
    have hb : ¬ (1 ≤ y) := by linarith
    simp [etaDD, ha, hb]

/-! ### `eta` is twice differentiable -/

lemma hasDerivAt_eta (x : ℝ) : HasDerivAt eta (etaD x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : eta =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hx) (fun y hy => eta_eq_zero (le_of_lt hy))
    exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he).congr_deriv
      (etaD_eq_zero hx.le).symm
  · have h1 : HasDerivWithinAt eta 0 (Set.Iic 0) 0 :=
      ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt).congr (fun y hy => eta_eq_zero hy)
        (eta_eq_zero le_rfl)
    have hr : rampD 0 = 0 := by norm_num [rampD]
    have h2 : HasDerivWithinAt eta 0 (Set.Icc 0 1) 0 := by
      have h := ((hasDerivAt_rampPoly 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1))
      rw [hr] at h
      exact h.congr (fun y hy => eta_eq_ramp hy.1 hy.2) (eta_eq_ramp le_rfl zero_le_one)
    have hnb : Set.Iic (0 : ℝ) ∪ Set.Icc 0 1 ∈ nhds (0 : ℝ) := by
      refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_
      intro y hy
      rcases le_or_gt y 0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.le, le_of_lt hy⟩
    exact ((h1.union h2).hasDerivAt hnb).congr_deriv (by rw [etaD_eq_zero le_rfl])
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have he : eta =ᶠ[nhds x] rampPoly :=
        Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx hx1) (fun y hy => eta_eq_ramp hy.1.le hy.2.le)
      exact ((hasDerivAt_rampPoly x).congr_of_eventuallyEq he).congr_deriv
        (etaD_eq_ramp hx.le hx1.le).symm
    · have hr : rampD 1 = 0 := by norm_num [rampD]
      have h1 : HasDerivWithinAt eta 0 (Set.Icc 0 1) 1 := by
        have h := ((hasDerivAt_rampPoly 1).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1))
        rw [hr] at h
        exact h.congr (fun y hy => eta_eq_ramp hy.1 hy.2) (eta_eq_ramp zero_le_one le_rfl)
      have h2 : HasDerivWithinAt eta 0 (Set.Ici 1) 1 :=
        ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).hasDerivWithinAt).congr (fun y hy => eta_eq_one hy)
          (eta_eq_one le_rfl)
      have hnb : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 ∈ nhds (1 : ℝ) := by
        refine Filter.mem_of_superset (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_
        intro y hy
        rcases le_or_gt y 1 with h | h
        · exact Or.inl ⟨hy.le, h⟩
        · exact Or.inr h.le
      exact ((h1.union h2).hasDerivAt hnb).congr_deriv (by rw [etaD_eq_zero' le_rfl])
    · have he : eta =ᶠ[nhds x] (fun _ => (1 : ℝ)) :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx1) (fun y hy => eta_eq_one hy.le)
      exact ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq he).congr_deriv
        (by rw [etaD_eq_zero' hx1.le])

lemma hasDerivAt_etaD (x : ℝ) : HasDerivAt etaD (etaDD x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : etaD =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hx) (fun y hy => etaD_eq_zero (le_of_lt hy))
    exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he).congr_deriv
      (etaDD_eq_zero hx.le).symm
  · have h1 : HasDerivWithinAt etaD 0 (Set.Iic 0) 0 :=
      ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt).congr (fun y hy => etaD_eq_zero hy)
        (etaD_eq_zero le_rfl)
    have hr : rampDD 0 = 0 := by norm_num [rampDD]
    have h2 : HasDerivWithinAt etaD 0 (Set.Icc 0 1) 0 := by
      have h := ((hasDerivAt_rampD 0).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1))
      rw [hr] at h
      exact h.congr (fun y hy => etaD_eq_ramp hy.1 hy.2) (etaD_eq_ramp le_rfl zero_le_one)
    have hnb : Set.Iic (0 : ℝ) ∪ Set.Icc 0 1 ∈ nhds (0 : ℝ) := by
      refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_
      intro y hy
      rcases le_or_gt y 0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.le, le_of_lt hy⟩
    exact ((h1.union h2).hasDerivAt hnb).congr_deriv (by rw [etaDD_eq_zero le_rfl])
  · rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · have he : etaD =ᶠ[nhds x] rampD :=
        Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx hx1) (fun y hy => etaD_eq_ramp hy.1.le hy.2.le)
      exact ((hasDerivAt_rampD x).congr_of_eventuallyEq he).congr_deriv
        (etaDD_eq_ramp hx.le hx1.le).symm
    · have hr : rampDD 1 = 0 := by norm_num [rampDD]
      have h1 : HasDerivWithinAt etaD 0 (Set.Icc 0 1) 1 := by
        have h := ((hasDerivAt_rampD 1).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1))
        rw [hr] at h
        exact h.congr (fun y hy => etaD_eq_ramp hy.1 hy.2) (etaD_eq_ramp zero_le_one le_rfl)
      have h2 : HasDerivWithinAt etaD 0 (Set.Ici 1) 1 :=
        ((hasDerivAt_const (1 : ℝ) (0 : ℝ)).hasDerivWithinAt).congr (fun y hy => etaD_eq_zero' hy)
          (etaD_eq_zero' le_rfl)
      have hnb : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 ∈ nhds (1 : ℝ) := by
        refine Filter.mem_of_superset (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_
        intro y hy
        rcases le_or_gt y 1 with h | h
        · exact Or.inl ⟨hy.le, h⟩
        · exact Or.inr h.le
      exact ((h1.union h2).hasDerivAt hnb).congr_deriv (by rw [etaDD_eq_zero' le_rfl])
    · have he : etaD =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx1) (fun y hy => etaD_eq_zero' hy.le)
      exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he).congr_deriv
        (by rw [etaDD_eq_zero' hx1.le])

lemma continuous_etaDD : Continuous etaDD := by
  have h1 : Continuous (fun x : ℝ => if (1 : ℝ) ≤ x then (0 : ℝ) else rampDD x) := by
    refine Continuous.if_le continuous_const (by unfold rampDD; fun_prop) continuous_const
      continuous_id ?_
    intro x hx
    rw [← hx]
    norm_num [rampDD]
  show Continuous (fun x : ℝ => if x ≤ 0 then (0 : ℝ) else if 1 ≤ x then 0 else rampDD x)
  refine Continuous.if_le continuous_const h1 continuous_id continuous_const ?_
  intro x hx
  rw [hx]
  norm_num [rampDD]

lemma differentiable_eta : Differentiable ℝ eta := fun x => (hasDerivAt_eta x).differentiableAt

lemma differentiable_etaD : Differentiable ℝ etaD := fun x => (hasDerivAt_etaD x).differentiableAt

lemma continuous_eta : Continuous eta := differentiable_eta.continuous

lemma continuous_etaD : Continuous etaD := differentiable_etaD.continuous

/-! ### Sign and size of `eta` and its derivatives -/

lemma rampPoly_nonneg {x : ℝ} (h1 : x ≤ 1) : 0 ≤ rampPoly x := by
  have key : rampPoly x = x ^ 4 * (1 + (1 - x) * (20 * (x - 5/4) ^ 2 + 11/4)) := by
    simp only [rampPoly]; ring
  rw [key]
  have h : 0 ≤ (1 - x) * (20 * (x - 5/4) ^ 2 + 11/4) :=
    mul_nonneg (by linarith) (by positivity)
  have hx : (0:ℝ) ≤ x ^ 4 := by positivity
  nlinarith

lemma rampPoly_le_one {x : ℝ} (h0 : 0 ≤ x) : rampPoly x ≤ 1 := by
  have key : 1 - rampPoly x = (1 - x) ^ 4 * (1 + x * (20 * ((1 - x) - 5/4) ^ 2 + 11/4)) := by
    simp only [rampPoly]; ring
  have h : 0 ≤ x * (20 * ((1 - x) - 5/4) ^ 2 + 11/4) := mul_nonneg h0 (by positivity)
  have h2 : (0:ℝ) ≤ (1 - x) ^ 4 := by positivity
  nlinarith

lemma eta_nonneg (x : ℝ) : 0 ≤ eta x := by
  rcases le_or_gt x 0 with h | h
  · rw [eta_eq_zero h]
  rcases le_or_gt 1 x with h1 | h1
  · rw [eta_eq_one h1]; norm_num
  · rw [eta_eq_ramp h.le h1.le]; exact rampPoly_nonneg h1.le

lemma eta_le_one (x : ℝ) : eta x ≤ 1 := by
  rcases le_or_gt x 0 with h | h
  · rw [eta_eq_zero h]; norm_num
  rcases le_or_gt 1 x with h1 | h1
  · rw [eta_eq_one h1]
  · rw [eta_eq_ramp h.le h1.le]; exact rampPoly_le_one h.le

lemma abs_eta (x : ℝ) : |eta x| = eta x := abs_of_nonneg (eta_nonneg x)

lemma etaD_nonneg (x : ℝ) : 0 ≤ etaD x := by
  rcases le_or_gt x 0 with h | h
  · rw [etaD_eq_zero h]
  rcases le_or_gt 1 x with h1 | h1
  · rw [etaD_eq_zero' h1]
  · rw [etaD_eq_ramp h.le h1.le, rampD]
    have h3 : (0:ℝ) ≤ (1 - x) ^ 3 := pow_nonneg (by linarith) 3
    nlinarith [pow_nonneg h.le 3]

lemma abs_etaD (x : ℝ) : |etaD x| = etaD x := abs_of_nonneg (etaD_nonneg x)

lemma etaDD_nonneg_of_le_half {x : ℝ} (h : x ≤ 1/2) : 0 ≤ etaDD x := by
  rcases le_or_gt x 0 with h0 | h0
  · rw [etaDD_eq_zero h0]
  · rw [etaDD_eq_ramp h0.le (by linarith), rampDD]
    have h1 : (0:ℝ) ≤ (1 - x) ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ x ^ 2 := by positivity
    have h3 : (0:ℝ) ≤ 1 - 2 * x := by linarith
    positivity

lemma etaDD_nonpos_of_half_le {x : ℝ} (h : 1/2 ≤ x) : etaDD x ≤ 0 := by
  rcases le_or_gt 1 x with h1 | h1
  · rw [etaDD_eq_zero' h1]
  · rw [etaDD_eq_ramp (by linarith) h1.le, rampDD]
    have h2 : (0:ℝ) ≤ 420 * x ^ 2 * (1 - x) ^ 2 := by positivity
    nlinarith

/-! ### An antiderivative for `(etaD)^2` -/

noncomputable def bigQ (x : ℝ) : ℝ :=
  19600 * (x ^ 7 / 7 - 3 * x ^ 8 / 4 + 5 * x ^ 9 / 3 - 2 * x ^ 10 + 15 * x ^ 11 / 11
    - x ^ 12 / 2 + x ^ 13 / 13)

lemma hasDerivAt_bigQ (x : ℝ) : HasDerivAt bigQ (rampD x ^ 2) x := by
  have h7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * x ^ 6) x := by simpa using hasDerivAt_pow 7 x
  have h8 : HasDerivAt (fun y : ℝ => y ^ 8) (8 * x ^ 7) x := by simpa using hasDerivAt_pow 8 x
  have h9 : HasDerivAt (fun y : ℝ => y ^ 9) (9 * x ^ 8) x := by simpa using hasDerivAt_pow 9 x
  have h10 : HasDerivAt (fun y : ℝ => y ^ 10) (10 * x ^ 9) x := by simpa using hasDerivAt_pow 10 x
  have h11 : HasDerivAt (fun y : ℝ => y ^ 11) (11 * x ^ 10) x := by simpa using hasDerivAt_pow 11 x
  have h12 : HasDerivAt (fun y : ℝ => y ^ 12) (12 * x ^ 11) x := by simpa using hasDerivAt_pow 12 x
  have h13 : HasDerivAt (fun y : ℝ => y ^ 13) (13 * x ^ 12) x := by simpa using hasDerivAt_pow 13 x
  exact ((((((((h7.div_const 7).sub ((h8.const_mul 3).div_const 4)).add
    ((h9.const_mul 5).div_const 3)).sub (h10.const_mul 2)).add
    ((h11.const_mul 15).div_const 11)).sub (h12.div_const 2)).add
    (h13.div_const 13)).const_mul 19600).congr_deriv (by simp only [rampD]; ring)

/-! ### Interval integrals of `eta` and its derivatives -/

lemma integral_abs_eta_le {c : ℝ} (hc : 0 ≤ c) : (∫ x in (0:ℝ)..c, |eta x|) ≤ c := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun x => |eta x|) (g := fun _ : ℝ => (1:ℝ)) hc
    (continuous_eta.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun x _ => by rw [abs_eta]; exact eta_le_one x)
  simpa using h

lemma integral_abs_eta_sq_le {c : ℝ} (hc : 0 ≤ c) : (∫ x in (0:ℝ)..c, |eta x ^ 2|) ≤ c := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun x => |eta x ^ 2|) (g := fun _ : ℝ => (1:ℝ)) hc
    ((continuous_eta.pow 2).abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun x _ => by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ eta x ^ 2)]
      nlinarith [eta_nonneg x, eta_le_one x])
  simpa using h

lemma integral_etaD {c : ℝ} (hc : 1 ≤ c) : (∫ x in (0:ℝ)..c, etaD x) = 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_eta x)
    (continuous_etaD.intervalIntegrable _ _), eta_eq_one hc, eta_eq_zero le_rfl]
  norm_num

lemma integral_two_eta_etaD {c : ℝ} (hc : 1 ≤ c) : (∫ x in (0:ℝ)..c, 2 * eta x * etaD x) = 1 := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) c, HasDerivAt (fun y => eta y ^ 2) (2 * eta x * etaD x) x := by
    intro x _
    simpa using ((hasDerivAt_eta x).fun_pow 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_const.mul continuous_eta).mul continuous_etaD).intervalIntegrable _ _),
    eta_eq_one hc, eta_eq_zero le_rfl]
  norm_num

lemma integral_abs_etaDD {c : ℝ} (hc : 1 ≤ c) : (∫ x in (0:ℝ)..c, |etaDD x|) = 35/8 := by
  have hsplit : (∫ x in (0:ℝ)..(1/2), |etaDD x|) + (∫ x in (1/2:ℝ)..c, |etaDD x|)
      = ∫ x in (0:ℝ)..c, |etaDD x| :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuous_etaDD.abs.intervalIntegrable _ _) (continuous_etaDD.abs.intervalIntegrable _ _)
  have h1 : (∫ x in (0:ℝ)..(1/2), |etaDD x|) = 35/16 := by
    have e : (∫ x in (0:ℝ)..(1/2), |etaDD x|) = ∫ x in (0:ℝ)..(1/2), etaDD x := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hx
      exact abs_of_nonneg (etaDD_nonneg_of_le_half hx.2)
    rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_etaD x)
      (continuous_etaDD.intervalIntegrable _ _), etaD_eq_zero le_rfl,
      etaD_eq_ramp (by norm_num) (by norm_num)]
    norm_num [rampD]
  have h2 : (∫ x in (1/2:ℝ)..c, |etaDD x|) = 35/16 := by
    have e : (∫ x in (1/2:ℝ)..c, |etaDD x|) = ∫ x in (1/2:ℝ)..c, -etaDD x := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (1:ℝ)/2 ≤ c)] at hx
      exact abs_of_nonpos (etaDD_nonpos_of_half_le hx.1)
    rw [e, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_etaD x)
      (continuous_etaDD.intervalIntegrable _ _), etaD_eq_zero' hc,
      etaD_eq_ramp (by norm_num) (by norm_num)]
    norm_num [rampD]
  rw [← hsplit, h1, h2]
  norm_num

lemma integral_etaD_sq {c : ℝ} (hc : 1 ≤ c) : (∫ x in (0:ℝ)..c, etaD x ^ 2) = 700/429 := by
  have hsplit : (∫ x in (0:ℝ)..1, etaD x ^ 2) + (∫ x in (1:ℝ)..c, etaD x ^ 2)
      = ∫ x in (0:ℝ)..c, etaD x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      ((continuous_etaD.pow 2).intervalIntegrable _ _)
      ((continuous_etaD.pow 2).intervalIntegrable _ _)
  have h1 : (∫ x in (0:ℝ)..1, etaD x ^ 2) = 700/429 := by
    have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt bigQ (etaD x ^ 2) x := by
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      rw [etaD_eq_ramp hx.1 hx.2]
      exact hasDerivAt_bigQ x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_etaD.pow 2).intervalIntegrable _ _)]
    norm_num [bigQ]
  have h2 : (∫ x in (1:ℝ)..c, etaD x ^ 2) = 0 := by
    have e : (∫ x in (1:ℝ)..c, etaD x ^ 2) = ∫ _ in (1:ℝ)..c, (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hc] at hx
      show etaD x ^ 2 = (0:ℝ)
      rw [etaD_eq_zero' hx.1]
      norm_num
    rw [e]
    simp
  rw [← hsplit, h1, h2]
  norm_num

lemma integral_eta_abs_etaDD_le {c : ℝ} (hc : 1 ≤ c) :
    (∫ x in (0:ℝ)..c, eta x * |etaDD x|) ≤ 35/8 := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun x => eta x * |etaDD x|)
    (g := fun x => |etaDD x|) (by linarith : (0:ℝ) ≤ c)
    ((continuous_eta.mul continuous_etaDD.abs).intervalIntegrable _ _)
    (continuous_etaDD.abs.intervalIntegrable _ _)
    (fun x _ => by
      nlinarith [eta_nonneg x, eta_le_one x, abs_nonneg (etaDD x)])
  rw [integral_abs_etaDD hc] at h
  exact h

/-! ### The window `psi` and its derivatives -/

noncomputable def psi (L u : ℝ) : ℝ := eta (L / 2 - |u|)
noncomputable def psiD (L u : ℝ) : ℝ := if 0 ≤ u then -etaD (L / 2 - u) else etaD (L / 2 + u)
noncomputable def psiDD (L u : ℝ) : ℝ := etaDD (L / 2 - |u|)
noncomputable def psiSq (L u : ℝ) : ℝ := psi L u ^ 2
noncomputable def psiSqD (L u : ℝ) : ℝ := 2 * psi L u * psiD L u
noncomputable def psiSqDD (L u : ℝ) : ℝ := 2 * psiD L u ^ 2 + 2 * psi L u * psiDD L u

variable {L : ℝ}

lemma psi_of_nonneg {u : ℝ} (h : 0 ≤ u) : psi L u = eta (L / 2 - u) := by
  rw [psi, abs_of_nonneg h]

lemma psi_of_neg {u : ℝ} (h : u < 0) : psi L u = eta (L / 2 + u) := by
  rw [psi, abs_of_neg h, sub_neg_eq_add]

lemma psiDD_of_nonneg {u : ℝ} (h : 0 ≤ u) : psiDD L u = etaDD (L / 2 - u) := by
  rw [psiDD, abs_of_nonneg h]

lemma psiDD_of_neg {u : ℝ} (h : u < 0) : psiDD L u = etaDD (L / 2 + u) := by
  rw [psiDD, abs_of_neg h, sub_neg_eq_add]

lemma psi_flat (hL : 8 ≤ L) {u : ℝ} (hu : |u| < 1) : psi L u = 1 := by
  rw [psi, eta_eq_one (by linarith)]

lemma psiD_flat (hL : 8 ≤ L) {u : ℝ} (hu : |u| < 1) : psiD L u = 0 := by
  rcases le_or_gt 0 u with h | h
  · rw [psiD, if_pos h, etaD_eq_zero' (by rw [abs_of_nonneg h] at hu; linarith)]
    norm_num
  · rw [psiD, if_neg (not_le.mpr h), etaD_eq_zero' (by rw [abs_of_neg h] at hu; linarith)]

lemma hasDerivAt_psi (hL : 8 ≤ L) (u : ℝ) : HasDerivAt (psi L) (psiD L u) u := by
  rcases lt_trichotomy u 0 with h | rfl | h
  · have hc : HasDerivAt (fun v : ℝ => L / 2 + v) 1 u := by
      simpa using (hasDerivAt_id u).const_add (L / 2)
    have h2 : HasDerivAt (fun v : ℝ => eta (L / 2 + v)) (etaD (L / 2 + u) * 1) u :=
      (hasDerivAt_eta (L / 2 + u)).comp u hc
    have he : psi L =ᶠ[nhds u] (fun v : ℝ => eta (L / 2 + v)) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds h) (fun v hv => psi_of_neg hv)
    exact (h2.congr_of_eventuallyEq he).congr_deriv
      (by rw [psiD, if_neg (not_le.mpr h)]; ring)
  · have he : psi L =ᶠ[nhds (0:ℝ)] (fun _ : ℝ => (1:ℝ)) := by
      refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
        (by norm_num : (0:ℝ) < 1)) (fun v hv => psi_flat hL ?_)
      rw [abs_lt]
      exact ⟨hv.1, hv.2⟩
    exact ((hasDerivAt_const (0:ℝ) (1:ℝ)).congr_of_eventuallyEq he).congr_deriv
      (psiD_flat hL (by norm_num)).symm
  · have hc : HasDerivAt (fun v : ℝ => L / 2 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (L / 2)
    have h2 : HasDerivAt (fun v : ℝ => eta (L / 2 - v)) (etaD (L / 2 - u) * (-1)) u :=
      (hasDerivAt_eta (L / 2 - u)).comp u hc
    have he : psi L =ᶠ[nhds u] (fun v : ℝ => eta (L / 2 - v)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds h) (fun v hv => psi_of_nonneg (le_of_lt hv))
    exact (h2.congr_of_eventuallyEq he).congr_deriv (by rw [psiD, if_pos h.le]; ring)

lemma hasDerivAt_psiD (hL : 8 ≤ L) (u : ℝ) : HasDerivAt (psiD L) (psiDD L u) u := by
  rcases lt_trichotomy u 0 with h | rfl | h
  · have hc : HasDerivAt (fun v : ℝ => L / 2 + v) 1 u := by
      simpa using (hasDerivAt_id u).const_add (L / 2)
    have h2 : HasDerivAt (fun v : ℝ => etaD (L / 2 + v)) (etaDD (L / 2 + u) * 1) u :=
      (hasDerivAt_etaD (L / 2 + u)).comp u hc
    have he : psiD L =ᶠ[nhds u] (fun v : ℝ => etaD (L / 2 + v)) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds h)
        (fun v hv => by rw [psiD, if_neg (not_le.mpr hv)])
    exact (h2.congr_of_eventuallyEq he).congr_deriv (by rw [psiDD_of_neg h]; ring)
  · have he : psiD L =ᶠ[nhds (0:ℝ)] (fun _ : ℝ => (0:ℝ)) := by
      refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
        (by norm_num : (0:ℝ) < 1)) (fun v hv => psiD_flat hL ?_)
      rw [abs_lt]
      exact ⟨hv.1, hv.2⟩
    refine ((hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq he).congr_deriv ?_
    rw [psiDD_of_nonneg le_rfl, sub_zero, etaDD_eq_zero' (by linarith)]
  · have hc : HasDerivAt (fun v : ℝ => L / 2 - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (L / 2)
    have h2 : HasDerivAt (fun v : ℝ => -etaD (L / 2 - v)) (-(etaDD (L / 2 - u) * (-1))) u :=
      ((hasDerivAt_etaD (L / 2 - u)).comp u hc).neg
    have he : psiD L =ᶠ[nhds u] (fun v : ℝ => -etaD (L / 2 - v)) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds h)
        (fun v hv => by rw [psiD, if_pos (le_of_lt hv)])
    exact (h2.congr_of_eventuallyEq he).congr_deriv (by rw [psiDD_of_nonneg h.le]; ring)

lemma hasDerivAt_psiSq (hL : 8 ≤ L) (u : ℝ) : HasDerivAt (psiSq L) (psiSqD L u) u := by
  have h := (hasDerivAt_psi hL u).pow 2
  exact h.congr_deriv (by rw [psiSqD]; push_cast; ring)

lemma hasDerivAt_psiSqD (hL : 8 ≤ L) (u : ℝ) : HasDerivAt (psiSqD L) (psiSqDD L u) u := by
  have h := ((hasDerivAt_psi hL u).const_mul 2).mul (hasDerivAt_psiD hL u)
  exact h.congr_deriv (by rw [psiSqDD]; ring)

lemma continuous_psi (hL : 8 ≤ L) : Continuous (psi L) :=
  Differentiable.continuous (fun u => (hasDerivAt_psi hL u).differentiableAt)

lemma continuous_psiD (hL : 8 ≤ L) : Continuous (psiD L) :=
  Differentiable.continuous (fun u => (hasDerivAt_psiD hL u).differentiableAt)

lemma continuous_psiDD : Continuous (psiDD L) :=
  continuous_etaDD.comp (continuous_const.sub continuous_abs)

lemma continuous_psiSq (hL : 8 ≤ L) : Continuous (psiSq L) :=
  Differentiable.continuous (fun u => (hasDerivAt_psiSq hL u).differentiableAt)

lemma continuous_psiSqD (hL : 8 ≤ L) : Continuous (psiSqD L) :=
  Differentiable.continuous (fun u => (hasDerivAt_psiSqD hL u).differentiableAt)

lemma continuous_psiSqDD (hL : 8 ≤ L) : Continuous (psiSqDD L) :=
  (continuous_const.mul ((continuous_psiD hL).pow 2)).add
    ((continuous_const.mul (continuous_psi hL)).mul continuous_psiDD)

lemma abs_psi (u : ℝ) : |psi L u| = eta (L / 2 - |u|) := abs_eta _

lemma abs_psiD (u : ℝ) : |psiD L u| = etaD (L / 2 - |u|) := by
  rcases le_or_gt 0 u with h | h
  · rw [psiD, if_pos h, abs_neg, abs_etaD, abs_of_nonneg h]
  · rw [psiD, if_neg (not_le.mpr h), abs_etaD, abs_of_neg h, sub_neg_eq_add]

lemma abs_psiDD (u : ℝ) : |psiDD L u| = |etaDD (L / 2 - |u|)| := rfl

lemma psi_supp {u : ℝ} (h : L / 2 < |u|) : psi L u = 0 := eta_eq_zero (by linarith)

lemma psiD_supp {u : ℝ} (h : L / 2 < |u|) : psiD L u = 0 := by
  have := abs_psiD (L := L) u
  rw [etaD_eq_zero (by linarith)] at this
  exact abs_eq_zero.mp this

lemma psiDD_supp {u : ℝ} (h : L / 2 < |u|) : psiDD L u = 0 := etaDD_eq_zero (by linarith)

/-! ### Reduction of integrals over `ℝ` to interval integrals -/

open MeasureTheory in
lemma integral_Ioi_eq_intervalIntegral {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ x : ℝ, c ≤ x → g x = 0) : (∫ x in Set.Ioi (0:ℝ), g x) = ∫ x in (0:ℝ)..c, g x := by
  rw [intervalIntegral.integral_of_le hc, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioc]
  congr 1
  funext x
  by_cases h1 : x ∈ Set.Ioi (0:ℝ)
  · by_cases h2 : x ∈ Set.Ioc (0:ℝ) c
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      simp only [Set.mem_Ioi] at h1
      simp only [Set.mem_Ioc, not_and, not_le] at h2
      exact h0 x (le_of_lt (h2 h1))
  · rw [Set.indicator_of_notMem h1,
      Set.indicator_of_notMem (fun hh => h1 (Set.Ioc_subset_Ioi_self hh))]

open MeasureTheory in
/-- The key reduction: an even, compactly supported integrand built from `g (c - |u|)`. -/
lemma integral_shift_abs {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ x : ℝ, x ≤ 0 → g x = 0) :
    (∫ u : ℝ, g (c - |u|)) = 2 * ∫ x in (0:ℝ)..c, g x := by
  have h0 : ∀ x : ℝ, c ≤ x → (fun t => g (c - t)) x = 0 := fun x hx => hg _ (by simp; linarith)
  have hstep : (∫ u : ℝ, g (c - |u|)) = 2 * ∫ x in Set.Ioi (0:ℝ), g (c - x) :=
    integral_comp_abs (f := fun t => g (c - t))
  rw [hstep, integral_Ioi_eq_intervalIntegral hc h0]
  congr 1
  simp

open MeasureTheory in
lemma integrable_shift_abs {g : ℝ → ℝ} {c : ℝ} (hg : Continuous g)
    (h0 : ∀ x : ℝ, x ≤ 0 → g x = 0) : Integrable (fun u : ℝ => g (c - |u|)) := by
  refine (hg.comp (continuous_const.sub continuous_abs)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) ?_)
  intro x hx
  have hx' : c < |x| := by
    by_contra hcon
    push_neg at hcon
    exact hx (Set.mem_Icc.2 ⟨(abs_le.mp hcon).1, (abs_le.mp hcon).2⟩)
  exact h0 _ (by simp only [Pi.sub_apply]; linarith)

/-! ### The `L¹` norms of the window and its derivatives -/

lemma eta_zero_of_nonpos : ∀ x : ℝ, x ≤ 0 → |eta x| = 0 := fun x hx => by
  rw [eta_eq_zero hx, abs_zero]

lemma integral_abs_psi_le (hL : 8 ≤ L) : (∫ u : ℝ, |psi L u|) ≤ L := by
  have h : (∫ u : ℝ, |psi L u|) = 2 * ∫ x in (0:ℝ)..(L/2), |eta x| :=
    integral_shift_abs (g := fun x => |eta x|) (by linarith) eta_zero_of_nonpos
  rw [h]
  have := integral_abs_eta_le (c := L/2) (by linarith)
  linarith

lemma integral_abs_psiD_le (hL : 8 ≤ L) : (∫ u : ℝ, |psiD L u|) ≤ 2 := by
  have hfun : (fun u : ℝ => |psiD L u|) = fun u : ℝ => etaD (L / 2 - |u|) :=
    funext (fun u => abs_psiD u)
  rw [hfun, integral_shift_abs (g := etaD) (by linarith)
    (fun x hx => etaD_eq_zero hx), integral_etaD (by linarith)]
  norm_num

lemma integral_abs_psiDD_le (hL : 8 ≤ L) : (∫ u : ℝ, |psiDD L u|) ≤ 35/4 := by
  have h : (∫ u : ℝ, |psiDD L u|) = 2 * ∫ x in (0:ℝ)..(L/2), |etaDD x| :=
    integral_shift_abs (g := fun x => |etaDD x|) (by linarith)
    (fun x hx => by rw [etaDD_eq_zero hx, abs_zero])
  rw [h, integral_abs_etaDD (by linarith)]
  norm_num

lemma integral_abs_psiSq_le (hL : 8 ≤ L) : (∫ u : ℝ, |psiSq L u|) ≤ L := by
  have h : (∫ u : ℝ, |psiSq L u|) = 2 * ∫ x in (0:ℝ)..(L/2), |eta x ^ 2| :=
    integral_shift_abs (g := fun x => |eta x ^ 2|) (by linarith)
    (fun x hx => by rw [eta_eq_zero hx]; norm_num)
  rw [h]
  have := integral_abs_eta_sq_le (c := L/2) (by linarith)
  linarith

lemma integral_abs_psiSqD_le (hL : 8 ≤ L) : (∫ u : ℝ, |psiSqD L u|) ≤ 2 := by
  have hfun : (fun u : ℝ => |psiSqD L u|)
      = fun u : ℝ => 2 * eta (L / 2 - |u|) * etaD (L / 2 - |u|) := by
    funext u
    rw [psiSqD, abs_mul, abs_mul, abs_two, abs_psi, abs_psiD]
  rw [hfun, integral_shift_abs (g := fun x => 2 * eta x * etaD x) (by linarith)
    (fun x hx => by rw [eta_eq_zero hx]; ring), integral_two_eta_etaD (by linarith)]
  norm_num

open MeasureTheory in
lemma integral_abs_psiSqDD_le (hL : 8 ≤ L) : (∫ u : ℝ, |psiSqDD L u|) ≤ 20615/858 := by
  set g : ℝ → ℝ := fun x => 2 * etaD x ^ 2 + 2 * eta x * |etaDD x| with hgdef
  have hgc : Continuous g := by
    refine (continuous_const.mul (continuous_etaD.pow 2)).add ?_
    exact (continuous_const.mul continuous_eta).mul continuous_etaDD.abs
  have hg0 : ∀ x : ℝ, x ≤ 0 → g x = 0 := by
    intro x hx
    rw [hgdef]
    simp only
    rw [eta_eq_zero hx, etaD_eq_zero hx]
    ring
  have hmaj : ∀ u : ℝ, |psiSqDD L u| ≤ g (L / 2 - |u|) := by
    intro u
    have h1 : |2 * psiD L u ^ 2| = 2 * etaD (L / 2 - |u|) ^ 2 := by
      rw [abs_mul, abs_two, abs_pow, abs_psiD]
    have h2 : |2 * psi L u * psiDD L u| = 2 * eta (L / 2 - |u|) * |etaDD (L / 2 - |u|)| := by
      rw [abs_mul, abs_mul, abs_two, abs_psi, abs_psiDD]
    calc |psiSqDD L u| ≤ |2 * psiD L u ^ 2| + |2 * psi L u * psiDD L u| := by
          rw [psiSqDD]; exact abs_add_le _ _
      _ = g (L / 2 - |u|) := by rw [h1, h2]
  have hint : Integrable (fun u : ℝ => g (L / 2 - |u|)) := integrable_shift_abs hgc hg0
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun u => abs_nonneg (psiSqDD L u))) hint
    (Filter.Eventually.of_forall hmaj)
  refine hmono.trans ?_
  rw [integral_shift_abs (g := g) (by linarith) hg0]
  have hsplit : (∫ x in (0:ℝ)..(L/2), g x)
      = (∫ x in (0:ℝ)..(L/2), 2 * etaD x ^ 2) + ∫ x in (0:ℝ)..(L/2), 2 * eta x * |etaDD x| := by
    refine intervalIntegral.integral_add ?_ ?_
    · exact (continuous_const.mul (continuous_etaD.pow 2)).intervalIntegrable _ _
    · exact ((continuous_const.mul continuous_eta).mul continuous_etaDD.abs).intervalIntegrable _ _
  have e1 : (∫ x in (0:ℝ)..(L/2), 2 * etaD x ^ 2) = 2 * (700/429) := by
    rw [intervalIntegral.integral_const_mul, integral_etaD_sq (by linarith)]
  have e2 : (∫ x in (0:ℝ)..(L/2), 2 * eta x * |etaDD x|)
      = 2 * ∫ x in (0:ℝ)..(L/2), eta x * |etaDD x| := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    ring
  have e3 := integral_eta_abs_etaDD_le (c := L/2) (by linarith)
  rw [hsplit, e1, e2]
  linarith

/-! ### The general bound for a tapered window -/

open MeasureTheory in
/-- Generic `L¹` bound for the second derivative of `u ↦ P (u / L) * W u`, where `W` is a
twice differentiable window supported in `[-L/2, L/2]`. -/
lemma taper_general (P : ℝ → ℝ) (L B0 B1 B2 : ℝ) (hL : 0 < L)
    (hP : ContDiffOn ℝ 2 P (Set.Ioo (-(1/2) : ℝ) (1/2)))
    (W W1 W2 : ℝ → ℝ)
    (hW : ∀ u, HasDerivAt W (W1 u) u) (hW1 : ∀ u, HasDerivAt W1 (W2 u) u)
    (hW2c : Continuous W2)
    (hsupp : ∀ u : ℝ, L / 2 < |u| → W u = 0 ∧ W1 u = 0 ∧ W2 u = 0)
    (hB0 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |P y| ≤ B0)
    (hB1 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv P y| ≤ B1)
    (hB2 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv (deriv P) y| ≤ B2) :
    (∫ u : ℝ, |iteratedDeriv 2 (fun u : ℝ => P (u / L) * W u) u|)
      ≤ (B2 / L ^ 2) * (∫ u : ℝ, |W u|) + (2 * B1 / L) * (∫ u : ℝ, |W1 u|)
        + B0 * (∫ u : ℝ, |W2 u|) := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hWc : Continuous W := Differentiable.continuous (fun u => (hW u).differentiableAt)
  have hW1c : Continuous W1 := Differentiable.continuous (fun u => (hW1 u).differentiableAt)
  set φ : ℝ → ℝ := fun u => P (u / L) * W u with hφdef
  have hPd : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), HasDerivAt P (deriv P y) y := by
    intro y hy
    exact ((hP.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  have hPd2 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), HasDerivAt (deriv P) (deriv (deriv P) y) y := by
    have h1 : ContDiffOn ℝ 1 (deriv P) (Set.Ioo (-(1/2) : ℝ) (1/2)) :=
      hP.deriv_of_isOpen isOpen_Ioo (by norm_num)
    intro y hy
    exact ((h1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  have hmem : ∀ u : ℝ, |u| < L / 2 → u / L ∈ Set.Ioo (-(1/2) : ℝ) (1/2) := by
    intro u hu
    rw [abs_lt] at hu
    constructor
    · rw [lt_div_iff₀ hL]; linarith [hu.1]
    · rw [div_lt_iff₀ hL]; linarith [hu.2]
  have hQ1 : ∀ u : ℝ, |u| < L / 2 →
      HasDerivAt (fun v : ℝ => P (v / L)) (deriv P (u / L) / L) u := by
    intro u hu
    have hd : HasDerivAt (fun v : ℝ => v / L) (1 / L) u := by
      simpa using (hasDerivAt_id u).div_const L
    exact ((hPd _ (hmem u hu)).comp u hd).congr_deriv (by field_simp)
  have hQ2 : ∀ u : ℝ, |u| < L / 2 →
      HasDerivAt (fun v : ℝ => deriv P (v / L) / L) (deriv (deriv P) (u / L) / L ^ 2) u := by
    intro u hu
    have hd : HasDerivAt (fun v : ℝ => v / L) (1 / L) u := by
      simpa using (hasDerivAt_id u).div_const L
    refine (((hPd2 _ (hmem u hu)).comp u hd).div_const L).congr_deriv ?_
    rw [mul_one_div, div_div, ← pow_two]
  have hEq : ∀ u : ℝ, |u| < L / 2 →
      deriv φ =ᶠ[nhds u] (fun v : ℝ => deriv P (v / L) / L * W v + P (v / L) * W1 v) := by
    intro u hu
    refine Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_abs continuous_const).mem_nhds (show |u| < L / 2 from hu)) ?_
    intro v hv
    exact ((hQ1 v hv).mul (hW v)).deriv
  have hiter : iteratedDeriv 2 φ = deriv (deriv φ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hsecond : ∀ u : ℝ, |u| < L / 2 → iteratedDeriv 2 φ u =
      deriv (deriv P) (u / L) / L ^ 2 * W u + 2 * (deriv P (u / L) / L) * W1 u
        + P (u / L) * W2 u := by
    intro u hu
    have h2 : HasDerivAt (fun v : ℝ => deriv P (v / L) / L * W v + P (v / L) * W1 v)
        (deriv (deriv P) (u / L) / L ^ 2 * W u + deriv P (u / L) / L * W1 u +
          (deriv P (u / L) / L * W1 u + P (u / L) * W2 u)) u :=
      ((hQ2 u hu).mul (hW u)).add ((hQ1 u hu).mul (hW1 u))
    have h3 := (h2.congr_of_eventuallyEq (hEq u hu)).deriv
    rw [hiter, h3]; ring
  have hzero : ∀ u : ℝ, L / 2 < |u| → iteratedDeriv 2 φ u = 0 := by
    intro u hu
    have hnb : {v : ℝ | L / 2 < |v|} ∈ nhds u :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hu
    have h0 : φ =ᶠ[nhds u] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem hnb (fun v hv => by simp [hφdef, (hsupp v hv).1])
    have h1 : deriv φ =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by simpa using h0.deriv
    rw [hiter, h1.deriv_eq]
    simp
  -- the pointwise (a.e.) bound
  have hae : ∀ᵐ u : ℝ, |iteratedDeriv 2 φ u|
      ≤ (B2 / L ^ 2) * |W u| + (2 * B1 / L) * |W1 u| + B0 * |W2 u| := by
    have hnull : volume ({-(L / 2), L / 2} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
    rw [ae_iff]
    refine measure_mono_null (fun u hu => ?_) hnull
    simp only [Set.mem_setOf_eq, not_le] at hu
    by_contra hnot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnot
    push_neg at hnot
    have habs : |u| ≠ L / 2 := by
      intro h
      rcases (abs_eq (le_of_lt (show (0 : ℝ) < L / 2 by linarith))).mp h with h1 | h1
      · exact hnot.2 h1
      · exact hnot.1 h1
    rcases lt_or_gt_of_ne habs with h | h
    · have hy := hmem u h
      have b1 : |deriv (deriv P) (u / L)| ≤ B2 := hB2 _ hy
      have b2 : |deriv P (u / L)| ≤ B1 := hB1 _ hy
      have b3 : |P (u / L)| ≤ B0 := hB0 _ hy
      have e1 : |deriv (deriv P) (u / L) / L ^ 2 * W u|
          = |deriv (deriv P) (u / L)| / L ^ 2 * |W u| := by
        rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < L ^ 2 by positivity)]
      have e2 : |2 * (deriv P (u / L) / L) * W1 u| = 2 * |deriv P (u / L)| / L * |W1 u| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hL, abs_two]; ring
      have e3 : |P (u / L) * W2 u| = |P (u / L)| * |W2 u| := abs_mul _ _
      have htri := abs_add_three (deriv (deriv P) (u / L) / L ^ 2 * W u)
        (2 * (deriv P (u / L) / L) * W1 u) (P (u / L) * W2 u)
      rw [e1, e2, e3] at htri
      have c1 : |deriv (deriv P) (u / L)| / L ^ 2 * |W u| ≤ B2 / L ^ 2 * |W u| := by
        gcongr
      have c2 : 2 * |deriv P (u / L)| / L * |W1 u| ≤ 2 * B1 / L * |W1 u| := by
        gcongr
      have c3 : |P (u / L)| * |W2 u| ≤ B0 * |W2 u| := by gcongr
      rw [hsecond u h] at hu
      linarith
    · rw [hzero u h] at hu
      have hb0 : 0 ≤ B0 := le_trans (abs_nonneg _) (hB0 0 (by norm_num))
      have hb1 : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 0 (by norm_num))
      have hb2 : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 0 (by norm_num))
      have p1 : 0 ≤ B2 / L ^ 2 * |W u| := by positivity
      have p2 : 0 ≤ 2 * B1 / L * |W1 u| := by positivity
      have p3 : 0 ≤ B0 * |W2 u| := by positivity
      simp only [abs_zero] at hu
      linarith
  -- integrability and conclusion
  have hint : ∀ f : ℝ → ℝ, Continuous f → (∀ u : ℝ, L / 2 < |u| → f u = 0) →
      Integrable (fun u => |f u|) := by
    intro f hf h0
    refine (hf.abs).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -(L / 2)) (b := L / 2)) ?_)
    intro x hx
    have hx' : L / 2 < |x| := by
      by_contra hcon
      push_neg at hcon
      exact hx (Set.mem_Icc.2 ⟨(abs_le.mp hcon).1, (abs_le.mp hcon).2⟩)
    simp [h0 x hx']
  have i0 := hint W hWc (fun u hu => (hsupp u hu).1)
  have i1 := hint W1 hW1c (fun u hu => (hsupp u hu).2.1)
  have i2 := hint W2 hW2c (fun u hu => (hsupp u hu).2.2)
  have hG : Integrable (fun u : ℝ => (B2 / L ^ 2) * |W u| + (2 * B1 / L) * |W1 u| + B0 * |W2 u|) :=
    ((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun u => abs_nonneg (iteratedDeriv 2 φ u))) hG hae
  refine hmono.trans_eq ?_
  have f2 := integral_add (μ := volume) (i0.const_mul (B2 / L ^ 2)) (i1.const_mul (2 * B1 / L))
  have f1 := integral_add (μ := volume)
    ((i0.const_mul (B2 / L ^ 2)).add (i1.const_mul (2 * B1 / L))) (i2.const_mul B0)
  simp only [Pi.add_apply] at f1
  rw [f1, f2, integral_const_mul, integral_const_mul, integral_const_mul]

end TaperAux

open TaperAux

-- Note: the hypothesis `hφ` (global `C²` regularity of the composite) is kept because it is part
-- of the requested statement, but the proof below does not need it: the product rule is applied
-- only on the open interval `(-L/2, L/2)`, the function vanishes identically outside
-- `[-L/2, L/2]`, and the two remaining points form a null set.
theorem taper_second_deriv_L1_bound_open
    (P : ℝ → ℝ) (L B0 B1 B2 : ℝ) (hL : 8 ≤ L)
    (hP : ContDiffOn ℝ 2 P (Set.Ioo (-(1/2) : ℝ) (1/2)))
    (hφ : ContDiff ℝ 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|)))
    (hB0 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |P y| ≤ B0)
    (hB1 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv P y| ≤ B1)
    (hB2 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv (deriv P) y| ≤ B2) :
    (∫ u : ℝ, |iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|)) u|)
      ≤ B2 / L + 4 * B1 / L + (35 / 4) * B0 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hb0 : 0 ≤ B0 := le_trans (abs_nonneg _) (hB0 0 (by norm_num))
  have hb1 : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 0 (by norm_num))
  have hb2 : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 0 (by norm_num))
  have key := taper_general P L B0 B1 B2 hL0 hP (psi L) (psiD L) (psiDD L)
    (hasDerivAt_psi hL) (hasDerivAt_psiD hL) continuous_psiDD
    (fun u hu => ⟨psi_supp hu, psiD_supp hu, psiDD_supp hu⟩) hB0 hB1 hB2
  refine le_trans key ?_
  have i0 := integral_abs_psi_le hL
  have i1 := integral_abs_psiD_le hL
  have i2 := integral_abs_psiDD_le hL
  have m0 : (B2 / L ^ 2) * (∫ u : ℝ, |psi L u|) ≤ (B2 / L ^ 2) * L :=
    mul_le_mul_of_nonneg_left i0 (by positivity)
  have m1 : (2 * B1 / L) * (∫ u : ℝ, |psiD L u|) ≤ (2 * B1 / L) * 2 :=
    mul_le_mul_of_nonneg_left i1 (by positivity)
  have m2 : B0 * (∫ u : ℝ, |psiDD L u|) ≤ B0 * (35 / 4) :=
    mul_le_mul_of_nonneg_left i2 hb0
  have e0 : (B2 / L ^ 2) * L = B2 / L := by field_simp
  have e1 : (2 * B1 / L) * 2 = 4 * B1 / L := by ring
  linarith

-- As above, the hypothesis `hφ` is part of the requested statement but is not needed here.
theorem taper_sq_second_deriv_L1_bound_open
    (P : ℝ → ℝ) (L B0 B1 B2 : ℝ) (hL : 8 ≤ L)
    (hP : ContDiffOn ℝ 2 P (Set.Ioo (-(1/2) : ℝ) (1/2)))
    (hφ : ContDiff ℝ 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|) ^ 2))
    (hB0 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |P y| ≤ B0)
    (hB1 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv P y| ≤ B1)
    (hB2 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv (deriv P) y| ≤ B2) :
    (∫ u : ℝ, |iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|) ^ 2) u|)
      ≤ B2 / L + 4 * B1 / L + (20615 / 858) * B0 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hb0 : 0 ≤ B0 := le_trans (abs_nonneg _) (hB0 0 (by norm_num))
  have hb1 : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 0 (by norm_num))
  have hb2 : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 0 (by norm_num))
  have key := taper_general P L B0 B1 B2 hL0 hP (psiSq L) (psiSqD L) (psiSqDD L)
    (hasDerivAt_psiSq hL) (hasDerivAt_psiSqD hL) (continuous_psiSqDD hL)
    (fun u hu => ⟨by rw [psiSq, psi_supp hu]; ring,
      by rw [psiSqD, psi_supp hu]; ring,
      by rw [psiSqDD, psi_supp hu, psiD_supp hu]; ring⟩) hB0 hB1 hB2
  refine le_trans key ?_
  have i0 := integral_abs_psiSq_le hL
  have i1 := integral_abs_psiSqD_le hL
  have i2 := integral_abs_psiSqDD_le hL
  have m0 : (B2 / L ^ 2) * (∫ u : ℝ, |psiSq L u|) ≤ (B2 / L ^ 2) * L :=
    mul_le_mul_of_nonneg_left i0 (by positivity)
  have m1 : (2 * B1 / L) * (∫ u : ℝ, |psiSqD L u|) ≤ (2 * B1 / L) * 2 :=
    mul_le_mul_of_nonneg_left i1 (by positivity)
  have m2 : B0 * (∫ u : ℝ, |psiSqDD L u|) ≤ B0 * (20615 / 858) :=
    mul_le_mul_of_nonneg_left i2 hb0
  have e0 : (B2 / L ^ 2) * L = B2 / L := by field_simp
  have e1 : (2 * B1 / L) * 2 = 4 * B1 / L := by ring
  linarith


end AristotleTU2