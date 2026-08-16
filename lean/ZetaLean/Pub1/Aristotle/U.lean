import Mathlib

namespace AristotleU

noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

namespace TaperAux

open Set MeasureTheory

/-- The derivative of `rampPoly`. -/
noncomputable def rampPolyD (x : ℝ) : ℝ :=
  140 * x ^ 3 - 420 * x ^ 4 + 420 * x ^ 5 - 140 * x ^ 6

/-- The second derivative of `rampPoly`. -/
noncomputable def rampPolyDD (x : ℝ) : ℝ :=
  420 * x ^ 2 - 1680 * x ^ 3 + 2100 * x ^ 4 - 840 * x ^ 5

/-- Clamping to `[0,1]`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The derivative of `eta`. -/
noncomputable def etaD (x : ℝ) : ℝ := rampPolyD (clamp01 x)

/-- The second derivative of `eta`. -/
noncomputable def etaDD (x : ℝ) : ℝ := rampPolyDD (clamp01 x)

lemma continuous_rampPoly : Continuous rampPoly := by
  unfold rampPoly; fun_prop

lemma continuous_rampPolyD : Continuous rampPolyD := by
  unfold rampPolyD; fun_prop

lemma continuous_rampPolyDD : Continuous rampPolyDD := by
  unfold rampPolyDD; fun_prop

lemma continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

lemma rampPoly_zero : rampPoly 0 = 0 := by unfold rampPoly; norm_num
lemma rampPoly_one : rampPoly 1 = 1 := by unfold rampPoly; norm_num
lemma rampPolyD_zero : rampPolyD 0 = 0 := by unfold rampPolyD; norm_num
lemma rampPolyD_one : rampPolyD 1 = 0 := by unfold rampPolyD; norm_num
lemma rampPolyDD_zero : rampPolyDD 0 = 0 := by unfold rampPolyDD; norm_num
lemma rampPolyDD_one : rampPolyDD 1 = 0 := by unfold rampPolyDD; norm_num

lemma hasDerivAt_rampPoly (x : ℝ) : HasDerivAt rampPoly (rampPolyD x) x := by
  unfold rampPoly rampPolyD
  have h : HasDerivAt (fun x : ℝ => 35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7)
      (35 * (4 * x ^ 3) - 84 * (5 * x ^ 4) + 70 * (6 * x ^ 5) - 20 * (7 * x ^ 6)) x := by
    exact (((((hasDerivAt_pow 4 x).const_mul 35).sub ((hasDerivAt_pow 5 x).const_mul 84)).add
      ((hasDerivAt_pow 6 x).const_mul 70)).sub ((hasDerivAt_pow 7 x).const_mul 20)).congr_deriv
      (by push_cast; ring)
  exact h.congr_deriv (by ring)

lemma hasDerivAt_rampPolyD (x : ℝ) : HasDerivAt rampPolyD (rampPolyDD x) x := by
  unfold rampPolyD rampPolyDD
  have h : HasDerivAt (fun x : ℝ => 140 * x ^ 3 - 420 * x ^ 4 + 420 * x ^ 5 - 140 * x ^ 6)
      (140 * (3 * x ^ 2) - 420 * (4 * x ^ 3) + 420 * (5 * x ^ 4) - 140 * (6 * x ^ 5)) x := by
    exact (((((hasDerivAt_pow 3 x).const_mul 140).sub ((hasDerivAt_pow 4 x).const_mul 420)).add
      ((hasDerivAt_pow 5 x).const_mul 420)).sub ((hasDerivAt_pow 6 x).const_mul 140)).congr_deriv
      (by push_cast; ring)
  exact h.congr_deriv (by ring)

/-! ### Basic values of `eta` -/

lemma eta_of_nonpos {x : ℝ} (h : x ≤ 0) : eta x = 0 := by
  unfold eta; rw [if_pos h]

lemma eta_of_one_le {x : ℝ} (h : 1 ≤ x) : eta x = 1 := by
  unfold eta
  rw [if_neg (by linarith), if_pos h]

lemma eta_eq_ramp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : eta x = rampPoly x := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, eta_of_nonpos le_rfl, rampPoly_zero]
  · rcases eq_or_lt_of_le h1 with h' | h'
    · rw [h', eta_of_one_le le_rfl, rampPoly_one]
    · unfold eta; rw [if_neg (by linarith), if_neg (by linarith)]

lemma clamp01_of_nonpos {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  unfold clamp01
  have : min 1 x = x := min_eq_right (by linarith)
  rw [this]; exact max_eq_left h

lemma clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01
  rw [min_eq_left h]; exact max_eq_right zero_le_one

lemma clamp01_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right h1]; exact max_eq_right h0

lemma eta_eq_ramp_clamp (x : ℝ) : eta x = rampPoly (clamp01 x) := by
  by_cases h : x ≤ 0
  · rw [eta_of_nonpos h, clamp01_of_nonpos h, rampPoly_zero]
  · push_neg at h
    by_cases h' : 1 ≤ x
    · rw [eta_of_one_le h', clamp01_of_one_le h', rampPoly_one]
    · push_neg at h'
      rw [eta_eq_ramp h.le h'.le, clamp01_of_mem h.le h'.le]

lemma continuous_eta : Continuous eta := by
  have : eta = fun x => rampPoly (clamp01 x) := funext eta_eq_ramp_clamp
  rw [this]
  exact continuous_rampPoly.comp continuous_clamp01

lemma continuous_etaD : Continuous etaD :=
  continuous_rampPolyD.comp continuous_clamp01

lemma continuous_etaDD : Continuous etaDD :=
  continuous_rampPolyDD.comp continuous_clamp01

lemma etaD_of_nonpos {x : ℝ} (h : x ≤ 0) : etaD x = 0 := by
  unfold etaD; rw [clamp01_of_nonpos h, rampPolyD_zero]

lemma etaD_of_one_le {x : ℝ} (h : 1 ≤ x) : etaD x = 0 := by
  unfold etaD; rw [clamp01_of_one_le h, rampPolyD_one]

lemma etaD_eq_rampD {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : etaD x = rampPolyD x := by
  unfold etaD; rw [clamp01_of_mem h0 h1]

lemma etaDD_of_nonpos {x : ℝ} (h : x ≤ 0) : etaDD x = 0 := by
  unfold etaDD; rw [clamp01_of_nonpos h, rampPolyDD_zero]

lemma etaDD_of_one_le {x : ℝ} (h : 1 ≤ x) : etaDD x = 0 := by
  unfold etaDD; rw [clamp01_of_one_le h, rampPolyDD_one]

lemma etaDD_eq_rampDD {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : etaDD x = rampPolyDD x := by
  unfold etaDD; rw [clamp01_of_mem h0 h1]

/-! ### Bounds -/

lemma rampPoly_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ rampPoly x := by
  unfold rampPoly
  nlinarith [pow_nonneg h0 4, sq_nonneg x, sq_nonneg (1 - x), pow_nonneg h0 2,
    mul_nonneg (pow_nonneg h0 4) (sub_nonneg.2 h1), pow_nonneg h0 3]

lemma rampPoly_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : rampPoly x ≤ 1 := by
  have h : rampPoly (1 - x) = 1 - rampPoly x := by unfold rampPoly; ring
  have := rampPoly_nonneg (x := 1 - x) (by linarith) (by linarith)
  linarith [h ▸ this]

lemma rampPolyD_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ rampPolyD x := by
  have : rampPolyD x = 140 * x ^ 3 * (1 - x) ^ 3 := by unfold rampPolyD; ring
  rw [this]
  exact mul_nonneg (by positivity) (pow_nonneg (by linarith) 3)

lemma eta_nonneg (x : ℝ) : 0 ≤ eta x := by
  by_cases h : x ≤ 0
  · rw [eta_of_nonpos h]
  · push_neg at h
    by_cases h' : 1 ≤ x
    · rw [eta_of_one_le h']; norm_num
    · push_neg at h'; rw [eta_eq_ramp h.le h'.le]; exact rampPoly_nonneg h.le h'.le

lemma eta_le_one (x : ℝ) : eta x ≤ 1 := by
  by_cases h : x ≤ 0
  · rw [eta_of_nonpos h]; norm_num
  · push_neg at h
    by_cases h' : 1 ≤ x
    · rw [eta_of_one_le h']
    · push_neg at h'; rw [eta_eq_ramp h.le h'.le]; exact rampPoly_le_one h.le h'.le

lemma etaD_nonneg (x : ℝ) : 0 ≤ etaD x := by
  by_cases h : x ≤ 0
  · rw [etaD_of_nonpos h]
  · push_neg at h
    by_cases h' : 1 ≤ x
    · rw [etaD_of_one_le h']
    · push_neg at h'; rw [etaD_eq_rampD h.le h'.le]; exact rampPolyD_nonneg h.le h'.le

/-! ### `eta` is twice differentiable -/

private lemma glue (F f g : ℝ → ℝ) (a d : ℝ) (l r : ℝ) (hl : l < a) (hr : a < r)
    (hf : HasDerivAt f d a) (hg : HasDerivAt g d a)
    (hF1 : EqOn F f (Icc l a)) (hF2 : EqOn F g (Icc a r)) :
    HasDerivAt F d a := by
  rw [← hasDerivWithinAt_univ, ← Set.Iic_union_Ici (a := a)]
  refine HasDerivWithinAt.union ?_ ?_
  · refine (hf.hasDerivWithinAt (s := Iic a)).congr_of_eventuallyEq ?_ (hF1 ⟨hl.le, le_rfl⟩)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hl hr), self_mem_nhdsWithin]
      with x hx1 hx2
    exact hF1 ⟨hx1.1.le, hx2⟩
  · refine (hg.hasDerivWithinAt (s := Ici a)).congr_of_eventuallyEq ?_ (hF2 ⟨le_rfl, hr.le⟩)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hl hr), self_mem_nhdsWithin]
      with x hx1 hx2
    exact hF2 ⟨hx2, hx1.2.le⟩

lemma hasDerivAt_eta (x : ℝ) : HasDerivAt eta (etaD x) x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [etaD_of_nonpos h.le]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact eta_of_nonpos hy.le
  · subst h
    rw [etaD_of_nonpos le_rfl]
    refine glue eta (fun _ => 0) rampPoly 0 0 (-1) 1 (by norm_num) (by norm_num)
      (hasDerivAt_const _ _) ?_ ?_ ?_
    · exact (hasDerivAt_rampPoly 0).congr_deriv rampPolyD_zero
    · intro y hy; exact eta_of_nonpos hy.2
    · intro y hy; exact eta_eq_ramp hy.1 hy.2
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · rw [etaD_eq_rampD h.le h1.le]
      refine (hasDerivAt_rampPoly x).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds h h1] with y hy
      exact eta_eq_ramp hy.1.le hy.2.le
    · subst h1
      rw [etaD_of_one_le le_rfl]
      refine glue eta rampPoly (fun _ => 1) 1 0 0 2 (by norm_num) (by norm_num) ?_
        (hasDerivAt_const _ _) ?_ ?_
      · exact (hasDerivAt_rampPoly 1).congr_deriv rampPolyD_one
      · intro y hy; exact eta_eq_ramp hy.1 hy.2
      · intro y hy; exact eta_of_one_le hy.1
    · rw [etaD_of_one_le h1.le]
      refine (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact eta_of_one_le hy.le

lemma hasDerivAt_etaD (x : ℝ) : HasDerivAt etaD (etaDD x) x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [etaDD_of_nonpos h.le]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    exact etaD_of_nonpos hy.le
  · subst h
    rw [etaDD_of_nonpos le_rfl]
    refine glue etaD (fun _ => 0) rampPolyD 0 0 (-1) 1 (by norm_num) (by norm_num)
      (hasDerivAt_const _ _) ?_ ?_ ?_
    · exact (hasDerivAt_rampPolyD 0).congr_deriv rampPolyDD_zero
    · intro y hy; exact etaD_of_nonpos hy.2
    · intro y hy; exact etaD_eq_rampD hy.1 hy.2
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · rw [etaDD_eq_rampDD h.le h1.le]
      refine (hasDerivAt_rampPolyD x).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds h h1] with y hy
      exact etaD_eq_rampD hy.1.le hy.2.le
    · subst h1
      rw [etaDD_of_one_le le_rfl]
      refine glue etaD rampPolyD (fun _ => 0) 1 0 0 2 (by norm_num) (by norm_num) ?_
        (hasDerivAt_const _ _) ?_ ?_
      · exact (hasDerivAt_rampPolyD 1).congr_deriv rampPolyDD_one
      · intro y hy; exact etaD_eq_rampD hy.1 hy.2
      · intro y hy; exact etaD_of_one_le hy.1
    · rw [etaDD_of_one_le h1.le]
      refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact etaD_of_one_le hy.le

/-! ### The squared window profile -/

/-- `V = eta ^ 2`. -/
noncomputable def V (s : ℝ) : ℝ := eta s ^ 2

/-- Derivative of `V`. -/
noncomputable def V1 (s : ℝ) : ℝ := 2 * eta s * etaD s

/-- Second derivative of `V`. -/
noncomputable def V2 (s : ℝ) : ℝ := 2 * etaD s ^ 2 + 2 * eta s * etaDD s

lemma hasDerivAt_V (s : ℝ) : HasDerivAt V (V1 s) s := by
  unfold V
  exact ((hasDerivAt_eta s).pow 2).congr_deriv (by unfold V1; push_cast; ring)

lemma hasDerivAt_V1 (s : ℝ) : HasDerivAt V1 (V2 s) s := by
  unfold V1
  exact (((hasDerivAt_eta s).const_mul (2:ℝ)).mul (hasDerivAt_etaD s)).congr_deriv
    (by unfold V2; ring)

lemma continuous_V : Continuous V := continuous_eta.pow 2

lemma continuous_V1 : Continuous V1 :=
  (continuous_const.mul continuous_eta).mul continuous_etaD

lemma continuous_V2 : Continuous V2 :=
  (continuous_const.mul (continuous_etaD.pow 2)).add
    ((continuous_const.mul continuous_eta).mul continuous_etaDD)

lemma V_zero : V 0 = 0 := by unfold V; rw [eta_of_nonpos le_rfl]; ring

lemma V_of_one_le {s : ℝ} (h : 1 ≤ s) : V s = 1 := by
  unfold V; rw [eta_of_one_le h]; ring

lemma V_of_nonpos {s : ℝ} (h : s ≤ 0) : V s = 0 := by
  unfold V; rw [eta_of_nonpos h]; ring

lemma V_nonneg (s : ℝ) : 0 ≤ V s := by unfold V; positivity

lemma V_le_one (s : ℝ) : V s ≤ 1 := by
  unfold V
  nlinarith [eta_nonneg s, eta_le_one s]

lemma V1_nonneg (s : ℝ) : 0 ≤ V1 s := by
  unfold V1
  exact mul_nonneg (by linarith [eta_nonneg s]) (etaD_nonneg s)

lemma V1_of_nonpos {s : ℝ} (h : s ≤ 0) : V1 s = 0 := by
  unfold V1; rw [etaD_of_nonpos h]; ring

lemma V1_of_one_le {s : ℝ} (h : 1 ≤ s) : V1 s = 0 := by
  unfold V1; rw [etaD_of_one_le h]; ring

lemma V2_of_nonpos {s : ℝ} (h : s ≤ 0) : V2 s = 0 := by
  unfold V2; rw [etaD_of_nonpos h, etaDD_of_nonpos h]; ring

lemma V2_of_one_le {s : ℝ} (h : 1 ≤ s) : V2 s = 0 := by
  unfold V2; rw [etaD_of_one_le h, etaDD_of_one_le h]; ring

/-! ### The window `W` and its derivatives -/

/-- The squared tapered window, written without absolute values. -/
noncomputable def W (c u : ℝ) : ℝ := V (c - u) + V (c + u) - 1

/-- Derivative of `W c`. -/
noncomputable def W1 (c u : ℝ) : ℝ := V1 (c + u) - V1 (c - u)

/-- Second derivative of `W c`. -/
noncomputable def W2 (c u : ℝ) : ℝ := V2 (c + u) + V2 (c - u)

lemma hasDerivAt_W (c u : ℝ) : HasDerivAt (W c) (W1 c u) u := by
  have h1 : HasDerivAt (fun u : ℝ => V (c - u)) (-V1 (c - u)) u := by
    have := (hasDerivAt_V (c - u)).comp u ((hasDerivAt_id u).const_sub c)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun u : ℝ => V (c + u)) (V1 (c + u)) u := by
    have := (hasDerivAt_V (c + u)).comp u ((hasDerivAt_id u).const_add c)
    exact this.congr_deriv (by ring)
  exact ((h1.add h2).sub_const 1).congr_deriv (by unfold W1; ring)

lemma hasDerivAt_W1 (c u : ℝ) : HasDerivAt (W1 c) (W2 c u) u := by
  have h1 : HasDerivAt (fun u : ℝ => V1 (c - u)) (-V2 (c - u)) u := by
    have := (hasDerivAt_V1 (c - u)).comp u ((hasDerivAt_id u).const_sub c)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun u : ℝ => V1 (c + u)) (V2 (c + u)) u := by
    have := (hasDerivAt_V1 (c + u)).comp u ((hasDerivAt_id u).const_add c)
    exact this.congr_deriv (by ring)
  exact (h2.sub h1).congr_deriv (by unfold W2; ring)

lemma continuous_W (c : ℝ) : Continuous (W c) :=
  ((continuous_V.comp (continuous_const.sub continuous_id)).add
    (continuous_V.comp (continuous_const.add continuous_id))).sub continuous_const

lemma continuous_W1 (c : ℝ) : Continuous (W1 c) :=
  (continuous_V1.comp (continuous_const.add continuous_id)).sub
    (continuous_V1.comp (continuous_const.sub continuous_id))

lemma continuous_W2 (c : ℝ) : Continuous (W2 c) :=
  (continuous_V2.comp (continuous_const.add continuous_id)).add
    (continuous_V2.comp (continuous_const.sub continuous_id))

lemma W_eq_abs {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : W c u = V (c - |u|) := by
  unfold W
  by_cases h : 0 ≤ u
  · rw [abs_of_nonneg h, V_of_one_le (show (1:ℝ) ≤ c + u by linarith)]; ring
  · push_neg at h
    rw [abs_of_neg h, V_of_one_le (show (1:ℝ) ≤ c - u by linarith)]
    ring_nf

lemma W_even (c u : ℝ) : W c (-u) = W c u := by
  unfold W; rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring

lemma W2_even (c u : ℝ) : W2 c (-u) = W2 c u := by
  unfold W2; rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring

lemma W1_odd (c u : ℝ) : W1 c (-u) = -W1 c u := by
  unfold W1; rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring

lemma W_nonneg {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : 0 ≤ W c u := by
  rw [W_eq_abs hc]; exact V_nonneg _

lemma W_le_one {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : W c u ≤ 1 := by
  rw [W_eq_abs hc]; exact V_le_one _

lemma W_of_le_abs {c : ℝ} (hc : 1 ≤ c) {u : ℝ} (h : c ≤ |u|) : W c u = 0 := by
  rw [W_eq_abs hc]; exact V_of_nonpos (by linarith)

lemma W1_of_le_abs {c : ℝ} (hc : 1 ≤ c) {u : ℝ} (h : c ≤ |u|) : W1 c u = 0 := by
  unfold W1
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu] at h
    rw [V1_of_one_le (by linarith), V1_of_nonpos (by linarith)]; ring
  · push_neg at hu
    rw [abs_of_neg hu] at h
    rw [V1_of_nonpos (by linarith), V1_of_one_le (by linarith)]; ring

lemma W2_of_le_abs {c : ℝ} (hc : 1 ≤ c) {u : ℝ} (h : c ≤ |u|) : W2 c u = 0 := by
  unfold W2
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu] at h
    rw [V2_of_one_le (by linarith), V2_of_nonpos (by linarith)]; ring
  · push_neg at hu
    rw [abs_of_neg hu] at h
    rw [V2_of_nonpos (by linarith), V2_of_one_le (by linarith)]; ring

/-! ### Reduction of the integral over `ℝ` to an interval integral -/

lemma integral_reduce {c : ℝ} (hc : 0 ≤ c) (h Φ : ℝ → ℝ)
    (hcont : Continuous h)
    (hzero : ∀ u : ℝ, c ≤ |u| → h u = 0)
    (heven : ∀ u : ℝ, h (-u) = h u)
    (heq : ∀ u : ℝ, 0 ≤ u → u ≤ c → h u = Φ (c - u)) :
    ∫ u : ℝ, h u = 2 * ∫ s in (0:ℝ)..c, Φ s := by
  have hcompl : ∀ x ∉ Ioc (-c) c, h x = 0 := by
    intro x hx
    rw [Set.mem_Ioc] at hx
    push_neg at hx
    rcases le_or_gt x (-c) with hx1 | hx1
    · exact hzero x (by rw [abs_of_nonpos (by linarith)]; linarith)
    · exact hzero x (by rw [abs_of_nonneg (by linarith [hx hx1])]; linarith [hx hx1])
  have e1 : ∫ u : ℝ, h u = ∫ u in (-c)..c, h u := by
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
  have e2 : ∫ u in (-c)..c, h u = (∫ u in (-c)..(0:ℝ), h u) + ∫ u in (0:ℝ)..c, h u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have e3 : (∫ u in (-c)..(0:ℝ), h u) = ∫ u in (0:ℝ)..c, h u := by
    have hn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := c) h
    simp only [neg_zero] at hn
    rw [← hn]
    simp only [heven]
  have e4 : (∫ u in (0:ℝ)..c, h u) = ∫ s in (0:ℝ)..c, Φ s := by
    have : (∫ u in (0:ℝ)..c, h u) = ∫ u in (0:ℝ)..c, Φ (c - u) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hc] at hx
      exact heq x hx.1 hx.2
    rw [this, intervalIntegral.integral_comp_sub_left Φ c]
    simp
  rw [e1, e2, e3, e4]; ring

/-! ### Explicit polynomial integrals -/

/-- An antiderivative of `rampPolyD ^ 2`. -/
noncomputable def quadAnti (x : ℝ) : ℝ :=
  2800 * x ^ 7 - 14700 * x ^ 8 + 98000 / 3 * x ^ 9 - 39200 * x ^ 10 + 294000 / 11 * x ^ 11
    - 9800 * x ^ 12 + 19600 / 13 * x ^ 13

lemma hasDerivAt_quadAnti (x : ℝ) : HasDerivAt quadAnti (rampPolyD x ^ 2) x := by
  unfold quadAnti rampPolyD
  have h :=
    ((((((((hasDerivAt_pow 7 x).const_mul (2800:ℝ)).sub
      ((hasDerivAt_pow 8 x).const_mul (14700:ℝ))).add
      ((hasDerivAt_pow 9 x).const_mul ((98000:ℝ)/3))).sub
      ((hasDerivAt_pow 10 x).const_mul (39200:ℝ))).add
      ((hasDerivAt_pow 11 x).const_mul ((294000:ℝ)/11))).sub
      ((hasDerivAt_pow 12 x).const_mul (9800:ℝ))).add
      ((hasDerivAt_pow 13 x).const_mul ((19600:ℝ)/13)))
  exact h.congr_deriv (by push_cast; ring)

lemma integral_rampPolyD_sq : (∫ s in (0:ℝ)..1, rampPolyD s ^ 2) = 700 / 429 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_quadAnti x)
    ((continuous_rampPolyD.pow 2).intervalIntegrable _ _)]
  unfold quadAnti
  norm_num

lemma rampPolyDD_nonneg_left {x : ℝ} (h1 : x ≤ 1/2) : 0 ≤ rampPolyDD x := by
  have hx : rampPolyDD x = 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x) := by unfold rampPolyDD; ring
  rw [hx]
  have : (0:ℝ) ≤ 1 - 2 * x := by linarith
  positivity

lemma rampPolyDD_nonpos_right {x : ℝ} (h0 : 1/2 ≤ x) : rampPolyDD x ≤ 0 := by
  have hx : rampPolyDD x = -(420 * x ^ 2 * (1 - x) ^ 2 * (2 * x - 1)) := by unfold rampPolyDD; ring
  rw [hx, neg_nonpos]
  have : (0:ℝ) ≤ 2 * x - 1 := by linarith
  positivity

lemma integral_abs_rampPolyDD : (∫ s in (0:ℝ)..1, |rampPolyDD s|) = 35 / 8 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => |rampPolyDD s|) MeasureTheory.volume a b :=
    fun a b => (continuous_rampPolyDD.abs).intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := (1:ℝ)/2) (c := (1:ℝ)) (hint _ _) (hint _ _)
  have h1 : (∫ s in (0:ℝ)..(1/2 : ℝ), |rampPolyDD s|) = 35 / 16 := by
    have hcongr : (∫ s in (0:ℝ)..(1/2 : ℝ), |rampPolyDD s|)
        = ∫ s in (0:ℝ)..(1/2 : ℝ), rampPolyDD s := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact abs_of_nonneg (rampPolyDD_nonneg_left hx.2)
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_rampPolyD x)
      (continuous_rampPolyDD.intervalIntegrable _ _)]
    unfold rampPolyD
    norm_num
  have h2 : (∫ s in ((1:ℝ)/2)..(1:ℝ), |rampPolyDD s|) = 35 / 16 := by
    have hcongr : (∫ s in ((1:ℝ)/2)..(1:ℝ), |rampPolyDD s|)
        = ∫ s in ((1:ℝ)/2)..(1:ℝ), -rampPolyDD s := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact abs_of_nonpos (rampPolyDD_nonpos_right hx.1)
    rw [hcongr, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_rampPolyD x)
      (continuous_rampPolyDD.intervalIntegrable _ _)]
    unfold rampPolyD
    norm_num
  rw [← hsplit, h1, h2]
  norm_num

/-- Pointwise majorant for `|V2|` on `[0,1]`. -/
noncomputable def majorant (s : ℝ) : ℝ := 2 * rampPolyD s ^ 2 + 2 * |rampPolyDD s|

lemma continuous_majorant : Continuous majorant :=
  (continuous_const.mul (continuous_rampPolyD.pow 2)).add
    (continuous_const.mul continuous_rampPolyDD.abs)

lemma integral_majorant : (∫ s in (0:ℝ)..1, majorant s) = 20615 / 1716 := by
  have hcA : Continuous (fun s : ℝ => 2 * rampPolyD s ^ 2) :=
    continuous_const.mul (continuous_rampPolyD.pow 2)
  have hcB : Continuous (fun s : ℝ => 2 * |rampPolyDD s|) :=
    continuous_const.mul continuous_rampPolyDD.abs
  have hA : IntervalIntegrable (fun s : ℝ => 2 * rampPolyD s ^ 2) MeasureTheory.volume 0 1 :=
    hcA.intervalIntegrable _ _
  have hB : IntervalIntegrable (fun s : ℝ => 2 * |rampPolyDD s|) MeasureTheory.volume 0 1 :=
    hcB.intervalIntegrable _ _
  unfold majorant
  rw [intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rampPolyD_sq, integral_abs_rampPolyDD]
  norm_num

lemma abs_V2_le_majorant {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : |V2 s| ≤ majorant s := by
  unfold V2 majorant
  rw [eta_eq_ramp h0 h1, etaD_eq_rampD h0 h1, etaDD_eq_rampDD h0 h1, abs_le]
  have hp0 := rampPoly_nonneg h0 h1
  have hp1 := rampPoly_le_one h0 h1
  have ha1 := le_abs_self (rampPolyDD s)
  have ha2 := neg_abs_le (rampPolyDD s)
  have ha3 := abs_nonneg (rampPolyDD s)
  have hsq := sq_nonneg (rampPolyD s)
  have ha4 : (0:ℝ) ≤ rampPolyDD s + |rampPolyDD s| := by linarith
  have ha5 : (0:ℝ) ≤ |rampPolyDD s| - rampPolyDD s := by linarith
  have ha6 : (0:ℝ) ≤ 1 - rampPoly s := by linarith
  constructor
  · nlinarith [mul_nonneg hp0 ha4, mul_nonneg ha6 ha3]
  · nlinarith [mul_nonneg hp0 ha5, mul_nonneg ha6 ha3]

/-! ### The three integral bounds -/

lemma integral_W_le {c : ℝ} (hc : 1 ≤ c) : (∫ u : ℝ, W c u) ≤ 2 * c := by
  have h := integral_reduce (c := c) (by linarith) (W c) V (continuous_W c)
    (fun u hu => W_of_le_abs hc hu) (W_even c)
    (fun u hu0 _ => by rw [W_eq_abs hc, abs_of_nonneg hu0])
  rw [h]
  have hmono : (∫ s in (0:ℝ)..c, V s) ≤ ∫ _s in (0:ℝ)..c, (1:ℝ) :=
    intervalIntegral.integral_mono_on (by linarith) (continuous_V.intervalIntegrable _ _)
      intervalIntegrable_const (fun x _ => V_le_one x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul, mul_one, sub_zero] at hmono
  linarith

lemma integral_absW1 {c : ℝ} (hc : 1 ≤ c) : (∫ u : ℝ, |W1 c u|) = 2 := by
  have h := integral_reduce (c := c) (by linarith) (fun u => |W1 c u|) (fun s => |V1 s|)
    ((continuous_W1 c).abs)
    (fun u hu => by show |W1 c u| = 0; rw [W1_of_le_abs hc hu, abs_zero])
    (fun u => by show |W1 c (-u)| = |W1 c u|; rw [W1_odd, abs_neg])
    (fun u hu0 _ => by
      show |W1 c u| = |V1 (c - u)|
      unfold W1
      rw [V1_of_one_le (show (1:ℝ) ≤ c + u by linarith), zero_sub, abs_neg])
  rw [h]
  have habs : ∀ s : ℝ, |V1 s| = V1 s := fun s => abs_of_nonneg (V1_nonneg s)
  simp only [habs]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_V x)
    (continuous_V1.intervalIntegrable _ _), V_of_one_le hc, V_zero]
  norm_num

lemma integral_V2_le {c : ℝ} (hc : 1 ≤ c) : (∫ s in (0:ℝ)..c, |V2 s|) ≤ 20615 / 1716 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => |V2 s|) MeasureTheory.volume a b :=
    fun a b => continuous_V2.abs.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := (1:ℝ)) (c := c) (hint _ _) (hint _ _)
  have h2 : (∫ s in (1:ℝ)..c, |V2 s|) = 0 := by
    have hcongr : (∫ s in (1:ℝ)..c, |V2 s|) = ∫ _s in (1:ℝ)..c, (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hc] at hx
      show |V2 x| = 0
      rw [V2_of_one_le hx.1, abs_zero]
    rw [hcongr]
    simp
  have h1 : (∫ s in (0:ℝ)..1, |V2 s|) ≤ 20615 / 1716 := by
    rw [← integral_majorant]
    refine intervalIntegral.integral_mono_on (by norm_num) (hint _ _)
      (continuous_majorant.intervalIntegrable _ _) (fun x hx => abs_V2_le_majorant hx.1 hx.2)
  rw [← hsplit, h2]
  linarith

lemma integral_absW2 {c : ℝ} (hc : 1 ≤ c) : (∫ u : ℝ, |W2 c u|) ≤ 20615 / 858 := by
  have h := integral_reduce (c := c) (by linarith) (fun u => |W2 c u|) (fun s => |V2 s|)
    ((continuous_W2 c).abs)
    (fun u hu => by show |W2 c u| = 0; rw [W2_of_le_abs hc hu, abs_zero])
    (fun u => by show |W2 c (-u)| = |W2 c u|; rw [W2_even])
    (fun u hu0 _ => by
      show |W2 c u| = |V2 (c - u)|
      unfold W2
      rw [V2_of_one_le (show (1:ℝ) ≤ c + u by linarith), zero_add])
  rw [h]
  linarith [integral_V2_le hc]

lemma integrable_of_support (c : ℝ) (hc : 0 ≤ c) (h : ℝ → ℝ) (hcont : Continuous h)
    (hzero : ∀ u : ℝ, c ≤ |u| → h u = 0) : MeasureTheory.Integrable h := by
  refine hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) ?_)
  intro x hx
  rw [Set.mem_Icc] at hx
  push_neg at hx
  by_cases h1 : -c ≤ x
  · exact hzero x (by rw [abs_of_nonneg (by linarith [hx h1])]; linarith [hx h1])
  · push_neg at h1
    exact hzero x (by rw [abs_of_nonpos (by linarith)]; linarith)

end TaperAux

open TaperAux

theorem taper_sq_second_deriv_L1_bound
    (P : ℝ → ℝ) (L B0 B1 B2 : ℝ) (hL : 8 ≤ L) (hP : ContDiff ℝ 2 P)
    (hB0 : ∀ y : ℝ, |y| ≤ 1/2 → |P y| ≤ B0)
    (hB1 : ∀ y : ℝ, |y| ≤ 1/2 → |deriv P y| ≤ B1)
    (hB2 : ∀ y : ℝ, |y| ≤ 1/2 → |deriv (deriv P) y| ≤ B2) :
    (∫ u : ℝ, |iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|) ^ 2) u|)
      ≤ B2 / L + 4 * B1 / L + (20615 / 858) * B0 := by
  have hL0 : (0:ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hc : (1:ℝ) ≤ L / 2 := by linarith
  have hL2 : (0:ℝ) < L ^ 2 := by positivity
  have hB0' : (0:ℝ) ≤ B0 := le_trans (abs_nonneg _) (hB0 0 (by norm_num))
  have hB1' : (0:ℝ) ≤ B1 := le_trans (abs_nonneg _) (hB1 0 (by norm_num))
  have hB2' : (0:ℝ) ≤ B2 := le_trans (abs_nonneg _) (hB2 0 (by norm_num))
  have hPd : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hPd2 : Differentiable ℝ (deriv P) := by
    have h := hP.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  have hin : ∀ u : ℝ, HasDerivAt (fun u : ℝ => u / L) (1 / L) u := fun u =>
    (hasDerivAt_id u).div_const L
  have hPc : ∀ u : ℝ, HasDerivAt (fun u : ℝ => P (u / L)) (deriv P (u / L) / L) u := by
    intro u
    have h0 : HasDerivAt (fun u : ℝ => P (u / L)) (deriv P (u / L) * (1 / L)) u :=
      ((hPd (u / L)).hasDerivAt).comp u (hin u)
    exact h0.congr_deriv (mul_one_div _ _)
  have hPc2 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => deriv P (u / L) / L)
      (deriv (deriv P) (u / L) / L ^ 2) u := by
    intro u
    have hcomp : HasDerivAt ((deriv P) ∘ fun u : ℝ => u / L)
        (deriv (deriv P) (u / L) * (1 / L)) u := ((hPd2 (u / L)).hasDerivAt).comp u (hin u)
    have h0 : HasDerivAt (fun u : ℝ => deriv P (u / L)) (deriv (deriv P) (u / L) * (1 / L)) u :=
      hcomp
    exact (h0.div_const L).congr_deriv (by rw [mul_one_div, div_div, ← pow_two])
  have hd1 : ∀ u : ℝ, HasDerivAt (fun u : ℝ => P (u / L) * W (L / 2) u)
      (deriv P (u / L) / L * W (L / 2) u + P (u / L) * W1 (L / 2) u) u := fun u =>
    (hPc u).mul (hasDerivAt_W (L / 2) u)
  have hd2 : ∀ u : ℝ,
      HasDerivAt (fun u : ℝ => deriv P (u / L) / L * W (L / 2) u + P (u / L) * W1 (L / 2) u)
        (deriv (deriv P) (u / L) / L ^ 2 * W (L / 2) u
          + 2 * (deriv P (u / L) / L) * W1 (L / 2) u + P (u / L) * W2 (L / 2) u) u := by
    intro u
    exact (((hPc2 u).mul (hasDerivAt_W (L / 2) u)).add
      ((hPc u).mul (hasDerivAt_W1 (L / 2) u))).congr_deriv (by ring)
  have hfeq : (fun u : ℝ => P (u / L) * eta (L / 2 - |u|) ^ 2)
      = fun u : ℝ => P (u / L) * W (L / 2) u := by
    funext u
    rw [W_eq_abs hc u]
    rfl
  have hderiv1 : deriv (fun u : ℝ => P (u / L) * W (L / 2) u)
      = fun u : ℝ => deriv P (u / L) / L * W (L / 2) u + P (u / L) * W1 (L / 2) u :=
    funext fun u => (hd1 u).deriv
  have hiter : iteratedDeriv 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|) ^ 2)
      = fun u : ℝ => deriv (deriv P) (u / L) / L ^ 2 * W (L / 2) u
        + 2 * (deriv P (u / L) / L) * W1 (L / 2) u + P (u / L) * W2 (L / 2) u := by
    rw [hfeq, show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv1]
    exact funext fun u => (hd2 u).deriv
  rw [hiter]
  -- the pointwise majorant
  have hpt : ∀ u : ℝ, |deriv (deriv P) (u / L) / L ^ 2 * W (L / 2) u
      + 2 * (deriv P (u / L) / L) * W1 (L / 2) u + P (u / L) * W2 (L / 2) u|
      ≤ B2 / L ^ 2 * W (L / 2) u + 2 * B1 / L * |W1 (L / 2) u| + B0 * |W2 (L / 2) u| := by
    intro u
    by_cases hu : L / 2 ≤ |u|
    · rw [W_of_le_abs hc hu, W1_of_le_abs hc hu, W2_of_le_abs hc hu]
      simp
    · push_neg at hu
      have hy : |u / L| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]
        linarith
      have hw := W_nonneg hc u
      have h1 : |deriv (deriv P) (u / L) / L ^ 2 * W (L / 2) u| ≤ B2 / L ^ 2 * W (L / 2) u := by
        rw [abs_mul, abs_of_nonneg hw, abs_div, abs_of_pos hL2]
        gcongr
        exact hB2 _ hy
      have h2 : |2 * (deriv P (u / L) / L) * W1 (L / 2) u| ≤ 2 * B1 / L * |W1 (L / 2) u| := by
        rw [abs_mul]
        have habs : |2 * (deriv P (u / L) / L)| = 2 * |deriv P (u / L)| / L := by
          rw [abs_mul, abs_div, abs_of_pos hL0, mul_div_assoc]
          norm_num
        rw [habs]
        gcongr
        exact hB1 _ hy
      have h3 : |P (u / L) * W2 (L / 2) u| ≤ B0 * |W2 (L / 2) u| := by
        rw [abs_mul]
        gcongr
        exact hB0 _ hy
      refine le_trans (abs_add_le _ _) ?_
      refine le_trans (add_le_add (abs_add_le _ _) (le_refl |P (u / L) * W2 (L / 2) u|)) ?_
      linarith
  -- integrability
  have hc0 : (0:ℝ) ≤ L / 2 := by linarith
  have hiW : MeasureTheory.Integrable (W (L / 2)) :=
    integrable_of_support (L / 2) hc0 _ (continuous_W _) (fun u hu => W_of_le_abs hc hu)
  have hiW1 : MeasureTheory.Integrable (fun u : ℝ => |W1 (L / 2) u|) :=
    integrable_of_support (L / 2) hc0 _ (continuous_W1 _).abs
      (fun u hu => by show |W1 (L / 2) u| = 0; rw [W1_of_le_abs hc hu, abs_zero])
  have hiW2 : MeasureTheory.Integrable (fun u : ℝ => |W2 (L / 2) u|) :=
    integrable_of_support (L / 2) hc0 _ (continuous_W2 _).abs
      (fun u hu => by show |W2 (L / 2) u| = 0; rw [W2_of_le_abs hc hu, abs_zero])
  have hiA : MeasureTheory.Integrable (fun u : ℝ => B2 / L ^ 2 * W (L / 2) u) :=
    hiW.const_mul _
  have hiB : MeasureTheory.Integrable (fun u : ℝ => 2 * B1 / L * |W1 (L / 2) u|) :=
    hiW1.const_mul _
  have hiC : MeasureTheory.Integrable (fun u : ℝ => B0 * |W2 (L / 2) u|) :=
    hiW2.const_mul _
  have hiAB : MeasureTheory.Integrable (fun u : ℝ => B2 / L ^ 2 * W (L / 2) u
      + 2 * B1 / L * |W1 (L / 2) u|) := hiA.add hiB
  have hiG : MeasureTheory.Integrable (fun u : ℝ => B2 / L ^ 2 * W (L / 2) u
      + 2 * B1 / L * |W1 (L / 2) u| + B0 * |W2 (L / 2) u|) := hiAB.add hiC
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun u : ℝ => abs_nonneg _)) hiG
    (Filter.Eventually.of_forall hpt)
  refine le_trans hmono ?_
  have hGint : (∫ u : ℝ, B2 / L ^ 2 * W (L / 2) u + 2 * B1 / L * |W1 (L / 2) u|
        + B0 * |W2 (L / 2) u|)
      = B2 / L ^ 2 * (∫ u : ℝ, W (L / 2) u) + 2 * B1 / L * (∫ u : ℝ, |W1 (L / 2) u|)
        + B0 * (∫ u : ℝ, |W2 (L / 2) u|) := by
    rw [MeasureTheory.integral_add hiAB hiC, MeasureTheory.integral_add hiA hiB,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hGint]
  have e1 := integral_W_le hc
  have e2 := integral_absW1 hc
  have e3 := integral_absW2 hc
  have t1 : B2 / L ^ 2 * (∫ u : ℝ, W (L / 2) u) ≤ B2 / L := by
    have h := mul_le_mul_of_nonneg_left e1 (by positivity : (0:ℝ) ≤ B2 / L ^ 2)
    have h2 : B2 / L ^ 2 * (2 * (L / 2)) = B2 / L := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) hLne]
      ring
    linarith [h2 ▸ h]
  have t2 : 2 * B1 / L * (∫ u : ℝ, |W1 (L / 2) u|) = 4 * B1 / L := by rw [e2]; ring
  have t3 : B0 * (∫ u : ℝ, |W2 (L / 2) u|) ≤ 20615 / 858 * B0 := by
    have h := mul_le_mul_of_nonneg_left e3 hB0'
    linarith
  linarith


end AristotleU