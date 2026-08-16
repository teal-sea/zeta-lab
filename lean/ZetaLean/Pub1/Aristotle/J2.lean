import Mathlib

namespace AristotleJ2

noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

namespace TaperAux

lemma pow_le_pow_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have hb : 0 ≤ b := le_trans ha hab
    calc a ^ (k + 1) = a ^ k * a := by ring
      _ ≤ b ^ k * b := mul_le_mul ih hab ha (pow_nonneg hb k)
      _ = b ^ (k + 1) := by ring

lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-- First derivative of `eta`. -/
noncomputable def eta1 (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 0 else 140 * x ^ 3 * (1 - x) ^ 3

/-- Second derivative of `eta`. -/
noncomputable def eta2 (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 0 else 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)

lemma eta_of_nonpos {x : ℝ} (hx : x ≤ 0) : eta x = 0 := by
  simp [eta, hx]

lemma eta_of_one_le {x : ℝ} (hx : 1 ≤ x) : eta x = 1 := by
  have : ¬ (x ≤ 0) := by linarith
  simp [eta, this, hx]

lemma eta_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : eta x = rampPoly x := by
  have h2 : ¬ (x ≤ 0) := by linarith
  have h3 : ¬ (1 ≤ x) := by linarith
  simp [eta, h2, h3]

lemma eta1_of_nonpos {x : ℝ} (hx : x ≤ 0) : eta1 x = 0 := by
  simp [eta1, hx]

lemma eta1_of_one_le {x : ℝ} (hx : 1 ≤ x) : eta1 x = 0 := by
  have : ¬ (x ≤ 0) := by linarith
  simp [eta1, this, hx]

lemma eta1_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    eta1 x = 140 * x ^ 3 * (1 - x) ^ 3 := by
  have h2 : ¬ (x ≤ 0) := by linarith
  have h3 : ¬ (1 ≤ x) := by linarith
  simp [eta1, h2, h3]

lemma eta2_of_nonpos {x : ℝ} (hx : x ≤ 0) : eta2 x = 0 := by
  simp [eta2, hx]

lemma eta2_of_one_le {x : ℝ} (hx : 1 ≤ x) : eta2 x = 0 := by
  have : ¬ (x ≤ 0) := by linarith
  simp [eta2, this, hx]

lemma eta2_of_mem {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    eta2 x = 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x) := by
  have h2 : ¬ (x ≤ 0) := by linarith
  have h3 : ¬ (1 ≤ x) := by linarith
  simp [eta2, h2, h3]

/-! ### Global polynomial bounds -/

lemma abs_eta_le (x : ℝ) : |eta x| ≤ 209 * |x| ^ 4 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [eta_of_nonpos hx, abs_zero]
    positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [eta_of_one_le hx1, abs_one]
    have h : (1:ℝ) ≤ |x| := by rw [abs_of_pos hx]; exact hx1
    have : (1:ℝ) ≤ |x| ^ 4 := one_le_pow₀ h
    linarith
  · rw [eta_of_mem hx hx1, abs_of_nonneg hx.le]
    rw [abs_le]
    constructor
    · simp only [rampPoly]; nlinarith [pow_pos hx 4, pow_pos hx 5, pow_pos hx 6, pow_pos hx 7,
        sq_nonneg x]
    · simp only [rampPoly]; nlinarith [pow_pos hx 4, pow_pos hx 5, pow_pos hx 6, pow_pos hx 7]

lemma abs_eta_sub_one_le (x : ℝ) : |eta x - 1| ≤ 35 * |x - 1| ^ 4 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [eta_of_nonpos hx]
    have h : (1:ℝ) ≤ |x - 1| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    have : (1:ℝ) ≤ |x - 1| ^ 4 := one_le_pow₀ h
    rw [show (0:ℝ) - 1 = -1 by ring, abs_neg, abs_one]
    linarith
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [eta_of_one_le hx1, sub_self, abs_zero]; positivity
  · rw [eta_of_mem hx hx1]
    have key : rampPoly x - 1 = -((1 - x) ^ 4 * (1 + 4 * x + 10 * x ^ 2 + 20 * x ^ 3)) := by
      simp only [rampPoly]; ring
    rw [key, abs_neg]
    have h1 : |x - 1| = 1 - x := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h1, abs_of_nonneg (by positivity)]
    have h2 : 1 + 4 * x + 10 * x ^ 2 + 20 * x ^ 3 ≤ 35 := by nlinarith
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 - x) 4]

lemma abs_eta1_le (x : ℝ) : |eta1 x| ≤ 140 * |x| ^ 3 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [eta1_of_nonpos hx, abs_zero]; positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [eta1_of_one_le hx1, abs_zero]; positivity
  · rw [eta1_of_mem hx hx1, abs_of_nonneg hx.le]
    have h1 : (0:ℝ) ≤ 1 - x := by linarith
    rw [abs_of_nonneg (by positivity)]
    nlinarith [pow_pos hx 3, pow_le_one₀ h1 (by linarith : 1 - x ≤ 1) (n := 3)]

lemma abs_eta1_le' (x : ℝ) : |eta1 x| ≤ 140 * |x - 1| ^ 3 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [eta1_of_nonpos hx, abs_zero]; positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [eta1_of_one_le hx1, abs_zero]; positivity
  · rw [eta1_of_mem hx hx1]
    have h1 : (0:ℝ) ≤ 1 - x := by linarith
    have h2 : |x - 1| = 1 - x := by rw [abs_of_nonpos (by linarith)]; ring
    rw [h2, abs_of_nonneg (by positivity)]
    nlinarith [pow_nonneg h1 3, pow_le_one₀ hx.le (by linarith : x ≤ 1) (n := 3),
      pow_pos hx 3]

lemma abs_eta2_le (x : ℝ) : |eta2 x| ≤ 420 * |x| ^ 2 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [eta2_of_nonpos hx, abs_zero]; positivity
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [eta2_of_one_le hx1, abs_zero]; positivity
  · rw [eta2_of_mem hx hx1, abs_of_nonneg hx.le]
    have h1 : (0:ℝ) ≤ 1 - x := by linarith
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg x, sq_nonneg (1 - x), pow_le_one₀ h1 (by linarith : 1 - x ≤ 1) (n := 2),
        sq_nonneg (x * (1 - x))]
    · nlinarith [sq_nonneg x, sq_nonneg (1 - x), pow_le_one₀ h1 (by linarith : 1 - x ≤ 1) (n := 2),
        sq_nonneg (x * (1 - x))]


open Filter Topology

/-- If `f` vanishes at `x` to order at least two (in the sense of a global polynomial bound),
then `f` is differentiable at `x` with derivative `0`. -/
lemma hasDerivAt_zero_of_pow_bound {f : ℝ → ℝ} {x C : ℝ} {n : ℕ} (hf : f x = 0)
    (h : ∀ y, |f y| ≤ C * |y - x| ^ (n + 2)) : HasDerivAt f 0 x := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply squeeze_zero_norm (a := fun y => C * |y - x| ^ (n + 1))
  · intro y
    rcases eq_or_ne y x with rfl | hy
    · simp
    · have hxy : (0:ℝ) < |y - x| := by
        rw [abs_pos, sub_ne_zero]; exact hy
      rw [slope_def_field, hf, Real.norm_eq_abs, abs_div, sub_zero]
      rw [div_le_iff₀ hxy]
      calc |f y| ≤ C * |y - x| ^ (n + 2) := h y
        _ = C * |y - x| ^ (n + 1) * |y - x| := by ring
  · have hc : Continuous (fun y : ℝ => C * |y - x| ^ (n + 1)) := by fun_prop
    have := hc.tendsto x
    simp only [sub_self, abs_zero] at this
    rw [zero_pow (by omega), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

/-- Continuity at `x` from a quadratic vanishing bound. -/
lemma continuousAt_zero_of_pow_bound {f : ℝ → ℝ} {x C : ℝ} (hf : f x = 0)
    (h : ∀ y, |f y| ≤ C * |y - x| ^ 2) : ContinuousAt f x := by
  rw [ContinuousAt, hf]
  apply squeeze_zero_norm (a := fun y => C * |y - x| ^ 2)
  · intro y; simpa using h y
  · have hc : Continuous (fun y : ℝ => C * |y - x| ^ 2) := by fun_prop
    have := hc.tendsto x
    simp only [sub_self, abs_zero] at this
    rw [zero_pow (by omega), mul_zero] at this
    exact this

lemma hasDerivAt_rampPoly (x : ℝ) : HasDerivAt rampPoly (140 * x ^ 3 * (1 - x) ^ 3) x := by
  have h : HasDerivAt (fun y : ℝ => 35 * y ^ 4 - 84 * y ^ 5 + 70 * y ^ 6 - 20 * y ^ 7)
      (35 * (4 * x ^ 3) - 84 * (5 * x ^ 4) + 70 * (6 * x ^ 5) - 20 * (7 * x ^ 6)) x := by
    have h4 := (hasDerivAt_pow 4 x).const_mul (35 : ℝ)
    have h5 := (hasDerivAt_pow 5 x).const_mul (84 : ℝ)
    have h6 := (hasDerivAt_pow 6 x).const_mul (70 : ℝ)
    have h7 := (hasDerivAt_pow 7 x).const_mul (20 : ℝ)
    exact (((h4.sub h5).add h6).sub h7).congr_deriv (by push_cast; ring)
  exact h.congr_deriv (by ring)

lemma hasDerivAt_eta (x : ℝ) : HasDerivAt eta (eta1 x) x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eta1_of_nonpos le_rfl]
    refine hasDerivAt_zero_of_pow_bound (n := 2) (C := 209) (eta_of_nonpos le_rfl) ?_
    intro y; simpa using abs_eta_le y
  rcases eq_or_ne x 1 with rfl | hx1
  · rw [eta1_of_one_le le_rfl]
    have h : HasDerivAt (fun y => eta y - 1) 0 1 := by
      refine hasDerivAt_zero_of_pow_bound (n := 2) (C := 35) ?_ ?_
      · rw [eta_of_one_le le_rfl]; ring
      · intro y; simpa using abs_eta_sub_one_le y
    simpa using h.add_const (1:ℝ)
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · rw [eta1_of_nonpos hneg.le]
    have hev : eta =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      exact eta_of_nonpos hy.le
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev
  · exact absurd h0 hx0
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · rw [eta1_of_mem hpos h1]
    have hev : eta =ᶠ[𝓝 x] rampPoly := by
      filter_upwards [Ioo_mem_nhds hpos h1] with y hy
      exact eta_of_mem hy.1 hy.2
    exact (hasDerivAt_rampPoly x).congr_of_eventuallyEq hev
  · exact absurd h1 hx1
  · rw [eta1_of_one_le h1.le]
    have hev : eta =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact eta_of_one_le hy.le
    exact (hasDerivAt_const x (1:ℝ)).congr_of_eventuallyEq hev

lemma hasDerivAt_eta1 (x : ℝ) : HasDerivAt eta1 (eta2 x) x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eta2_of_nonpos le_rfl]
    refine hasDerivAt_zero_of_pow_bound (n := 1) (C := 140) (eta1_of_nonpos le_rfl) ?_
    intro y; simpa using abs_eta1_le y
  rcases eq_or_ne x 1 with rfl | hx1
  · rw [eta2_of_one_le le_rfl]
    refine hasDerivAt_zero_of_pow_bound (n := 1) (C := 140) (eta1_of_one_le le_rfl) ?_
    intro y; simpa using abs_eta1_le' y
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · rw [eta2_of_nonpos hneg.le]
    have hev : eta1 =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      exact eta1_of_nonpos hy.le
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev
  · exact absurd h0 hx0
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · rw [eta2_of_mem hpos h1]
    have hev : eta1 =ᶠ[𝓝 x] (fun y : ℝ => 140 * y ^ 3 * (1 - y) ^ 3) := by
      filter_upwards [Ioo_mem_nhds hpos h1] with y hy
      exact eta1_of_mem hy.1 hy.2
    have hd : HasDerivAt (fun y : ℝ => 140 * y ^ 3 * (1 - y) ^ 3)
        (420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)) x := by
      have ha : HasDerivAt (fun y : ℝ => 140 * y ^ 3) (140 * (3 * x ^ 2)) x :=
        ((hasDerivAt_pow 3 x).const_mul (140 : ℝ)).congr_deriv (by push_cast; ring)
      have hb : HasDerivAt (fun y : ℝ => (1 - y) ^ 3) (3 * (1 - x) ^ 2 * (-1)) x := by
        have h3 : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := (hasDerivAt_id x).const_sub 1
        exact (h3.pow 3).congr_deriv (by push_cast; ring)
      exact (ha.mul hb).congr_deriv (by ring)
    exact hd.congr_of_eventuallyEq hev
  · exact absurd h1 hx1
  · rw [eta2_of_one_le h1.le]
    have hev : eta1 =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact eta1_of_one_le hy.le
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev

lemma continuous_eta2 : Continuous eta2 := by
  have h1 : Continuous (fun x : ℝ => if 1 ≤ x then (0:ℝ)
      else 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)) := by
    apply Continuous.if_le continuous_const (by fun_prop) continuous_const continuous_id
    intro x hx
    simp only [id_eq] at hx
    rw [← hx]; ring
  have h2 : Continuous (fun x : ℝ => if x ≤ 0 then (0:ℝ)
      else if 1 ≤ x then (0:ℝ) else 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)) := by
    apply Continuous.if_le continuous_const h1 continuous_id continuous_const
    intro x hx
    simp only [id_eq] at hx
    rw [hx]
    norm_num
  exact h2



/-- The tapered window. -/
noncomputable def taper (P : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ := P (u / L) * eta (L / 2 - |u|)

/-- The sign function used in the derivative of `|·|`. -/
noncomputable def taperSign (u : ℝ) : ℝ := if 0 ≤ u then 1 else -1

/-- Candidate first derivative of `taper`. -/
noncomputable def taperD1 (P : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ :=
  deriv P (u / L) / L * eta (L / 2 - |u|) - taperSign u * (P (u / L) * eta1 (L / 2 - |u|))

/-- Candidate second derivative of `taper`. -/
noncomputable def taperD2 (P : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ :=
  deriv (deriv P) (u / L) / L ^ 2 * eta (L / 2 - |u|)
    - 2 * taperSign u * (deriv P (u / L) / L * eta1 (L / 2 - |u|))
    + P (u / L) * eta2 (L / 2 - |u|)

lemma taper_eq_zero (P : ℝ → ℝ) (L u : ℝ) (h : L / 2 ≤ |u|) : taper P L u = 0 := by
  have h1 : L / 2 - |u| ≤ 0 := by linarith
  simp [taper, eta_of_nonpos h1]

lemma taperD1_eq_zero (P : ℝ → ℝ) (L u : ℝ) (h : L / 2 ≤ |u|) : taperD1 P L u = 0 := by
  have h1 : L / 2 - |u| ≤ 0 := by linarith
  simp [taperD1, eta_of_nonpos h1, eta1_of_nonpos h1]

lemma taperD2_eq_zero (P : ℝ → ℝ) (L u : ℝ) (h : L / 2 ≤ |u|) : taperD2 P L u = 0 := by
  have h1 : L / 2 - |u| ≤ 0 := by linarith
  simp [taperD2, eta_of_nonpos h1, eta1_of_nonpos h1, eta2_of_nonpos h1]

lemma continuous_eta : Continuous eta :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_eta x).continuousAt

lemma continuous_eta1 : Continuous eta1 :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_eta1 x).continuousAt


lemma abs_gap_le_right (L u : ℝ) (hL : 0 ≤ L) : abs (L / 2 - |u|) ≤ |u - L / 2| := by
  rw [abs_sub_comm]
  have h : abs (|u| - |L / 2|) ≤ |u - L / 2| := abs_abs_sub_abs_le_abs_sub u (L / 2)
  rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ L / 2)] at h

lemma abs_gap_le_left (L u : ℝ) (hL : 0 ≤ L) : abs (L / 2 - |u|) ≤ |u - -(L / 2)| := by
  rw [abs_sub_comm]
  have h : abs (|u| - |-(L / 2)|) ≤ |u - -(L / 2)| := abs_abs_sub_abs_le_abs_sub u (-(L / 2))
  rwa [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ L / 2)] at h

variable {P : ℝ → ℝ} {L C0 C1 C2 : ℝ}

lemma abs_taper_le (hC0nn : 0 ≤ C0)
    (hbP : ∀ v : ℝ, |v| < L / 2 → |P (v / L)| ≤ C0) (u : ℝ) :
    |taper P L u| ≤ 209 * C0 * abs (L / 2 - |u|) ^ 4 := by
  rcases lt_or_ge |u| (L / 2) with h | h
  · rw [taper, abs_mul]
    calc |P (u / L)| * |eta (L / 2 - |u|)|
        ≤ C0 * (209 * abs (L / 2 - |u|) ^ 4) :=
          mul_le_mul (hbP u h) (abs_eta_le _) (abs_nonneg _) hC0nn
      _ = 209 * C0 * abs (L / 2 - |u|) ^ 4 := by ring
  · rw [taper_eq_zero P L u h, abs_zero]; positivity

lemma abs_taperD1_le (hL : 8 ≤ L) (hC0nn : 0 ≤ C0) (hC1nn : 0 ≤ C1)
    (hbP : ∀ v : ℝ, |v| < L / 2 → |P (v / L)| ≤ C0)
    (hbP1 : ∀ v : ℝ, |v| < L / 2 → |deriv P (v / L)| ≤ C1) (u : ℝ) :
    |taperD1 P L u| ≤ (209 * C1 + 140 * C0) * abs (L / 2 - |u|) ^ 3 := by
  have hLpos : (0:ℝ) < L := by linarith
  rcases lt_or_ge |u| (L / 2) with h | h
  · have hs1 : |taperSign u| = 1 := by
      simp only [taperSign]; split <;> norm_num
    have h1 : |taperD1 P L u| ≤ |deriv P (u / L) / L| * |eta (L / 2 - |u|)|
        + |P (u / L)| * |eta1 (L / 2 - |u|)| := by
      rw [taperD1]
      refine le_trans (abs_sub_le' _ _) ?_
      rw [abs_mul (deriv P (u / L) / L), abs_mul (taperSign u), hs1, one_mul,
        abs_mul (P (u / L))]
    have ht0 : (0:ℝ) ≤ L / 2 - |u| := by linarith
    have hu0 : (0:ℝ) ≤ |u| := abs_nonneg u
    have habs : abs (L / 2 - |u|) = L / 2 - |u| := abs_of_nonneg ht0
    rw [habs]
    set t := L / 2 - |u| with hts
    have htL : t ≤ L := by rw [hts]; linarith
    have he0 : |eta t| ≤ 209 * t ^ 4 := by
      have := abs_eta_le t; rwa [abs_of_nonneg ht0] at this
    have he1 : |eta1 t| ≤ 140 * t ^ 3 := by
      have := abs_eta1_le t; rwa [abs_of_nonneg ht0] at this
    have hd : |deriv P (u / L)| / L ≤ C1 / L := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hbP1 u h) (inv_nonneg.mpr hLpos.le)
    have h2 : |deriv P (u / L) / L| * |eta t| ≤ C1 / L * (209 * t ^ 4) := by
      rw [abs_div, abs_of_nonneg hLpos.le]
      exact mul_le_mul hd he0 (abs_nonneg _) (by positivity)
    have h3 : |P (u / L)| * |eta1 t| ≤ C0 * (140 * t ^ 3) :=
      mul_le_mul (hbP u h) he1 (abs_nonneg _) hC0nn
    have h4 : C1 / L * (209 * t ^ 4) ≤ 209 * C1 * t ^ 3 := by
      have heq : C1 / L * (209 * t ^ 4) = C1 * (209 * t ^ 4) / L := by ring
      rw [heq, div_le_iff₀ hLpos]
      have hnn : (0:ℝ) ≤ 209 * C1 * t ^ 3 :=
        mul_nonneg (mul_nonneg (by norm_num) hC1nn) (pow_nonneg ht0 3)
      nlinarith [mul_nonneg hnn (by linarith : (0:ℝ) ≤ L - t)]
    linarith
  · rw [taperD1_eq_zero P L u h, abs_zero]
    have h9 : (0:ℝ) ≤ 209 * C1 + 140 * C0 := by linarith
    positivity

lemma abs_taperD2_le (hL : 8 ≤ L) (hC0nn : 0 ≤ C0) (hC1nn : 0 ≤ C1) (hC2nn : 0 ≤ C2)
    (hbP : ∀ v : ℝ, |v| < L / 2 → |P (v / L)| ≤ C0)
    (hbP1 : ∀ v : ℝ, |v| < L / 2 → |deriv P (v / L)| ≤ C1)
    (hbP2 : ∀ v : ℝ, |v| < L / 2 → |deriv (deriv P) (v / L)| ≤ C2) (u : ℝ) :
    |taperD2 P L u| ≤ (209 * C2 + 280 * C1 + 420 * C0) * abs (L / 2 - |u|) ^ 2 := by
  have hLpos : (0:ℝ) < L := by linarith
  rcases lt_or_ge |u| (L / 2) with h | h
  · have hs2 : |2 * taperSign u| = 2 := by
      simp only [taperSign]; split <;> norm_num
    have h1 : |taperD2 P L u| ≤ |deriv (deriv P) (u / L) / L ^ 2| * |eta (L / 2 - |u|)|
        + 2 * (|deriv P (u / L) / L| * |eta1 (L / 2 - |u|)|)
        + |P (u / L)| * |eta2 (L / 2 - |u|)| := by
      rw [taperD2]
      refine le_trans (abs_add_le _ _) ?_
      refine le_trans (add_le_add (abs_sub_le' _ _) (le_refl _)) ?_
      rw [abs_mul (deriv (deriv P) (u / L) / L ^ 2), abs_mul (2 * taperSign u), hs2,
        abs_mul (deriv P (u / L) / L), abs_mul (P (u / L))]
    have ht0 : (0:ℝ) ≤ L / 2 - |u| := by linarith
    have hu0 : (0:ℝ) ≤ |u| := abs_nonneg u
    have habs : abs (L / 2 - |u|) = L / 2 - |u| := abs_of_nonneg ht0
    rw [habs]
    set t := L / 2 - |u| with hts
    have htL : t ≤ L := by rw [hts]; linarith
    have he0 : |eta t| ≤ 209 * t ^ 4 := by
      have := abs_eta_le t; rwa [abs_of_nonneg ht0] at this
    have he1 : |eta1 t| ≤ 140 * t ^ 3 := by
      have := abs_eta1_le t; rwa [abs_of_nonneg ht0] at this
    have he2 : |eta2 t| ≤ 420 * t ^ 2 := by
      have := abs_eta2_le t; rwa [abs_of_nonneg ht0] at this
    have hd2 : |deriv (deriv P) (u / L)| / L ^ 2 ≤ C2 / L ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hbP2 u h) (inv_nonneg.mpr (by positivity))
    have hd1 : |deriv P (u / L)| / L ≤ C1 / L := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hbP1 u h) (inv_nonneg.mpr hLpos.le)
    have h2 : |deriv (deriv P) (u / L) / L ^ 2| * |eta t| ≤ C2 / L ^ 2 * (209 * t ^ 4) := by
      rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ L ^ 2)]
      exact mul_le_mul hd2 he0 (abs_nonneg _) (by positivity)
    have h3 : |deriv P (u / L) / L| * |eta1 t| ≤ C1 / L * (140 * t ^ 3) := by
      rw [abs_div, abs_of_nonneg hLpos.le]
      exact mul_le_mul hd1 he1 (abs_nonneg _) (by positivity)
    have h4 : |P (u / L)| * |eta2 t| ≤ C0 * (420 * t ^ 2) :=
      mul_le_mul (hbP u h) he2 (abs_nonneg _) hC0nn
    have ht2 : t ^ 2 ≤ L ^ 2 := by nlinarith
    have h5 : C2 / L ^ 2 * (209 * t ^ 4) ≤ 209 * C2 * t ^ 2 := by
      have heq : C2 / L ^ 2 * (209 * t ^ 4) = C2 * (209 * t ^ 4) / L ^ 2 := by ring
      rw [heq, div_le_iff₀ (by positivity)]
      have hnn : (0:ℝ) ≤ 209 * C2 * t ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hC2nn) (pow_nonneg ht0 2)
      nlinarith [mul_nonneg hnn (by linarith : (0:ℝ) ≤ L ^ 2 - t ^ 2)]
    have h6 : C1 / L * (140 * t ^ 3) ≤ 140 * C1 * t ^ 2 := by
      have heq : C1 / L * (140 * t ^ 3) = C1 * (140 * t ^ 3) / L := by ring
      rw [heq, div_le_iff₀ hLpos]
      have hnn : (0:ℝ) ≤ 140 * C1 * t ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hC1nn) (pow_nonneg ht0 2)
      nlinarith [mul_nonneg hnn (by linarith : (0:ℝ) ≤ L - t)]
    linarith
  · rw [taperD2_eq_zero P L u h, abs_zero]
    have h9 : (0:ℝ) ≤ 209 * C2 + 280 * C1 + 420 * C0 := by linarith
    positivity

end TaperAux

open Filter Topology TaperAux in
theorem taper_contDiff_open (P : ℝ → ℝ) (L : ℝ) (hL : 8 ≤ L)
    (hP : ContDiffOn ℝ 2 P (Set.Ioo (-(1/2) : ℝ) (1/2)))
    (C0 C1 C2 : ℝ)
    (hC0 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |P y| ≤ C0)
    (hC1 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv P y| ≤ C1)
    (hC2 : ∀ y ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv (deriv P) y| ≤ C2) :
    ContDiff ℝ 2 (fun u : ℝ => P (u / L) * eta (L / 2 - |u|)) := by
  have hLpos : (0:ℝ) < L := by linarith
  have hmem : ∀ v : ℝ, |v| < L / 2 → v / L ∈ Set.Ioo (-(1/2) : ℝ) (1/2) := by
    intro v hv
    rw [abs_lt] at hv
    constructor
    · rw [lt_div_iff₀ hLpos]; linarith [hv.1]
    · rw [div_lt_iff₀ hLpos]; linarith [hv.2]
  have hbP : ∀ v : ℝ, |v| < L / 2 → |P (v / L)| ≤ C0 := fun v hv => hC0 _ (hmem v hv)
  have hbP1 : ∀ v : ℝ, |v| < L / 2 → |deriv P (v / L)| ≤ C1 := fun v hv => hC1 _ (hmem v hv)
  have hbP2 : ∀ v : ℝ, |v| < L / 2 → |deriv (deriv P) (v / L)| ≤ C2 :=
    fun v hv => hC2 _ (hmem v hv)
  have hzmem : (0:ℝ) ∈ Set.Ioo (-(1/2) : ℝ) (1/2) := by norm_num
  have hC0nn : 0 ≤ C0 := le_trans (abs_nonneg _) (hC0 0 hzmem)
  have hC1nn : 0 ≤ C1 := le_trans (abs_nonneg _) (hC1 0 hzmem)
  have hC2nn : 0 ≤ C2 := le_trans (abs_nonneg _) (hC2 0 hzmem)
  -- derivatives of `P`
  have hPd : ∀ v : ℝ, |v| < L / 2 → HasDerivAt P (deriv P (v / L)) (v / L) := by
    intro v hv
    exact ((hP.contDiffAt (isOpen_Ioo.mem_nhds (hmem v hv))).differentiableAt
      (by norm_num)).hasDerivAt
  have hP1 : ContDiffOn ℝ 1 (deriv P) (Set.Ioo (-(1/2) : ℝ) (1/2)) :=
    hP.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hPd1 : ∀ v : ℝ, |v| < L / 2 →
      HasDerivAt (deriv P) (deriv (deriv P) (v / L)) (v / L) := by
    intro v hv
    exact ((hP1.contDiffAt (isOpen_Ioo.mem_nhds (hmem v hv))).differentiableAt
      (by norm_num)).hasDerivAt
  have hP2 : ContDiffOn ℝ 0 (deriv (deriv P)) (Set.Ioo (-(1/2) : ℝ) (1/2)) :=
    hP1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hPc0 : ∀ v : ℝ, |v| < L / 2 → ContinuousAt P (v / L) :=
    fun v hv => (hPd v hv).continuousAt
  have hPc1 : ∀ v : ℝ, |v| < L / 2 → ContinuousAt (deriv P) (v / L) :=
    fun v hv => (hPd1 v hv).continuousAt
  have hPc2 : ∀ v : ℝ, |v| < L / 2 → ContinuousAt (deriv (deriv P)) (v / L) :=
    fun v hv => (hP2.contDiffAt (isOpen_Ioo.mem_nhds (hmem v hv))).continuousAt
  -- composition with `y ↦ y / L`
  have hcP : ∀ v : ℝ, |v| < L / 2 →
      HasDerivAt (fun y : ℝ => P (y / L)) (deriv P (v / L) / L) v := by
    intro v hv
    exact ((hPd v hv).comp v ((hasDerivAt_id v).div_const L)).congr_deriv (by ring)
  have hcP1 : ∀ v : ℝ, |v| < L / 2 →
      HasDerivAt (fun y : ℝ => deriv P (y / L) / L) (deriv (deriv P) (v / L) / L ^ 2) v := by
    intro v hv
    have h := ((hPd1 v hv).comp v ((hasDerivAt_id v).div_const L)).div_const L
    refine h.congr_deriv ?_
    field_simp
  -- composition with `y ↦ L / 2 ∓ y`
  have hE0m : ∀ v : ℝ, HasDerivAt (fun y : ℝ => eta (L / 2 - y)) (-eta1 (L / 2 - v)) v := by
    intro v
    exact ((hasDerivAt_eta (L / 2 - v)).comp v ((hasDerivAt_id v).const_sub (L / 2))).congr_deriv
      (by ring)
  have hE0p : ∀ v : ℝ, HasDerivAt (fun y : ℝ => eta (L / 2 + y)) (eta1 (L / 2 + v)) v := by
    intro v
    exact ((hasDerivAt_eta (L / 2 + v)).comp v ((hasDerivAt_id v).const_add (L / 2))).congr_deriv
      (by ring)
  have hE1m : ∀ v : ℝ, HasDerivAt (fun y : ℝ => eta1 (L / 2 - y)) (-eta2 (L / 2 - v)) v := by
    intro v
    exact ((hasDerivAt_eta1 (L / 2 - v)).comp v ((hasDerivAt_id v).const_sub (L / 2))).congr_deriv
      (by ring)
  have hE1p : ∀ v : ℝ, HasDerivAt (fun y : ℝ => eta1 (L / 2 + y)) (eta2 (L / 2 + v)) v := by
    intro v
    exact ((hasDerivAt_eta1 (L / 2 + v)).comp v ((hasDerivAt_id v).const_add (L / 2))).congr_deriv
      (by ring)
  -- near the origin the taper is flat
  have hnear0 : ∀ v : ℝ, |v| < 1 →
      eta (L / 2 - |v|) = 1 ∧ eta1 (L / 2 - |v|) = 0 ∧ eta2 (L / 2 - |v|) = 0 := by
    intro v hv
    have h1 : (1:ℝ) ≤ L / 2 - |v| := by linarith
    exact ⟨eta_of_one_le h1, eta1_of_one_le h1, eta2_of_one_le h1⟩
  have hOutOpen : IsOpen {v : ℝ | L / 2 < |v|} := isOpen_lt continuous_const continuous_abs
  have hIooMem : Set.Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  -- first derivative
  have step1 : ∀ u : ℝ, HasDerivAt (taper P L) (taperD1 P L u) u := by
    intro u
    rcases lt_trichotomy |u| (L / 2) with hin | hon | hout
    · rcases lt_trichotomy u 0 with hu | hu | hu
      · have hev : taper P L =ᶠ[𝓝 u] fun y : ℝ => P (y / L) * eta (L / 2 + y) := by
          filter_upwards [Iio_mem_nhds hu] with y hy
          show P (y / L) * eta (L / 2 - |y|) = P (y / L) * eta (L / 2 + y)
          rw [abs_of_neg hy, sub_neg_eq_add]
        have heq : taperD1 P L u
            = deriv P (u / L) / L * eta (L / 2 + u) + P (u / L) * eta1 (L / 2 + u) := by
          rw [taperD1, taperSign, if_neg (not_le.mpr hu), abs_of_neg hu, sub_neg_eq_add]
          ring
        rw [heq]
        exact ((hcP u hin).mul (hE0p u)).congr_of_eventuallyEq hev
      · subst hu
        have h0 := hnear0 0 (by norm_num)
        have hev : taper P L =ᶠ[𝓝 (0:ℝ)] fun y : ℝ => P (y / L) := by
          filter_upwards [hIooMem] with y hy
          show P (y / L) * eta (L / 2 - |y|) = P (y / L)
          rw [(hnear0 y (abs_lt.mpr ⟨hy.1, hy.2⟩)).1, mul_one]
        have heq : taperD1 P L 0 = deriv P (0 / L) / L := by
          rw [taperD1, taperSign, if_pos le_rfl, h0.1, h0.2.1]
          ring
        rw [heq]
        exact (hcP 0 hin).congr_of_eventuallyEq hev
      · have hev : taper P L =ᶠ[𝓝 u] fun y : ℝ => P (y / L) * eta (L / 2 - y) := by
          filter_upwards [Ioi_mem_nhds hu] with y hy
          show P (y / L) * eta (L / 2 - |y|) = P (y / L) * eta (L / 2 - y)
          rw [abs_of_pos hy]
        have heq : taperD1 P L u
            = deriv P (u / L) / L * eta (L / 2 - u) + P (u / L) * -eta1 (L / 2 - u) := by
          rw [taperD1, taperSign, if_pos hu.le, abs_of_pos hu]
          ring
        rw [heq]
        exact ((hcP u hin).mul (hE0m u)).congr_of_eventuallyEq hev
    · rw [taperD1_eq_zero P L u hon.ge]
      rcases (abs_eq (by linarith : (0:ℝ) ≤ L / 2)).mp hon with hu | hu
      · subst hu
        refine hasDerivAt_zero_of_pow_bound (n := 2) (C := 209 * C0)
          (taper_eq_zero P L _ hon.ge) ?_
        intro y
        refine le_trans (abs_taper_le hC0nn hbP y) ?_
        have hp : abs (L / 2 - |y|) ^ 4 ≤ |y - L / 2| ^ 4 :=
          pow_le_pow_of_le (abs_nonneg _) (abs_gap_le_right L y hLpos.le) 4
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      · subst hu
        refine hasDerivAt_zero_of_pow_bound (n := 2) (C := 209 * C0)
          (taper_eq_zero P L _ hon.ge) ?_
        intro y
        refine le_trans (abs_taper_le hC0nn hbP y) ?_
        have hp : abs (L / 2 - |y|) ^ 4 ≤ |y - -(L / 2)| ^ 4 :=
          pow_le_pow_of_le (abs_nonneg _) (abs_gap_le_left L y hLpos.le) 4
        exact mul_le_mul_of_nonneg_left hp (by positivity)
    · rw [taperD1_eq_zero P L u hout.le]
      have hev : taper P L =ᶠ[𝓝 u] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [hOutOpen.mem_nhds hout] with y hy
        exact taper_eq_zero P L y (le_of_lt hy)
      exact (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq hev
  -- second derivative
  have step2 : ∀ u : ℝ, HasDerivAt (taperD1 P L) (taperD2 P L u) u := by
    intro u
    rcases lt_trichotomy |u| (L / 2) with hin | hon | hout
    · rcases lt_trichotomy u 0 with hu | hu | hu
      · have hev : taperD1 P L =ᶠ[𝓝 u] fun y : ℝ =>
            deriv P (y / L) / L * eta (L / 2 + y) + P (y / L) * eta1 (L / 2 + y) := by
          filter_upwards [Iio_mem_nhds hu] with y hy
          rw [taperD1, taperSign, if_neg (not_le.mpr hy), abs_of_neg hy, sub_neg_eq_add]
          ring
        have heq : taperD2 P L u
            = (deriv (deriv P) (u / L) / L ^ 2 * eta (L / 2 + u)
                + deriv P (u / L) / L * eta1 (L / 2 + u))
              + (deriv P (u / L) / L * eta1 (L / 2 + u) + P (u / L) * eta2 (L / 2 + u)) := by
          rw [taperD2, taperSign, if_neg (not_le.mpr hu), abs_of_neg hu, sub_neg_eq_add]
          ring
        rw [heq]
        exact (((hcP1 u hin).mul (hE0p u)).add ((hcP u hin).mul (hE1p u))).congr_of_eventuallyEq hev
      · subst hu
        have h0 := hnear0 0 (by norm_num)
        have hev : taperD1 P L =ᶠ[𝓝 (0:ℝ)] fun y : ℝ => deriv P (y / L) / L := by
          filter_upwards [hIooMem] with y hy
          have hy1 := hnear0 y (abs_lt.mpr ⟨hy.1, hy.2⟩)
          rw [taperD1, hy1.1, hy1.2.1]
          ring
        have heq : taperD2 P L 0 = deriv (deriv P) (0 / L) / L ^ 2 := by
          rw [taperD2, h0.1, h0.2.1, h0.2.2]
          ring
        rw [heq]
        exact (hcP1 0 hin).congr_of_eventuallyEq hev
      · have hev : taperD1 P L =ᶠ[𝓝 u] fun y : ℝ =>
            deriv P (y / L) / L * eta (L / 2 - y) - P (y / L) * eta1 (L / 2 - y) := by
          filter_upwards [Ioi_mem_nhds hu] with y hy
          rw [taperD1, taperSign, if_pos hy.le, abs_of_pos hy]
          ring
        have heq : taperD2 P L u
            = (deriv (deriv P) (u / L) / L ^ 2 * eta (L / 2 - u)
                + deriv P (u / L) / L * -eta1 (L / 2 - u))
              - (deriv P (u / L) / L * eta1 (L / 2 - u) + P (u / L) * -eta2 (L / 2 - u)) := by
          rw [taperD2, taperSign, if_pos hu.le, abs_of_pos hu]
          ring
        rw [heq]
        exact (((hcP1 u hin).mul (hE0m u)).sub ((hcP u hin).mul (hE1m u))).congr_of_eventuallyEq hev
    · rw [taperD2_eq_zero P L u hon.ge]
      rcases (abs_eq (by linarith : (0:ℝ) ≤ L / 2)).mp hon with hu | hu
      · subst hu
        refine hasDerivAt_zero_of_pow_bound (n := 1) (C := 209 * C1 + 140 * C0)
          (taperD1_eq_zero P L _ hon.ge) ?_
        intro y
        refine le_trans (abs_taperD1_le hL hC0nn hC1nn hbP hbP1 y) ?_
        have hp : abs (L / 2 - |y|) ^ 3 ≤ |y - L / 2| ^ 3 :=
          pow_le_pow_of_le (abs_nonneg _) (abs_gap_le_right L y hLpos.le) 3
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      · subst hu
        refine hasDerivAt_zero_of_pow_bound (n := 1) (C := 209 * C1 + 140 * C0)
          (taperD1_eq_zero P L _ hon.ge) ?_
        intro y
        refine le_trans (abs_taperD1_le hL hC0nn hC1nn hbP hbP1 y) ?_
        have hp : abs (L / 2 - |y|) ^ 3 ≤ |y - -(L / 2)| ^ 3 :=
          pow_le_pow_of_le (abs_nonneg _) (abs_gap_le_left L y hLpos.le) 3
        exact mul_le_mul_of_nonneg_left hp (by positivity)
    · rw [taperD2_eq_zero P L u hout.le]
      have hev : taperD1 P L =ᶠ[𝓝 u] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [hOutOpen.mem_nhds hout] with y hy
        exact taperD1_eq_zero P L y (le_of_lt hy)
      exact (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq hev
  -- continuity of the second derivative
  have hcontE0m : Continuous fun y : ℝ => eta (L / 2 - y) := continuous_eta.comp (by fun_prop)
  have hcontE0p : Continuous fun y : ℝ => eta (L / 2 + y) := continuous_eta.comp (by fun_prop)
  have hcontE1m : Continuous fun y : ℝ => eta1 (L / 2 - y) := continuous_eta1.comp (by fun_prop)
  have hcontE1p : Continuous fun y : ℝ => eta1 (L / 2 + y) := continuous_eta1.comp (by fun_prop)
  have hcontE2m : Continuous fun y : ℝ => eta2 (L / 2 - y) := continuous_eta2.comp (by fun_prop)
  have hcontE2p : Continuous fun y : ℝ => eta2 (L / 2 + y) := continuous_eta2.comp (by fun_prop)
  have hdivc : ∀ v : ℝ, ContinuousAt (fun y : ℝ => y / L) v := by
    intro v; fun_prop
  have step3 : Continuous (taperD2 P L) := by
    rw [continuous_iff_continuousAt]
    intro u
    rcases lt_trichotomy |u| (L / 2) with hin | hon | hout
    · have c2a : ContinuousAt (fun y : ℝ => deriv (deriv P) (y / L)) u :=
        ContinuousAt.comp (g := deriv (deriv P)) (x := u) (hPc2 u hin) (hdivc u)
      have c1a : ContinuousAt (fun y : ℝ => deriv P (y / L)) u :=
        ContinuousAt.comp (g := deriv P) (x := u) (hPc1 u hin) (hdivc u)
      have c0 : ContinuousAt (fun y : ℝ => P (y / L)) u :=
        ContinuousAt.comp (g := P) (x := u) (hPc0 u hin) (hdivc u)
      have c2 : ContinuousAt (fun y : ℝ => deriv (deriv P) (y / L) / L ^ 2) u :=
        c2a.div_const _
      have c1 : ContinuousAt (fun y : ℝ => deriv P (y / L) / L) u := c1a.div_const _
      rcases lt_trichotomy u 0 with hu | hu | hu
      · have hev2 : taperD2 P L =ᶠ[𝓝 u] fun y : ℝ =>
            deriv (deriv P) (y / L) / L ^ 2 * eta (L / 2 + y)
              + 2 * (deriv P (y / L) / L * eta1 (L / 2 + y))
              + P (y / L) * eta2 (L / 2 + y) := by
          filter_upwards [Iio_mem_nhds hu] with y hy
          rw [taperD2, taperSign, if_neg (not_le.mpr hy), abs_of_neg hy, sub_neg_eq_add]
          ring
        refine ContinuousAt.congr ?_ hev2.symm
        exact ((c2.mul hcontE0p.continuousAt).add
          ((continuousAt_const (y := (2:ℝ))).mul (c1.mul hcontE1p.continuousAt))).add
          (c0.mul hcontE2p.continuousAt)
      · subst hu
        have hev2 : taperD2 P L =ᶠ[𝓝 (0:ℝ)] fun y : ℝ => deriv (deriv P) (y / L) / L ^ 2 := by
          filter_upwards [hIooMem] with y hy
          have hy1 := hnear0 y (abs_lt.mpr ⟨hy.1, hy.2⟩)
          rw [taperD2, hy1.1, hy1.2.1, hy1.2.2]
          ring
        exact ContinuousAt.congr c2 hev2.symm
      · have hev2 : taperD2 P L =ᶠ[𝓝 u] fun y : ℝ =>
            deriv (deriv P) (y / L) / L ^ 2 * eta (L / 2 - y)
              - 2 * (deriv P (y / L) / L * eta1 (L / 2 - y))
              + P (y / L) * eta2 (L / 2 - y) := by
          filter_upwards [Ioi_mem_nhds hu] with y hy
          rw [taperD2, taperSign, if_pos hy.le, abs_of_pos hy]
          ring
        refine ContinuousAt.congr ?_ hev2.symm
        exact ((c2.mul hcontE0m.continuousAt).sub
          ((continuousAt_const (y := (2:ℝ))).mul (c1.mul hcontE1m.continuousAt))).add
          (c0.mul hcontE2m.continuousAt)
    · rcases (abs_eq (by linarith : (0:ℝ) ≤ L / 2)).mp hon with hu | hu
      · subst hu
        refine continuousAt_zero_of_pow_bound (C := 209 * C2 + 280 * C1 + 420 * C0)
          (taperD2_eq_zero P L _ hon.ge) ?_
        intro y
        refine le_trans (abs_taperD2_le hL hC0nn hC1nn hC2nn hbP hbP1 hbP2 y) ?_
        have hp : abs (L / 2 - |y|) ^ 2 ≤ |y - L / 2| ^ 2 :=
          pow_le_pow_of_le (abs_nonneg _) (abs_gap_le_right L y hLpos.le) 2
        exact mul_le_mul_of_nonneg_left hp (by positivity)
      · subst hu
        refine continuousAt_zero_of_pow_bound (C := 209 * C2 + 280 * C1 + 420 * C0)
          (taperD2_eq_zero P L _ hon.ge) ?_
        intro y
        refine le_trans (abs_taperD2_le hL hC0nn hC1nn hC2nn hbP hbP1 hbP2 y) ?_
        have hp : abs (L / 2 - |y|) ^ 2 ≤ |y - -(L / 2)| ^ 2 :=
          pow_le_pow_of_le (abs_nonneg _) (abs_gap_le_left L y hLpos.le) 2
        exact mul_le_mul_of_nonneg_left hp (by positivity)
    · have hev2 : taperD2 P L =ᶠ[𝓝 u] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [hOutOpen.mem_nhds hout] with y hy
        exact taperD2_eq_zero P L y (le_of_lt hy)
      exact ContinuousAt.congr continuousAt_const hev2.symm
  -- assembling
  have hd1 : deriv (taper P L) = taperD1 P L := funext fun u => (step1 u).deriv
  have hd2 : deriv (taperD1 P L) = taperD2 P L := funext fun u => (step2 u).deriv
  have key : ContDiff ℝ 1 (taperD1 P L) := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun u => (step2 u).differentiableAt, by rw [hd2]; exact step3⟩
  show ContDiff ℝ 2 (taper P L)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun u => (step1 u).differentiableAt, ?_⟩
  -- the middle component below is the vacuous `1 = ω → _` clause
  first
    | exact ⟨by simp, by rw [hd1]; exact key⟩
    | exact hd1 ▸ key


theorem sqrt_comp_contDiffOn_bounds (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w (Set.Ioo (-(1/2) : ℝ) (1/2)))
    (hwlow : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2), 1/5 ≤ w s)
    (hwup : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2), w s ≤ 1)
    (B1 B2 : ℝ)
    (hB1 : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv w s| ≤ B1)
    (hB2 : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2), |deriv (deriv w) s| ≤ B2) :
    ContDiffOn ℝ 2 (fun s => Real.sqrt (w s)) (Set.Ioo (-(1/2) : ℝ) (1/2)) ∧
    ∃ C0 C1 C2 : ℝ, ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2),
      |Real.sqrt (w s)| ≤ C0 ∧ |deriv (fun y => Real.sqrt (w y)) s| ≤ C1 ∧
      |deriv (deriv (fun y => Real.sqrt (w y))) s| ≤ C2 := by
  have hSopen : IsOpen (Set.Ioo (-(1/2) : ℝ) (1/2)) := isOpen_Ioo
  have hne : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2), w s ≠ 0 := by
    intro s hs
    have := hwlow s hs
    intro h; rw [h] at this; linarith
  have hdiff : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2), DifferentiableAt ℝ w s := by
    intro s hs
    exact (hwC2.contDiffAt (hSopen.mem_nhds hs)).differentiableAt (by norm_num)
  have hderiv_eq : ∀ s ∈ Set.Ioo (-(1/2) : ℝ) (1/2),
      deriv (fun y => Real.sqrt (w y)) s = deriv w s / (2 * Real.sqrt (w s)) := by
    intro s hs
    exact deriv_sqrt (hdiff s hs) (hne s hs)
  have hmem : (0:ℝ) ∈ Set.Ioo (-(1/2) : ℝ) (1/2) := by norm_num
  have hB1nn : 0 ≤ B1 := le_trans (abs_nonneg _) (hB1 0 hmem)
  have hB2nn : 0 ≤ B2 := le_trans (abs_nonneg _) (hB2 0 hmem)
  refine ⟨hwC2.sqrt hne, 1, 2 * B1 + 1, 2 * B2 + 7 * B1 ^ 2 + 1, ?_⟩
  intro s hs
  have hlow := hwlow s hs
  have hup := hwup s hs
  have hwpos : 0 < w s := by linarith
  have hr13 : (1:ℝ)/3 ≤ Real.sqrt (w s) := by
    have h : Real.sqrt ((1:ℝ)/9) ≤ Real.sqrt (w s) := Real.sqrt_le_sqrt (by linarith)
    rwa [show (1:ℝ)/9 = (1/3)^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hr1 : Real.sqrt (w s) ≤ 1 := by
    have h : Real.sqrt (w s) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hup
    rwa [Real.sqrt_one] at h
  have hrpos : 0 < Real.sqrt (w s) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hr1
  · rw [hderiv_eq s hs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (w s)),
      div_le_iff₀ (by positivity)]
    have := hB1 s hs
    nlinarith [abs_nonneg (deriv w s)]
  · -- second derivative
    have hev : deriv (fun y => Real.sqrt (w y))
        =ᶠ[nhds s] fun y => deriv w y / (2 * Real.sqrt (w y)) := by
      filter_upwards [hSopen.mem_nhds hs] with y hy using hderiv_eq y hy
    rw [Filter.EventuallyEq.deriv_eq hev]
    set A := deriv w s with hA
    set B := deriv (deriv w) s with hB
    set r := Real.sqrt (w s) with hrdef
    have hnum : HasDerivAt (deriv w) B s := by
      have h1 : ContDiffOn ℝ 1 (deriv w) (Set.Ioo (-(1/2) : ℝ) (1/2)) :=
        hwC2.deriv_of_isOpen hSopen (by norm_num)
      exact ((h1.contDiffAt (hSopen.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
    have hden : HasDerivAt (fun y => 2 * Real.sqrt (w y)) (2 * (A / (2 * r))) s :=
      (((hdiff s hs).hasDerivAt).sqrt (hne s hs)).const_mul 2
    have hdiv : HasDerivAt (fun y => deriv w y / (2 * Real.sqrt (w y)))
        ((B * (2 * r) - A * (2 * (A / (2 * r)))) / (2 * r) ^ 2) s :=
      hnum.div hden (by positivity)
    rw [hdiv.deriv]
    have hEq : (B * (2 * r) - A * (2 * (A / (2 * r)))) / (2 * r) ^ 2
        = B / (2 * r) - A ^ 2 / (4 * r ^ 3) := by
      field_simp
      ring
    rw [hEq]
    have hAb : |A| ≤ B1 := hB1 s hs
    have hBb : |B| ≤ B2 := hB2 s hs
    have hA2 : A ^ 2 ≤ B1 ^ 2 := by
      have := abs_nonneg A
      nlinarith [sq_abs A]
    have h1 : |B / (2 * r)| ≤ (3/2) * B2 := by
      rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * r), div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg B]
    have hr3 : (1:ℝ)/27 ≤ r ^ 3 := by nlinarith [sq_nonneg r, hrpos]
    have h2 : |A ^ 2 / (4 * r ^ 3)| ≤ (27/4) * B1 ^ 2 := by
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hr3 (sq_nonneg B1)]
    calc |B / (2 * r) - A ^ 2 / (4 * r ^ 3)| ≤ |B / (2 * r)| + |A ^ 2 / (4 * r ^ 3)| :=
          TaperAux.abs_sub_le' _ _
      _ ≤ (3/2) * B2 + (27/4) * B1 ^ 2 := by linarith
      _ ≤ 2 * B2 + 7 * B1 ^ 2 + 1 := by nlinarith [sq_nonneg B1]

end AristotleJ2