import Mathlib

namespace AristotleJ

noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

/-! ### Auxiliary material -/

private lemma contDiff_succ_of_hasDerivAt {f g : ℝ → ℝ} {n : ℕ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ContDiff ℝ n g) :
    ContDiff ℝ (n + 1 : ℕ) f := by
  have hd : deriv f = g := funext fun x => (hf x).deriv
  have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; ring
  rw [hcast, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hf x).differentiableAt, by simp, ?_⟩
  rw [hd]; exact hg

/-- The positive part function. -/
private noncomputable def pmax (x : ℝ) : ℝ := max 0 x

private lemma continuous_pmax : Continuous pmax := by unfold pmax; fun_prop

private lemma pmax_eq_zero_nhds {y : ℝ} (h : y < 0) : ∀ᶠ t in nhds y, pmax t = 0 := by
  filter_upwards [Iio_mem_nhds h] with t ht
  simp only [Set.mem_Iio] at ht
  simp [pmax, max_eq_left ht.le]

private lemma pmax_eq_id_nhds {y : ℝ} (h : 0 < y) : ∀ᶠ t in nhds y, pmax t = t := by
  filter_upwards [Ioi_mem_nhds h] with t ht
  simp only [Set.mem_Ioi] at ht
  simp [pmax, max_eq_right ht.le]

private lemma hasDerivAt_pmax_pow (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    HasDerivAt (fun t : ℝ => pmax t ^ (k + 1)) ((k + 1) * pmax x ^ k) x := by
  have key : ∀ y : ℝ, y ≠ 0 →
      HasDerivAt (fun t : ℝ => pmax t ^ (k + 1)) ((k + 1) * pmax y ^ k) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with h | h
    · have he : (fun t : ℝ => pmax t ^ (k + 1)) =ᶠ[nhds y] fun _ => 0 := by
        filter_upwards [pmax_eq_zero_nhds h] with t ht
        simp [ht]
      have hderiv := (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq he
      have hp : pmax y = 0 := max_eq_left h.le
      simpa [hp, zero_pow (by omega : k ≠ 0)] using hderiv
    · have he : (fun t : ℝ => pmax t ^ (k + 1)) =ᶠ[nhds y] fun t => t ^ (k + 1) := by
        filter_upwards [pmax_eq_id_nhds h] with t ht
        simp [ht]
      have h2 : HasDerivAt (fun t : ℝ => t ^ (k + 1)) ((k + 1) * y ^ k) y := by
        simpa using (hasDerivAt_pow (k + 1) y)
      have hderiv := h2.congr_of_eventuallyEq he
      have hp : pmax y = y := max_eq_right h.le
      simpa [hp] using hderiv
  rcases eq_or_ne x 0 with rfl | hx
  · exact hasDerivAt_of_hasDerivAt_of_ne key ((continuous_pmax.pow _).continuousAt)
      ((continuous_const.mul (continuous_pmax.pow k)).continuousAt)
  · exact key x hx

private lemma contDiff_pmax_sq : ContDiff ℝ 1 (fun t : ℝ => pmax t ^ 2) := by
  have h := contDiff_succ_of_hasDerivAt (n := 0)
    (f := fun t : ℝ => pmax t ^ 2) (g := fun x : ℝ => ((1:ℕ) + 1) * pmax x ^ 1)
    (fun x => hasDerivAt_pmax_pow 1 le_rfl x)
    (contDiff_zero.mpr (continuous_const.mul (continuous_pmax.pow 1)))
  simpa using h

private lemma contDiff_pmax_cube : ContDiff ℝ 2 (fun t : ℝ => pmax t ^ 3) := by
  have hg : ContDiff ℝ 1 (fun x : ℝ => ((2:ℕ) + 1) * pmax x ^ 2) :=
    contDiff_const.mul contDiff_pmax_sq
  have h := contDiff_succ_of_hasDerivAt (n := 1)
    (f := fun t : ℝ => pmax t ^ 3) (g := fun x : ℝ => ((2:ℕ) + 1) * pmax x ^ 2)
    (fun x => by simpa using hasDerivAt_pmax_pow 2 (by norm_num) x) hg
  simpa using h

/-- The derivative of `eta`. -/
private noncomputable def etaDeriv (x : ℝ) : ℝ := 140 * pmax x ^ 3 * pmax (1 - x) ^ 3

private lemma continuous_etaDeriv : Continuous etaDeriv := by
  unfold etaDeriv
  exact (continuous_const.mul (continuous_pmax.pow 3)).mul
    ((continuous_pmax.comp (continuous_const.sub continuous_id)).pow 3)

private lemma contDiff_etaDeriv : ContDiff ℝ 2 etaDeriv := by
  unfold etaDeriv
  exact (contDiff_const.mul contDiff_pmax_cube).mul
    (contDiff_pmax_cube.comp (contDiff_const.sub contDiff_id))

private lemma continuous_rampPoly : Continuous rampPoly := by
  unfold rampPoly; fun_prop

private lemma hasDerivAt_rampPoly (x : ℝ) :
    HasDerivAt rampPoly (140 * x ^ 3 * (1 - x) ^ 3) x := by
  have h : HasDerivAt (fun x : ℝ => 35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7)
      (35 * (4 * x ^ 3) - 84 * (5 * x ^ 4) + 70 * (6 * x ^ 5) - 20 * (7 * x ^ 6)) x := by
    exact ((((hasDerivAt_pow 4 x).const_mul 35).sub ((hasDerivAt_pow 5 x).const_mul 84)).add
      ((hasDerivAt_pow 6 x).const_mul 70)).sub ((hasDerivAt_pow 7 x).const_mul 20)
  have heq : 35 * (4 * x ^ 3) - 84 * (5 * x ^ 4) + 70 * (6 * x ^ 5) - 20 * (7 * x ^ 6)
      = 140 * x ^ 3 * (1 - x) ^ 3 := by ring
  rw [heq] at h
  exact h

private lemma rampPoly_zero : rampPoly 0 = 0 := by norm_num [rampPoly]

private lemma rampPoly_one : rampPoly 1 = 1 := by norm_num [rampPoly]

/-- `eta` with only the lower corner. -/
private noncomputable def eta0 (x : ℝ) : ℝ := if x ≤ 0 then 0 else rampPoly x

/-- `eta` with only the upper corner. -/
private noncomputable def eta1 (x : ℝ) : ℝ := if x ≤ 1 then rampPoly x else 1

private lemma eta0_eq : eta0 = fun x => rampPoly (pmax x) := by
  funext x
  unfold eta0 pmax
  by_cases h : x ≤ 0
  · simp [h, rampPoly_zero]
  · push_neg at h
    simp [not_le.mpr h, max_eq_right h.le]

private lemma eta1_eq : eta1 = fun x => rampPoly (min 1 x) := by
  funext x
  unfold eta1
  by_cases h : x ≤ 1
  · simp [h]
  · push_neg at h
    simp [not_le.mpr h, min_eq_left h.le, rampPoly_one]

private lemma eta_eq : eta = fun x => rampPoly (pmax (min 1 x)) := by
  funext x
  unfold eta pmax
  by_cases h0 : x ≤ 0
  · have h1 : min 1 x = x := min_eq_right (h0.trans zero_le_one)
    simp [h0, h1, rampPoly_zero]
  · push_neg at h0
    by_cases h1 : 1 ≤ x
    · have : min 1 x = 1 := min_eq_left h1
      simp [not_le.mpr h0, h1, rampPoly_one]
    · push_neg at h1
      have : min 1 x = x := min_eq_right h1.le
      simp [not_le.mpr h0, not_le.mpr h1, this, max_eq_right h0.le]

private lemma continuous_eta : Continuous eta := by
  rw [eta_eq]
  exact continuous_rampPoly.comp (continuous_pmax.comp (continuous_const.min continuous_id))

private lemma continuous_eta0 : Continuous eta0 := by
  rw [eta0_eq]; exact continuous_rampPoly.comp continuous_pmax

private lemma continuous_eta1 : Continuous eta1 := by
  rw [eta1_eq]; exact continuous_rampPoly.comp (continuous_const.min continuous_id)

private lemma hasDerivAt_eta0_zero : HasDerivAt eta0 0 0 := by
  have hg : Continuous (fun t : ℝ => 140 * pmax t ^ 3 * (1 - t) ^ 3) :=
    (continuous_const.mul (continuous_pmax.pow 3)).mul
      ((continuous_const.sub continuous_id).pow 3)
  have key : ∀ y : ℝ, y ≠ 0 → HasDerivAt eta0 (140 * pmax y ^ 3 * (1 - y) ^ 3) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with h | h
    · have he : eta0 =ᶠ[nhds y] fun _ => (0:ℝ) := by
        filter_upwards [Iio_mem_nhds h] with t ht
        simp only [Set.mem_Iio] at ht
        simp [eta0, ht.le]
      have hd := (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq he
      have hp : pmax y = 0 := max_eq_left h.le
      simpa [hp] using hd
    · have he : eta0 =ᶠ[nhds y] rampPoly := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp only [Set.mem_Ioi] at ht
        simp [eta0, not_le.mpr ht]
      have hd := (hasDerivAt_rampPoly y).congr_of_eventuallyEq he
      have hp : pmax y = y := max_eq_right h.le
      simpa [hp] using hd
  have := hasDerivAt_of_hasDerivAt_of_ne key continuous_eta0.continuousAt hg.continuousAt
  simpa [pmax] using this

private lemma hasDerivAt_eta1_one : HasDerivAt eta1 0 1 := by
  have hg : Continuous (fun t : ℝ => 140 * t ^ 3 * pmax (1 - t) ^ 3) :=
    (continuous_const.mul (continuous_pow 3)).mul
      ((continuous_pmax.comp (continuous_const.sub continuous_id)).pow 3)
  have key : ∀ y : ℝ, y ≠ 1 → HasDerivAt eta1 (140 * y ^ 3 * pmax (1 - y) ^ 3) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with h | h
    · have he : eta1 =ᶠ[nhds y] rampPoly := by
        filter_upwards [Iio_mem_nhds h] with t ht
        simp only [Set.mem_Iio] at ht
        simp [eta1, ht.le]
      have hd := (hasDerivAt_rampPoly y).congr_of_eventuallyEq he
      have hp : pmax (1 - y) = 1 - y := max_eq_right (by linarith)
      simpa [hp] using hd
    · have he : eta1 =ᶠ[nhds y] fun _ => (1:ℝ) := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp only [Set.mem_Ioi] at ht
        simp [eta1, not_le.mpr ht]
      have hd := (hasDerivAt_const y (1:ℝ)).congr_of_eventuallyEq he
      have hp : pmax (1 - y) = 0 := max_eq_left (by linarith)
      simpa [hp] using hd
  have := hasDerivAt_of_hasDerivAt_of_ne key continuous_eta1.continuousAt hg.continuousAt
  simpa [pmax] using this

private lemma hasDerivAt_eta (x : ℝ) : HasDerivAt eta (etaDeriv x) x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · have he : eta =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds h] with t ht
      simp only [Set.mem_Iio] at ht
      simp [eta, ht.le]
    have hd := (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
    have hp : pmax x = 0 := max_eq_left h.le
    simpa [etaDeriv, hp] using hd
  · have he : eta =ᶠ[nhds (0:ℝ)] eta0 := by
      filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with t ht
      simp only [Set.mem_Iio] at ht
      by_cases h0 : t ≤ 0
      · simp [eta, eta0, h0]
      · simp [eta, eta0, h0, not_le.mpr ht]
    have hd := hasDerivAt_eta0_zero.congr_of_eventuallyEq he
    have hp : pmax (0:ℝ) = 0 := max_eq_left le_rfl
    simpa [etaDeriv, hp] using hd
  · rcases lt_trichotomy x 1 with h1 | rfl | h1
    · have he : eta =ᶠ[nhds x] rampPoly := by
        filter_upwards [Ioo_mem_nhds h h1] with t ht
        simp [eta, not_le.mpr ht.1, not_le.mpr ht.2]
      have hd := (hasDerivAt_rampPoly x).congr_of_eventuallyEq he
      have hpx : pmax x = x := max_eq_right h.le
      have hpy : pmax (1 - x) = 1 - x := max_eq_right (by linarith)
      simpa [etaDeriv, hpx, hpy] using hd
    · have he : eta =ᶠ[nhds (1:ℝ)] eta1 := by
        filter_upwards [Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num)] with t ht
        simp only [Set.mem_Ioi] at ht
        by_cases h1 : t ≤ 1
        · rcases eq_or_lt_of_le h1 with rfl | h1'
          · simp [eta, eta1, not_le.mpr ht, rampPoly_one]
          · simp [eta, eta1, not_le.mpr ht, not_le.mpr h1', h1]
        · push_neg at h1
          simp [eta, eta1, not_le.mpr ht, h1.le, not_le.mpr h1]
      have hd := hasDerivAt_eta1_one.congr_of_eventuallyEq he
      simpa [etaDeriv, pmax] using hd
    · have he : eta =ᶠ[nhds x] fun _ => (1:ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with t ht
        simp only [Set.mem_Ioi] at ht
        simp [eta, not_le.mpr (lt_trans zero_lt_one ht), ht.le]
      have hd := (hasDerivAt_const x (1:ℝ)).congr_of_eventuallyEq he
      have hp : pmax (1 - x) = 0 := max_eq_left (by linarith)
      simpa [etaDeriv, hp] using hd

private lemma contDiff_eta : ContDiff ℝ 2 eta := by
  have h := contDiff_succ_of_hasDerivAt (n := 2) hasDerivAt_eta contDiff_etaDeriv
  have h3 : ContDiff ℝ (3 : ℕ) eta := by simpa using h
  exact h3.of_le (by norm_num)

private lemma eta_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) : eta x = 1 := by
  have : ¬ x ≤ 0 := by linarith
  simp [eta, this, hx]

private lemma eta_eq_zero_of_le_zero {x : ℝ} (hx : x ≤ 0) : eta x = 0 := by
  simp [eta, hx]

/-! ### Main results -/

theorem eta_radial_contDiff (L : ℝ) (hL : 8 ≤ L) :
    ContDiff ℝ 2 (fun u : ℝ => eta (L / 2 - |u|)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_trichotomy u 0 with h | rfl | h
  · have he : (fun u : ℝ => eta (L / 2 - |u|)) =ᶠ[nhds u] fun x : ℝ => eta (L / 2 + x) := by
      filter_upwards [Iio_mem_nhds h] with t ht
      simp only [Set.mem_Iio] at ht
      rw [abs_of_neg ht]; ring_nf
    refine ContDiffAt.congr_of_eventuallyEq ?_ he
    exact (contDiff_eta.comp (contDiff_const.add contDiff_id)).contDiffAt
  · have hL2 : (0:ℝ) < L / 2 - 1 := by linarith
    have he : (fun u : ℝ => eta (L / 2 - |u|)) =ᶠ[nhds (0:ℝ)] fun _ : ℝ => (1:ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) hL2] with t ht
      have : |t| < L / 2 - 1 := by simpa [Real.dist_eq] using ht
      exact eta_eq_one_of_one_le (by linarith)
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const he
  · have he : (fun u : ℝ => eta (L / 2 - |u|)) =ᶠ[nhds u] fun x : ℝ => eta (L / 2 - x) := by
      filter_upwards [Ioi_mem_nhds h] with t ht
      simp only [Set.mem_Ioi] at ht
      rw [abs_of_pos ht]
    refine ContDiffAt.congr_of_eventuallyEq ?_ he
    exact (contDiff_eta.comp (contDiff_const.sub contDiff_id)).contDiffAt

theorem taper_contDiff (w : ℝ → ℝ) (L : ℝ) (hL : 8 ≤ L)
    (hwC2 : ContDiffOn ℝ 2 w (Set.Ioo (-(3 / 5) : ℝ) (3 / 5)))
    (hwpos : ∀ s ∈ Set.Ioo (-(3 / 5) : ℝ) (3 / 5), 0 < w s) :
    ContDiff ℝ 2 (fun u : ℝ => Real.sqrt (w (u / L)) * eta (L / 2 - |u|)) := by
  have hLpos : (0:ℝ) < L := by linarith
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : |u| < 3 * L / 5
  · -- product of two `C²` functions near `u`
    have hmem : u / L ∈ Set.Ioo (-(3 / 5) : ℝ) (3 / 5) := by
      rw [abs_lt] at hu
      constructor
      · rw [lt_div_iff₀ hLpos]; linarith [hu.1]
      · rw [div_lt_iff₀ hLpos]; linarith [hu.2]
    have hwat : ContDiffAt ℝ 2 w (u / L) :=
      hwC2.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have hsqrt : ContDiffAt ℝ 2 Real.sqrt (w (u / L)) :=
      Real.contDiffAt_sqrt (ne_of_gt (hwpos _ hmem))
    have h1 : ContDiffAt ℝ 2 (fun x : ℝ => Real.sqrt (w (x / L))) u := by
      exact hsqrt.comp u (hwat.comp u (contDiffAt_id.div_const L))
    exact h1.mul ((eta_radial_contDiff L hL).contDiffAt)
  · push_neg at hu
    have hgt : L / 2 < |u| := by linarith
    have he : (fun u : ℝ => Real.sqrt (w (u / L)) * eta (L / 2 - |u|)) =ᶠ[nhds u]
        fun _ : ℝ => (0:ℝ) := by
      have hset : {x : ℝ | L / 2 < |x|} ∈ nhds u := by
        have hopen : IsOpen {x : ℝ | L / 2 < |x|} :=
          isOpen_lt continuous_const continuous_abs
        exact hopen.mem_nhds hgt
      filter_upwards [hset] with t ht
      have : eta (L / 2 - |t|) = 0 := eta_eq_zero_of_le_zero (by
        have : L / 2 < |t| := ht
        linarith)
      simp [this]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const he


end AristotleJ