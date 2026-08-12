import Zeta23Ext.TruncEst.Sums

/-!
# Lemma 2 of `PROBLEM.md`: Poisson summation

The infinite lattice sum of the interaction is a **finite** sum:

  `∑_{d ∈ ℤ} T (d*s) y = (8π/(s A²)) * ∑_{k ∈ ℤ} c2 (2πk/s) * cosh (2πky/s)^2`,

the right-hand side having only finitely many nonzero terms because `c2` is
supported in `[-1,1]`.

The proof applies Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` to the
rescaled kernel `v ↦ c2 (2πv/s) * cosh (2πvy/s)^2`, which is continuous and
compactly supported, and whose Fourier transform is `(s A²/(8π)) * T (x*s) y`,
of order `|x|^{-2}` by Lemma 1.
-/

noncomputable section

open MeasureTheory Real Complex FourierTransform Asymptotics Filter

namespace TruncEst

/-- The (even, continuous, compactly supported) kernel `w ↦ c2 w * cosh (y w)^2`. -/
def phi (y w : ℝ) : ℝ := c2 w * Real.cosh (y * w) ^ 2

lemma continuous_phi (y : ℝ) : Continuous (phi y) := by
  unfold phi; exact continuous_c2.mul (by fun_prop)

lemma phi_neg (y w : ℝ) : phi y (-w) = phi y w := by
  simp [phi, c2_neg, mul_neg, Real.cosh_neg]

lemma phi_eq_zero {y w : ℝ} (h : 1 < |w|) : phi y w = 0 := by
  simp [phi, c2_eq_zero_of_one_lt h]

lemma hasCompactSupport_phi (y : ℝ) : HasCompactSupport (phi y) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro x hx
  apply phi_eq_zero
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma integrable_phi_mul (y : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun u => f u * phi y u) := by
  apply Continuous.integrable_of_hasCompactSupport (hf.mul (continuous_phi y))
  exact HasCompactSupport.mul_left (hasCompactSupport_phi y)

/-! ### `T` as an integral over the whole line -/

lemma T_eq_full (dt y : ℝ) : T dt y = (4 / A ^ 2) * ∫ w : ℝ, Real.cos (dt * w) * phi y w := by
  unfold T
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun w => by unfold phi; ring))
  · intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [c2_eq_zero_of_one_le h]
    ring

lemma T_neg (dt y : ℝ) : T (-dt) y = T dt y := by
  unfold T
  congr 1
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp [neg_mul, Real.cos_neg]

/-! ### The Fourier transform of the rescaled kernel -/

lemma integral_sin_phi (y c : ℝ) : ∫ u : ℝ, Real.sin (c * u) * phi y u = 0 := by
  have hodd : ∀ u : ℝ, Real.sin (c * (-u)) * phi y (-u) = -(Real.sin (c * u) * phi y u) := by
    intro u; rw [phi_neg, mul_neg, Real.sin_neg]; ring
  have h := integral_neg_eq_self (fun u : ℝ => Real.sin (c * u) * phi y u) volume
  rw [show (∫ u : ℝ, Real.sin (c * (-u)) * phi y (-u)) = ∫ u : ℝ, -(Real.sin (c * u) * phi y u)
    from integral_congr_ae (Filter.Eventually.of_forall hodd)] at h
  rw [integral_neg] at h
  linarith

lemma integral_exp_phi (y c : ℝ) :
    (∫ u : ℝ, Complex.exp ((↑(-(c * u)) : ℂ) * I) * (phi y u : ℂ))
      = ((∫ u : ℝ, Real.cos (c * u) * phi y u : ℝ) : ℂ) := by
  have hexp : ∀ u : ℝ, Complex.exp ((↑(-(c * u)) : ℂ) * I) * (phi y u : ℂ)
      = ((Real.cos (c * u) * phi y u : ℝ) : ℂ)
        + ((-(Real.sin (c * u) * phi y u) : ℝ) : ℂ) * I := by
    intro u
    rw [Complex.exp_mul_I]
    push_cast
    simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have hi1 : Integrable (fun u : ℝ => ((Real.cos (c * u) * phi y u : ℝ) : ℂ)) :=
    (integrable_phi_mul y _ (by fun_prop)).ofReal
  have hi2 : Integrable (fun u : ℝ => ((-(Real.sin (c * u) * phi y u) : ℝ) : ℂ) * I) := by
    apply Integrable.mul_const
    exact ((integrable_phi_mul y _ (by fun_prop)).neg).ofReal
  have hz : (∫ a : ℝ, ((-(Real.sin (c * a) * phi y a) : ℝ) : ℂ)) = 0 := by
    rw [integral_complex_ofReal, integral_neg, integral_sin_phi]
    simp
  rw [integral_add hi1 hi2, integral_mul_const, hz, integral_complex_ofReal]
  simp

/-- The rescaled kernel, as a complex-valued function on `ℝ`. -/
def Fs (s y : ℝ) : ℝ → ℂ := fun v => ((phi y (2 * π * v / s) : ℝ) : ℂ)

lemma continuous_Fs (s y : ℝ) : Continuous (Fs s y) := by
  unfold Fs
  exact Complex.continuous_ofReal.comp ((continuous_phi y).comp (by fun_prop))

lemma Fs_eq_zero {s y : ℝ} (hs : 0 < s) {v : ℝ} (hv : s / (2 * π) < |v|) : Fs s y v = 0 := by
  have hpi : (0:ℝ) < 2 * π := by positivity
  have h : 1 < |2 * π * v / s| := by
    rw [abs_div, abs_of_pos hs, lt_div_iff₀ hs, abs_mul, abs_of_pos hpi]
    rw [div_lt_iff₀ hpi] at hv
    linarith
  simp [Fs, phi_eq_zero h]

/-- The Fourier transform of the rescaled kernel, in terms of `T`. -/
lemma fourier_Fs {s : ℝ} (hs : 0 < s) (y x : ℝ) :
    𝓕 (Fs s y) x = (((s / (2 * π)) * (A ^ 2 / 4) * T (x * s) y : ℝ) : ℂ) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have ha : (0:ℝ) < s / (2 * π) := by positivity
  have hFourier : 𝓕 (Fs s y) x
      = ∫ v : ℝ, Complex.exp ((↑(-(2 * π * (v * x))) : ℂ) * I) * (Fs s y v) := by
    rw [Real.fourier_eq']
    congr 1
    funext v
    rw [smul_eq_mul]
    congr 2
    simp [RCLike.inner_apply]
    ring
  have hcov := Measure.integral_comp_mul_left
    (fun v : ℝ => Complex.exp ((↑(-(2 * π * (v * x))) : ℂ) * I) * (Fs s y v)) (s / (2 * π))
  have hga : ∀ u : ℝ, Complex.exp ((↑(-(2 * π * ((s / (2 * π)) * u * x))) : ℂ) * I)
        * (Fs s y ((s / (2 * π)) * u))
      = Complex.exp ((↑(-(s * x * u)) : ℂ) * I) * (phi y u : ℂ) := by
    intro u
    have h1 : 2 * π * ((s / (2 * π)) * u * x) = s * x * u := by
      field_simp
    have h2 : 2 * π * ((s / (2 * π)) * u) / s = u := by
      field_simp
    simp only [Fs, h1, h2]
  have hlhs : (∫ u : ℝ, Complex.exp ((↑(-(2 * π * ((s / (2 * π)) * u * x))) : ℂ) * I)
        * (Fs s y ((s / (2 * π)) * u)))
      = ((∫ u : ℝ, Real.cos (s * x * u) * phi y u : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hga), integral_exp_phi]
  rw [hlhs, abs_of_pos (by positivity : (0:ℝ) < (s / (2 * π))⁻¹)] at hcov
  have hsne : ((s / (2 * π) : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt ha
  have hint : (∫ v : ℝ, Complex.exp ((↑(-(2 * π * (v * x))) : ℂ) * I) * (Fs s y v))
      = ((s / (2 * π) : ℝ) : ℂ) * ((∫ u : ℝ, Real.cos (s * x * u) * phi y u : ℝ) : ℂ) := by
    rw [hcov, real_smul, Complex.ofReal_inv]
    field_simp
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    push_cast
    ring_nf
  have hswap : (∫ u : ℝ, Real.cos (x * s * u) * phi y u)
      = ∫ u : ℝ, Real.cos (s * x * u) * phi y u := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    rw [mul_comm x s]
  have hT : T (x * s) y = (4 / A ^ 2) * ∫ u : ℝ, Real.cos (s * x * u) * phi y u := by
    rw [T_eq_full, hswap]
  have hA : A ^ 2 ≠ 0 := ne_of_gt A_sq_pos
  have hAne : (A : ℂ) ≠ 0 := by
    simpa using A_ne_zero
  rw [hFourier, hint, hT]
  push_cast
  field_simp

/-! ### Decay of the Fourier transform -/

lemma eventually_cocompact_abs_gt (R : ℝ) : ∀ᶠ x : ℝ in Filter.cocompact ℝ, R < |x| := by
  have h : Filter.Tendsto (fun x : ℝ => ‖x‖) (Filter.cocompact ℝ) Filter.atTop :=
    tendsto_norm_cocompact_atTop
  filter_upwards [h.eventually_gt_atTop R] with x hx
  simpa [Real.norm_eq_abs] using hx

lemma isBigO_Fs {s y : ℝ} (hs : 0 < s) :
    (Fs s y) =O[Filter.cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
  have hev : (Fs s y) =ᶠ[Filter.cocompact ℝ] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [eventually_cocompact_abs_gt (s / (2 * π))] with v hv
    exact Fs_eq_zero hs hv
  exact hev.trans_isBigO (isBigO_zero _ _)

lemma rpow_neg_two_eq (x : ℝ) : |x| ^ (-2 : ℝ) = 1 / x ^ 2 := by
  rw [Real.rpow_neg (abs_nonneg x), show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, sq_abs]
  simp [one_div]

lemma isBigO_fourier_Fs {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    (𝓕 (Fs s y)) =O[Filter.cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set K : ℝ := (s / (2 * π)) * (A ^ 2 / 4) * (Cdec / s ^ 2) with hK
  refine Asymptotics.isBigO_iff.2 ⟨K, ?_⟩
  filter_upwards [eventually_cocompact_abs_gt 0] with x hx
  have hxne : x ≠ 0 := by
    intro h; rw [h] at hx; simp at hx
  have hTle : |T (x * s) y| ≤ Cdec / (x * s) ^ 2 :=
    abs_T_le (by positivity) hy0 hy1
  have hval : Cdec / (x * s) ^ 2 = (Cdec / s ^ 2) * (1 / x ^ 2) := by
    field_simp
  have hnorm : ‖|x| ^ (-2 : ℝ)‖ = 1 / x ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
      rpow_neg_two_eq x]
  rw [fourier_Fs hs y x, Complex.norm_real, Real.norm_eq_abs, hnorm]
  have hcoef : (0:ℝ) ≤ (s / (2 * π)) * (A ^ 2 / 4) := by positivity
  calc |(s / (2 * π)) * (A ^ 2 / 4) * T (x * s) y|
      = ((s / (2 * π)) * (A ^ 2 / 4)) * |T (x * s) y| := by
        rw [abs_mul, abs_of_nonneg hcoef]
    _ ≤ ((s / (2 * π)) * (A ^ 2 / 4)) * ((Cdec / s ^ 2) * (1 / x ^ 2)) := by
        rw [← hval]
        exact mul_le_mul_of_nonneg_left hTle hcoef
    _ = K * (1 / x ^ 2) := by rw [hK]; ring

/-! ### Lemma 2 -/

/-- **Lemma 2 (Poisson summation)**. -/
theorem poisson_T {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    ∑' d : ℤ, T ((d : ℝ) * s) y
      = (8 * π / (s * A ^ 2)) * ∑' k : ℤ, c2 (2 * π * k / s) * Real.cosh (2 * π * k * y / s) ^ 2 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hA : A ^ 2 ≠ 0 := ne_of_gt A_sq_pos
  have hpoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay (f := Fs s y) (continuous_Fs s y)
    (b := 2) (by norm_num) (isBigO_Fs hs) (isBigO_fourier_Fs hs hy0 hy1) 0
  simp only [zero_add] at hpoisson
  have hRHS : ∀ n : ℤ, 𝓕 (Fs s y) n * fourier n ((0 : ℝ) : UnitAddCircle)
      = (((s / (2 * π)) * (A ^ 2 / 4) * T ((n : ℝ) * s) y : ℝ) : ℂ) := by
    intro n
    rw [fourier_Fs hs y (n : ℝ)]
    simp
  rw [tsum_congr hRHS] at hpoisson
  have hLHS : ∀ n : ℤ, Fs s y (n : ℝ) = ((phi y (2 * π * n / s) : ℝ) : ℂ) := fun n => rfl
  rw [tsum_congr hLHS] at hpoisson
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum] at hpoisson
  have hreal : (∑' n : ℤ, phi y (2 * π * n / s))
      = ∑' n : ℤ, ((s / (2 * π)) * (A ^ 2 / 4)) * T ((n : ℝ) * s) y := by
    exact_mod_cast hpoisson
  rw [tsum_mul_left] at hreal
  have hcoef : ((s / (2 * π)) * (A ^ 2 / 4)) ≠ 0 := by positivity
  have hAne : A ≠ 0 := A_ne_zero
  have hc : (8 * π / (s * A ^ 2)) * ((s / (2 * π)) * (A ^ 2 / 4)) = 1 := by
    field_simp
    ring
  have hfinal : ∑' n : ℤ, T ((n : ℝ) * s) y
      = (8 * π / (s * A ^ 2)) * ∑' n : ℤ, phi y (2 * π * n / s) := by
    calc ∑' n : ℤ, T ((n : ℝ) * s) y
        = ((8 * π / (s * A ^ 2)) * ((s / (2 * π)) * (A ^ 2 / 4))) * ∑' n : ℤ, T ((n : ℝ) * s) y := by
          rw [hc, one_mul]
      _ = (8 * π / (s * A ^ 2)) * (((s / (2 * π)) * (A ^ 2 / 4)) * ∑' n : ℤ, T ((n : ℝ) * s) y) := by
          ring
      _ = (8 * π / (s * A ^ 2)) * ∑' n : ℤ, phi y (2 * π * n / s) := by rw [← hreal]
  rw [hfinal]
  congr 1
  refine tsum_congr (fun k => ?_)
  unfold phi
  congr 2
  field_simp

/-- The equivalent form of Lemma 2: `b_inf = (dual sum) - T 0 y`. -/
theorem bInf_eq_poisson {s y : ℝ} (hs : 0 < s) (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    bInf s y
      = (8 * π / (s * A ^ 2))
          * (∑' k : ℤ, c2 (2 * π * k / s) * Real.cosh (2 * π * k * y / s) ^ 2) - T 0 y := by
  set f : ℤ → ℝ := fun d => T ((d : ℝ) * s) y with hf
  have hpos : ∀ n : ℕ, f ((n : ℤ) + 1) = T (((n : ℝ) + 1) * s) y := by
    intro n; simp [hf]
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) = T (((n : ℝ) + 1) * s) y := by
    intro n
    have : ((-((n : ℤ) + 1) : ℤ) : ℝ) * s = -(((n : ℝ) + 1) * s) := by push_cast; ring
    rw [hf]
    simp only [this]
    exact T_neg _ _
  have hs1 : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    refine (summable_T hs hy0 hy1).congr (fun n => (hpos n).symm)
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    refine (summable_T hs hy0 hy1).congr (fun n => (hneg n).symm)
  have hsplit := tsum_of_add_one_of_neg_add_one (f := f) hs1 hs2
  rw [tsum_congr hpos, tsum_congr hneg] at hsplit
  have hzero : f 0 = T 0 y := by simp [hf]
  rw [hzero] at hsplit
  have hP := poisson_T (s := s) (y := y) hs hy0 hy1
  have hsplit' : (∑' d : ℤ, T ((d : ℝ) * s) y)
      = (∑' b : ℕ, T (((b : ℝ) + 1) * s) y) + T 0 y
        + ∑' b : ℕ, T (((b : ℝ) + 1) * s) y := hsplit
  rw [hsplit'] at hP
  unfold bInf
  linarith

/-- The right-hand side of Lemma 2 is a finite sum: only `k` with `|2πk/s| < 1` contribute. -/
theorem poisson_rhs_finite {s : ℝ} (hs : 0 < s) (y : ℝ) :
    {k : ℤ | c2 (2 * π * k / s) * Real.cosh (2 * π * k * y / s) ^ 2 ≠ 0}.Finite := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  apply Set.Finite.subset (Set.finite_Icc (-⌈s / (2 * π)⌉) ⌈s / (2 * π)⌉)
  intro k hk
  simp only [Set.mem_setOf_eq, ne_eq] at hk
  by_contra hmem
  apply hk
  have habs : s / (2 * π) < |(k : ℝ)| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hmem
    have hc : (s / (2 * π)) ≤ (⌈s / (2 * π)⌉ : ℝ) := Int.le_ceil _
    have hceil : (0:ℝ) ≤ (⌈s / (2 * π)⌉ : ℝ) := by
      exact_mod_cast Int.ceil_nonneg (le_of_lt (by positivity : (0:ℝ) < s / (2 * π)))
    rcases hmem with h | h
    · have hk' : ((k : ℝ)) < -(⌈s / (2 * π)⌉ : ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hk' : ((⌈s / (2 * π)⌉ : ℝ)) < (k : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have h1 : 1 < |2 * π * (k : ℝ) / s| := by
    rw [abs_div, abs_of_pos hs, lt_div_iff₀ hs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*π)]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * π)] at habs
    linarith
  rw [c2_eq_zero_of_one_lt h1]
  ring

end TruncEst
