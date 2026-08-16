import Mathlib

namespace AristotleM

open MeasureTheory

noncomputable def massI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s

noncomputable def normSqI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2

/-- The bilinear form of `A = I + T_K` on `I = [-1/2, 1/2]`. -/
noncomputable def bil (K : ℝ → ℝ → ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ s in (-(1:ℝ)/2)..(1/2), f s * g s)
    + ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)

section Aux

/-- The interval `I = [-1/2, 1/2]` is nondegenerate. -/
private lemma Ile : (-(1:ℝ)/2) ≤ (1:ℝ)/2 := by norm_num

/-- Continuous functions are integrable on `I`. -/
private lemma II {u : ℝ → ℝ} (hu : Continuous u) :
    IntervalIntegrable u volume (-(1:ℝ)/2) (1/2) := hu.intervalIntegrable _ _

private lemma normSqI_nonneg (v : ℝ → ℝ) : 0 ≤ normSqI v :=
  intervalIntegral.integral_nonneg Ile fun _ _ => sq_nonneg _

/-- Continuity of a partial integral in the remaining variable. -/
private lemma contOuter {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), F s t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF _ _

/-- Fubini for continuous functions on the square `[a,b]²`. -/
private lemma swapII (F : ℝ → ℝ → ℝ) (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ s in a..b, ∫ t in a..b, F s t) = ∫ s in a..b, ∫ t in a..b, F t s := by
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b))) := by
    rw [Measure.prod_restrict]
    apply IntegrableOn.mono_set (t := Set.Icc a b ×ˢ Set.Icc a b)
    · exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    · exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  simp_rw [intervalIntegral.integral_of_le hab]
  exact integral_integral_swap hint

/-- Additivity of the double integral over `I × I`. -/
private lemma dadd (F G : ℝ → ℝ → ℝ) (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), F s t)
      + (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), G s t)
      = ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), (F s t + G s t) := by
  rw [← intervalIntegral.integral_add (II (contOuter hF)) (II (contOuter hG))]
  exact intervalIntegral.integral_congr fun s _ =>
    (intervalIntegral.integral_add (II (by fun_prop)) (II (by fun_prop))).symm

/-- Subtractivity of the double integral over `I × I`. -/
private lemma dsub (F G : ℝ → ℝ → ℝ) (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), F s t)
      - (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), G s t)
      = ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), (F s t - G s t) := by
  rw [← intervalIntegral.integral_sub (II (contOuter hF)) (II (contOuter hG))]
  exact intervalIntegral.integral_congr fun s _ =>
    (intervalIntegral.integral_sub (II (by fun_prop)) (II (by fun_prop))).symm

/-- Weighted arithmetic-geometric mean inequality. -/
private lemma amgm_mul (x y lam : ℝ) (hlam : 0 < lam) : |x * y| ≤ (lam * x ^ 2 + y ^ 2 / lam) / 2 := by
  rw [abs_mul, le_div_iff₀ (by norm_num : (0:ℝ) < 2), ← sub_nonneg]
  have h : lam * x ^ 2 + y ^ 2 / lam - |x| * |y| * 2 = (lam * |x| - |y|) ^ 2 / lam := by
    rw [← sq_abs x, ← sq_abs y]; field_simp; try ring
  rw [h]; positivity

/-- Optimising the scaling parameter in a family of bounds. -/
private lemma sqrt_opt {X A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∀ lam : ℝ, 0 < lam → X ≤ C / 2 * (lam * A + B / lam)) :
    X ≤ C * Real.sqrt A * Real.sqrt B := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have := h 1 one_pos
    simp [← hC0] at this ⊢
    linarith [this]
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hsa : Real.sqrt A = 0 := by rw [← hA0]; simp
    rw [hsa]
    simp only [mul_zero, zero_mul]
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hB with hB0 | hBpos
    · have := h 1 one_pos
      rw [← hA0, ← hB0] at this
      norm_num at this
      linarith
    · have hlam : 0 < C * B / X := by positivity
      have hx := h _ hlam
      rw [← hA0] at hx
      have hBX : B / (C * B / X) = X / C := by field_simp; try ring
      rw [hBX] at hx
      have : X ≤ X / 2 := by
        calc X ≤ C / 2 * (0 + X / C) := by simpa using hx
          _ = X / 2 := by field_simp; try ring
      linarith
  · rcases eq_or_lt_of_le hB with hB0 | hBpos
    · have hsb : Real.sqrt B = 0 := by rw [← hB0]; simp
      rw [hsb, mul_zero]
      by_contra hcon
      push_neg at hcon
      have hlam : 0 < X / (C * A) := by positivity
      have hx := h _ hlam
      rw [← hB0] at hx
      have : X ≤ X / 2 := by
        calc X ≤ C / 2 * (X / (C * A) * A + 0 / (X / (C * A))) := hx
          _ = X / 2 := by field_simp; try ring
      linarith
    · set sa := Real.sqrt A with hsa
      set sb := Real.sqrt B with hsb
      have hsapos : 0 < sa := Real.sqrt_pos.mpr hApos
      have hsbpos : 0 < sb := Real.sqrt_pos.mpr hBpos
      have hsa2 : sa ^ 2 = A := by
        rw [hsa]; first | exact Real.sq_sqrt hA | (rw [sq]; exact Real.mul_self_sqrt hA)
      have hsb2 : sb ^ 2 = B := by
        rw [hsb]; first | exact Real.sq_sqrt hB | (rw [sq]; exact Real.mul_self_sqrt hB)
      have hx := h (sb / sa) (by positivity)
      have heq : C / 2 * (sb / sa * A + B / (sb / sa)) = C * sa * sb := by
        rw [← hsa2, ← hsb2]; field_simp; try ring
      linarith [heq ▸ hx]

/-- Pointwise (in `s`) Schur-type bound for the inner integral. -/
private lemma inner_bound (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t) (f g : ℝ → ℝ) (hg : Continuous g)
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) :
    |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|
      ≤ (lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t)
        + (1 / (2 * lam)) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2) := by
  have hKs : Continuous fun t => K s t :=
    hK.comp (by fun_prop : Continuous fun t : ℝ => ((s, t) : ℝ × ℝ))
  have step : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|
      ≤ ∫ t in (-(1:ℝ)/2)..(1/2), K s t * ((lam * f s ^ 2 + g t ^ 2 / lam) / 2) := by
    calc |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|
        ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K s t * (f s * g t)| :=
          intervalIntegral.abs_integral_le_integral_abs Ile
      _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), K s t * ((lam * f s ^ 2 + g t ^ 2 / lam) / 2) := by
          apply intervalIntegral.integral_mono_on Ile (II (by fun_prop)) (II (by fun_prop))
          intro t _
          rw [abs_mul, abs_of_nonneg (hKnn s t)]
          exact mul_le_mul_of_nonneg_left (amgm_mul (f s) (g t) lam hlam) (hKnn s t)
  have heq : (∫ t in (-(1:ℝ)/2)..(1/2), K s t * ((lam * f s ^ 2 + g t ^ 2 / lam) / 2))
      = (lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t)
        + (1 / (2 * lam)) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2) := by
    have hpt : ∀ t : ℝ, K s t * ((lam * f s ^ 2 + g t ^ 2 / lam) / 2)
        = (lam * f s ^ 2 / 2) * K s t + (1 / (2 * lam)) * (K s t * g t ^ 2) := by
      intro t; field_simp; try ring
    simp only [hpt]
    rw [intervalIntegral.integral_add (II (by fun_prop)) (II (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  linarith [heq ▸ step]

/-- Schur bound for the kernel part of the form. -/
private lemma kernel_bound (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t) (hsymm : ∀ s t, K s t = K t s)
    (θ : ℝ) (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K s t) ≤ θ)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (lam : ℝ) (hlam : 0 < lam) :
    |∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|
      ≤ θ / 2 * (lam * normSqI f + normSqI g / lam) := by
  have hrowC : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t := contOuter hK
  have hKswap : Continuous fun p : ℝ × ℝ => K p.2 p.1 := hK.comp continuous_swap
  have hcolC : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K t s := contOuter hKswap
  have hgC : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2 :=
    contOuter (by fun_prop)
  have hcol : ∀ s : ℝ, (∫ t in (-(1:ℝ)/2)..(1/2), K t s) ≤ θ := by
    intro s
    have h : (∫ t in (-(1:ℝ)/2)..(1/2), K t s) = ∫ t in (-(1:ℝ)/2)..(1/2), K s t :=
      intervalIntegral.integral_congr fun t _ => (hsymm s t).symm
    rw [h]; exact hrow s
  -- first term
  have hT1 : (∫ s in (-(1:ℝ)/2)..(1/2),
      (lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t)) ≤ (lam * θ / 2) * normSqI f := by
    have h1 : (∫ s in (-(1:ℝ)/2)..(1/2),
        (lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t))
        ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (lam * θ / 2) * f s ^ 2 := by
      apply intervalIntegral.integral_mono_on Ile (II (by fun_prop)) (II (by fun_prop))
      intro s _
      have hnn : (0:ℝ) ≤ lam * f s ^ 2 / 2 := by positivity
      have h := mul_le_mul_of_nonneg_left (hrow s) hnn
      have heq : lam * f s ^ 2 / 2 * θ = lam * θ / 2 * f s ^ 2 := by ring
      rw [heq] at h
      exact h
    rwa [intervalIntegral.integral_const_mul] at h1
  -- second term
  have hT2 : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2)
      ≤ θ * normSqI g := by
    have hswap : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2)
        = ∫ s in (-(1:ℝ)/2)..(1/2), (∫ t in (-(1:ℝ)/2)..(1/2), K t s) * g s ^ 2 := by
      rw [swapII (fun s t => K s t * g t ^ 2) (by fun_prop) _ _ Ile]
      exact intervalIntegral.integral_congr fun s _ => intervalIntegral.integral_mul_const _ _
    rw [hswap]
    have h2 : (∫ s in (-(1:ℝ)/2)..(1/2), (∫ t in (-(1:ℝ)/2)..(1/2), K t s) * g s ^ 2)
        ≤ ∫ s in (-(1:ℝ)/2)..(1/2), θ * g s ^ 2 := by
      apply intervalIntegral.integral_mono_on Ile (II (by fun_prop)) (II (by fun_prop))
      intro s _
      exact mul_le_mul_of_nonneg_right (hcol s) (sq_nonneg _)
    rwa [intervalIntegral.integral_const_mul] at h2
  -- combine
  have hmain : |∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|
      ≤ (∫ s in (-(1:ℝ)/2)..(1/2), (lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t))
        + (1 / (2 * lam)) *
            (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2) := by
    have h1 : |∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|
        ≤ ∫ s in (-(1:ℝ)/2)..(1/2), |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)| :=
      intervalIntegral.abs_integral_le_integral_abs Ile
    have h2 : (∫ s in (-(1:ℝ)/2)..(1/2), |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)|)
        ≤ ∫ s in (-(1:ℝ)/2)..(1/2), ((lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t)
            + (1 / (2 * lam)) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2)) := by
      apply intervalIntegral.integral_mono_on Ile
        (II ((contOuter (by fun_prop)).abs)) (II (by fun_prop))
      intro s _
      exact inner_bound K hK hKnn f g hg lam hlam s
    have h3 : (∫ s in (-(1:ℝ)/2)..(1/2), ((lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t)
            + (1 / (2 * lam)) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2)))
        = (∫ s in (-(1:ℝ)/2)..(1/2), (lam * f s ^ 2 / 2) * (∫ t in (-(1:ℝ)/2)..(1/2), K s t))
          + (1 / (2 * lam)) *
              (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t ^ 2) := by
      rw [intervalIntegral.integral_add (II (by fun_prop)) (II (by fun_prop)),
        intervalIntegral.integral_const_mul]
    linarith [h3 ▸ h2]
  have hθ : 0 ≤ θ :=
    le_trans (intervalIntegral.integral_nonneg Ile fun t _ => hKnn 0 t) (hrow 0)
  have hBnn : 0 ≤ normSqI g := normSqI_nonneg g
  have hfin : (lam * θ / 2) * normSqI f + (1 / (2 * lam)) * (θ * normSqI g)
      = θ / 2 * (lam * normSqI f + normSqI g / lam) := by
    field_simp; try ring
  have hpos : (0:ℝ) ≤ 1 / (2 * lam) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hT2 hpos]

end Aux

theorem mass_diff_le (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    |massI f - massI g| ≤ Real.sqrt (normSqI (fun s => f s - g s)) := by
  have hmass : massI f - massI g = ∫ s in (-(1:ℝ)/2)..(1/2), (f s - g s) := by
    rw [massI, massI, ← intervalIntegral.integral_sub (II hf) (II hg)]
  rw [hmass]
  have key : ∀ lam : ℝ, 0 < lam →
      |∫ s in (-(1:ℝ)/2)..(1/2), (f s - g s)|
        ≤ 1 / 2 * (lam * normSqI (fun s => f s - g s) + 1 / lam) := by
    intro lam hlam
    have h1 : |∫ s in (-(1:ℝ)/2)..(1/2), (f s - g s)| ≤ ∫ s in (-(1:ℝ)/2)..(1/2), |f s - g s| :=
      intervalIntegral.abs_integral_le_integral_abs Ile
    have h2 : (∫ s in (-(1:ℝ)/2)..(1/2), |f s - g s|)
        ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (lam * (f s - g s) ^ 2 + 1 / lam) / 2 := by
      apply intervalIntegral.integral_mono_on Ile (II (by fun_prop)) (II (by fun_prop))
      intro x _
      simpa using amgm_mul (f x - g x) 1 lam hlam
    have h3 : (∫ s in (-(1:ℝ)/2)..(1/2), (lam * (f s - g s) ^ 2 + 1 / lam) / 2)
        = 1 / 2 * (lam * normSqI (fun s => f s - g s) + 1 / lam) := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add (II (by fun_prop)) (II (by fun_prop)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp [normSqI]
      try ring
    linarith
  have := sqrt_opt (X := |∫ s in (-(1:ℝ)/2)..(1/2), (f s - g s)|)
    (A := normSqI fun s => f s - g s) (B := 1) (C := 1)
    (normSqI_nonneg _) zero_le_one zero_le_one (by simpa using key)
  simpa using this

theorem bil_sub (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hsymm : ∀ s t, K s t = K t s) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    bil K f f - bil K g g
      = bil K (fun s => f s - g s) (fun s => f s + g s) := by
  have hkey : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t))
      = ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (g s * f t) := by
    rw [swapII (fun s t => K s t * (g s * f t)) (by fun_prop) _ _ Ile]
    have hpt : ∀ s t : ℝ, K s t * (f s * g t) = K t s * (g t * f s) := by
      intro s t; rw [hsymm t s]; ring
    simp only [hpt]
  have hA : (∫ s in (-(1:ℝ)/2)..(1/2), f s * f s) - (∫ s in (-(1:ℝ)/2)..(1/2), g s * g s)
      = ∫ s in (-(1:ℝ)/2)..(1/2), (f s - g s) * (f s + g s) := by
    rw [← intervalIntegral.integral_sub (II (by fun_prop)) (II (by fun_prop))]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show f s * f s - g s * g s = (f s - g s) * (f s + g s)
    ring
  have hcross : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2),
      (K s t * (f s * g t) - K s t * (g s * f t))) = 0 := by
    rw [← dsub _ _ (by fun_prop) (by fun_prop), hkey, sub_self]
  have hB : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * f t))
      - (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (g s * g t))
      = ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2),
          K s t * ((f s - g s) * (f t + g t)) := by
    rw [dsub _ _ (by fun_prop) (by fun_prop)]
    have hpt : ∀ s t : ℝ, K s t * ((f s - g s) * (f t + g t))
        = (K s t * (f s * f t) - K s t * (g s * g t))
          + (K s t * (f s * g t) - K s t * (g s * f t)) := by intro s t; ring
    simp only [hpt]
    rw [← dadd _ _ (by fun_prop) (by fun_prop), hcross, add_zero]
  simp only [bil]
  linarith

theorem bil_bound (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t) (hsymm : ∀ s t, K s t = K t s)
    (θ : ℝ) (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K s t) ≤ θ)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    |bil K f g| ≤ (1 + θ) * Real.sqrt (normSqI f) * Real.sqrt (normSqI g) := by
  have hθ : 0 ≤ θ :=
    le_trans (intervalIntegral.integral_nonneg Ile fun t _ => hKnn 0 t) (hrow 0)
  have key : ∀ lam : ℝ, 0 < lam →
      |bil K f g| ≤ (1 + θ) / 2 * (lam * normSqI f + normSqI g / lam) := by
    intro lam hlam
    have hdiag : |∫ s in (-(1:ℝ)/2)..(1/2), f s * g s|
        ≤ 1 / 2 * (lam * normSqI f + normSqI g / lam) := by
      have h1 : |∫ s in (-(1:ℝ)/2)..(1/2), f s * g s|
          ≤ ∫ s in (-(1:ℝ)/2)..(1/2), |f s * g s| :=
        intervalIntegral.abs_integral_le_integral_abs Ile
      have h2 : (∫ s in (-(1:ℝ)/2)..(1/2), |f s * g s|)
          ≤ ∫ s in (-(1:ℝ)/2)..(1/2), ((lam / 2) * f s ^ 2 + (1 / (2 * lam)) * g s ^ 2) := by
        apply intervalIntegral.integral_mono_on Ile (II (by fun_prop)) (II (by fun_prop))
        intro s _
        have h := amgm_mul (f s) (g s) lam hlam
        have heq : (lam * f s ^ 2 + g s ^ 2 / lam) / 2
            = (lam / 2) * f s ^ 2 + (1 / (2 * lam)) * g s ^ 2 := by field_simp; try ring
        linarith [heq ▸ h]
      have h3 : (∫ s in (-(1:ℝ)/2)..(1/2), ((lam / 2) * f s ^ 2 + (1 / (2 * lam)) * g s ^ 2))
          = (lam / 2) * normSqI f + (1 / (2 * lam)) * normSqI g := by
        rw [intervalIntegral.integral_add (II (by fun_prop)) (II (by fun_prop)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rfl
      have h4 : (lam / 2) * normSqI f + (1 / (2 * lam)) * normSqI g
          = 1 / 2 * (lam * normSqI f + normSqI g / lam) := by field_simp; try ring
      linarith [h3 ▸ h2]
    have hker := kernel_bound K hK hKnn hsymm θ hrow f g hf hg lam hlam
    have : |bil K f g| ≤ |∫ s in (-(1:ℝ)/2)..(1/2), f s * g s|
        + |∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)| := by
      have hsplit : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y => by
        first | exact abs_add_le x y | exact abs_add x y
      simpa [bil] using hsplit (∫ s in (-(1:ℝ)/2)..(1/2), f s * g s)
        (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t))
    have hsum : 1 / 2 * (lam * normSqI f + normSqI g / lam)
        + θ / 2 * (lam * normSqI f + normSqI g / lam)
        = (1 + θ) / 2 * (lam * normSqI f + normSqI g / lam) := by ring
    linarith
  exact sqrt_opt (normSqI_nonneg f) (normSqI_nonneg g) (by linarith) key


end AristotleM