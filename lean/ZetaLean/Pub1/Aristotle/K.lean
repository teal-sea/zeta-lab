import Mathlib

namespace AristotleK

open MeasureTheory

noncomputable def massI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s

noncomputable def normSqI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2

/-- The bilinear form of `A = I + T_K` on `I = [-1/2, 1/2]`. -/
noncomputable def bil (K : ℝ → ℝ → ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ s in (-(1:ℝ)/2)..(1/2), f s * g s)
    + ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)

/-! ### Auxiliary lemmas -/

/-- Fubini on the square `[-1/2,1/2]²` for a continuous integrand. -/
private lemma fubini_sq (F : ℝ → ℝ → ℝ) (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), F s t)
      = ∫ t in (-(1:ℝ)/2)..(1/2), ∫ s in (-(1:ℝ)/2)..(1/2), F s t := by
  have hle : (-(1:ℝ)/2 : ℝ) ≤ 1/2 := by norm_num
  simp_rw [intervalIntegral.integral_of_le hle]
  refine MeasureTheory.integral_integral_swap ?_
  rw [MeasureTheory.Measure.prod_restrict]
  have hcpt : IsCompact (Set.Icc (-(1:ℝ)/2) (1/2) ×ˢ Set.Icc (-(1:ℝ)/2) (1/2) : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn (Function.uncurry F)
      (Set.Icc (-(1:ℝ)/2) (1/2) ×ˢ Set.Icc (-(1:ℝ)/2) (1/2)) volume := by
    have hcont : ContinuousOn (Function.uncurry F)
        (Set.Icc (-(1:ℝ)/2) (1/2) ×ˢ Set.Icc (-(1:ℝ)/2) (1/2)) :=
      (hF.congr fun _ => rfl).continuousOn
    first
      | exact hcont.integrableOn_compact hcpt
      | exact ContinuousOn.integrableOn_compact hcpt hcont
  exact h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- A parametric interval integral of a continuous function is continuous in the parameter. -/
private lemma cont_partial (F : ℝ → ℝ → ℝ) (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), F s t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_const

private lemma cont_slice (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (s : ℝ) :
    Continuous fun t => K s t := hK.comp (Continuous.prodMk continuous_const continuous_id)

private lemma bil_sub_left (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (f₁ f₂ g : ℝ → ℝ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hg : Continuous g) :
    bil K (fun x => f₁ x - f₂ x) g = bil K f₁ g - bil K f₂ g := by
  have hs := cont_slice K hK
  have i1 : IntervalIntegrable (fun s => f₁ s * g s) volume (-(1:ℝ)/2) (1/2) :=
    (by fun_prop : Continuous fun s => f₁ s * g s).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => f₂ s * g s) volume (-(1:ℝ)/2) (1/2) :=
    (by fun_prop : Continuous fun s => f₂ s * g s).intervalIntegrable _ _
  have e1 : (∫ s in (-(1:ℝ)/2)..(1/2), (f₁ s - f₂ s) * g s)
      = (∫ s in (-(1:ℝ)/2)..(1/2), f₁ s * g s) - ∫ s in (-(1:ℝ)/2)..(1/2), f₂ s * g s := by
    rw [intervalIntegral.integral_congr (g := fun s => f₁ s * g s - f₂ s * g s)
        (fun s _ => by ring), intervalIntegral.integral_sub i1 i2]
  have e2 : ∀ s : ℝ, (∫ t in (-(1:ℝ)/2)..(1/2), K s t * ((f₁ s - f₂ s) * g t))
      = (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f₁ s * g t))
        - ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f₂ s * g t) := by
    intro s
    have j1 : IntervalIntegrable (fun t => K s t * (f₁ s * g t)) volume (-(1:ℝ)/2) (1/2) :=
      ((hs s).mul (continuous_const.mul hg) : Continuous fun t => K s t * (f₁ s * g t)
        ).intervalIntegrable _ _
    have j2 : IntervalIntegrable (fun t => K s t * (f₂ s * g t)) volume (-(1:ℝ)/2) (1/2) :=
      ((hs s).mul (continuous_const.mul hg) : Continuous fun t => K s t * (f₂ s * g t)
        ).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr
        (g := fun t => K s t * (f₁ s * g t) - K s t * (f₂ s * g t)) (fun t _ => by ring),
      intervalIntegral.integral_sub j1 j2]
  have k1 : IntervalIntegrable
      (fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f₁ s * g t)) volume (-(1:ℝ)/2) (1/2) :=
    (cont_partial (fun s t => K s t * (f₁ s * g t)) (by fun_prop)).intervalIntegrable _ _
  have k2 : IntervalIntegrable
      (fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f₂ s * g t)) volume (-(1:ℝ)/2) (1/2) :=
    (cont_partial (fun s t => K s t * (f₂ s * g t)) (by fun_prop)).intervalIntegrable _ _
  simp only [bil, e1]
  rw [intervalIntegral.integral_congr
      (g := fun s => (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f₁ s * g t))
        - ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f₂ s * g t)) (fun s _ => e2 s),
    intervalIntegral.integral_sub k1 k2]
  ring

private lemma bil_sub_right (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (f g₁ g₂ : ℝ → ℝ) (hf : Continuous f) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) :
    bil K f (fun x => g₁ x - g₂ x) = bil K f g₁ - bil K f g₂ := by
  have hs := cont_slice K hK
  have i1 : IntervalIntegrable (fun s => f s * g₁ s) volume (-(1:ℝ)/2) (1/2) :=
    (by fun_prop : Continuous fun s => f s * g₁ s).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => f s * g₂ s) volume (-(1:ℝ)/2) (1/2) :=
    (by fun_prop : Continuous fun s => f s * g₂ s).intervalIntegrable _ _
  have e1 : (∫ s in (-(1:ℝ)/2)..(1/2), f s * (g₁ s - g₂ s))
      = (∫ s in (-(1:ℝ)/2)..(1/2), f s * g₁ s) - ∫ s in (-(1:ℝ)/2)..(1/2), f s * g₂ s := by
    rw [intervalIntegral.integral_congr (g := fun s => f s * g₁ s - f s * g₂ s)
        (fun s _ => by ring), intervalIntegral.integral_sub i1 i2]
  have e2 : ∀ s : ℝ, (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * (g₁ t - g₂ t)))
      = (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g₁ t))
        - ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g₂ t) := by
    intro s
    have j1 : IntervalIntegrable (fun t => K s t * (f s * g₁ t)) volume (-(1:ℝ)/2) (1/2) :=
      ((hs s).mul (continuous_const.mul hg₁) : Continuous fun t => K s t * (f s * g₁ t)
        ).intervalIntegrable _ _
    have j2 : IntervalIntegrable (fun t => K s t * (f s * g₂ t)) volume (-(1:ℝ)/2) (1/2) :=
      ((hs s).mul (continuous_const.mul hg₂) : Continuous fun t => K s t * (f s * g₂ t)
        ).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr
        (g := fun t => K s t * (f s * g₁ t) - K s t * (f s * g₂ t)) (fun t _ => by ring),
      intervalIntegral.integral_sub j1 j2]
  have k1 : IntervalIntegrable
      (fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g₁ t)) volume (-(1:ℝ)/2) (1/2) :=
    (cont_partial (fun s t => K s t * (f s * g₁ t)) (by fun_prop)).intervalIntegrable _ _
  have k2 : IntervalIntegrable
      (fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g₂ t)) volume (-(1:ℝ)/2) (1/2) :=
    (cont_partial (fun s t => K s t * (f s * g₂ t)) (by fun_prop)).intervalIntegrable _ _
  simp only [bil, e1]
  rw [intervalIntegral.integral_congr
      (g := fun s => (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g₁ t))
        - ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g₂ t)) (fun s _ => e2 s),
    intervalIntegral.integral_sub k1 k2]
  ring

private lemma bil_smul_left (K : ℝ → ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    bil K (fun x => c * f x) g = c * bil K f g := by
  have e1 : (∫ s in (-(1:ℝ)/2)..(1/2), (c * f s) * g s)
      = c * ∫ s in (-(1:ℝ)/2)..(1/2), f s * g s := by
    rw [intervalIntegral.integral_congr (g := fun s => c * (f s * g s)) (fun s _ => by ring),
      intervalIntegral.integral_const_mul]
  have e2 : ∀ s : ℝ, (∫ t in (-(1:ℝ)/2)..(1/2), K s t * ((c * f s) * g t))
      = c * ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t) := by
    intro s
    rw [intervalIntegral.integral_congr (g := fun t => c * (K s t * (f s * g t)))
        (fun t _ => by ring), intervalIntegral.integral_const_mul]
  simp only [bil, e1]
  rw [intervalIntegral.integral_congr
      (g := fun s => c * ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)) (fun s _ => e2 s),
    intervalIntegral.integral_const_mul]
  ring

private lemma bil_smul_right (K : ℝ → ℝ → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    bil K f (fun x => c * g x) = c * bil K f g := by
  have e1 : (∫ s in (-(1:ℝ)/2)..(1/2), f s * (c * g s))
      = c * ∫ s in (-(1:ℝ)/2)..(1/2), f s * g s := by
    rw [intervalIntegral.integral_congr (g := fun s => c * (f s * g s)) (fun s _ => by ring),
      intervalIntegral.integral_const_mul]
  have e2 : ∀ s : ℝ, (∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * (c * g t)))
      = c * ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t) := by
    intro s
    rw [intervalIntegral.integral_congr (g := fun t => c * (K s t * (f s * g t)))
        (fun t _ => by ring), intervalIntegral.integral_const_mul]
  simp only [bil, e1]
  rw [intervalIntegral.integral_congr
      (g := fun s => c * ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t)) (fun s _ => e2 s),
    intervalIntegral.integral_const_mul]
  ring

/-! ### Main results -/

theorem bil_symm (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hsymm : ∀ s t, K s t = K t s) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    bil K f g = bil K g f := by
  have e1 : (∫ s in (-(1:ℝ)/2)..(1/2), f s * g s)
      = ∫ s in (-(1:ℝ)/2)..(1/2), g s * f s :=
    intervalIntegral.integral_congr (fun s _ => by ring)
  have e2 : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (f s * g t))
      = ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (g s * f t) := by
    rw [fubini_sq (fun s t => K s t * (f s * g t)) (by fun_prop)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact intervalIntegral.integral_congr (fun y _ => by rw [hsymm y x]; ring)
  simp only [bil, e1, e2]

theorem bil_cauchy_schwarz (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hsymm : ∀ s t, K s t = K t s)
    (hpsd : ∀ v : ℝ → ℝ, Continuous v → 0 ≤ bil K v v)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (bil K f g) ^ 2 ≤ bil K f f * bil K g g := by
  have hquad : ∀ c : ℝ,
      0 ≤ bil K g g * (c * c) + (-2 * bil K f g) * c + bil K f f := by
    intro c
    have hcg : Continuous fun x => c * g x := continuous_const.mul hg
    have hd : Continuous fun x => f x - c * g x := hf.sub hcg
    have h0 := hpsd _ hd
    have h1 : bil K (fun x => f x - c * g x) (fun x => f x - c * g x)
        = bil K f (fun x => f x - c * g x) - bil K (fun x => c * g x) (fun x => f x - c * g x) :=
      bil_sub_left K hK f (fun x => c * g x) _ hf hcg hd
    have h2 : bil K f (fun x => f x - c * g x) = bil K f f - bil K f (fun x => c * g x) :=
      bil_sub_right K hK f f (fun x => c * g x) hf hf hcg
    have h3 : bil K f (fun x => c * g x) = c * bil K f g := bil_smul_right K c f g
    have h4 : bil K (fun x => c * g x) (fun x => f x - c * g x)
        = c * bil K g (fun x => f x - c * g x) := bil_smul_left K c g _
    have h5 : bil K g (fun x => f x - c * g x) = bil K g f - bil K g (fun x => c * g x) :=
      bil_sub_right K hK g f (fun x => c * g x) hg hf hcg
    have h6 : bil K g (fun x => c * g x) = c * bil K g g := bil_smul_right K c g g
    have h7 : bil K g f = bil K f g := (bil_symm K hK hsymm f g hf hg).symm
    rw [h1, h2, h3, h4, h5, h6, h7] at h0
    nlinarith [h0]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

theorem bil_repr (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hsymm : ∀ s t, K s t = K t s) (w : ℝ → ℝ) (hw : Continuous w)
    (heq : ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t) = 1)
    (v : ℝ → ℝ) (hv : Continuous v) :
    bil K w v = massI v := by
  have inner : ∀ x : ℝ, (∫ y in (-(1:ℝ)/2)..(1/2), K y x * (w y * v x)) = v x * (1 - w x) := by
    intro x
    have hx : (∫ y in (-(1:ℝ)/2)..(1/2), K y x * (w y * v x))
        = v x * ∫ y in (-(1:ℝ)/2)..(1/2), K x y * w y := by
      rw [intervalIntegral.integral_congr (g := fun y => v x * (K x y * w y))
          (fun y _ => by rw [hsymm y x]; ring), intervalIntegral.integral_const_mul]
    rw [hx]
    have := heq x
    have : (∫ y in (-(1:ℝ)/2)..(1/2), K x y * w y) = 1 - w x := by linarith
    rw [this]
  have e2 : (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (w s * v t))
      = ∫ x in (-(1:ℝ)/2)..(1/2), v x * (1 - w x) := by
    rw [fubini_sq (fun s t => K s t * (w s * v t)) (by fun_prop)]
    exact intervalIntegral.integral_congr (fun x _ => inner x)
  have i1 : IntervalIntegrable v volume (-(1:ℝ)/2) (1/2) := hv.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => w x * v x) volume (-(1:ℝ)/2) (1/2) :=
    (by fun_prop : Continuous fun x => w x * v x).intervalIntegrable _ _
  have e3 : (∫ x in (-(1:ℝ)/2)..(1/2), v x * (1 - w x))
      = (∫ x in (-(1:ℝ)/2)..(1/2), v x) - ∫ x in (-(1:ℝ)/2)..(1/2), w x * v x := by
    rw [intervalIntegral.integral_congr (g := fun x => v x - w x * v x) (fun x _ => by ring),
      intervalIntegral.integral_sub i1 i2]
  simp only [bil, massI, e2, e3]
  ring


end AristotleK