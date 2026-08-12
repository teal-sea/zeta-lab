import Zeta23Ext.EForm2.Bridge

/-!
# Real estimates

* `Aconst_ge`, `Aconst_le_one` : `11/12 ≤ A ≤ 1`.
* `phiR_lower` : `phiR r ≥ -27/100` for every real `r` (a global lower bound for the
  cosine transform of the window).
* `Shq_lower` : `Shq y ≥ y²/16`.
* `Qim_sq_le_unif` : the Cauchy–Schwarz damage bound `Qim y s ^ 2 ≤ ((A + 27/100)/2) * Shq y`.
* `Qim_far` : the far-field decay `|Qim y s| ≤ (14/5) * y / |s|`.
-/

open scoped BigOperators
open MeasureTheory

namespace Retention

/-! ### Elementary bounds on the window and on `sinh`, `cosh` -/

/-- On the support of the window, `cos (√2 u) ≥ 3/4`. -/
lemma cos_win_ge {u : ℝ} (hu : u ∈ Set.Icc (-(1/2:ℝ)) (1/2)) :
    3/4 ≤ Real.cos (Real.sqrt 2 * u) := by
  simp only [Set.mem_Icc] at hu
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 2 * u) ^ 2 = 2 * u ^ 2 := by rw [mul_pow, h2]
  have h4 := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * u)
  rw [h3] at h4
  nlinarith [hu.1, hu.2]

lemma exp_le_inv_one_sub {z : ℝ} (h : z < 1) : Real.exp z ≤ 1 / (1 - z) := by
  have h1 : (1 : ℝ) - z ≤ Real.exp (-z) := by
    have := Real.add_one_le_exp (-z); linarith
  have h2 : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : (0:ℝ) < 1 - z := by linarith
  rw [le_div_iff₀ h3]
  nlinarith [Real.exp_pos (-z), Real.exp_pos z]

/-- `sinh z ≤ (7/6) z` on `[0, 1/4]`. -/
lemma sinh_le_quarter {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1/4) : Real.sinh z ≤ (7/6) * z := by
  have hs : Real.sinh z = (Real.exp z - Real.exp (-z)) / 2 := Real.sinh_eq z
  have hu : Real.exp z ≤ 1 / (1 - z) := exp_le_inv_one_sub (by linarith)
  have hl : (1:ℝ) - z ≤ Real.exp (-z) := by have := Real.add_one_le_exp (-z); linarith
  have h3 : (0:ℝ) < 1 - z := by linarith
  rw [hs, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have : 1 / (1 - z) ≤ (7/6) * z * 2 + (1 - z) := by
    rw [div_le_iff₀ h3]
    nlinarith
  linarith

/-- `|sinh z| ≤ (7/6) |z|` on `[-1/4, 1/4]`. -/
lemma abs_sinh_le_quarter {z : ℝ} (h : |z| ≤ 1/4) : |Real.sinh z| ≤ (7/6) * |z| := by
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hz)]
    exact sinh_le_quarter hz (by rwa [abs_of_nonneg hz] at h)
  · have hz' : 0 ≤ -z := by linarith
    have h' : -z ≤ 1/4 := by rwa [abs_of_neg hz] at h
    have := sinh_le_quarter hz' h'
    rw [Real.sinh_neg] at this
    rw [abs_of_neg hz, abs_of_nonpos (by
      have : Real.sinh z ≤ 0 := by
        have := Real.sinh_nonneg_iff (x := -z)
        nlinarith [Real.sinh_neg z, Real.sinh_nonneg_iff.mpr hz']
      exact this)]
    linarith

/-- `cosh z ≤ 16/15` on `[-1/4, 1/4]`. -/
lemma cosh_le_quarter {z : ℝ} (h : |z| ≤ 1/4) : Real.cosh z ≤ 16/15 := by
  have h1 : Real.cosh z = Real.cosh |z| := by
    rcases abs_cases z with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
    simp [Real.cosh_neg]
  set w := |z| with hw
  have hw0 : 0 ≤ w := abs_nonneg z
  rw [h1, Real.cosh_eq]
  have hu : Real.exp w ≤ 1 / (1 - w) := exp_le_inv_one_sub (by linarith)
  have hu2 : Real.exp (-w) ≤ 1 / (1 + w) := by
    have hp : (0:ℝ) < 1 + w := by linarith
    have he : Real.exp (-w) = 1 / Real.exp w := by rw [Real.exp_neg]; ring
    rw [he]
    exact div_le_div_of_nonneg_left (by norm_num) hp (by linarith [Real.add_one_le_exp w])
  have h3 : (0:ℝ) < 1 - w := by linarith
  have h4 : (0:ℝ) < 1 + w := by linarith
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have e1 : 1 / (1 - w) + 1 / (1 + w) ≤ 16/15 * 2 := by
    rw [div_add_div _ _ (ne_of_gt h3) (ne_of_gt h4), div_le_iff₀ (by nlinarith)]
    nlinarith
  linarith

lemma sinh_sq_ge (z : ℝ) : z ^ 2 ≤ Real.sinh z ^ 2 := by
  rcases le_or_gt 0 z with h | h
  · have := Real.self_le_sinh_iff.mpr h
    nlinarith
  · have h1 : Real.sinh (-z) ≥ -z := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_neg] at h1
    nlinarith

/-! ### The constant `A` -/

lemma Aconst_ge : (11:ℝ)/12 ≤ Aconst := by
  rw [← integral_cos_sqrt_two]
  have hcomp : ∫ u in (-(1/2:ℝ))..(1/2), (1 - u^2) = 11/12 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [integral_pow]
    norm_num
  rw [← hcomp]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro u hu
  simp only [Set.mem_Icc] at hu
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 2 * u) ^ 2 = 2 * u ^ 2 := by rw [mul_pow, h2]
  have h4 := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * u)
  rw [h3] at h4
  linarith

lemma Aconst_le_one : Aconst ≤ 1 := by
  rw [← integral_cos_sqrt_two]
  have h1 : ∫ _u in (-(1/2:ℝ))..(1/2), (1:ℝ) = 1 := by norm_num
  have hle : ∫ u in (-(1/2:ℝ))..(1/2), Real.cos (Real.sqrt 2 * u)
      ≤ ∫ _u in (-(1/2:ℝ))..(1/2), (1:ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro u _
    exact Real.cos_le_one _
  rw [h1] at hle
  exact hle

/-! ### A global lower bound for the cosine transform -/

/-- `Jint c = ∫_{-1/2}^{1/2} cos (c u) du`. -/
noncomputable def Jint (c : ℝ) : ℝ := ∫ u in (-(1/2:ℝ))..(1/2), Real.cos (c * u)

lemma Jint_eval {c : ℝ} (hc : c ≠ 0) : Jint c = c⁻¹ * (2 * Real.sin (c/2)) := by
  unfold Jint
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc]
  simp only [integral_cos, smul_eq_mul]
  rw [show c * -(1/2) = -(c/2) by ring, show c * (1/2) = c/2 by ring, Real.sin_neg]
  ring

lemma Jint_neg (c : ℝ) : Jint (-c) = Jint c := by
  unfold Jint
  congr 1
  ext u
  rw [show -c * u = -(c*u) by ring, Real.cos_neg]

lemma Jint_nonneg {c : ℝ} (h : |c| ≤ 2 * Real.pi) : 0 ≤ Jint c := by
  rcases eq_or_ne c 0 with rfl | hc
  · unfold Jint; norm_num
  · rcases lt_or_gt_of_ne hc with hneg | hpos
    · rw [← Jint_neg c, Jint_eval (by linarith : -c ≠ 0)]
      have h2 : -c/2 ≤ Real.pi := by rw [abs_of_neg hneg] at h; linarith
      have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : (0:ℝ) ≤ -c/2) h2
      exact mul_nonneg (inv_nonneg.mpr (by linarith)) (by linarith)
    · rw [Jint_eval hc]
      have h2 : c/2 ≤ Real.pi := by rw [abs_of_pos hpos] at h; linarith
      have := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : (0:ℝ) ≤ c/2) h2
      exact mul_nonneg (inv_nonneg.mpr (by linarith)) (by linarith)

lemma Jint_ge {c : ℝ} (hc : c ≠ 0) : -(2/|c|) ≤ Jint c := by
  rw [Jint_eval hc]
  have hpos : 0 < |c| := abs_pos.2 hc
  have h1 : |c⁻¹ * (2 * Real.sin (c/2))| ≤ 2/|c| := by
    calc |c⁻¹ * (2 * Real.sin (c/2))| = |c|⁻¹ * (2 * |Real.sin (c/2)|) := by
          rw [abs_mul, abs_inv, abs_mul, abs_two]
      _ ≤ |c|⁻¹ * (2 * 1) := by
          have := Real.abs_sin_le_one (c/2)
          have h0 : (0:ℝ) ≤ |c|⁻¹ := by positivity
          nlinarith
      _ = 2/|c| := by field_simp
  linarith [(abs_le.1 h1).1]

lemma phiR_split (r : ℝ) : phiR r = (Jint (Real.sqrt 2 - r) + Jint (Real.sqrt 2 + r))/2 := by
  unfold phiR Jint
  rw [← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_div]
  congr 1
  ext u
  rw [show (Real.sqrt 2 - r) * u = Real.sqrt 2 * u - r * u by ring,
    show (Real.sqrt 2 + r) * u = Real.sqrt 2 * u + r * u by ring,
    Real.cos_sub, Real.cos_add]
  ring

lemma phiR_neg (r : ℝ) : phiR (-r) = phiR r := by
  unfold phiR
  congr 1
  ext u
  rw [show -r * u = -(r*u) by ring, Real.cos_neg]

lemma phiR_lower_aux {r : ℝ} (hr : 0 ≤ r) : -(27/100 : ℝ) ≤ phiR r := by
  have hs2l : (1.414:ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hs2u : Real.sqrt 2 ≤ 1.415 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hpi : (3.1415:ℝ) < Real.pi := Real.pi_gt_d4
  rw [phiR_split]
  rcases le_or_gt (Real.sqrt 2 + r) (2 * Real.pi) with hb | hb
  · have h1 : 0 ≤ Jint (Real.sqrt 2 - r) := by
      apply Jint_nonneg
      rw [abs_le]
      constructor <;> linarith
    have h2 : 0 ≤ Jint (Real.sqrt 2 + r) := by
      apply Jint_nonneg
      rw [abs_le]
      constructor <;> linarith
    linarith
  · have hbpos : 0 < Real.sqrt 2 + r := by linarith
    have h2 : -(2/(Real.sqrt 2 + r)) ≤ Jint (Real.sqrt 2 + r) := by
      have := Jint_ge (c := Real.sqrt 2 + r) (by linarith)
      rwa [abs_of_pos hbpos] at this
    have hb2 : 2/(Real.sqrt 2 + r) ≤ 2/(2*Real.pi) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hb.le
    rcases le_or_gt (r - Real.sqrt 2) (2 * Real.pi) with ha | ha
    · have h1 : 0 ≤ Jint (Real.sqrt 2 - r) := by
        apply Jint_nonneg
        rw [abs_le]
        constructor <;> linarith
      have e1 : 2/(2*Real.pi) ≤ 0.32 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    · have hapos : 0 < r - Real.sqrt 2 := by linarith
      have h1 : -(2/(r - Real.sqrt 2)) ≤ Jint (Real.sqrt 2 - r) := by
        have := Jint_ge (c := Real.sqrt 2 - r) (by linarith)
        rwa [abs_of_neg (by linarith : Real.sqrt 2 - r < 0), neg_sub] at this
      have ha2 : 2/(r - Real.sqrt 2) ≤ 2/(2*Real.pi) :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) ha.le
      have hb3 : 2/(Real.sqrt 2 + r) ≤ 2/(2*Real.pi + 2*Real.sqrt 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      have e1 : 2/(2*Real.pi) ≤ 0.3184 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have e2 : 2/(2*Real.pi + 2*Real.sqrt 2) ≤ 0.2196 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith

/-- A global lower bound for the cosine transform of the window. -/
lemma phiR_lower (r : ℝ) : -(27/100 : ℝ) ≤ phiR r := by
  rcases le_or_gt 0 r with h | h
  · exact phiR_lower_aux h
  · rw [← phiR_neg r]
    exact phiR_lower_aux (by linarith)

/-! ### The slack quantity `Shq` -/

lemma Shq_nonneg (y : ℝ) : 0 ≤ Shq y := by
  unfold Shq
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  have := cos_win_ge hu
  positivity

lemma Shq_lower (y : ℝ) : y ^ 2 / 16 ≤ Shq y := by
  unfold Shq
  have hcomp : ∫ u in (-(1/2:ℝ))..(1/2), (3/4) * (y^2 * u^2) = y^2/16 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  rw [← hcomp]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro u hu
  have hc := cos_win_ge hu
  have hsq : (y*u)^2 ≤ Real.sinh (y*u) ^ 2 := sinh_sq_ge _
  have he : y^2 * u^2 = (y*u)^2 := by ring
  nlinarith [sq_nonneg (Real.sinh (y*u))]

/-! ### The damage bounds -/

/-- `kap s = ∫ g(u) sin²(su) du`, the Cauchy–Schwarz weight of the oscillating factor. -/
noncomputable def kap (s : ℝ) : ℝ :=
  ∫ u in (-(1/2:ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) * Real.sin (s*u)^2

/-- `∫ g(u) sin (su)² du = (A - phiR (2s))/2`. -/
lemma kap_eq (s : ℝ) : kap s = (Aconst - phiR (2*s))/2 := by
  unfold kap phiR
  have hpt : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * Real.sin (s*u)^2
      = (Real.cos (Real.sqrt 2 * u) - Real.cos (Real.sqrt 2 * u) * Real.cos (2*s*u))/2 := by
    intro u
    have h2 : Real.cos (2*s*u) = 1 - 2 * Real.sin (s*u)^2 := by
      rw [show 2*s*u = 2*(s*u) by ring, Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq (s*u)]
    rw [h2]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_cos_sqrt_two]

lemma kap_le (s : ℝ) : kap s ≤ (Aconst + 27/100)/2 := by
  rw [kap_eq]
  linarith [phiR_lower (2*s)]

/-- The (unnegated) damage integral. -/
noncomputable def Qic (y s : ℝ) : ℝ :=
  ∫ u in (-(1/2:ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) * (Real.sin (s * u) * Real.sinh (y * u))

/-- Cauchy–Schwarz: the damage of one on-line point is at most `((A + 27/100)/2) * Shq y`. -/
lemma Qim_sq_le_unif (y s : ℝ) : (Qim y s) ^ 2 ≤ ((Aconst + 27/100)/2) * Shq y := by
  have hk := kap_le s
  have hQim : Qim y s = -(Qic y s) := rfl
  have key : ∀ l : ℝ, 0 ≤ kap s * (l * l) + (-2 * Qic y s) * l + Shq y := by
    intro l
    have hnn : 0 ≤ ∫ u in (-(1/2:ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) *
        (l * Real.sin (s*u) - Real.sinh (y*u))^2 := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro u hu
      have := cos_win_ge hu
      positivity
    have hexp : (∫ u in (-(1/2:ℝ))..(1/2), Real.cos (Real.sqrt 2 * u) *
        (l * Real.sin (s*u) - Real.sinh (y*u))^2)
        = kap s * (l * l) + (-2 * Qic y s) * l + Shq y := by
      have hc : ∀ u : ℝ, Real.cos (Real.sqrt 2 * u) * (l * Real.sin (s*u) - Real.sinh (y*u))^2
          = (l*l) * (Real.cos (Real.sqrt 2 * u) * Real.sin (s*u)^2)
            + ((-2*l) * (Real.cos (Real.sqrt 2 * u) * (Real.sin (s*u) * Real.sinh (y*u)))
              + Real.cos (Real.sqrt 2 * u) * Real.sinh (y*u)^2) := by
        intro u; ring
      simp_rw [hc]
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
          (by apply Continuous.intervalIntegrable; fun_prop),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      unfold kap Qic Shq
      ring
    rw [← hexp]
    exact hnn
  have hd := discrim_le_zero key
  rw [discrim] at hd
  have hS := Shq_nonneg y
  have h1 : (Qic y s)^2 ≤ kap s * Shq y := by nlinarith
  have h2 : kap s * Shq y ≤ ((Aconst + 27/100)/2) * Shq y := mul_le_mul_of_nonneg_right hk hS
  rw [hQim]
  nlinarith

/-- Far-field decay of the damage amplitude: one integration by parts. -/
lemma Qim_far {y s : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) (hs : s ≠ 0) :
    |Qim y s| ≤ (14/5) * y / |s| := by
  have hsa : 0 < |s| := abs_pos.2 hs
  have hs2u : Real.sqrt 2 ≤ 1.415 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hs2p : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- the antiderivative of `sin (s ·)` and its bound
  have hvbd : ∀ x : ℝ, |(-Real.cos (s*x)/s)| ≤ 1/|s| := by
    intro x
    calc |(-Real.cos (s*x)/s)| = |Real.cos (s*x)|/|s| := by rw [abs_div, abs_neg]
      _ ≤ 1/|s| := by gcongr; exact Real.abs_cos_le_one _
  have hsinh : ∀ x : ℝ, |x| ≤ 1/2 → |Real.sinh (y*x)| ≤ (7/12)*y := by
    intro x hx
    have h1 : |y*x| ≤ 1/4 := by
      rw [abs_mul, abs_of_nonneg hy0]
      nlinarith [abs_nonneg x]
    have h9 := abs_sinh_le_quarter h1
    have h2 : |y*x| ≤ y/2 := by
      rw [abs_mul, abs_of_nonneg hy0]
      nlinarith [abs_nonneg x]
    nlinarith
  have hcoshb : ∀ x : ℝ, |x| ≤ 1/2 → Real.cosh (y*x) ≤ 16/15 := by
    intro x hx
    apply cosh_le_quarter
    rw [abs_mul, abs_of_nonneg hy0]
    nlinarith [abs_nonneg x]
  -- the bound on the derivative of the amplitude
  have hphibd : ∀ x : ℝ, |x| ≤ 1/2 →
      |(-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
        + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)| ≤ (19/10)*y := by
    intro x hx
    have h1 : |(-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)|
        ≤ Real.sqrt 2 * ((7/12)*y) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs2p]
      calc |Real.sin (Real.sqrt 2 * x)| * Real.sqrt 2 * |Real.sinh (y*x)|
          ≤ 1 * Real.sqrt 2 * ((7/12)*y) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) hs2p)
              (hsinh x hx) (abs_nonneg _) (by positivity)
        _ = Real.sqrt 2 * ((7/12)*y) := by ring
    have h4 : |Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)| ≤ (16/15)*y := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.cosh_pos (y*x)).le, abs_of_nonneg hy0]
      calc |Real.cos (Real.sqrt 2 * x)| * (Real.cosh (y*x) * y)
          ≤ 1 * ((16/15) * y) := by
            apply mul_le_mul (Real.abs_cos_le_one _)
              (mul_le_mul_of_nonneg_right (hcoshb x hx) hy0) (by positivity) (by norm_num)
        _ = (16/15)*y := by ring
    have h10 := abs_add_le ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x))
      (Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y))
    nlinarith
  -- integration by parts
  have hd1 : ∀ x : ℝ, HasDerivAt (fun u : ℝ => Real.cos (Real.sqrt 2 * u) * Real.sinh (y*u))
      ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
        + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) x := by
    intro x
    have ha : HasDerivAt (fun u : ℝ => Real.sqrt 2 * u) (Real.sqrt 2) x := by
      simpa using (hasDerivAt_id x).const_mul (Real.sqrt 2)
    have hb : HasDerivAt (fun u : ℝ => y * u) y x := by
      simpa using (hasDerivAt_id x).const_mul y
    exact (ha.cos).mul (hb.sinh)
  have hd2 : ∀ x : ℝ, HasDerivAt (fun u : ℝ => -Real.cos (s*u)/s) (Real.sin (s*x)) x := by
    intro x
    have ha : HasDerivAt (fun u : ℝ => s * u) s x := by
      simpa using (hasDerivAt_id x).const_mul s
    have h1 := ((ha.cos).neg).div_const s
    convert h1 using 1
    field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => Real.cos (Real.sqrt 2 * u) * Real.sinh (y*u))
    (v := fun u : ℝ => -Real.cos (s*u)/s)
    (u' := fun x : ℝ => (-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
        + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y))
    (v' := fun x : ℝ => Real.sin (s*x))
    (a := -(1/2:ℝ)) (b := (1/2:ℝ))
    (fun x _ => hd1 x) (fun x _ => hd2 x)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  have hQ : Qim y s = -(∫ x in (-(1/2:ℝ))..(1/2),
      (Real.cos (Real.sqrt 2 * x) * Real.sinh (y*x)) * Real.sin (s*x)) := by
    unfold Qim
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    ring
  -- bound the three pieces
  have hcosb : |Real.cos (Real.sqrt 2 * (1/2:ℝ))| ≤ 77/100 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hxsq : (Real.sqrt 2 * (1/2:ℝ))^2 = 1/2 := by rw [mul_pow, h2]; norm_num
    have hle : |Real.sqrt 2 * (1/2:ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [Real.sqrt_nonneg 2]
    have hb := Real.cos_bound hle
    have h4 : |Real.sqrt 2 * (1/2:ℝ)|^4 = 1/4 := by
      have he : |Real.sqrt 2 * (1/2:ℝ)|^4 = ((Real.sqrt 2 * (1/2:ℝ))^2)^2 := by
        rw [← abs_pow, show (4:ℕ) = 2*2 by norm_num, pow_mul, abs_of_nonneg (sq_nonneg _)]
      rw [he, hxsq]; norm_num
    rw [h4, hxsq] at hb
    have := abs_le.1 hb
    rw [abs_le]
    constructor <;> linarith
  have hcosb' : |Real.cos (Real.sqrt 2 * (-(1/2:ℝ)))| ≤ 77/100 := by
    rw [show Real.sqrt 2 * (-(1/2:ℝ)) = -(Real.sqrt 2 * (1/2:ℝ)) by ring, Real.cos_neg]
    exact hcosb
  have hb1 : |Real.sinh (y*(1/2:ℝ))| ≤ (7/12)*y := hsinh (1/2) (by norm_num)
  have hb2 : |Real.sinh (y*(-(1/2:ℝ)))| ≤ (7/12)*y :=
    hsinh (-(1/2)) (by norm_num)
  have hbd1 : |(Real.cos (Real.sqrt 2 * (1/2:ℝ)) * Real.sinh (y*(1/2:ℝ)))
      * (-Real.cos (s*(1/2:ℝ))/s)| ≤ (539/1200)*y*(1/|s|) := by
    rw [abs_mul, abs_mul]
    calc |Real.cos (Real.sqrt 2 * (1/2:ℝ))| * |Real.sinh (y*(1/2:ℝ))|
          * |(-Real.cos (s*(1/2:ℝ))/s)|
        ≤ ((77/100) * ((7/12)*y)) * (1/|s|) :=
          mul_le_mul (mul_le_mul hcosb hb1 (abs_nonneg _) (by norm_num))
            (hvbd _) (abs_nonneg _) (by positivity)
      _ = (539/1200)*y*(1/|s|) := by ring
  have hbd2 : |(Real.cos (Real.sqrt 2 * (-(1/2:ℝ))) * Real.sinh (y*(-(1/2:ℝ))))
      * (-Real.cos (s*(-(1/2:ℝ)))/s)| ≤ (539/1200)*y*(1/|s|) := by
    rw [abs_mul, abs_mul]
    calc |Real.cos (Real.sqrt 2 * (-(1/2:ℝ)))| * |Real.sinh (y*(-(1/2:ℝ)))|
          * |(-Real.cos (s*(-(1/2:ℝ)))/s)|
        ≤ ((77/100) * ((7/12)*y)) * (1/|s|) :=
          mul_le_mul (mul_le_mul hcosb' hb2 (abs_nonneg _) (by norm_num))
            (hvbd _) (abs_nonneg _) (by positivity)
      _ = (539/1200)*y*(1/|s|) := by ring
  have hbd3 : |∫ x in (-(1/2:ℝ))..(1/2),
      ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
        + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) * (-Real.cos (s*x)/s)|
      ≤ (19/10)*y*(1/|s|) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(1/2:ℝ)) (b := (1/2:ℝ))
      (f := fun x : ℝ => ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
        + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) * (-Real.cos (s*x)/s))
      (C := (19/10)*y*(1/|s|)) ?_
    · calc |∫ x in (-(1/2:ℝ))..(1/2),
              ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
                + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) * (-Real.cos (s*x)/s)|
            = ‖∫ x in (-(1/2:ℝ))..(1/2),
              ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
                + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) * (-Real.cos (s*x)/s)‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ((19/10)*y*(1/|s|)) * |(1/2:ℝ) - -(1/2)| := h
        _ = (19/10)*y*(1/|s|) := by norm_num
    · intro x hx
      rw [Set.uIoc_of_le (by norm_num : (-(1/2:ℝ)) ≤ 1/2)] at hx
      have hxa : |x| ≤ 1/2 := abs_le.2 ⟨hx.1.le, hx.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hphibd x hxa) (hvbd x) (abs_nonneg _) (by positivity)
  have hibp' : (∫ x in (-(1/2:ℝ))..(1/2),
        (Real.cos (Real.sqrt 2 * x) * Real.sinh (y*x)) * Real.sin (s*x))
      = (Real.cos (Real.sqrt 2 * (1/2:ℝ)) * Real.sinh (y*(1/2:ℝ)))
          * (-Real.cos (s*(1/2:ℝ))/s)
        - (Real.cos (Real.sqrt 2 * (-(1/2:ℝ))) * Real.sinh (y*(-(1/2:ℝ))))
          * (-Real.cos (s*(-(1/2:ℝ)))/s)
        - ∫ x in (-(1/2:ℝ))..(1/2),
          ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
            + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) * (-Real.cos (s*x)/s) := hibp
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    rw [sub_eq_add_neg]
    exact (abs_add_le a (-b)).trans (by rw [abs_neg])
  rw [hQ, abs_neg, hibp']
  have t1 := habs ((Real.cos (Real.sqrt 2 * (1/2:ℝ)) * Real.sinh (y*(1/2:ℝ)))
      * (-Real.cos (s*(1/2:ℝ))/s)
      - (Real.cos (Real.sqrt 2 * (-(1/2:ℝ))) * Real.sinh (y*(-(1/2:ℝ))))
        * (-Real.cos (s*(-(1/2:ℝ)))/s))
    (∫ x in (-(1/2:ℝ))..(1/2),
      ((-Real.sin (Real.sqrt 2 * x) * Real.sqrt 2) * Real.sinh (y*x)
        + Real.cos (Real.sqrt 2 * x) * (Real.cosh (y*x) * y)) * (-Real.cos (s*x)/s))
  have t2 := habs ((Real.cos (Real.sqrt 2 * (1/2:ℝ)) * Real.sinh (y*(1/2:ℝ)))
      * (-Real.cos (s*(1/2:ℝ))/s))
    ((Real.cos (Real.sqrt 2 * (-(1/2:ℝ))) * Real.sinh (y*(-(1/2:ℝ))))
      * (-Real.cos (s*(-(1/2:ℝ)))/s))
  have hfin : (14/5) * y / |s| = (14/5)*y*(1/|s|) := by field_simp
  have hnn : 0 ≤ y * (1/|s|) := by positivity
  rw [hfin]
  linarith

/-- Far-field decay in the form used for the summation. -/
lemma Qim_sq_far {y s : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) (hs : s ≠ 0) :
    (Qim y s) ^ 2 ≤ (3136/25) * Shq y / s ^ 2 := by
  have h1 : |Qim y s| ≤ (14/5) * y / |s| := Qim_far hy0 hy1 hs
  have hs2 : (0:ℝ) < |s| := abs_pos.2 hs
  have h2 : (Qim y s) ^ 2 ≤ ((14/5) * y / |s|) ^ 2 := by
    nlinarith [sq_abs (Qim y s), abs_nonneg (Qim y s),
      div_nonneg (by positivity : (0:ℝ) ≤ (14/5) * y) hs2.le]
  have h3 : ((14/5) * y / |s|) ^ 2 = (196/25) * y ^ 2 / s ^ 2 := by
    rw [div_pow, sq_abs]
    ring
  have h5 : (196/25) * y ^ 2 ≤ (3136/25) * Shq y := by
    have := Shq_lower y
    linarith
  calc (Qim y s) ^ 2 ≤ (196/25) * y ^ 2 / s ^ 2 := by rw [← h3]; exact h2
    _ ≤ (3136/25) * Shq y / s ^ 2 := by gcongr

end Retention
