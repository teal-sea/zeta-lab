import ZetaLean.WScratch.EForm3.Estimates

/-!
# The far-field bound

`PROBLEM.md` asks for a *second-order* far-field bound `|Qim y s| ≤ C₂ y / s²`.
**That statement is false.**  `Qim y ·` is the imaginary part of the Fourier–Laplace transform of
the window `g`, which jumps at `u = ±1/2`, so `Qim` decays exactly like `1/|s|` and no better:
in the identity below, `Qim y s * |D|² = C_q sin (s/2) + C_p cos (s/2)` with `C_p ≍ s³ y`
and `|D|² ≍ s⁴`, and along `s = 4πk` (where `cos (s/2) = 1`, `sin (s/2) = 0`) this gives
`|Qim| ≍ y/s`.  See `Qim_far_first_order` for the true first-order decay, and
`no_second_order_far_field` (in `Refutation.lean`) for the refutation of the `1/s²` claim.

What *is* true, and what the counting argument really needs, is a bound with the sharp constant:
`Qim y s ^ 2 ≤ y^2 * Wt (s^2 - 2)` where `Wt w = 5/(8w) + 12.22/w² + 67.11/w³ + 103.32/w⁴`,
i.e. `Qim² ≲ 0.625 y²/s²` for large `s`, keeping all of the `√2`-interference.
Summed over `2π`-separated offsets this is small enough to close the retention inequality.
-/

open scoped BigOperators Real
open MeasureTheory

set_option maxHeartbeats 1000000

namespace Retention

/-- Monotonicity of a product of three bounded nonnegative factors. -/
lemma mul3_le {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) : a * b * c ≤ A * B * C := by
  have hA0 : 0 ≤ A := le_trans ha hA
  have hB0 : 0 ≤ B := le_trans hb hB
  exact mul_le_mul (mul_le_mul hA hB hb hA0) hC hc (by positivity)

/-- The far-field majorant, as a function of `w = s² - 2`. -/
noncomputable def Wt (w : ℝ) : ℝ := (5/8)/w + (611/50)/w^2 + (6711/100)/w^3 + (2583/25)/w^4

lemma Wt_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ Wt w := by
  unfold Wt; positivity

lemma Wt_anti {w w' : ℝ} (hw : 0 < w) (h : w ≤ w') : Wt w' ≤ Wt w := by
  have hw' : 0 < w' := lt_of_lt_of_le hw h
  unfold Wt
  gcongr

lemma Wt_eq {w : ℝ} (hw : 0 < w) :
    Wt w = ((5/8)*w^3 + (611/50)*w^2 + (6711/100)*w + 2583/25) / w^4 := by
  unfold Wt
  field_simp

/-- The cubic majorant inequality underlying `Wt`. -/
lemma base_poly_le {w : ℝ} (hw : 0 ≤ w) :
    (1.57*(w+2)+3.6)^2 + (w+2)*(0.79*(w+2)+3.8)^2
      ≤ (5/8)*w^3 + (611/50)*w^2 + (6711/100)*w + 2583/25 := by
  nlinarith [pow_nonneg hw 3, sq_nonneg w, hw]

/-- The exact identity behind the far-field bound (pure algebra, with `r² = 2`). -/
lemma far_identity (y s r c0 s0 P S q p : ℝ) (hr : r^2 = 2)
    (hDp : y^2+(s+r)^2 ≠ 0) (hDm : y^2+(s-r)^2 ≠ 0) :
    ((P*(c0*q+s0*p) - (s+r)*S*(c0*p-s0*q))/(y^2+(s+r)^2)
      + (P*(c0*q-s0*p) - (s-r)*S*(c0*p+s0*q))/(y^2+(s-r)^2))
      * ((y^2+s^2+2)^2 - 8*s^2)
    = (2*P*c0*(y^2+s^2+2) + 2*S*(r*s0)*(y^2+2-s^2)) * q
      + (-4*s*P*(r*s0) - 2*S*s*c0*(y^2+s^2-2)) * p := by
  have e1 : y^2+(s+r)^2 = (y^2+s^2+2) + 2*r*s := by linear_combination hr
  have e2 : y^2+(s-r)^2 = (y^2+s^2+2) - 2*r*s := by linear_combination hr
  have hprod : (y^2+(s+r)^2) * (y^2+(s-r)^2) = (y^2+s^2+2)^2 - 8*s^2 := by
    rw [e1, e2]; linear_combination (-4*s^2) * hr
  have hnum : (P*(c0*q+s0*p) - (s+r)*S*(c0*p-s0*q)) * (y^2+(s-r)^2)
      + (P*(c0*q-s0*p) - (s-r)*S*(c0*p+s0*q)) * (y^2+(s+r)^2)
      = (2*P*c0*(y^2+s^2+2) + 2*S*(r*s0)*(y^2+2-s^2)) * q
        + (-4*s*P*(r*s0) - 2*S*s*c0*(y^2+s^2-2)) * p := by
    rw [e1, e2]; linear_combination (4*S*s*c0*p) * hr
  rw [← hprod, ← hnum]
  field_simp

/-- `Qim` is odd in its second argument. -/
lemma Qim_neg_right (y s : ℝ) : Qim y (-s) = -Qim y s := by
  unfold Qim
  rw [← integral_neg]
  congr 1
  funext u
  rw [show (-s)*u = -(s*u) by ring, Real.sin_neg]
  ring

/-- The far-field bound in the form used by the counting argument. -/
theorem Qim_far_sq {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) (hs : 28/5 ≤ s) :
    Qim y s ^ 2 ≤ y^2 * Wt (s^2 - 2) := by
  have hr : (Real.sqrt 2)^2 = 2 := sqrt2_sq
  have hrpos : 0 < Real.sqrt 2 := sqrt2_pos
  have hrub : Real.sqrt 2 ≤ 1.4142136 := sqrt2_ub
  have hs2 : (31.36:ℝ) ≤ s^2 := by nlinarith
  have hspos : (0:ℝ) < s := by linarith
  have hy2 : y^2 ≤ 1/4 := by nlinarith
  have hy20 : 0 ≤ y^2 := sq_nonneg y
  set r := Real.sqrt 2 with hrdef
  set c0 := Real.cos (1 / r) with hc0def
  set s0 := Real.sin (1 / r) with hs0def
  set P := y * Real.cosh (y/2) with hPdef
  set S := Real.sinh (y/2) with hSdef
  set q := Real.sin (s/2) with hqdef
  set p := Real.cos (s/2) with hpdef
  have hhalf : r / 2 = 1 / r := sqrt2_half
  have hDp : y^2+(s+r)^2 ≠ 0 := by positivity
  have hDm : y^2+(s-r)^2 ≠ 0 := by
    have h : (0:ℝ) < (s - r)^2 := by nlinarith
    positivity
  -- the closed form, rewritten via the addition formulas
  have hQ : Qim y s = (P*(c0*q+s0*p) - (s+r)*S*(c0*p-s0*q))/(y^2+(s+r)^2)
      + (P*(c0*q-s0*p) - (s-r)*S*(c0*p+s0*q))/(y^2+(s-r)^2) := by
    rw [Qim_closed y s hDp hDm]
    have ep : (s + r)/2 = s/2 + 1/r := by rw [← hhalf]; ring
    have em : (s - r)/2 = s/2 - 1/r := by rw [← hhalf]; ring
    rw [ep, em, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub]
    rw [← hc0def, ← hs0def, ← hqdef, ← hpdef, hPdef, hSdef]
    ring
  have hid : Qim y s * ((y^2+s^2+2)^2 - 8*s^2)
      = (2*P*c0*(y^2+s^2+2) + 2*S*(r*s0)*(y^2+2-s^2)) * q
        + (-4*s*P*(r*s0) - 2*S*s*c0*(y^2+s^2-2)) * p := by
    rw [hQ]; exact far_identity y s r c0 s0 P S q p hr hDp hDm
  set Cq := 2*P*c0*(y^2+s^2+2) + 2*S*(r*s0)*(y^2+2-s^2) with hCqdef
  set Cp := -4*s*P*(r*s0) - 2*S*s*c0*(y^2+s^2-2) with hCpdef
  -- Cauchy–Schwarz
  have hpq : q^2 + p^2 = 1 := by rw [hqdef, hpdef]; exact Real.sin_sq_add_cos_sq _
  have hCS : (Cq * q + Cp * p)^2 ≤ Cq^2 + Cp^2 := by
    nlinarith only [sq_nonneg (Cq*p - Cp*q), hpq, sq_nonneg (Cq*q + Cp*p)]
  -- elementary bounds on the ingredients
  have hcosh : Real.cosh (y/2) ≤ 32/31 :=
    cosh_le_of_abs_le_quarter (by rw [abs_le]; constructor <;> linarith)
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hPu : P ≤ (32/31) * y := by
    rw [hPdef]; nlinarith [Real.one_le_cosh (y/2)]
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Real.sinh_nonneg_iff.2 (by linarith)
  have hSu : S ≤ (16/31) * y := by
    rw [hSdef]
    have h := sinh_le_mul_cosh (t := y/2) (by linarith)
    nlinarith
  have hc00 : 0 ≤ c0 := by
    rw [hc0def]; have := cos_inv_sqrt2_lb; rw [← hrdef] at this; linarith
  have hc0u : c0 ≤ 0.7604167 := by
    rw [hc0def]; have := cos_inv_sqrt2_ub; rw [← hrdef] at this; linarith
  have hAeq : r * s0 = Aconst := by rw [hs0def, Aconst, hrdef]
  have hA0 : 0 ≤ r * s0 := by rw [hAeq]; exact le_of_lt Aconst_pos
  have hAu : r * s0 ≤ 441/480 := by rw [hAeq]; exact Aconst_ub
  -- bound on `Cq`
  have hCqb : |Cq| ≤ y * (1.57 * s^2 + 3.6) := by
    have hZ0 : (0:ℝ) ≤ y^2+s^2+2 := by linarith
    have hZ1 : y^2+s^2+2 ≤ s^2+2.25 := by linarith
    have hZ2 : (0:ℝ) ≤ s^2-y^2-2 := by linarith
    have hZ3 : s^2-y^2-2 ≤ s^2 := by linarith
    have hT1 : (2*P) * c0 * (y^2+s^2+2) ≤ (2*((32/31)*y)) * 0.7604167 * (s^2+2.25) :=
      mul3_le (by linarith) hc00 hZ0 (by linarith) hc0u hZ1
    have hT1' : 0 ≤ (2*P) * c0 * (y^2+s^2+2) := by positivity
    have hT2 : (2*S) * (r*s0) * (s^2-y^2-2) ≤ (2*((16/31)*y)) * (441/480) * (s^2) :=
      mul3_le (by linarith) hA0 hZ2 (by linarith) hAu hZ3
    have hT2' : 0 ≤ (2*S) * (r*s0) * (s^2-y^2-2) := by positivity
    have heq1 : Cq = (2*P) * c0 * (y^2+s^2+2) - (2*S) * (r*s0) * (s^2-y^2-2) := by
      rw [hCqdef]; ring
    have hys2 : (0:ℝ) ≤ y * s^2 := mul_nonneg hy0 (sq_nonneg s)
    rw [abs_le, heq1]
    constructor
    · linarith only [hT2, hT1', hys2, hy0]
    · linarith only [hT1, hT2', hys2, hy0]
  -- bound on `Cp`
  have hCpb : |Cp| ≤ y * s * (0.79 * s^2 + 3.8) := by
    have hT1 : (4*s) * P * (r*s0) ≤ (4*s) * ((32/31)*y) * (441/480) :=
      mul3_le (by linarith) hP0 hA0 (le_refl _) hPu hAu
    have hT1' : 0 ≤ (4*s) * P * (r*s0) := by positivity
    have h2Ss : (2*S) * s ≤ (2*((16/31)*y)) * s :=
      mul_le_mul_of_nonneg_right (by linarith only [hSu]) (le_of_lt hspos)
    have hZ4 : (0:ℝ) ≤ y^2+s^2-2 := by linarith
    have hZ5 : y^2+s^2-2 ≤ s^2 := by linarith
    have hSs0 : (0:ℝ) ≤ (2*S) * s := by positivity
    have hT2 : ((2*S) * s) * c0 * (y^2+s^2-2) ≤ ((2*((16/31)*y)) * s) * 0.7604167 * (s^2) :=
      mul3_le hSs0 hc00 hZ4 h2Ss hc0u hZ5
    have hT2' : 0 ≤ ((2*S) * s) * c0 * (y^2+s^2-2) := by positivity
    have heq1 : Cp = -((4*s) * P * (r*s0)) - ((2*S) * s) * c0 * (y^2+s^2-2) := by
      rw [hCpdef]; ring
    have hys1 : (0:ℝ) ≤ y * s := mul_nonneg hy0 (le_of_lt hspos)
    have hys3 : (0:ℝ) ≤ y * s^3 := by positivity
    rw [abs_le, heq1]
    constructor
    · linarith only [hT1, hT2, hys1, hys3]
    · linarith only [hT1', hT2', hys1, hys3]
  -- squares
  have hB1 : 0 ≤ y * (1.57 * s^2 + 3.6) := by positivity
  have hB2 : 0 ≤ y * s * (0.79 * s^2 + 3.8) := by positivity
  have hCqsq : Cq^2 ≤ y^2 * (1.57*s^2+3.6)^2 := by
    have h := sq_le_sq' (abs_le.1 hCqb).1 (abs_le.1 hCqb).2
    have e : (y * (1.57 * s^2 + 3.6))^2 = y^2 * (1.57*s^2+3.6)^2 := by ring
    rw [e] at h; exact h
  have hCpsq : Cp^2 ≤ y^2 * (s^2 * (0.79*s^2+3.8)^2) := by
    have h := sq_le_sq' (abs_le.1 hCpb).1 (abs_le.1 hCpb).2
    have e : (y * s * (0.79 * s^2 + 3.8))^2 = y^2 * (s^2 * (0.79*s^2+3.8)^2) := by ring
    rw [e] at h; exact h
  -- the denominator
  have hden : (s^2-2)^2 ≤ (y^2+s^2+2)^2 - 8*s^2 := by nlinarith only [hy20, hs2, sq_nonneg y]
  have hden0 : (0:ℝ) < (s^2-2)^2 := by nlinarith only [hs2]
  have hQsq : Qim y s ^2 * (s^2-2)^4 ≤ Cq^2 + Cp^2 := by
    have h1 : Qim y s ^2 * (s^2-2)^4
        ≤ Qim y s ^2 * ((y^2+s^2+2)^2 - 8*s^2)^2 := by
      have hle : (s^2-2)^4 ≤ ((y^2+s^2+2)^2 - 8*s^2)^2 := by
        have e : (s^2-2)^4 = ((s^2-2)^2)^2 := by ring
        rw [e]
        exact pow_le_pow_left₀ (le_of_lt hden0) hden 2
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    have h2 : Qim y s ^2 * ((y^2+s^2+2)^2 - 8*s^2)^2 = (Cq*q + Cp*p)^2 := by
      rw [← hid]; ring
    linarith only [h1, h2 ▸ hCS]
  -- the polynomial majorant
  have hw : (0:ℝ) < s^2 - 2 := by linarith
  have hbase : (1.57*s^2+3.6)^2 + (s^2 * (0.79*s^2+3.8)^2)
      ≤ (5/8)*(s^2-2)^3 + (611/50)*(s^2-2)^2 + (6711/100)*(s^2-2) + 2583/25 := by
    have h := base_poly_le (w := s^2-2) (by linarith)
    have e : s^2 - 2 + 2 = s^2 := by ring
    rw [e] at h
    linarith only [h]
  have hfinal : Qim y s ^2 * (s^2-2)^4
      ≤ y^2 * ((5/8)*(s^2-2)^3 + (611/50)*(s^2-2)^2 + (6711/100)*(s^2-2) + 2583/25) := by
    have hstep : Cq^2 + Cp^2
        ≤ y^2 * ((1.57*s^2+3.6)^2 + (s^2 * (0.79*s^2+3.8)^2)) := by
      have e : y^2 * ((1.57*s^2+3.6)^2 + (s^2 * (0.79*s^2+3.8)^2))
          = y^2 * (1.57*s^2+3.6)^2 + y^2 * (s^2 * (0.79*s^2+3.8)^2) := by ring
      rw [e]; linarith only [hCqsq, hCpsq]
    have hmaj := mul_le_mul_of_nonneg_left hbase hy20
    linarith only [hQsq, hstep, hmaj]
  have hw4 : (0:ℝ) < (s^2-2)^4 := by positivity
  rw [Wt_eq hw, ← mul_div_assoc, le_div_iff₀ hw4]
  exact hfinal

/-- The far-field bound for either sign of `s`. -/
theorem Qim_far_sq_abs {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) (hs : 28/5 ≤ |s|) :
    Qim y s ^ 2 ≤ y^2 * Wt (s^2 - 2) := by
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    exact Qim_far_sq hy0 hy hs
  · rw [abs_of_nonpos h] at hs
    have h1 := Qim_far_sq (y := y) (s := -s) hy0 hy hs
    rw [Qim_neg_right] at h1
    have e : (-s)^2 = s^2 := by ring
    rw [e] at h1
    nlinarith [h1]

/-- A uniform bound on the per-offset damage, valid for **every** offset `s`:
in the near field there is no damage at all, and in the far field `Qim²` is at most
`y² Wt(29.36) ≤ 0.0383 y²`. -/
theorem uniform_damage {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) :
    Qim y s ^ 2 - Qre y s ^ 2 ≤ y^2 * (383/10000) := by
  have hy2 : (0:ℝ) ≤ y^2 := sq_nonneg y
  rcases le_or_gt |s| (28/5) with h | h
  · have := no_damage hy0 hy h
    nlinarith only [this, hy2]
  · have hs2 : (31.36:ℝ) ≤ s^2 := by
      have h1 : (28/5:ℝ)^2 ≤ |s|^2 := by nlinarith [abs_nonneg s]
      rw [sq_abs] at h1; linarith
    have h1 : Qim y s ^ 2 ≤ y^2 * Wt (s^2 - 2) := Qim_far_sq_abs hy0 hy (le_of_lt h)
    have h2 : Wt (s^2 - 2) ≤ Wt (2936/100) := Wt_anti (by norm_num) (by linarith)
    have h3 : Wt (2936/100 : ℝ) ≤ 383/10000 := by rw [Wt]; norm_num
    nlinarith only [h1, h2, h3, hy2, sq_nonneg (Qre y s)]

/-- `Wt w ≤ (36/25)/(w+2)` on the far field. -/
lemma Wt_le_first_order {w : ℝ} (hw : 29.36 ≤ w) : Wt w ≤ (36/25)/(w+2) := by
  have hw0 : (0:ℝ) < w := by linarith
  rw [Wt_eq hw0, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hw, sq_nonneg w, pow_pos hw0 3, pow_pos hw0 4, sq_nonneg (w - 29.36)]

/-- The true first-order far-field decay: `|Qim y s| ≤ (6/5) y / |s|`. -/
theorem Qim_far_first_order {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) (hs : 28/5 ≤ |s|) :
    |Qim y s| ≤ (6/5) * y / |s| := by
  have hs0 : (0:ℝ) < |s| := by linarith
  have hs2 : (31.36:ℝ) ≤ s^2 := by
    have h : (28/5:ℝ)^2 ≤ |s|^2 := by nlinarith
    rw [sq_abs] at h; linarith
  have hkey := Qim_far_sq_abs hy0 hy hs
  have hWt : Wt (s^2-2) ≤ (36/25) / s^2 := by
    have h := Wt_le_first_order (w := s^2-2) (by linarith)
    have e : s^2 - 2 + 2 = s^2 := by ring
    rwa [e] at h
  have h2 : Qim y s ^2 ≤ y^2 * ((36/25)/s^2) := by
    have hy20 : (0:ℝ) ≤ y^2 := sq_nonneg y
    nlinarith [hkey, hWt, hy20]
  have hsq : (|Qim y s|)^2 ≤ ((6/5) * y / |s|)^2 := by
    rw [sq_abs]
    have e : ((6/5) * y / |s|)^2 = y^2 * ((36/25)/s^2) := by
      rw [div_pow, mul_pow, sq_abs]
      field_simp
      ring
    rw [e]; exact h2
  have hnn : (0:ℝ) ≤ (6/5) * y / |s| := by positivity
  nlinarith [hsq, abs_nonneg (Qim y s), hnn]

end Retention
