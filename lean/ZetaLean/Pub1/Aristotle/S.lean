import Mathlib

namespace AristotleS

noncomputable def aCoef (k : ℕ) : ℝ :=
  2 ^ (2 * k + 3) * (Nat.factorial k : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)

/-- The form factor on the half line: `F₁ x = fKer |x|`. -/
noncomputable def fKer (y : ℝ) : ℝ :=
  y - 4 * y ^ 2 + ∑' k : ℕ, aCoef k * y ^ (2 * k + 3)

namespace FKerAux

/-- A summability condition on the coefficients `c` and exponents `e` of the series
`∑' k, c k * y ^ e k`, strong enough to be preserved under termwise differentiation. -/
private def SeriesBound (c : ℕ → ℝ) (e : ℕ → ℕ) : Prop :=
  ∀ (d : ℕ) (r : ℝ), 1 ≤ r → Summable fun k => |c k| * ((e k : ℝ) + 1) ^ d * r ^ e k

private lemma seriesBound_deriv {c : ℕ → ℝ} {e : ℕ → ℕ} (h : SeriesBound c e) :
    SeriesBound (fun k => c k * (e k : ℝ)) (fun k => e k - 1) := by
  intro d r hr
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h (d + 1) r hr)
  have hcast : ((e k - 1 : ℕ) : ℝ) ≤ (e k : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (Nat.sub_le (e k) 1)
  have h1 : ((e k - 1 : ℕ) : ℝ) + 1 ≤ (e k : ℝ) + 1 := by linarith
  have h2 : r ^ (e k - 1) ≤ r ^ e k := pow_le_pow_right₀ hr (Nat.sub_le (e k) 1)
  have h3 : |c k * (e k : ℝ)| = |c k| * (e k : ℝ) := by
    rw [abs_mul, Nat.abs_cast]
  rw [h3]
  have hc : (0 : ℝ) ≤ |c k| := abs_nonneg _
  have hek : (0 : ℝ) ≤ (e k : ℝ) := Nat.cast_nonneg _
  have hpowd : (((e k - 1 : ℕ) : ℝ) + 1) ^ d ≤ ((e k : ℝ) + 1) ^ d :=
    pow_le_pow_left₀ (by positivity) h1 d
  have hrk : (0 : ℝ) ≤ r ^ (e k - 1) := by positivity
  have hpow1 : (0 : ℝ) ≤ ((e k : ℝ) + 1) ^ d := by positivity
  calc |c k| * (e k : ℝ) * (((e k - 1 : ℕ) : ℝ) + 1) ^ d * r ^ (e k - 1)
      ≤ |c k| * ((e k : ℝ) + 1) * ((e k : ℝ) + 1) ^ d * r ^ e k := by
        have s1 : |c k| * (e k : ℝ) ≤ |c k| * ((e k : ℝ) + 1) := by nlinarith
        have s2 : |c k| * (e k : ℝ) * (((e k - 1 : ℕ) : ℝ) + 1) ^ d
            ≤ |c k| * ((e k : ℝ) + 1) * ((e k : ℝ) + 1) ^ d := by
          have t1 : |c k| * (e k : ℝ) * (((e k - 1 : ℕ) : ℝ) + 1) ^ d
              ≤ |c k| * (e k : ℝ) * ((e k : ℝ) + 1) ^ d :=
            mul_le_mul_of_nonneg_left hpowd (by positivity)
          exact t1.trans (mul_le_mul_of_nonneg_right s1 hpow1)
        have t2 : |c k| * (e k : ℝ) * (((e k - 1 : ℕ) : ℝ) + 1) ^ d * r ^ (e k - 1)
            ≤ |c k| * ((e k : ℝ) + 1) * ((e k : ℝ) + 1) ^ d * r ^ (e k - 1) :=
          mul_le_mul_of_nonneg_right s2 hrk
        exact t2.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = |c k| * ((e k : ℝ) + 1) ^ (d + 1) * r ^ e k := by ring

private lemma hasDerivAt_series {c : ℕ → ℝ} {e : ℕ → ℕ} (h : SeriesBound c e) (y : ℝ) :
    HasDerivAt (fun z : ℝ => ∑' k, c k * z ^ e k)
      (∑' k, c k * (e k : ℝ) * y ^ (e k - 1)) y := by
  set R : ℝ := |y| + 1 with hRdef
  have h1R : (1 : ℝ) ≤ R := by
    have := abs_nonneg y
    simp only [hRdef]
    linarith
  have h0R : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one h1R
  have hu : Summable fun k => |c k| * ((e k : ℝ) + 1) * R ^ e k := by
    have := h 1 R h1R
    simpa using this
  have hu1 : Summable fun k => |c k| * ((e k : ℝ) + 1) * (1 : ℝ) ^ e k := by
    have := h 1 (1 : ℝ) le_rfl
    simpa using this
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |c k| * ((e k : ℝ) + 1) * R ^ e k)
    (g := fun k z => c k * z ^ e k) (g' := fun k z => c k * (e k : ℝ) * z ^ (e k - 1))
    (t := Metric.ball (0 : ℝ) R) (y₀ := 0) hu Metric.isOpen_ball
    ((convex_ball (0 : ℝ) R).isPreconnected) (fun k z _ => ?_) (fun k z hz => ?_)
    (by simpa using h0R) ?_
    (show y ∈ Metric.ball (0 : ℝ) R by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, hRdef]
      linarith)
  · exact ((hasDerivAt_pow (e k) z).const_mul (c k)).congr_deriv (by ring)
  · have hz' : |z| ≤ R := by
      have : |z| < R := by simpa [Real.dist_eq] using hz
      exact le_of_lt this
    have hstep : |z| ^ (e k - 1) ≤ R ^ e k := by
      calc |z| ^ (e k - 1) ≤ R ^ (e k - 1) := by
            exact pow_le_pow_left₀ (abs_nonneg z) hz' _
        _ ≤ R ^ e k := pow_le_pow_right₀ h1R (Nat.sub_le (e k) 1)
    have hnorm : ‖c k * (e k : ℝ) * z ^ (e k - 1)‖ = |c k| * (e k : ℝ) * |z| ^ (e k - 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    rw [hnorm]
    have hc : (0 : ℝ) ≤ |c k| := abs_nonneg _
    have hek : (0 : ℝ) ≤ (e k : ℝ) := Nat.cast_nonneg _
    have hle1 : |c k| * (e k : ℝ) ≤ |c k| * ((e k : ℝ) + 1) := by nlinarith
    have hz0 : (0 : ℝ) ≤ |z| ^ (e k - 1) := by positivity
    calc |c k| * (e k : ℝ) * |z| ^ (e k - 1)
        ≤ |c k| * ((e k : ℝ) + 1) * |z| ^ (e k - 1) :=
          mul_le_mul_of_nonneg_right hle1 hz0
      _ ≤ |c k| * ((e k : ℝ) + 1) * R ^ e k :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  · refine Summable.of_norm_bounded hu1 (fun k => ?_)
    have h0 : |(0 : ℝ) ^ e k| ≤ 1 := by
      rcases Nat.eq_zero_or_pos (e k) with hk | hk
      · simp [hk]
      · rw [zero_pow (by omega)]; simp
    have : ‖c k * (0 : ℝ) ^ e k‖ ≤ |c k| * 1 := by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
    refine this.trans ?_
    have h1 : (1 : ℝ) ≤ ((e k : ℝ) + 1) * (1 : ℝ) ^ e k := by
      have : (0 : ℝ) ≤ (e k : ℝ) := Nat.cast_nonneg _
      simp only [one_pow, mul_one]
      linarith
    calc |c k| * 1 ≤ |c k| * (((e k : ℝ) + 1) * (1 : ℝ) ^ e k) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |c k| * ((e k : ℝ) + 1) * (1 : ℝ) ^ e k := by ring

private lemma contDiff_series : ∀ (n : ℕ) (c : ℕ → ℝ) (e : ℕ → ℕ), SeriesBound c e →
    ContDiff ℝ (n : WithTop ℕ∞) (fun y : ℝ => ∑' k, c k * y ^ e k) := by
  intro n
  induction n with
  | zero =>
      intro c e h
      have hcont : Continuous (fun y : ℝ => ∑' k, c k * y ^ e k) := by
        refine continuous_iff_continuousAt.mpr (fun y => ?_)
        exact ((hasDerivAt_series h y).differentiableAt).continuousAt
      have : ContDiff ℝ 0 (fun y : ℝ => ∑' k, c k * y ^ e k) := contDiff_zero.mpr hcont
      simpa using this
  | succ n ih =>
      intro c e h
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
        push_cast; ring
      rw [hcast, contDiff_succ_iff_deriv]
      refine ⟨fun y => (hasDerivAt_series h y).differentiableAt, ?_, ?_⟩
      · intro hw
        exact absurd hw (by simp)
      · have hd : (deriv fun y : ℝ => ∑' k, c k * y ^ e k)
            = fun y : ℝ => ∑' k, (c k * (e k : ℝ)) * y ^ (e k - 1) :=
          funext fun y => (hasDerivAt_series h y).deriv
        rw [hd]
        exact ih _ _ (seriesBound_deriv h)

/-! ### The concrete series -/

private lemma aCoef_nonneg (k : ℕ) : 0 ≤ aCoef k := by
  unfold aCoef
  positivity

private lemma aCoef_le (k : ℕ) : aCoef k ≤ 8 * 4 ^ k / (Nat.factorial k : ℝ) := by
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hfac2 : (0 : ℝ) < (Nat.factorial (2 * k + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * k + 2)
  have hdvd : Nat.factorial k * Nat.factorial k ≤ Nat.factorial (2 * k + 2) := by
    have h1 : Nat.factorial k * Nat.factorial k ∣ Nat.factorial (k + k) :=
      Nat.factorial_mul_factorial_dvd_factorial_add k k
    have h2 : Nat.factorial k * Nat.factorial k ≤ Nat.factorial (k + k) :=
      Nat.le_of_dvd (Nat.factorial_pos _) h1
    exact h2.trans (Nat.factorial_le (by omega))
  have hdvdR : (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ) ≤ (Nat.factorial (2 * k + 2) : ℝ) := by
    exact_mod_cast hdvd
  have hpow : (2 : ℝ) ^ (2 * k + 3) = 8 * 4 ^ k := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  unfold aCoef
  rw [hpow, div_le_div_iff₀ hfac2 hfac]
  have h8 : (0 : ℝ) ≤ 8 * 4 ^ k := by positivity
  calc 8 * 4 ^ k * (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)
      = 8 * 4 ^ k * ((Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)) := by ring
    _ ≤ 8 * 4 ^ k * (Nat.factorial (2 * k + 2) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hdvdR h8

private lemma two_mul_add_four_le (k : ℕ) : (2 * (k : ℝ) + 4) ≤ 4 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      push_cast
      push_cast at ih
      rw [pow_succ]
      nlinarith

private lemma summable_pow_factorial (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Summable fun k : ℕ => (2 * (k : ℝ) + 4) ^ d * x ^ k / (Nat.factorial k : ℝ) := by
  have hbase : Summable fun k : ℕ => ((2 ^ d * x) ^ k / (Nat.factorial k : ℝ)) :=
    Real.summable_pow_div_factorial (2 ^ d * x)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hbase.mul_left ((4 : ℝ) ^ d))
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h1 : (2 * (k : ℝ) + 4) ^ d ≤ (4 * 2 ^ k) ^ d := by
    apply pow_le_pow_left₀ (by positivity) (two_mul_add_four_le k)
  have h2 : (4 * (2 : ℝ) ^ k) ^ d * x ^ k = 4 ^ d * ((2 ^ d * x) ^ k) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k d]
    ring
  have hxk : (0 : ℝ) ≤ x ^ k := by positivity
  have key : (2 * (k : ℝ) + 4) ^ d * x ^ k ≤ 4 ^ d * (2 ^ d * x) ^ k :=
    (mul_le_mul_of_nonneg_right h1 hxk).trans_eq h2
  calc (2 * (k : ℝ) + 4) ^ d * x ^ k / (Nat.factorial k : ℝ)
      ≤ 4 ^ d * (2 ^ d * x) ^ k / (Nat.factorial k : ℝ) := by gcongr
    _ = 4 ^ d * ((2 ^ d * x) ^ k / (Nat.factorial k : ℝ)) := by
        rw [mul_div_assoc]

private lemma seriesBound_aCoef : SeriesBound aCoef (fun k => 2 * k + 3) := by
  intro d r hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hmain := (summable_pow_factorial d (4 * r ^ 2) (by positivity)).mul_left (8 * r ^ 3)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hmain
  have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hcast : (((2 * k + 3 : ℕ) : ℝ) + 1) = 2 * (k : ℝ) + 4 := by push_cast; ring
  have hexp : r ^ (2 * k + 3) = r ^ 3 * (r ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  have habs : |aCoef k| = aCoef k := abs_of_nonneg (aCoef_nonneg k)
  rw [habs, hcast, hexp]
  have h1 : aCoef k ≤ 8 * 4 ^ k / (Nat.factorial k : ℝ) := aCoef_le k
  have hpos : (0 : ℝ) ≤ (2 * (k : ℝ) + 4) ^ d * (r ^ 3 * (r ^ 2) ^ k) := by positivity
  calc aCoef k * (2 * (k : ℝ) + 4) ^ d * (r ^ 3 * (r ^ 2) ^ k)
      = aCoef k * ((2 * (k : ℝ) + 4) ^ d * (r ^ 3 * (r ^ 2) ^ k)) := by ring
    _ ≤ (8 * 4 ^ k / (Nat.factorial k : ℝ)) * ((2 * (k : ℝ) + 4) ^ d * (r ^ 3 * (r ^ 2) ^ k)) := by
        exact mul_le_mul_of_nonneg_right h1 hpos
    _ = 8 * r ^ 3 * ((2 * (k : ℝ) + 4) ^ d * (4 * r ^ 2) ^ k / (Nat.factorial k : ℝ)) := by
        rw [mul_pow]
        field_simp

/-! ### Derivatives of `fKer` -/

private lemma hasDerivAt_G0 (y : ℝ) :
    HasDerivAt (fun z : ℝ => ∑' k : ℕ, aCoef k * z ^ (2 * k + 3))
      (∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * y ^ (2 * k + 3 - 1)) y :=
  hasDerivAt_series seriesBound_aCoef y

private lemma hasDerivAt_fKer (y : ℝ) :
    HasDerivAt fKer
      (1 - 8 * y + ∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * y ^ (2 * k + 3 - 1)) y := by
  have hpoly : HasDerivAt (fun z : ℝ => z - 4 * z ^ 2) (1 - 8 * y) y := by
    have h1 : HasDerivAt (fun z : ℝ => z) 1 y := hasDerivAt_id y
    have h2 : HasDerivAt (fun z : ℝ => 4 * z ^ 2) (4 * (2 * y ^ 1)) y :=
      (hasDerivAt_pow 2 y).const_mul 4
    exact (h1.sub h2).congr_deriv (by ring)
  have := hpoly.add (hasDerivAt_G0 y)
  exact this

private lemma hasDerivAt_G1 (y : ℝ) :
    HasDerivAt (fun z : ℝ => ∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * z ^ (2 * k + 3 - 1))
      (∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 3 - 1 : ℕ) : ℝ) *
        y ^ (2 * k + 3 - 1 - 1)) y := by
  have h := hasDerivAt_series (seriesBound_deriv seriesBound_aCoef) y
  simpa [mul_assoc] using h

end FKerAux

open FKerAux in
theorem fKer_contDiff : ContDiff ℝ 3 fKer := by
  have hser : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞)
      (fun y : ℝ => ∑' k : ℕ, aCoef k * y ^ (2 * k + 3)) :=
    contDiff_series 3 aCoef (fun k => 2 * k + 3) seriesBound_aCoef
  have hpoly : ContDiff ℝ 3 (fun y : ℝ => y - 4 * y ^ 2) := by
    exact contDiff_id.sub ((contDiff_id.pow 2).const_smul (4 : ℝ))
  have : ContDiff ℝ 3 (fun y : ℝ => y - 4 * y ^ 2 + ∑' k : ℕ, aCoef k * y ^ (2 * k + 3)) := by
    refine hpoly.add ?_
    simpa using hser
  exact this

theorem fKer_zero : fKer 0 = 0 := by
  simp [fKer]

open FKerAux in
theorem fKer_deriv_zero : deriv fKer 0 = 1 := by
  have h := hasDerivAt_fKer 0
  have hz : (∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * (0 : ℝ) ^ (2 * k + 3 - 1)) = 0 := by
    simp
  rw [hz] at h
  simpa using h.deriv

open FKerAux in
theorem fKer_second_deriv (y : ℝ) :
    deriv (deriv fKer) y
      = -8 + ∑' k : ℕ, aCoef k * ((2 * k + 3) * (2 * k + 2) : ℝ) * y ^ (2 * k + 1) := by
  have hd1 : deriv fKer
      = fun z : ℝ => 1 - 8 * z + ∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * z ^ (2 * k + 3 - 1) :=
    funext fun z => (hasDerivAt_fKer z).deriv
  rw [hd1]
  have hpoly : HasDerivAt (fun z : ℝ => 1 - 8 * z) (-8) y := by
    have h1 : HasDerivAt (fun z : ℝ => (8 : ℝ) * z) 8 y := by
      simpa using (hasDerivAt_id y).const_mul (8 : ℝ)
    exact ((hasDerivAt_const y (1 : ℝ)).sub h1).congr_deriv (by ring)
  have h : HasDerivAt
      (fun z : ℝ => 1 - 8 * z + ∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * z ^ (2 * k + 3 - 1))
      (-8 + ∑' k : ℕ, aCoef k * ((2 * k + 3 : ℕ) : ℝ) * ((2 * k + 3 - 1 : ℕ) : ℝ) *
        y ^ (2 * k + 3 - 1 - 1)) y := hpoly.add (hasDerivAt_G1 y)
  rw [h.deriv]
  congr 1
  refine tsum_congr fun k => ?_
  have e1 : 2 * k + 3 - 1 - 1 = 2 * k + 1 := by omega
  have e2 : ((2 * k + 3 - 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by
    have : 2 * k + 3 - 1 = 2 * k + 2 := by omega
    rw [this]; push_cast; ring
  rw [e1, e2]
  push_cast
  ring



end AristotleS