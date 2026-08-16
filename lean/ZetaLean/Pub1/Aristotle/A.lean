import Mathlib

namespace AristotleA

noncomputable def rampPoly (x : ℝ) : ℝ :=
  35 * x ^ 4 - 84 * x ^ 5 + 70 * x ^ 6 - 20 * x ^ 7

noncomputable def eta (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else rampPoly x

namespace EtaAux

open Set Filter Topology

/-- Generic piecewise gluing: `0` on the left, the constant `c` on the right, `p` in between. -/
private noncomputable def pwg (c : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then c else p x

private lemma pwg_left {c : ℝ} {p : ℝ → ℝ} {x : ℝ} (h : x ≤ 0) : pwg c p x = 0 := if_pos h

private lemma pwg_right {c : ℝ} {p : ℝ → ℝ} {x : ℝ} (h : 1 ≤ x) : pwg c p x = c := by
  rw [pwg, if_neg (by linarith : ¬ x ≤ 0), if_pos h]

private lemma pwg_mid {c : ℝ} {p : ℝ → ℝ} {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    pwg c p x = p x := by
  rw [pwg, if_neg (not_le.2 h0), if_neg (not_le.2 h1)]

private lemma pwg_continuous {c : ℝ} {p : ℝ → ℝ} (hp : Continuous p) (h0 : p 0 = 0)
    (h1 : p 1 = c) : Continuous (pwg c p) := by
  have inner : Continuous fun x : ℝ => if (1 : ℝ) ≤ x then c else p x :=
    Continuous.if_le continuous_const hp continuous_const continuous_id
      (fun x hx => by rw [← hx, h1])
  have : Continuous fun x : ℝ => if x ≤ (0 : ℝ) then (0 : ℝ) else if (1 : ℝ) ≤ x then c else p x :=
    Continuous.if_le continuous_const inner continuous_id continuous_const
      (fun x hx => by rw [hx]; simp [h0])
  exact this

/-- Derivative of a piecewise glued function, when the polynomial part matches at the ends. -/
private lemma pwg_hasDerivAt {c : ℝ} {p q : ℝ → ℝ} (hpq : ∀ x, HasDerivAt p (q x) x)
    (hp0 : p 0 = 0) (hp1 : p 1 = c) (hq0 : q 0 = 0) (hq1 : q 1 = 0) (x : ℝ) :
    HasDerivAt (pwg c p) (pwg 0 q x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hev : pwg c p =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using pwg_left (le_of_lt hy)
    rw [pwg_left (le_of_lt hx)]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · subst hx
    have hL : HasDerivWithinAt (pwg c p) 0 (Iic (0 : ℝ)) 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) (Iic (0 : ℝ)) (0 : ℝ)).congr ?_ ?_
      · intro y hy; exact pwg_left hy
      · exact pwg_left le_rfl
    have hev : pwg c p =ᶠ[𝓝[Ici (0 : ℝ)] 0] p := by
      have h1 : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with y hy hy0
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ y from hy0) with h | h
      · rw [← h, pwg_left le_rfl, hp0]
      · exact pwg_mid h hy
    have hR : HasDerivWithinAt (pwg c p) 0 (Ici (0 : ℝ)) 0 := by
      have := ((hpq 0).hasDerivWithinAt (s := Ici (0:ℝ))).congr_of_eventuallyEq hev
        (by rw [pwg_left le_rfl, hp0])
      rwa [hq0] at this
    have hU := hL.union hR
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hU
    rwa [pwg_left (le_refl (0:ℝ))]
  · rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
    · have hev : pwg c p =ᶠ[𝓝 x] p := by
        filter_upwards [Ioo_mem_nhds hx hx1] with y hy using pwg_mid hy.1 hy.2
      rw [pwg_mid hx hx1]
      exact (hpq x).congr_of_eventuallyEq hev
    · subst hx1
      have hev : pwg c p =ᶠ[𝓝[Iic (1 : ℝ)] 1] p := by
        have h0 : Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) := Ioi_mem_nhds (by norm_num)
        filter_upwards [nhdsWithin_le_nhds h0, self_mem_nhdsWithin] with y hy hy1
        rcases eq_or_lt_of_le (show y ≤ (1:ℝ) from hy1) with h | h
        · rw [h, pwg_right le_rfl, hp1]
        · exact pwg_mid hy h
      have hL : HasDerivWithinAt (pwg c p) 0 (Iic (1 : ℝ)) 1 := by
        have := ((hpq 1).hasDerivWithinAt (s := Iic (1:ℝ))).congr_of_eventuallyEq hev
          (by rw [pwg_right le_rfl, hp1])
        rwa [hq1] at this
      have hR : HasDerivWithinAt (pwg c p) 0 (Ici (1 : ℝ)) 1 := by
        refine (hasDerivWithinAt_const (1 : ℝ) (Ici (1 : ℝ)) c).congr ?_ ?_
        · intro y hy; exact pwg_right hy
        · exact pwg_right le_rfl
      have hU := hL.union hR
      rw [Iic_union_Ici, hasDerivWithinAt_univ] at hU
      rwa [pwg_right (le_refl (1:ℝ))]
    · have hev : pwg c p =ᶠ[𝓝 x] fun _ => c := by
        filter_upwards [Ioi_mem_nhds hx1] with y hy using pwg_right (le_of_lt hy)
      rw [pwg_right (le_of_lt hx1)]
      exact (hasDerivAt_const x c).congr_of_eventuallyEq hev

private lemma hasDerivAt_quad (a b c d : ℝ) (i j k l : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => a * t ^ i - b * t ^ j + c * t ^ k - d * t ^ l)
      (a * (i * x ^ (i - 1)) - b * (j * x ^ (j - 1)) + c * (k * x ^ (k - 1))
        - d * (l * x ^ (l - 1))) x :=
  ((((hasDerivAt_pow i x).const_mul a).sub ((hasDerivAt_pow j x).const_mul b)).add
      ((hasDerivAt_pow k x).const_mul c)).sub ((hasDerivAt_pow l x).const_mul d)

private noncomputable def p1 (x : ℝ) : ℝ := 140 * x ^ 3 - 420 * x ^ 4 + 420 * x ^ 5 - 140 * x ^ 6
private noncomputable def p2 (x : ℝ) : ℝ := 420 * x ^ 2 - 1680 * x ^ 3 + 2100 * x ^ 4 - 840 * x ^ 5
private noncomputable def p3 (x : ℝ) : ℝ := 840 * x ^ 1 - 5040 * x ^ 2 + 8400 * x ^ 3 - 4200 * x ^ 4

private lemma hd_ramp (x : ℝ) : HasDerivAt rampPoly (p1 x) x := by
  have h := hasDerivAt_quad 35 84 70 20 4 5 6 7 x
  have : rampPoly = fun t : ℝ => 35 * t ^ 4 - 84 * t ^ 5 + 70 * t ^ 6 - 20 * t ^ 7 := rfl
  rw [this]
  convert h using 1
  simp only [p1]
  push_cast
  ring

private lemma hd_p1 (x : ℝ) : HasDerivAt p1 (p2 x) x := by
  have h := hasDerivAt_quad 140 420 420 140 3 4 5 6 x
  have : p1 = fun t : ℝ => 140 * t ^ 3 - 420 * t ^ 4 + 420 * t ^ 5 - 140 * t ^ 6 := rfl
  rw [this]
  convert h using 1
  simp only [p2]
  push_cast
  ring

private lemma hd_p2 (x : ℝ) : HasDerivAt p2 (p3 x) x := by
  have h := hasDerivAt_quad 420 1680 2100 840 2 3 4 5 x
  have : p2 = fun t : ℝ => 420 * t ^ 2 - 1680 * t ^ 3 + 2100 * t ^ 4 - 840 * t ^ 5 := rfl
  rw [this]
  convert h using 1
  simp only [p3]
  push_cast
  ring

private lemma cont_p3 : Continuous p3 := by
  unfold p3; fun_prop

private lemma step {n : ℕ} {f g : ℝ → ℝ} (h : ∀ x, HasDerivAt f (g x) x)
    (hg : ContDiff ℝ n g) : ContDiff ℝ ((n : ℕ) + 1 : ℕ) f := by
  have hd : deriv f = g := funext fun x => (h x).deriv
  have hcast : ((n : WithTop ℕ∞) + 1) = (((n + 1 : ℕ) : ℕ) : WithTop ℕ∞) := by
    push_cast; ring
  rw [← hcast, contDiff_succ_iff_deriv, hd]
  refine ⟨fun x => (h x).differentiableAt, ?_, hg⟩
  intro hw
  exact absurd hw (by simp)

private lemma eta_eq : eta = pwg 1 rampPoly := rfl

end EtaAux

open EtaAux

theorem eta_contDiff : ContDiff ℝ 3 eta := by
  have h3 : ContDiff ℝ (0 : ℕ) (pwg 0 p3) := by
    rw [Nat.cast_zero, contDiff_zero]
    exact pwg_continuous cont_p3 (by norm_num [p3]) (by norm_num [p3])
  have h2 : ContDiff ℝ (1 : ℕ) (pwg 0 p2) :=
    step (pwg_hasDerivAt hd_p2 (by norm_num [p2]) (by norm_num [p2]) (by norm_num [p3])
      (by norm_num [p3])) h3
  have h1 : ContDiff ℝ (2 : ℕ) (pwg 0 p1) :=
    step (pwg_hasDerivAt hd_p1 (by norm_num [p1]) (by norm_num [p1]) (by norm_num [p2])
      (by norm_num [p2])) h2
  have h0 : ContDiff ℝ (3 : ℕ) (pwg 1 rampPoly) :=
    step (pwg_hasDerivAt hd_ramp (by norm_num [rampPoly]) (by norm_num [rampPoly]) (by norm_num [p1])
      (by norm_num [p1])) h1
  rw [eta_eq]
  exact_mod_cast h0


end AristotleA